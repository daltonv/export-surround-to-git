#! /usr/bin/python3

# export-surround-to-git.py
#
# Python script to export history from Seapine Surround in a format parsable by `git fast-import`
#
# Copyright (C) 2014 Jonathan Elchison <JElchison@gmail.com>
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along
# with this program; if not, write to the Free Software Foundation, Inc.,
# 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

import sys
import argparse
import subprocess
import re
from threading import Event
import time
import datetime
import sqlite3
import os
import pathlib
import shutil
import math
import logging

from tqdm import tqdm

from src.sscm import SSCM

#
# globals
#

VERSION = "0.5.0"

# global "mark" number.  incremented before used, as 1 is minimum value allowed.
mark = 0

# local time zone
# TODO how detect this?  right now we assume EST.
timezone = "-0500"

# keeps track of snapshot name --> mark number pairing
tagDict = {}


# actions enumeration
class Actions:
    BRANCH_SNAPSHOT = 1
    BRANCH_BASELINE = 2
    FILE_MODIFY = 3
    FILE_DELETE = 4
    FILE_RENAME = 5
    FILE_MERGE = 6
    FOLDER_RENAME = 7


# similar to the SSCMFileAction enum from the API
class SSCMFileAction:
    AllActions = 0
    AddToRepository = 1
    AddToBranch = 2
    AddFromBranch = 3
    CheckIn = 4
    Rebase = 5
    RebaseWithMerge = 6
    Label = 8
    AttachToDefect = 9
    Delete = 10
    Undelete = 11
    PromoteToBranch = 12
    PromoteFromBranchWithMerge = 13
    PromoteFromBranchWithOutMerge = 14
    Share = 15
    BreakShare = 16
    BranchRenamed = 17
    BranchRemoved = 18
    BranchRestored = 19
    FileRenamed = 20
    RepoRenamed = 21
    BranchDestroyed = 22
    FileDestroyed = 23
    RepoDestroyed = 24
    BranchTypeChange = 25
    BranchOwnerChange = 26
    RollbackRebase = 27
    RollbackPromote = 28
    RollbackFile = 29
    CustomFieldChanged = 30
    StateChanged = 31
    UnLabel = 32
    AttachToTestCase = 33
    AttachToRequirement = 34
    DuplicateChanges = 35
    FileMoved = 36
    RepoMoved = 37
    AttachedToExternal = 38
    RollbackChanges = 39
    ExportRepoToMainline = 40
    FileShareRemoved = 41


# map based on SSCMFileAction enum from the API
actionMap = {
    SSCMFileAction.AllActions: None,
    SSCMFileAction.AddToRepository: Actions.FILE_MODIFY,
    SSCMFileAction.AddToBranch: Actions.FILE_MODIFY,  # This doesn't feel like a modify. TODO investigate
    SSCMFileAction.AddFromBranch: Actions.FILE_MODIFY,
    SSCMFileAction.CheckIn: Actions.FILE_MODIFY,
    SSCMFileAction.Rebase: None,
    SSCMFileAction.RebaseWithMerge: None,
    SSCMFileAction.Label: None,
    SSCMFileAction.AttachToDefect: None,
    SSCMFileAction.Delete: Actions.FILE_DELETE,
    SSCMFileAction.Undelete: None,
    SSCMFileAction.PromoteToBranch: None,
    SSCMFileAction.PromoteFromBranchWithMerge: Actions.FILE_MERGE,
    SSCMFileAction.PromoteFromBranchWithOutMerge: Actions.FILE_MERGE,
    SSCMFileAction.Share: None,
    SSCMFileAction.BreakShare: None,
    SSCMFileAction.BranchRenamed: None,
    SSCMFileAction.BranchRemoved: None,
    SSCMFileAction.BranchRestored: None,
    SSCMFileAction.FileRenamed: Actions.FILE_RENAME,
    SSCMFileAction.RepoRenamed: Actions.FOLDER_RENAME,
    SSCMFileAction.BranchDestroyed: None,
    SSCMFileAction.FileDestroyed: Actions.FILE_DELETE,
    SSCMFileAction.RepoDestroyed: None,
    SSCMFileAction.BranchTypeChange: None,
    SSCMFileAction.BranchOwnerChange: None,
    SSCMFileAction.RollbackRebase: Actions.FILE_MODIFY,
    SSCMFileAction.RollbackPromote: Actions.FILE_MODIFY,
    SSCMFileAction.RollbackFile: Actions.FILE_MODIFY,
    SSCMFileAction.CustomFieldChanged: None,
    SSCMFileAction.StateChanged: None,
    SSCMFileAction.UnLabel: None,
    SSCMFileAction.AttachToTestCase: None,
    SSCMFileAction.AttachToRequirement: None,
    SSCMFileAction.DuplicateChanges: None,
    SSCMFileAction.FileMoved: Actions.FILE_RENAME,
    SSCMFileAction.RepoMoved: Actions.FOLDER_RENAME,
    SSCMFileAction.AttachedToExternal: None,
    SSCMFileAction.RollbackChanges: None,
    SSCMFileAction.ExportRepoToMainline: None,
    SSCMFileAction.FileShareRemoved: None,
}


#
# classes
#


class DatabaseRecord:
    def __init__(self, tuple):
        self.init(
            tuple[0],
            tuple[1],
            tuple[2],
            tuple[3],
            tuple[4],
            tuple[5],
            tuple[6],
            tuple[7],
            tuple[8],
            tuple[9],
            tuple[10],
        )

    def init(
        self,
        timestamp,
        action,
        mainline,
        branch,
        path,
        origPath,
        version,
        author,
        comment,
        data,
        repo,
    ):
        self.timestamp = timestamp
        self.action = action
        self.mainline = mainline
        self.repo = repo
        self.branch = branch
        self.path = path
        self.origPath = origPath
        self.version = version
        self.author = author
        self.comment = comment
        self.data = data
        self.blob_mark = None

    def set_blob_mark(self, mark):
        self.blob_mark = mark

    def get_tuple(self):
        return (
            self.timestamp,
            self.action,
            self.mainline,
            self.branch,
            self.path,
            self.origPath,
            self.version,
            self.author,
            self.comment,
            self.data,
            self.repo,
        )


# Hold all information about a Surround SCM branch
class Branch:
    def __init__(self, name, repo, btype, old_names):
        self.name = name
        self.repo = repo
        self.btype = btype
        self.old_names = old_names

    def is_snapshot(self):
        if self.btype == "snapshot":
            return True
        else:
            return False

    def is_main(self):
        if self.btype == "main":
            return True
        else:
            return False


class SCMItem:
    def __init__(self, path: pathlib.PurePosixPath, is_folder):
        self.path = path
        self.is_folder = is_folder
        self.branches = set()

    def __str__(self):
        return str(self.path)


# Hold all information from a file event returned by sscmhist.exe
class FileEvent:
    def __init__(
        self,
        file: pathlib.PurePosixPath,
        branch,
        version,
        timestamp,
        action,
        data,
        author,
        comment,
        is_folder,
    ):
        self.file = file
        self.branch = branch
        self.version = version
        self.timestamp = timestamp
        self.action = action
        self.data = data
        self.author = author
        self.comment = comment
        self.is_folder = is_folder


class GitFastImport:
    def __init__(self):
        self.proc = subprocess.Popen(
            ["git", "fast-import", "--stats", "--export-marks=marks.txt"],
            stdin=subprocess.PIPE,
            stdout=None,
            stderr=subprocess.PIPE,
            cwd=os.getcwd(),
        )
        self.running = True

        rc = self.proc.poll()

        if rc:
            raise Exception("git fast-import crashed with: %s")

    def check_rc(self):
        rc = self.proc.poll()

        if rc:
            raise Exception(
                "git fast-import crashed with: %s"
                % self.proc.stderr.read().decode("utf-8")
            )

    def write(self, data):
        if not isinstance(data, bytes):
            raise Exception("git fast-import requires a bytes object as input")

        self.check_rc()

        self.proc.stdin.write(data)

    def flush_stdin(self):
        self.check_rc()

        self.proc.stdin.flush()

    def terminate(self):
        self.check_rc()

        outs, errs = self.proc.communicate(input=b"done")

        logging.info(errs.decode("utf-8"))

        if self.proc.returncode != 0:
            raise Exception("git fast-import crashed")


def find_branch_renames(branch, path, sscm: SSCM):
    output, stderrdata = sscm.branchhistory(branch, path, False)
    if stderrdata:
        raise Exception(stderrdata)

    # This regex only looks for the original name. We don't care about what it
    # was renamed to because we already know it ultimately becomes branch
    r = r"Renamed from ([^\\\/\*?]+?) to"
    mi = re.finditer(r, output, re.MULTILINE)

    old_names = []

    for m in mi:
        if m:
            logging.info(
                '[*] found branch "%s" had a previous name of "%s"'
                % (branch, m.group(1))
            )
            old_names.append(m.group(1))

    return old_names


def find_all_branches(mainline, root_branch, sscm: SSCM):
    branches, stderrdata = sscm.lsbranch(mainline)
    if stderrdata:
        raise Exception("[*] sscm error from cmd lsbranch: %s\n" % stderrdata)

    logging.info('[*] Looking for subbranches of "%s" ...' % root_branch)

    our_branches = {}
    our_old_names = {}
    root_repo = None

    # Group 1 is the branch path (not the repo)
    # Group 2 is the branch name (last part of the branch path)
    # Group 3 is the branch's repo
    # Group 4 is the branch's type
    r = r"(.+\/?([^\/]+)) \<(.*)> \((baseline|mainline|snapshot)\)"

    # Parse the branches and find the branches in the path provided
    for branch in branches:
        match = re.search(r, branch)
        branch_path = pathlib.PurePosixPath(match.group(1))
        found_match = False

        branch_name = branch_path.name
        branch_repo = match.group(3)
        branch_type = match.group(4)

        if branch_name == root_branch:
            found_match = True
            root_repo = branch_repo
            branch_type = "main"
        else:
            for parent in branch_path.parents:
                if parent.name == root_branch:
                    found_match = True
                    break

        if found_match:
            old_names = find_branch_renames(branch_name, branch_repo, sscm)

            found_branch_obj = Branch(branch_name, branch_repo, branch_type, old_names)

            our_branches[found_branch_obj.name] = found_branch_obj

            for old_name in old_names:
                # This shouldn't happen, but our branches list will always be
                # small so might as well check
                if old_name in our_old_names:
                    raise Exception("%s already in our_old_names" % old_name)
                our_old_names[old_name] = found_branch_obj

    if root_repo is None:
        raise Exception('Did not find branch "%s" in mainline' % branch)

    return our_branches, our_old_names, root_repo


def find_deleted_files(branch, repo, file_set, sscm: SSCM):
    # Use the property command to get the list of deleted files and repos.
    # Then use property command on each item to detect if it is a file or repo
    # If it is another repo recursively call our selves. Otherwise add the file
    # to the fileset.

    def get_property_output(branch, repo, item, sscm: SSCM):
        output, stderrdata = sscm.lsremoved(item, branch, repo, False)
        sub_item = None

        # Okay the Surround people really hate making parsable output for the
        # sscm command. We can't guarantee we didn't get the comment as part of
        # the item name, so we will try at most 5 times to search for the file
        # in it. Hopfully this is rare
        no_record = "Record not found; the selected item may not exist."
        if stderrdata == no_record:
            logging.debug(
                "find_deleted_files():could not detect file from the"
                " line:\n\t%s.\n\tAttempting to search for file..." % item
            )

            item_words = item.split(" ")
            for i in range(1, 10):
                sub_item = " ".join(item_words[:i])
                output, stderrdata = sscm.lsremoved(sub_item, branch, repo, False)

                if not stderrdata:
                    break

                logging.debug(
                    "find_deleted_files(): Still unsuccessful with " "sub_item: %s",
                    sub_item,
                )

            if stderrdata:
                raise Exception("[*] sscm error from cmd property: %s\n" % stderrdata)
        elif stderrdata:
            raise Exception("[*] sscm error from cmd property: %s\n" % stderrdata)

        return output, sub_item

    logging.info(
        "[*] Looking for deleted files in branch '%s' under '%s' ..." % (branch, repo)
    )

    output, sub_item = get_property_output(branch, repo, "/", sscm)

    deleted_files = output[output.index("Deleted files:") :]

    # Fancy regex to get the file names from the output
    # WARNING: Surround made a reliable parse impossible because they
    # they place comments about the deletion on the same line of the file.
    # We get around this by saying files can have at most 2 spaces between
    # regular characters. That should satisfy just about every file name
    # and honestly you deserve to lose the file if you are using more than
    # 2 spaces.
    r_find_file = r"^  (([\w\-\.\(\)\^] {0,2})+)"
    mi = re.finditer(r_find_file, deleted_files, re.MULTILINE)

    for m in mi:
        # Strip to account for any trailing spaces
        item = m.group(1).strip()

        # property will output files called "None" if it didn't find anything
        # for some reason.
        if item == "None":
            continue

        item_output, sub_item = get_property_output(branch, repo, item, sscm)

        if sub_item:
            item = sub_item

        if item_output.startswith("File name with path:"):
            fullPath = pathlib.PurePosixPath("%s/%s" % (repo, item))
            if fullPath not in file_set:
                file_set[fullPath] = SCMItem(fullPath, False)
            file_set[fullPath].branches.add(branch)
        else:
            repo_path = pathlib.PurePosixPath(repo) / pathlib.PurePosixPath(item)
            if repo_path not in file_set:
                file_set[repo_path] = SCMItem(repo_path, True)
            file_set[repo_path].branches.add(branch)
            find_deleted_files(branch, str(repo_path), file_set, sscm)

    return


def find_all_files_in_branches(branches, skip_delete_check, parse_snapshot, sscm: SSCM):
    file_set = {}
    for branch in branches:
        if branches[branch].is_snapshot() and not parse_snapshot:
            continue

        logging.info("[*] Looking for files in branch '%s' ..." % branch)

        lines, stderrdata = sscm.ls(branch, branches[branch].repo)
        if stderrdata:
            raise Exception("sscm error from cmd ls: %s\n" % stderrdata)

        # directories are listed on their own line, before a section of their
        # files the last line of the output just prints the number of files
        # found so we can ignore it.
        for line in lines[:-1]:
            if (line.strip())[0] == "-":
                # This is a comment and not a file
                continue
            elif line[0] != " ":
                lastDirectory = line
                # deleted files won't show in the ls command, so we have to
                # handle them here for each folder we find. We can skip this
                # part in the export phase because we don't care about deleted
                # files there. Always skip this check for snapshots as these
                # should be static tags.
                if not skip_delete_check and not branches[branch].is_snapshot():
                    find_deleted_files(branch, lastDirectory, file_set, sscm)

            elif line[1] != " ":
                # Extract the file name for this line
                # file = (line.strip().split())[0]
                end_file_index = line.find(" current")
                if end_file_index == -1:
                    end_file_index = line.find(" unknown status")
                if end_file_index == -1:
                    raise Exception("Couldn't find the filename in ls output")
                file = line[:end_file_index].strip()
                fullPath = pathlib.PurePosixPath("%s/%s" % (lastDirectory, file))

                if fullPath not in file_set:
                    file_set[fullPath] = SCMItem(fullPath, False)
                file_set[fullPath].branches.add(branch)

    return file_set


def is_snapshot_branch(branch, repo, sscm: SSCM):
    result, stderrdata = sscm.branchproperty(branch, repo, False)

    return result.find("snapshot") != -1


def get_file_rename(timestamp, file, repo, branch, sscm: SSCM):
    output, stderrdata = sscm.history(file, branch, repo, get_lines=False)
    if stderrdata:
        raise Exception("sscm error from cmd history: %s" % stderrdata)

    old = None
    new = None

    output = "\n".join(output.splitlines())

    # silly hack to get a timestruct from this that doesn't include a timezone
    timestamp_struct = time.localtime(timestamp)
    timestamp_str = time.strftime("%m/%d/%Y %I:%M %p", time.localtime(timestamp))
    timestamp_struct = time.strptime(timestamp_str, "%m/%d/%Y %I:%M %p")

    # Group 1 = old name
    # Group 2 = new name
    # Group 3 = timestamp
    r = r"from \[([\S ]+)\] to \[([\S ]+)\].*\n{1,2}.*?(\d{1,2}\/\d{1,2}\/\d{4} \d{1,2}:\d{1,2} (AM|PM))"
    mi = re.finditer(r, output)

    for m in mi:
        rename_timestamp_str = m.group(3)
        renamed_timestamp_struct = time.strptime(
            rename_timestamp_str, "%m/%d/%Y %I:%M %p"
        )
        if renamed_timestamp_struct == timestamp_struct:
            old = m.group(1)
            new = m.group(2)
            break

    if (not old) and (not new):
        full_file_path = repo / file
        raise Exception("Could not find file rename info for %s" % full_file_path)

    if old.lower == new.lower:
        logging.warning(
            '[*] Warning "%s" has a rename in "%s" that is just a case change\n'
            % (file, branch)
        )

    return (old, new)


def round_timestamp(timestamp, round_target):
    # round the seconds up to the nearest 5 out of the time as it is too
    # precise. Many file changes only differ by a second as Surround
    # alters each file as part of a group check in operation
    time_struct = time.localtime(timestamp)

    timestamp_seconds = time_struct.tm_sec
    rounded_seconds = round_target * int(math.ceil(timestamp_seconds / round_target))

    time_string = time.strftime(("%Y%m%d%H:%M:" + str(rounded_seconds)), time_struct)
    new_time_struct = time.strptime(time_string, "%Y%m%d%H:%M:%S")

    rounded_timestamp = int(time.mktime(new_time_struct))

    return rounded_timestamp


# TODO the WHERE paramaters on this are probably ridiculous. I should update the DB
# to have a better primary key
def update_db_folder_renames(database):
    c0 = database.cursor()
    c1 = database.cursor()
    c2 = database.cursor()
    c3 = database.cursor()

    # Get all folder rename operations and loop through them
    c0.execute(
        """SELECT * FROM operations
                        WHERE action == 7
                        ORDER BY timestamp ASC"""
    )
    while frename := c0.fetchone():
        rename_op = DatabaseRecord(frename)
        old_folder = rename_op.origPath
        new_folder = rename_op.data
        sub_files_found = False

        logging.info(
            f"[*] Updating origPath for all files affected by the "
            f"rename of {old_folder} to {new_folder}"
        )

        # Now get a list of all files under this folder that is being renamed
        # and loop through it
        c1.execute(
            f'''SELECT DISTINCT path FROM operations
                            WHERE path like '{rename_op.path}/%' and
                            timestamp < {rename_op.timestamp} and
                            branch == "{rename_op.branch}"'''
        )
        while record := c1.fetchone():
            file_path = pathlib.PurePosixPath(record[0])
            sub_files_found = True

            # Loop through the previous operations on this file and update
            # their origPaths
            c2.execute(
                f"""SELECT * FROM operations
                                WHERE path == '{file_path}' and
                                      timestamp < {rename_op.timestamp}
                                ORDER BY timestamp DESC"""
            )
            while sub_record := c2.fetchone():
                sub_record_op = DatabaseRecord(sub_record)
                old_orig_path = None
                file_rename_data = None

                if sub_record_op.origPath:
                    old_orig_path = pathlib.PurePosixPath(sub_record_op.origPath)
                if sub_record_op.data:
                    file_rename_data = pathlib.PurePosixPath(sub_record_op.data)

                if old_orig_path:
                    # If we already have an origPath update the origPath to use
                    # the old_folder.
                    new_orig_path = old_folder / old_orig_path.relative_to(new_folder)
                else:
                    # If we don't have an origPath we just update the origPath
                    # from the file_path
                    new_orig_path = old_folder / file_path.relative_to(new_folder)

                if (
                    sub_record_op.action == Actions.FILE_RENAME
                    or sub_record_op.action == Actions.FOLDER_RENAME
                ):
                    # Rename operations are special. We need update both
                    # origPath and data here.
                    new_rename_data = old_folder / file_rename_data.relative_to(
                        new_folder
                    )

                    update_frename_tuple = (
                        str(new_orig_path),
                        str(new_rename_data),
                        sub_record_op.action,
                        rename_op.mainline,
                        rename_op.branch,
                        str(file_path),
                        sub_record_op.timestamp,
                    )
                    c3.execute(
                        """UPDATE operations SET origPath=?, data=?
                                        WHERE action=? AND
                                              mainline=? AND
                                              branch=? AND
                                              path=? AND
                                              timestamp == ?""",
                        update_frename_tuple,
                    )
                else:
                    # Update the origPath for this record to be our new
                    # origPAth that takes the folder rename into account
                    update_tuple = (
                        str(new_orig_path),
                        sub_record_op.action,
                        sub_record_op.mainline,
                        sub_record_op.branch,
                        str(file_path),
                        sub_record_op.timestamp,
                    )
                    c3.execute(
                        """UPDATE operations SET origPath=?
                                        WHERE action=? AND
                                              mainline=? AND
                                              branch=? AND
                                              path=? AND
                                              timestamp==?""",
                        update_tuple,
                    )

        if not sub_files_found:
            logging.info(
                "[*] \tThis is a rename operation on an empty folder. Removing from DB."
            )
            c2.execute(
                """DELETE FROM operations
                            WHERE timestamp=? AND
                                    action=? AND
                                    mainline=? AND
                                    branch=? AND
                                    path=? AND
                                    origPath=? AND
                                    version=? AND
                                    author=? AND
                                    comment=? AND
                                    data=? AND
                                    repo=?""",
                rename_op.get_tuple(),
            )
            if c2.rowcount != 1:
                raise Exception(
                    f"Deletion or {rename_op.path} rename record unsuccessful"
                )

    database.commit()


def add_operation_to_db(
    event: Event, branches, branch_renames, main_branch, repo, database, sscm
):
    timestamp = round_timestamp(event.timestamp, 10)
    author = event.author
    comment = event.comment
    branch = event.branch
    # The below variables could get rewritten depending on the action
    path = str(event.file)
    action = actionMap[event.action]
    version = event.version
    origPath = None
    data = None

    if (
        event.action == SSCMFileAction.FileMoved
        or event.action == SSCMFileAction.FileRenamed
        or event.action == SSCMFileAction.RepoRenamed
        or event.action == SSCMFileAction.RepoMoved
    ):

        if event.is_folder:
            file = "/"
            folder = event.file
        else:
            file = event.file.name
            folder = event.file.parent

        # Unfortunately the API only tells us a rename happened and not
        # what the rename was. To get these names we use a helper function
        # that calls 'sscm history'. Finding just the rename info is
        # relatively safe by parsing the output with regex.
        (oldName, newName) = get_file_rename(
            event.timestamp, file, folder, event.branch, sscm
        )
        newName_p = pathlib.PurePosixPath(newName)
        oldName_p = pathlib.PurePosixPath(oldName)

        if event.action == SSCMFileAction.FileRenamed:
            origPath = str(folder / oldName_p)
            data = str(folder / newName_p)
        elif event.action == SSCMFileAction.RepoRenamed:
            origPath = str((event.file.parent / oldName_p))
            data = str((event.file.parent / newName_p))
        elif event.action == SSCMFileAction.RepoMoved:
            origPath = str(oldName_p / event.file.name)
            data = str(newName_p / event.file.name)
        else:
            origPath = str(oldName_p / file)
            data = str(newName_p / file)

    elif event.action == SSCMFileAction.AddToBranch:
        # Special actions for branch operations
        data = event.data

        # If the destination branch was deleted ignore this operation as we
        # wont have the data to complete it in the export phase,
        # but if the source branch was just renamed fixup the name
        if data not in branches and data not in branch_renames:
            return None
        elif data not in branches and data in branch_renames:
            data = branch_renames[data].name

        if branches[data].is_snapshot():
            action = Actions.BRANCH_SNAPSHOT
        else:
            action = Actions.BRANCH_BASELINE

        # The path for branch operations is the root of the branch
        path = str(branches[data].repo)

        # Manually set these to ensure no duplicates in the DB
        # TODO: Maybe consider a better primary key to avoid this
        version = 0
        origPath = "NULL"

    elif event.action == SSCMFileAction.AddFromBranch:
        # In case we are parsing snapshots too ignore the AddFromBranch
        # commands as these commands are already parsed by the AddToBranch from
        # source branch
        if branches[event.branch].is_snapshot():
            return None

    elif (
        event.action == SSCMFileAction.PromoteFromBranchWithMerge
        or event.action == SSCMFileAction.PromoteFromBranchWithOutMerge
    ):
        # Special actions for merge operations
        data = event.data

        # If the source branch was deleted treat as a modify, but if the source
        # branch was just renamed fixup the name
        if data not in branches and data not in branch_renames:
            action = Actions.FILE_MODIFY
        elif data not in branches and data in branch_renames:
            data = branch_renames[data].name

        # If the source branch is a snapshot, well this is just silly.
        # Snapshots should not modify anything and we can have a tag as a merge
        # point, so for now just treat this as an in place modify.
        # TODO: maybe stop this and handle correctly in export phase.
        if branches[data].is_snapshot():
            action = Actions.FILE_MODIFY

    operation = DatabaseRecord(
        (
            timestamp,
            action,
            main_branch,
            branch,
            path,
            origPath,
            version,
            author,
            comment,
            data,
            str(repo),
        )
    )

    add_record_to_database(operation, database)


def find_all_file_events(branch, path, is_folder, sscm: SSCM):
    events = []

    if is_folder:
        file = "/"
        folder = path
    else:
        file = path.name
        folder = path.parent

    output, stderrdata = sscm.customhistory(file, branch, folder)
    if stderrdata:
        if stderrdata == (
            "sscm_file_history failed: Record not found; the "
            "selected item may not exist."
        ):
            logging.warning(
                '[*] sscmhistory could not find "%s" in branch "%s"'
                % ((folder / file), branch)
            )
            return events
        else:
            raise Exception("sscmhistory error: %s\n" % stderrdata)

    if not output:
        return events

    # join the lines again so we can split on the comment delimiter Add a final
    # newline as the last comment delimiter won't have one.
    output = "\n".join(output) + "\n"

    file_events = output.split("--END_COMMENT--\n")

    for ev in file_events:
        # the last operation might be empty due to how we split above. so we
        # can skip it.
        if not ev:
            continue

        ev_lines = ev.splitlines()

        # Get output from sscm cli
        version = int(ev_lines[0])
        timestamp = int(ev_lines[1])
        action = int(ev_lines[2])
        data = ev_lines[3]
        author = ev_lines[4]
        comment = "\n".join(ev_lines[5:])

        event = FileEvent(
            path, branch, version, timestamp, action, data, author, comment, is_folder
        )

        # We only care about rename events for folders
        if is_folder and (
            event.action != SSCMFileAction.RepoMoved
            and event.action != SSCMFileAction.RepoRenamed
        ):
            continue

        events.append(event)

    return events


def find_folder_renames(branches, renamed_folders, sscm: SSCM):
    logging.info("[*] Finding folder renames...")

    count = 0

    for branch in branches:
        if branches[branch].is_snapshot():
            continue

        output, stderrdata = sscm.history(
            "/", branch, branches[branch].repo, recursive=True, get_lines=False
        )
        if stderrdata:
            raise Exception(stderrdata)

        r = r"Repository: ([^\r\n]*)\r?\n Rename"
        mi = re.finditer(r, output)

        for m in mi:
            renamed_repo = pathlib.PurePosixPath(m.group(1))
            if renamed_repo not in renamed_folders:
                renamed_folders[renamed_repo] = SCMItem(renamed_repo, True)
            renamed_folders[renamed_repo].branches.add(branch)
            count += 1

    logging.info("[*] Found %d folder(s) that were renamed" % count)


def create_database():
    # database file is created in cwd
    name = (
        datetime.datetime.fromtimestamp(time.time()).strftime("%Y-%m-%d-%H-%M-%S")
        + ".db"
    )
    database = sqlite3.connect(name)
    c = database.cursor()
    # we intentionally avoid duplicates via the PRIMARY KEY
    c.execute(
        """CREATE TABLE operations (timestamp INTEGER NOT NULL, action INTEGER NOT NULL, mainline TEXT NOT NULL, branch TEXT NOT NULL, path TEXT, origPath TEXT, version INTEGER, author TEXT, comment TEXT, data TEXT, repo TEXT NOT NULL, PRIMARY KEY(action, mainline, branch, path, origPath, version, author, data))"""
    )
    database.commit()
    return database


def add_record_to_database(record, database):
    c = database.cursor()
    try:
        c.execute(
            """INSERT INTO operations VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            record.get_tuple(),
        )
    except sqlite3.IntegrityError:
        # TODO is there a better way to detect duplicates?  is sqlite3.IntegrityError too wide a net?
        # logging.debug("Detected duplicate record %s" % str(record.get_tuple()))
        pass
    database.commit()

    if record.action == Actions.FILE_RENAME:
        c.execute(
            """UPDATE operations SET origPath=? WHERE (action=? or action=?) AND mainline=? AND branch=? AND path=? AND (origPath IS NULL OR origPath='') AND version<=?""",
            (
                record.origPath,
                Actions.FILE_MODIFY,
                Actions.FILE_MERGE,
                record.mainline,
                record.branch,
                record.path,
                record.version,
            ),
        )
        database.commit()


def cmd_parse(mainline, main_branch, database, sscm, parse_snapshot):
    logging.info("[+] Beginning parse phase...")

    branches, branch_renames, repo = find_all_branches(mainline, main_branch, sscm)

    filesToWalk = find_all_files_in_branches(branches, False, parse_snapshot, sscm)
    find_folder_renames(branches, filesToWalk, sscm)

    for branch in branches:
        # Skip snapshot branches
        if not parse_snapshot and branches[branch].is_snapshot():
            continue

        logging.info("[*] Parsing branch '%s' ..." % branch)

        for fullPathWalk in tqdm(filesToWalk, dynamic_ncols=True):
            if branch not in filesToWalk[fullPathWalk].branches:
                continue

            logging.debug("[*] \tParsing file '%s' ..." % fullPathWalk)

            is_folder = filesToWalk[fullPathWalk].is_folder

            events = find_all_file_events(branch, fullPathWalk, is_folder, sscm)
            for ev in events:
                add_operation_to_db(
                    ev, branches, branch_renames, main_branch, repo, database, sscm
                )

    logging.info("[+] Updating the database with folder rename info...")
    update_db_folder_renames(database)

    logging.info("[+] Parse phase complete")


# Surround has different naming rules for branches than Git does for branches/tags.
# this function performs a one-way translation from Surround to Git.
def translate_branch_name(name):
    #
    # pre-processing
    #

    # 6. cannot contain multiple consecutive slashes
    # replace multiple with single
    name = re.sub(r"[\/]+", r"/", name)

    #
    # apply rules from `git check-ref-format`
    #

    # 1. no slash-separated component can begin with a dot .
    name = name.replace("/.", "/_")
    # 1. no slash-separated component can end with the sequence .lock
    name = re.sub(r"\.lock($|\/)", r"_lock", name)
    # 3. cannot have two consecutive dots ..  anywhere
    name = re.sub(r"[\.]+", r"_", name)
    # 4. cannot have ASCII control characters (i.e. bytes whose values are lower than \040, or \177 DEL) anywhere
    for char in name:
        if char < "\040" or char == "\177":
            # TODO I'm not sure that modifying 'char' here actually modifies 'name'.  Check this and fix if necessary.
            char = "_"
    # 4. cannot have space anywhere.
    # replace with dash for readability.
    name = name.replace(" ", "-")
    # 4. cannot have tilde ~, caret ^, or colon : anywhere
    # 5. cannot have question-mark ?, asterisk *, or open bracket [ anywhere
    # 10. cannot contain a \
    name = re.sub(r"[\~\^\:\?\*\[\\]+", r"_", name)
    # 6. cannot begin or end with a slash /
    # 7. cannot end with a dot .
    name = re.sub(r"(^[\/]|[\/\.]$)", r"_", name)
    # 8. cannot contain a sequence @{
    name = name.replace("@{", "__")
    # 9. cannot be the single character @
    if name == "@":
        name = "_"

    return name


# this is the function that prints most file data to the stream
def print_blob_for_file(
    branch, fullPath, sscm: SSCM, gitfi, scratchDir, timestamp=None
):
    global mark

    time_struct = time.localtime(timestamp)
    time_string = time.strftime("%Y%m%d%H:%M:%S", time_struct)

    path = fullPath.parent
    file = fullPath.name
    localPath = scratchDir / file
    if localPath.is_file():
        localPath.unlink()

    if timestamp:
        # get specified version. You would think the -v option would get the
        # version of the file you want, but this does not work for deleted files.
        # we need to use the time stamp with -s
        time_struct = time.localtime(timestamp)
        time_string = time.strftime("%Y%m%d%H:%M:%S", time_struct)
    else:
        time_string = None

    sscm.get(file, branch, path, scratchDir.name, time_string)

    if not localPath.is_file():
        logging.warning(
            "[+] Failed to download file %s from branch %s. "
            "Trying again...\n" % (fullPath, branch)
        )
        time.sleep(3)
        sscm.get(file, branch, path, scratchDir.name, time_string)

        if not localPath.is_file():
            raise Exception(
                "File %s from branch %s could not be downloaded "
                "with timestamp %s" % (fullPath, branch, time_string)
            )

    # git fast-import is very particular about the format of the blob command.
    # The data must be given in raw bytes for it to parse the files correctly.
    mark = mark + 1
    gitfi.write(b"blob\n")
    gitfi.write(b"mark :%d\n" % mark)
    line = localPath.read_bytes()
    gitfi.write(b"data %d\n" % len(line))
    gitfi.write(line)
    gitfi.write(b"\n")
    gitfi.flush_stdin()
    return mark


# Surround comments don't have headers so, we need to fixup up the comment
# to have a header of the appropriate length for git.
def fixup_comment_header(comment):
    comment = comment.strip()
    git_header_len = 72
    fixed_comment = ""

    if len(comment) < git_header_len:
        comment_header = comment
        comment_body = ""
    else:
        comment_header = comment[:git_header_len]
        comment_body = comment[git_header_len:]

    # best case scenario a line break occurs before the max git header len
    if (i := comment_header.find("\n")) != -1:
        # This means we are already a legal git comment
        if i != (len(comment_header) - 1) and comment_header[i + 1] == "\n":
            fixed_comment = comment_header + comment_body
        else:
            fixed_comment = (
                comment_header[:i] + "\n" + comment_header[i:] + comment_body
            )
    # our whole comment is enough to be the header
    elif not comment_body:
        fixed_comment = comment_header
    # if not we can break the comment at the end of the last sentence before the limit
    elif (i := comment_header[::-1].find(".")) != -1:
        fixed_comment = (
            comment_header[: (git_header_len - i)]
            + "\n\n"
            + comment_header[(git_header_len - i) :].lstrip()
            + comment_body
        )
    # If there are no periods we must break on the last space between
    # words before the limit
    elif (i := comment_header[:-3][::-1].find(" ")) != -1:
        fixed_comment = (
            comment_header[: (git_header_len - i - 3)].rstrip()
            + "...\n\n"
            + comment_header[(git_header_len - i - 3) :].lstrip()
            + comment_body
        )
    # Finally if a caveman is writing the comment and used no spaces we
    # force a cut off at the header limit
    else:
        fixed_comment = (
            comment_header[:git_header_len] + "\n\n" + comment_header[git_header_len:]
        )

    return fixed_comment


def process_combined_commit(
    record_group, sscm, gitfi, email_domain, scratchDir, default_branch, merge=False
):
    global mark
    unique_comments = {}

    for record in record_group:
        if record.action == Actions.FILE_MODIFY or record.action == Actions.FILE_MERGE:
            blob_mark = print_blob_for_file(
                record.branch,
                pathlib.PurePosixPath(record.path),
                sscm,
                gitfi,
                scratchDir,
                record.timestamp,
            )
            record.set_blob_mark(blob_mark)
        if record.comment:
            if record.comment not in unique_comments:
                unique_comments[record.comment] = []
            full_path = pathlib.PurePosixPath(record.path)
            repo = pathlib.PurePosixPath(record.repo)
            path = full_path.relative_to(repo)
            unique_comments[record.comment].append(path)

    mark = mark + 1
    branch = record.branch
    if branch == record.mainline:
        branch = default_branch
    gitfi.write(
        ("commit refs/heads/%s\n" % translate_branch_name(branch)).encode("utf-8")
    )
    gitfi.write(("mark :%d\n" % mark).encode("utf-8"))
    email = ""
    if email_domain:
        email = record_group[0].author + "@" + email_domain
    else:
        email = record_group[0].author
    gitfi.write(
        (
            "author %s <%s> %s %s\n"
            % (record_group[0].author, email, record_group[0].timestamp, timezone)
        ).encode("utf-8")
    )
    gitfi.write(
        (
            "committer %s <%s> %s %s\n"
            % (record_group[0].author, email, record_group[0].timestamp, timezone)
        ).encode("utf-8")
    )
    if len(unique_comments):
        full_comment = ""
        for comment, files in unique_comments.items():
            full_comment += comment + "\n"
            # If we're combining multiple comments lets tell the user which
            # file(s) each comment is associated with
            if len(unique_comments) > 1:
                for file in files:
                    full_comment += "^ %s\n" % file
                full_comment += "\n"

        encoded_comment = fixup_comment_header(full_comment).encode("utf-8")
        gitfi.write(b"data %d\n" % len(encoded_comment))
        gitfi.write(encoded_comment)
    else:
        gitfi.write(b"data 0\n")

    if merge:
        merge_branch = record.data
        if merge_branch == record.mainline:
            merge_branch = default_branch
        gitfi.write(
            ("merge refs/heads/%s\n" % translate_branch_name(merge_branch)).encode(
                "utf-8"
            )
        )

    for record in record_group:
        # fixup the paths so the root of the git repo matches the root
        # of the scm repo originally passed in
        full_path = pathlib.PurePosixPath(record.path)
        repo = pathlib.PurePosixPath(record.repo)
        path = full_path.relative_to(repo)
        if record.origPath and record.origPath != "NULL":
            full_origPath = pathlib.PurePosixPath(record.origPath)
            origPath = full_origPath.relative_to(repo)

        if record.action == Actions.FILE_MODIFY or record.action == Actions.FILE_MERGE:
            if record.origPath and record.origPath != "NULL":
                # looks like there was a previous rename.  use the original name.
                gitfi.write(
                    ('M 100644 :%d "%s"\n' % (record.blob_mark, origPath)).encode(
                        "utf-8"
                    )
                )
            else:
                # no previous rename.  good to use the current name.
                gitfi.write(
                    ('M 100644 :%d "%s"\n' % (record.blob_mark, path)).encode("utf-8")
                )
        elif record.action == Actions.FILE_DELETE:
            # If a folder was renamed after the deletion the deleted entry of
            # the file will show up in the new location. However in the parse
            # phase we set the origPath here and can delete the last real
            # location.
            if record.origPath and record.origPath != "NULL":
                gitfi.write(('D "%s"\n' % origPath).encode("utf-8"))
            else:
                gitfi.write(('D "%s"\n' % path).encode("utf-8"))
        elif (
            record.action == Actions.FILE_RENAME
            or record.action == Actions.FOLDER_RENAME
        ):
            # NOTE we're not using record.path here, as there may have been multiple renames in the file's history
            full_data_path = pathlib.PurePosixPath(record.data)
            data = full_data_path.relative_to(repo)
            gitfi.write(('R "%s" "%s"\n' % (origPath, data)).encode("utf-8"))
        else:
            raise Exception("Unknown record action")

    # Flush our buffer. We are going to print a lot, so this helps everything
    # stay in the right order.
    gitfi.flush_stdin()


def process_database_record_group(
    c, sscm, scratchDir, default_branch, gitfi, email_domain=None
):
    global mark

    # will contain a list of the MODIFY, DELETE, and RENAME records in this
    # group to be processed later
    normal_records = []

    # Any record that took part of a merge will be placed here. The merges are
    # seperated by the branch merged from. Its unlikely we actually have two
    # diffrent merges from different branches in the same record group, but
    # it is possible so it must be handled
    merge_records = {}

    while r := c.fetchone():
        record = DatabaseRecord(r)

        if record.action == Actions.BRANCH_SNAPSHOT:
            # the basic idea here is to use a "TAG_FIXUP" branch, as recommended in the manpage for git-fast-import.
            # this is necessary since Surround version-controls individual files, and Git controls the state of the entire branch.
            # the purpose of this commit it to bring the branch state to match the snapshot exactly.

            gitfi.write(b"reset TAG_FIXUP\n")
            parentBranch = record.branch
            if record.branch == record.mainline:
                parentBranch = default_branch
            gitfi.write(
                ("from refs/heads/%s\n" % translate_branch_name(parentBranch)).encode(
                    "utf-8"
                )
            )

            # get all files contained within snapshot
            branches_dict = {}
            # TODO: this is kind of hack because the parse phase uses a dict
            # of objs. Maybe make this cleaner? IDK its not really unsafe.
            branch_obj = Branch(record.data, record.path, "snapshot", None)
            branches_dict[record.data] = branch_obj
            files = find_all_files_in_branches(branches_dict, True, True, sscm)
            startMark = None
            for file in files:
                blobMark = print_blob_for_file(
                    record.data, file, sscm, gitfi, scratchDir
                )
                if not startMark:
                    # keep track of what mark represents the start of this snapshot data
                    startMark = blobMark

            mark = mark + 1
            gitfi.write(b"commit TAG_FIXUP\n")
            gitfi.write(b"mark :%d\n" % mark)
            email = ""
            if email_domain:
                email = record.author + "@" + email_domain
            else:
                email = record.author
            gitfi.write(
                (
                    "author %s <%s> %s %s\n"
                    % (record.author, email, record.timestamp, timezone)
                ).encode("utf-8")
            )
            gitfi.write(
                (
                    "committer %s <%s> %s %s\n"
                    % (record.author, email, record.timestamp, timezone)
                ).encode("utf-8")
            )
            if record.comment:
                comment = fixup_comment_header(record.comment).encode("utf-8")
                gitfi.write(b"data %d\n" % len(comment))
                gitfi.write(comment)
                gitfi.write(b"\n")
            else:
                gitfi.write(b"data 0\n")

            # 'deleteall' tells Git to forget about previous branch state
            gitfi.write(b"deleteall\n")
            # replay branch state from above-recorded marks
            iterMark = startMark
            for filePath in files:
                # Remove the repo from the file path
                repo = pathlib.PurePosixPath(record.repo)
                file = filePath.relative_to(repo)
                gitfi.write(("M 100644 :%d %s\n" % (iterMark, file)).encode("utf-8"))
                iterMark = iterMark + 1
            if iterMark != mark:
                raise Exception(
                    "Marks fell out of sync while tagging '%s'." % record.data
                )

            # finally, tag our result
            gitfi.write(
                ("tag %s\n" % translate_branch_name(record.data)).encode("utf-8")
            )
            gitfi.write(b"from TAG_FIXUP\n")
            gitfi.write(
                (
                    "tagger %s <%s> %s %s\n"
                    % (record.author, record.author, record.timestamp, timezone)
                ).encode("utf-8")
            )
            if record.comment:
                comment = record.comment.encode("utf-8")
                gitfi.write(b"data %d\n" % len(comment))
                gitfi.write(comment)
                gitfi.write(b"\n")
            else:
                gitfi.write(b"data 0\n")

            # save off the mapping between the tag name and the tag mark
            tagDict[record.data] = mark

        elif record.action == Actions.BRANCH_BASELINE:
            # the idea hers is to simply 'reset' to create our new branch, the name of which is contained in the 'data' field

            gitfi.write(
                ("reset refs/heads/%s\n" % translate_branch_name(record.data)).encode(
                    "utf-8"
                )
            )
            parentBranch = record.branch
            if record.branch == record.mainline:
                parentBranch = default_branch
            if is_snapshot_branch(parentBranch, str(record.path), sscm):
                # Git won't let us refer to the tag directly (maybe this will be fixed in a future version).
                # for now, we have to refer to the associated tag mark instead.
                # (if this is fixed in the future, we can get rid of tagDict altogether)
                gitfi.write(b"from :%d\n" % tagDict[parentBranch])
            else:
                # baseline branch
                parentBranch = translate_branch_name(parentBranch)
                gitfi.write(("from refs/heads/%s\n" % parentBranch).encode("utf-8"))

        elif (
            record.action == Actions.FILE_MODIFY
            or record.action == Actions.FILE_DELETE
            or record.action == Actions.FILE_RENAME
            or record.action == Actions.FOLDER_RENAME
        ):
            # this is the usual case
            # We process these at the end as we need to loop through the list
            # several times to get the print order right
            normal_records.append(record)

        elif record.action == Actions.FILE_MERGE:
            if record.data not in merge_records:
                merge_records[record.data] = []
            merge_records[record.data].append(record)

        else:
            raise Exception("Unknown record action")

        # Flush our buffer. We are going to print a lot, so this helps everything
        # stay in the right order.
        gitfi.flush_stdin()

    # Here we are going to combine all the record groups into a single commits
    #
    # We want to process merge commits first because Surround handles merges with
    # with renames in two steps. First the merge of the content and then a rename.
    # The rename needs to happen after or we get both names of the file after
    # merge
    for merge in merge_records:
        process_combined_commit(
            merge_records[merge],
            sscm,
            gitfi,
            email_domain,
            scratchDir,
            default_branch,
            True,
        )

    if len(normal_records):
        process_combined_commit(
            normal_records, sscm, gitfi, email_domain, scratchDir, default_branch, False
        )


def cmd_export(database, email_domain, sscm, default_branch):
    logging.info("[+] Beginning export phase...")

    # Create the git fast-import process
    gitfi = GitFastImport()

    # temp directory in cwd, holds files fetched from Surround
    scratchDir = pathlib.Path.cwd() / "scratch"

    if not os.path.exists(scratchDir):
        os.mkdir(scratchDir)

    # Group the database by timestamp, branch and author. This will allow us to find
    # each unique timestamp for each branch (multiple branches can have
    # actions performed at the same time, and a checking aught to have only one author).
    # We want to then go through each operation in these groups as we will group
    # all Surround actions in these timestamps as a single commit
    c1 = database.cursor()
    c2 = database.cursor()
    c1.execute(
        """SELECT timestamp, branch FROM operations GROUP BY timestamp, branch, author ORDER BY timestamp ASC"""
    )

    count = 0
    while record := c1.fetchone():
        c2.execute(
            "SELECT * FROM operations WHERE timestamp == %d AND branch == '%s' ORDER BY action ASC"
            % (record[0], record[1])
        )
        process_database_record_group(
            c2, sscm, scratchDir, default_branch, gitfi, email_domain
        )
        count = count + 1
        # print progress every 5 operations
        if count % 5 == 0 and record:
            # just print the date we're currently servicing
            logging.info(
                "progress %s" % time.strftime("%Y-%m-%d", time.localtime(record[0]))
            )

    # Make a new tag at the end to show the last surround commit
    gitfi.write(b"tag surround-import\n")
    gitfi.write(("from refs/heads/%s\n" % default_branch).encode("utf-8"))
    gitfi.write(
        (
            "tagger %s <%s> %d %s\n"
            % (
                "export-surround-to-git",
                "export-surround-to-git",
                int(time.time()),
                timezone,
            )
        ).encode("utf-8")
    )
    comment = (
        "Last Surround SCM commit\n"
        "\n"
        "This is the last commit from the Surround SCM version of this "
        "project\n"
    ).encode("utf-8")
    gitfi.write(b"data %d\n" % len(comment))
    gitfi.write(comment)
    gitfi.write(b"\n")
    gitfi.flush_stdin()

    gitfi.terminate()

    # cleanup
    try:
        shutil.rmtree(scratchDir)
    except OSError:
        pass
    if os.path.isfile("./.git/TAG_FIXUP"):
        # TODO why doesn't this work?  is this too early since we're piping our output, and then `git fast-import` just creates it again?
        os.remove("./.git/TAG_FIXUP")

    logging.info(
        "[+] Export complete.  Your new Git repository is ready to use.\nDon't forget to run `git repack` at some future time to improve data locality and access performance."
    )


def cmd_verify(mainline, path):
    # TODO verify that all Surround baseline branches are identical to their Git counterparts
    # TODO verify that all Surround snapshot branches are identical to their Git counterparts
    # should be able to do this without database
    pass


def handle_command(parser):
    args = parser.parse_args()

    sscm = SSCM(args.install, args.host, args.port, args.username, args.password)

    # setup logger
    fileHandler = logging.FileHandler("export.log", mode="w")
    fileHandler.setLevel(logging.DEBUG)

    stdoutHandler = logging.StreamHandler(sys.stdout)
    stdoutHandler.setLevel(logging.INFO)

    logging.basicConfig(
        level=logging.DEBUG, format="%(message)s", handlers=[fileHandler, stdoutHandler]
    )

    if args.command == "parse" and args.mainline and args.branch:
        database = create_database()
        cmd_parse(args.mainline, args.branch, database, sscm, args.snapshot)
    elif args.command == "export" and args.database:
        database = sqlite3.connect(args.database)
        cmd_export(database, args.email, sscm, args.default)
    elif args.command == "update" and args.database:
        database = sqlite3.connect(args.database)
        update_db_folder_renames(database)
    elif args.command == "all" and args.mainline and args.branch:
        # typical case
        database = create_database()
        cmd_parse(args.mainline, args.branch, database, sscm, args.snapshot)
        cmd_export(database, args.email, sscm, args.default)
    elif args.command == "verify" and args.mainline and args.path:
        # the 'verify' operation must take place after the export has completed.
        # as such, it will always be conducted as its own separate operation.
        cmd_verify(args.mainline, args.path)
    else:
        parser.print_help()
        sys.exit(1)


def parse_arguments():
    parser = argparse.ArgumentParser(
        prog="export-surround-to-git.py",
        description="Exports history from Seapine Surround in a format parsable by `git fast-import`.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--default", default="main", help="default branch in the git repo"
    )
    parser.add_argument(
        "-m", "--mainline", help="Mainline branch containing the branch to export"
    )
    parser.add_argument("-b", "--branch", help="Branch to export")
    parser.add_argument(
        "-d",
        "--database",
        help="Path to local database (only used when resuming an export)",
    )
    parser.add_argument("-u", "--username", help="Username for the scm server")
    parser.add_argument("-pw", "--password", help="Password for the scm server")
    parser.add_argument(
        "-i", "--install", default="sscm", help="Full path to sscm executable"
    )
    parser.add_argument("-ho", "--host", help="Surround SCM server host address")
    parser.add_argument("-po", "--port", help="Surround SCM server port number")
    parser.add_argument("--snapshot", action="store_true")
    parser.add_argument("--email", help="Domain for the email address")
    parser.add_argument("--version", action="version", version="%(prog)s " + VERSION)
    parser.add_argument("command", nargs="?", default="all")
    parser.epilog = 'Example flow:\n\tgit init my-new-repo\n\tcd my-new-repo\n\texport-surround-to-git.py -m Sandbox -p "Sandbox/Merge Test" -f blah.txt\n\t...\n\tgit repack ...'
    return parser


def main():
    parser = parse_arguments()
    handle_command(parser)
    sys.exit(0)


if __name__ == "__main__":
    main()
