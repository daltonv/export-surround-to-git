#!/usr/bin/env python3

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

# TODOs
# - dynamically find a temporary folder to store files. Python should have an os module for this
# - try using sscm setclient to handle authentication instead of passing the password here
# - allow the user to name the database file


# attempt to support both Python2.6+ and Python3
from __future__ import print_function
from enum import unique


VERSION = '0.5.0'


# Environment:  For now, this script requires:
#   * Python 2.7
#   * Bash
#   * sscm command-line client (in path)

# Last tested using:
#   * Python 2.7.6
#   * GNU bash, version 4.3.11(1)-release (i686-pc-linux-gnu)
#   * sscm command-line client version:  2013.0.0 Build 23 (Linux)
#   * Git version 1.9.1
#   * Ubuntu 14.04.1 LTS
#   * Linux 3.13.0-35-generic #62-Ubuntu SMP Fri Aug 15 01:58:01 UTC 2014 i686 i686 i686 GNU/Linux


import sys
import argparse
import subprocess
import re
import time
import datetime
import sqlite3
import os
import pathlib
import shutil
import math


#
# globals
#

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
    SSCMFileAction.AllActions                       : None,
    SSCMFileAction.AddToRepository                  : Actions.FILE_MODIFY,
    SSCMFileAction.AddToBranch                      : Actions.FILE_MODIFY, # This doesn't feel like a modify. TODO investigate
    SSCMFileAction.AddFromBranch                    : Actions.FILE_MODIFY,
    SSCMFileAction.CheckIn                          : Actions.FILE_MODIFY,
    SSCMFileAction.Rebase                           : None,
    SSCMFileAction.RebaseWithMerge                  : None,
    SSCMFileAction.Label                            : None,
    SSCMFileAction.AttachToDefect                   : None,
    SSCMFileAction.Delete                           : Actions.FILE_DELETE,
    SSCMFileAction.Undelete                         : None,
    SSCMFileAction.PromoteToBranch                  : None,
    SSCMFileAction.PromoteFromBranchWithMerge       : Actions.FILE_MERGE,
    SSCMFileAction.PromoteFromBranchWithOutMerge    : Actions.FILE_MERGE,
    SSCMFileAction.Share                            : None,
    SSCMFileAction.BreakShare                       : None,
    SSCMFileAction.BranchRenamed                    : None,
    SSCMFileAction.BranchRemoved                    : None,
    SSCMFileAction.BranchRestored                   : None,
    SSCMFileAction.FileRenamed                      : Actions.FILE_RENAME,
    SSCMFileAction.RepoRenamed                      : None,
    SSCMFileAction.BranchDestroyed                  : None,
    SSCMFileAction.FileDestroyed                    : Actions.FILE_DELETE,
    SSCMFileAction.RepoDestroyed                    : None,
    SSCMFileAction.BranchTypeChange                 : None,
    SSCMFileAction.BranchOwnerChange                : None,
    SSCMFileAction.RollbackRebase                   : Actions.FILE_MODIFY,
    SSCMFileAction.RollbackPromote                  : Actions.FILE_MODIFY,
    SSCMFileAction.RollbackFile                     : Actions.FILE_MODIFY,
    SSCMFileAction.CustomFieldChanged               : None,
    SSCMFileAction.StateChanged                     : None,
    SSCMFileAction.UnLabel                          : None,
    SSCMFileAction.AttachToTestCase                 : None,
    SSCMFileAction.AttachToRequirement              : None,
    SSCMFileAction.DuplicateChanges                 : None,
    SSCMFileAction.FileMoved                        : Actions.FILE_RENAME,
    SSCMFileAction.RepoMoved                        : None,
    SSCMFileAction.AttachedToExternal               : None,
    SSCMFileAction.RollbackChanges                  : None,
    SSCMFileAction.ExportRepoToMainline             : None,
    SSCMFileAction.FileShareRemoved                 : None,
}


#
# classes
#

class DatabaseRecord:
    def __init__(self, tuple):
        self.init(tuple[0], tuple[1], tuple[2], tuple[3], tuple[4], tuple[5], tuple[6], tuple[7], tuple[8], tuple[9], tuple[10])

    def init(self, timestamp, action, mainline, branch, path, origPath, version, author, comment, data, repo):
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
        return (self.timestamp, self.action, self.mainline, self.branch, self.path, self.origPath, self.version, self.author, self.comment, self.data, self.repo)

# Hold all the info we need to run sscm
class SSCM:
    def __init__(self, exe, host, port, username, password):
        self.exe = exe
        self.host = host
        self.port = port
        self.username = username
        self.password = password


def verify_surround_environment(sscm):
    # verify we have sscm client installed and in PATH
    cmd = sscm.exe + " version"
    with open(os.devnull, 'w') as fnull:
        p = subprocess.Popen(cmd, shell=True, stdout=fnull, stderr=fnull)
        p.communicate()
        return (p.returncode == 0)


def get_lines_from_sscm_cmd(sscm_cmd):
    # helper function to clean each item on a line since sscm has lots of newlines
    p = subprocess.Popen(sscm_cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdoutdata, stderrdata = p.communicate()
    stdoutdata = stdoutdata.decode('utf8')
    stderrdata = (stderrdata.strip()).decode('utf8')

    lines = [real_line for real_line in stdoutdata.splitlines() if real_line]
    return lines, stderrdata


def find_all_branches_in_mainline_containing_path(mainline, path, sscm):
    # use the -o command on lsbranch to get a full path definition of each
    # branch. This will help us parse later
    cmd = sscm.exe + ' lsbranch -b"%s" -p"%s" -o ' % (mainline, path)
    if sscm.username and sscm.password:
        cmd = cmd + '-y"%s":"%s" ' % (sscm.username, sscm.password)

    # This command yields branches that don't include the path specified.
    # we can however filter out the branches by using the -o option to print
    # the full path of each branch and manually parse incorrect branches out
    # NOTE: don't use '-f' with this command, as it really restricts overall usage.
    branches, stderrdata = get_lines_from_sscm_cmd(cmd)

    if stderrdata:
        sys.stderr.write('[*] sscm error from cmd lsbranch: %s\n' % stderrdata)

    our_branches = {}
    # Parse the branches and find the branches in the path provided
    for branch in branches:
        if branch.startswith(str(path)):
            # Since the branch currently shows the full path we need to get the
            # the branch name by getting only the last element in the path
            match = re.search(r'(.+\/([^\/]+))\s\<(.+)>\s\((baseline|mainline|snapshot)\)', branch)
            found_branch = pathlib.PurePosixPath(match.group(1))
            if str(found_branch).startswith((str(path) + '/')) or found_branch == path:
                branch_repo = pathlib.PurePosixPath(match.group(3))
                if str(branch_repo).startswith((str(path) + '/')) or branch_repo == path:
                    our_branches[found_branch.name] = branch_repo

    return our_branches


def find_all_files_in_branches_under_path(branches, sscm):
    fileSet = set()
    for branch in branches:
        sys.stderr.write("[*] Looking for files in branch '%s' ...\n" % branch)

        cmd = sscm.exe + ' ls -b"%s" -p"%s" -r ' % (branch, branches[branch])
        if sscm.username and sscm.password:
            cmd = cmd + '-y"%s":"%s" ' % (sscm.username, sscm.password)

        lines, stderrdata = get_lines_from_sscm_cmd(cmd)

        if stderrdata:
            sys.stderr.write('[*] sscm error from cmd ls: %s\n' % stderrdata)

        # directories are listed on their own line, before a section of their files
        # the last line of the output just prints the number of files found so
        # we can ignore it.
        for line in lines[:-1]:
            if (line.strip())[0] == '-':
                # This is a comment and not a file
                continue
            elif line[0] != ' ':
                lastDirectory = line
            elif line[1] != ' ':
                # Extract the file name for this line
                #file = (line.strip().split())[0]
                end_file_index = line.find(" current")
                if end_file_index == -1:
                    end_file_index = line.find(" unknown status")
                if end_file_index == -1:
                    raise Exception("Couldn't find the filename in ls output")
                file = line[:end_file_index].strip()
                fullPath = pathlib.PurePosixPath("%s/%s" % (lastDirectory, file))
                fileSet.add(fullPath)

    return fileSet


def is_snapshot_branch(branch, repo, sscm):
    # TODO can we eliminate 'repo' as an argument to this function?
    cmd = sscm.exe + ' branchproperty -b"%s" -p"%s" ' % (branch, repo)
    if sscm.username and sscm.password:
            cmd = cmd + '-y"%s":"%s" ' % (sscm.username, sscm.password)
    with open(os.devnull, 'w') as fnull:
        result = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=fnull).communicate()[0].decode("utf8")
    return result.find("snapshot") != -1


def get_file_rename(version, file, repo, branch, sscm):
    cmd = sscm.exe + ' history "%s" -b"%s" -p"%s" -v"%d:%d" ' % (file, branch, repo, version, version)
    if sscm.username and sscm.password:
        cmd += '-y"%s":"%s" ' % (sscm.username, sscm.password)

    old = None
    new = None

    lines, stderrdata = get_lines_from_sscm_cmd(cmd)

    if stderrdata:
        raise Exception("sscm error from cmd history: %s" % stderrdata)

    # Note if for some reason there are multiple file renames in the same version
    # we will ONLY take the last file rename.
    for line in lines[4:]:
        result = re.search(r'from\s\[([\S ]+)\]\sto\s\[([\S ]+)\]', line)
        if result:
            old = result.group(1)
            new = result.group(2)

    if (not old) and (not new):
        full_file_path = repo / file
        raise Exception("Could not find file rename info for %s" % full_file_path)

    return (old, new)


def find_all_file_versions(mainline, branch, path, sscm):
    repo = path.parent
    file = path.name
    # The sscm history command is too difficult to parse corerectly so here we
    # use a tool created with the sscm API that we control
    sscmhist = pathlib.Path(sys.path[0]) / "sscmhist" / "sscmhist.exe"
    if not sscmhist.exists():
        raise Exception("sscmhist does not exit. Try compiling it")

    cmd = str(sscmhist) + ' %s %s ' % (sscm.host, sscm.port)
    if sscm.username and sscm.password:
        cmd += '%s %s ' % (sscm.username, sscm.password)
    else:
        # TODO handle this better
        cmd += 'NULL NULL '
    cmd += '"%s" "%s" "%s" "%s"' % (branch, branch, repo, file)

    lines, stderrdata = get_lines_from_sscm_cmd(cmd)
    if stderrdata:
        if stderrdata == "sscm_file_history failed: Record not found; the selected item may not exist.":
            sys.stderr.write('[*] sscmhistory could not find %s in branch %s\n' % (file, branch))
        else:
            sys.stderr.write('[*] sscmhistory error: %s\n' % stderrdata)

    versionList = []

    if lines:
        # TODO: use an actual condition in the while loop instead of relying on
        # the break.
        while 1:
            i = lines.index("--END_COMMENT--")

            lines_group = lines[:i]

            version = int(lines_group[0])
            # round the seconds up to the nearest 5 out of the time as it is too
            # precise. Many file changes only differ by a second as Surround
            # alters each file as part of a group check in operation
            round_target = 10
            time_struct = time.localtime(int(lines_group[1]))
            timestamp_seconds = time_struct.tm_sec
            rounded_seconds = round_target * int(math.ceil(timestamp_seconds / round_target))
            time_string = time.strftime(("%Y%m%d%H:%M:" + str(rounded_seconds)), time_struct)
            new_time_struct = time.strptime(time_string, "%Y%m%d%H:%M:%S")
            timestamp = int(time.mktime(new_time_struct))
            action = int(lines_group[2])
            data = lines_group[3]
            if data == "(null)":
                data = None
            author = lines_group[4]
            comment = '\n'.join(lines_group[5:])
            origFile = "NULL"

            # Unfortunately the API only tells us a rename happened and not
            # what the rename was. To get these names we use a helper function
            # that calls 'sscm history'. Finding just the rename info is
            # relatively safe by parsing the output with regex.
            if action == SSCMFileAction.FileMoved or action == SSCMFileAction.FileRenamed:
                (oldName, newName) = get_file_rename(version , file, repo, branch, sscm)
                data = pathlib.PurePosixPath(newName)
                origFile = pathlib.PurePosixPath(oldName)

            versionList.append((timestamp, action, origFile, version, author, comment, data))

            if len(lines[i:]) > 1:
                lines = lines[(i+1):]
            else:
                break

    return versionList


def create_database():
    # database file is created in cwd
    name = datetime.datetime.fromtimestamp(time.time()).strftime('%Y%m%d%H%M%S') + '.db'
    database = sqlite3.connect(name)
    c = database.cursor()
    # we intentionally avoid duplicates via the PRIMARY KEY
    c.execute('''CREATE TABLE operations (timestamp INTEGER NOT NULL, action INTEGER NOT NULL, mainline TEXT NOT NULL, branch TEXT NOT NULL, path TEXT, origPath TEXT, version INTEGER, author TEXT, comment TEXT, data TEXT, repo TEXT NOT NULL, PRIMARY KEY(action, mainline, branch, path, origPath, version, author, data))''')
    database.commit()
    return database


def add_record_to_database(record, database):
    c = database.cursor()
    try:
        c.execute('''INSERT INTO operations VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)''', record.get_tuple())
    except sqlite3.IntegrityError as e:
        # TODO is there a better way to detect duplicates?  is sqlite3.IntegrityError too wide a net?
        #sys.stderr.write("\nDetected duplicate record %s" % str(record.get_tuple()))
        pass
    database.commit()

    if record.action == Actions.FILE_RENAME:
        c.execute('''UPDATE operations SET origPath=? WHERE (action=? or action=?) AND mainline=? AND branch=? AND path=? AND (origPath IS NULL OR origPath='') AND version<=?''', (record.origPath, Actions.FILE_MODIFY, Actions.FILE_MERGE, record.mainline, record.branch, record.path, record.version))
        database.commit()


def cmd_parse(mainline, path, database, sscm):
    sys.stderr.write("[+] Beginning parse phase...\n")

    repo = pathlib.PurePosixPath(path)

    branches = find_all_branches_in_mainline_containing_path(mainline, repo, sscm)

    # NOTE how we're passing branches, not branch.  this is to detect deleted files.
    filesToWalk = find_all_files_in_branches_under_path(branches, sscm)

    for branch in branches:
        # Skip snapshot branches
        if is_snapshot_branch(branch, repo, sscm):
            continue

        sys.stderr.write("[*] Parsing branch '%s' ...\n" % branch)

        for fullPathWalk in filesToWalk:
            #sys.stderr.write("\n[*] \tParsing file '%s' ..." % fullPathWalk)

            pathWalk = fullPathWalk.parent
            fileWalk = fullPathWalk.name

            versions = find_all_file_versions(mainline, branch, fullPathWalk, sscm)
            #sys.stderr.write("\n[*] \t\tversions = %s" % versions)
            for timestamp, action, origPath, version, author, comment, data in versions:
                # branch operations don't follow the actionMap
                if action == SSCMFileAction.AddToBranch:
                    if is_snapshot_branch(data, pathWalk, sscm):
                        branchAction = Actions.BRANCH_SNAPSHOT
                    else:
                        branchAction = Actions.BRANCH_BASELINE

                    # Some branch actions occur on deleted branches. In that case
                    # the branch won't appear in branches list. We will just treat
                    # the path as the repo path in this case. # TODO handle deleted
                    # branches better
                    if data in branches:
                        branch_path = str(branches[data])
                    else:
                        branch_path = str(repo)
                    # each add to branch command happens once for a new branch, but will show up on each file
                    # that is a part of the branch added too. To ensure there are no duplicates use an empty
                    # string for origPath (its irrelevant in the export phase for this action) and set the version
                    # to one. We cant use None/NULL for these values as SQLITE doesn't consider NULL==NULL as a true
                    # statement.
                    add_record_to_database(DatabaseRecord((timestamp, branchAction, mainline, branch, branch_path, "NULL", 1, author, comment, data, str(repo))), database)
                else:
                    origFullPath = None
                    if origPath:
                        if action == SSCMFileAction.FileRenamed:
                            origFullPath = str(pathWalk / origPath)
                            data = str(pathWalk / data)
                        elif action == SSCMFileAction.FileMoved:
                            origFullPath = str(origPath / fileWalk)
                            data = str(data / fileWalk)
                    add_record_to_database(DatabaseRecord((timestamp, actionMap[action], mainline, branch, str(fullPathWalk), origFullPath, version, author, comment, data, str(repo))), database)

    sys.stderr.write("[+] Parse phase complete\n")


# Surround has different naming rules for branches than Git does for branches/tags.
# this function performs a one-way translation from Surround to Git.
def translate_branch_name(name):
    #
    # pre-processing
    #

    # 6. cannot contain multiple consecutive slashes
    # replace multiple with single
    name = re.sub(r'[\/]+', r'/', name)

    #
    # apply rules from `git check-ref-format`
    #

    # 1. no slash-separated component can begin with a dot .
    name = name.replace("/.", "/_")
    # 1. no slash-separated component can end with the sequence .lock
    name = re.sub(r'\.lock($|\/)', r'_lock', name)
    # 3. cannot have two consecutive dots ..  anywhere
    name = re.sub(r'[\.]+', r'_', name)
    # 4. cannot have ASCII control characters (i.e. bytes whose values are lower than \040, or \177 DEL) anywhere
    for char in name:
        if char < '\040' or char == '\177':
            # TODO I'm not sure that modifying 'char' here actually modifies 'name'.  Check this and fix if necessary.
            char = '_'
    # 4. cannot have space anywhere.
    # replace with dash for readability.
    name = name.replace(" ", "-")
    # 4. cannot have tilde ~, caret ^, or colon : anywhere
    # 5. cannot have question-mark ?, asterisk *, or open bracket [ anywhere
    # 10. cannot contain a \
    name = re.sub(r'[\~\^\:\?\*\[\\]+', r'_', name)
    # 6. cannot begin or end with a slash /
    # 7. cannot end with a dot .
    name = re.sub(r'(^[\/]|[\/\.]$)', r'_', name)
    # 8. cannot contain a sequence @{
    name = name.replace("@{", "__")
    # 9. cannot be the single character @
    if name == "@":
        name = "_"

    return name


# this is the function that prints most file data to the stream
def print_blob_for_file(branch, fullPath, sscm, scratchDir, timestamp=None):
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
        cmd = sscm.exe + ' get "%s" -b"%s" -p"%s" -d"%s" -f -i -s"%s" -e ' % (file, branch, path, scratchDir.name, time_string)
        if sscm.username and sscm.password:
            cmd = cmd + '-y"%s":"%s" ' % (sscm.username, sscm.password)
    else:
        # get newest version
        cmd = sscm.exe + ' get "%s" -b"%s" -p"%s" -d"%s" -f -i -e ' % (file, branch, path, scratchDir.name)
        if sscm.username and sscm.password:
            cmd = cmd + '-y"%s":"%s" ' % (sscm.username, sscm.password)
    with open(os.devnull, 'w') as fnull:
        subprocess.Popen(cmd, shell=True, stdout=fnull, stderr=fnull).communicate()

    if not localPath.is_file():
        sys.stderr.write("[+] Failed to download file %s from branch %s. Trying again...\n" % (fullPath, branch))
        time.sleep(3)
        with open(os.devnull, 'w') as fnull:
            subprocess.Popen(cmd, shell=True, stdout=fnull, stderr=fnull).communicate()

        if not localPath.is_file():
            raise Exception("File %s from branch %s could not be downloaded with timestamp %s\ncmd = %s" % (fullPath, branch, time_string, cmd))

    # git fast-import is very particular about the format of the blob command.
    # The data must be given in raw bytes for it to parse the files correctly.
    mark = mark + 1
    sys.stdout.buffer.write(b'blob\n')
    sys.stdout.buffer.write(b'mark :%d\n' % mark)
    line = localPath.read_bytes()
    sys.stdout.buffer.write(b'data %d\n' % len(line))
    sys.stdout.buffer.write(line)
    sys.stdout.buffer.write(b'\n')
    sys.stdout.flush()
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
    if (i := comment_header.find('\n')) != -1:
        # This means we are already a legal git comment
        if i != (len(comment_header) - 1)  and comment_header[i+1] == '\n':
            fixed_comment = comment_header + comment_body
        else:
            fixed_comment = comment_header[:i] + '\n' + comment_header[i:] + comment_body
    # our whole comment is enough to be the header
    elif not comment_body:
        fixed_comment = comment_header
    # if not we can break the comment at the end of the last sentence before the limit
    elif (i := comment_header[::-1].find('.')) != -1:
        fixed_comment = comment_header[:(git_header_len - i)] + '\n\n' + comment_header[(git_header_len - i):].lstrip() + comment_body
    # If there are no periods we must break on the last space between
    # words before the limit
    elif (i := comment_header[:-3][::-1].find(' ')) != -1:
        fixed_comment = comment_header[:(git_header_len - i - 3)].rstrip() + '...\n\n' + comment_header[(git_header_len - i - 3):].lstrip() + comment_body
    # Finally if a caveman is writing the comment and used no spaces we
    # force a cut off at the header limit
    else:
        fixed_comment = comment_header[:git_header_len] + '\n\n' + comment_header[git_header_len:]

    return fixed_comment


def process_combined_commit(record_group, sscm, email_domain, scratchDir, default_branch, merge = False):
    global mark
    unique_comments = {}

    for record in record_group:
        if record.action == Actions.FILE_MODIFY or record.action == Actions.FILE_MERGE:
                blob_mark = print_blob_for_file(record.branch, pathlib.PurePosixPath(record.path), sscm, scratchDir, record.timestamp)
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
    sys.stdout.buffer.write(("commit refs/heads/%s\n" % translate_branch_name(branch)).encode("utf-8"))
    sys.stdout.buffer.write(("mark :%d\n" % mark).encode("utf-8"))
    email = ""
    if email_domain:
        email = record_group[0].author + "@" + email_domain
    else:
        email = record_group[0].author
    sys.stdout.buffer.write(("author %s <%s> %s %s\n" % (record_group[0].author, email, record_group[0].timestamp, timezone)).encode("utf-8"))
    sys.stdout.buffer.write(("committer %s <%s> %s %s\n" % (record_group[0].author, email, record_group[0].timestamp, timezone)).encode("utf-8"))
    if len(unique_comments):
        full_comment = ""
        for comment, files in unique_comments.items():
            full_comment += (comment + "\n")
            # If we're combining multiple comments lets tell the user which
            # file(s) each comment is associated with
            if len(unique_comments) > 1:
                for file in files:
                    full_comment += "^ %s\n" % file
                full_comment += "\n"

        encoded_comment = fixup_comment_header(full_comment).encode("utf-8")
        sys.stdout.buffer.write(b"data %d\n" % len(encoded_comment))
        sys.stdout.buffer.write(encoded_comment)
    else:
        sys.stdout.buffer.write(b"data 0\n")

    if merge:
        merge_branch = record.data
        if merge_branch == record.mainline:
            merge_branch = default_branch
        sys.stdout.buffer.write(("merge refs/heads/%s\n" % translate_branch_name(merge_branch)).encode("utf-8"))

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
                sys.stdout.buffer.write(('M 100644 :%d "%s"\n' % (record.blob_mark, origPath)).encode("utf-8"))
            else:
                # no previous rename.  good to use the current name.
                sys.stdout.buffer.write(('M 100644 :%d "%s"\n' % (record.blob_mark, path)).encode("utf-8"))
        elif record.action == Actions.FILE_DELETE:
            sys.stdout.buffer.write(('D "%s"\n' % path).encode("utf-8"))
        elif record.action == Actions.FILE_RENAME:
            # NOTE we're not using record.path here, as there may have been multiple renames in the file's history
            full_data_path = pathlib.PurePosixPath(record.data)
            data = full_data_path.relative_to(repo)
            sys.stdout.buffer.write(('R "%s" "%s"\n' % (origPath, data)).encode("utf-8"))
        else:
            raise Exception("Unknown record action")

    # Flush our buffer. We are going to print a lot, so this helps everything
    # stay in the right order.
    sys.stdout.flush()


def process_database_record_group(c, sscm, scratchDir, default_branch, email_domain = None):
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

            sys.stdout.buffer.write(b"reset TAG_FIXUP\n")
            parentBranch =  record.branch
            if record.branch == record.mainline:
                parentBranch = default_branch
            sys.stdout.buffer.write(("from refs/heads/%s\n" % translate_branch_name(parentBranch)).encode("utf-8"))

            # get all files contained within snapshot
            branches_dict = {}
            branches_dict[record.data] = record.path
            files = find_all_files_in_branches_under_path(branches_dict, sscm)
            startMark = None
            for file in files:
                blobMark = print_blob_for_file(record.data, file, sscm, scratchDir)
                if not startMark:
                    # keep track of what mark represents the start of this snapshot data
                    startMark = blobMark

            mark = mark + 1
            sys.stdout.buffer.write(b"commit TAG_FIXUP\n")
            sys.stdout.buffer.write(b"mark :%d\n" % mark)
            email = ""
            if email_domain:
                email = record.author + "@" + email_domain
            else:
                email = record.author
            sys.stdout.buffer.write(("author %s <%s> %s %s\n" % (record.author, email, record.timestamp, timezone)).encode("utf-8"))
            sys.stdout.buffer.write(("committer %s <%s> %s %s\n" % (record.author, email, record.timestamp, timezone)).encode("utf-8"))
            if record.comment:
                comment = fixup_comment_header(record.comment).encode("utf-8")
                sys.stdout.buffer.write(b"data %d\n" % len(comment))
                sys.stdout.buffer.write(comment)
                sys.stdout.buffer.write(b"\n")
            else:
                sys.stdout.buffer.write(b"data 0\n")

            # 'deleteall' tells Git to forget about previous branch state
            sys.stdout.buffer.write(b"deleteall\n")
            # replay branch state from above-recorded marks
            iterMark = startMark
            for filePath in files:
                # Remove the repo from the file path
                repo = pathlib.PurePosixPath(record.repo)
                file = filePath.relative_to(repo)
                sys.stdout.buffer.write(("M 100644 :%d %s\n" % (iterMark, file)).encode("utf-8"))
                iterMark = iterMark + 1
            if iterMark != mark:
                raise Exception("Marks fell out of sync while tagging '%s'." % record.data)

            # finally, tag our result
            sys.stdout.buffer.write(("tag %s\n" % translate_branch_name(record.data)).encode("utf-8"))
            sys.stdout.buffer.write(b"from TAG_FIXUP\n")
            sys.stdout.buffer.write(("tagger %s <%s> %s %s\n" % (record.author, record.author, record.timestamp, timezone)).encode("utf-8"))
            if record.comment:
                comment = record.comment.encode("utf-8")
                sys.stdout.buffer.write(b"data %d\n" % len(comment))
                sys.stdout.buffer.write(comment)
                sys.stdout.buffer.write(b"\n")
            else:
                sys.stdout.buffer.write(b"data 0\n")

            # save off the mapping between the tag name and the tag mark
            tagDict[translate_branch_name(record.data)] = mark

        elif record.action == Actions.BRANCH_BASELINE:
            # the idea hers is to simply 'reset' to create our new branch, the name of which is contained in the 'data' field

            sys.stdout.buffer.write(("reset refs/heads/%s\n" % translate_branch_name(record.data)).encode("utf-8"))
            parentBranch = record.branch
            if record.branch == record.mainline:
                parentBranch = default_branch
            parentBranch = translate_branch_name(parentBranch)
            if is_snapshot_branch(parentBranch, os.path.split(record.path)[0], sscm):
                # Git won't let us refer to the tag directly (maybe this will be fixed in a future version).
                # for now, we have to refer to the associated tag mark instead.
                # (if this is fixed in the future, we can get rid of tagDict altogether)
                sys.stdout.buffer.write(b"from :%d\n" % tagDict[parentBranch])
            else:
                # baseline branch
                sys.stdout.buffer.write(("from refs/heads/%s\n" % parentBranch).encode("utf-8"))

        elif record.action == Actions.FILE_MODIFY or record.action == Actions.FILE_DELETE or record.action == Actions.FILE_RENAME:
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
        sys.stdout.flush()

    # Here we are going to combine all the record groups into a single commits
    #
    # We want to process merge commits first because Surround handles merges with
    # with renames in two steps. First the merge of the content and then a rename.
    # The rename needs to happen after or we get both names of the file after
    # merge
    for merge in merge_records:
        process_combined_commit(merge_records[merge], sscm, email_domain, scratchDir, default_branch, True)

    if len(normal_records):
        process_combined_commit(normal_records, sscm, email_domain, scratchDir, default_branch, False)


def cmd_export(database, email_domain, sscm, default_branch):
    sys.stderr.write("[+] Beginning export phase...\n")

    # temp directory in cwd, holds files fetched from Surround
    scratchDir = (pathlib.Path.cwd() / "scratch")

    if not os.path.exists(scratchDir):
        os.mkdir(scratchDir)

    # Group the database by timestamp, branch and author. This will allow us to find
    # each unique timestamp for each branch (multiple branches can have
    # actions performed at the same time, and a checking aught to have only one author).
    # We want to then go through each operation in these groups as we will group
    # all Surround actions in these timestamps as a single commit
    c1 = database.cursor()
    c2 = database.cursor()
    c1.execute('''SELECT timestamp, branch FROM operations GROUP BY timestamp, branch, author ORDER BY timestamp ASC''')

    count = 0
    records_group = []
    while record := c1.fetchone():
        c2.execute("SELECT * FROM operations WHERE timestamp == %d AND branch == '%s' ORDER BY action ASC" % (record[0], record[1]))
        process_database_record_group(c2, sscm, scratchDir, default_branch, email_domain)
        count = count + 1
        # print progress every 5 operations
        if count % 5 == 0 and record:
            # just print the date we're currently servicing
            print("progress", time.strftime('%Y-%m-%d', time.localtime(record[0])))

    # cleanup
    try:
        shutil.rmtree(scratchDir)
    except OSError:
        pass
    if os.path.isfile("./.git/TAG_FIXUP"):
        # TODO why doesn't this work?  is this too early since we're piping our output, and then `git fast-import` just creates it again?
        os.remove("./.git/TAG_FIXUP")

    sys.stderr.write("[+] Export complete.  Your new Git repository is ready to use.\nDon't forget to run `git repack` at some future time to improve data locality and access performance.\n\n")


def cmd_verify(mainline, path):
    # TODO verify that all Surround baseline branches are identical to their Git counterparts
    # TODO verify that all Surround snapshot branches are identical to their Git counterparts
    # should be able to do this without database
    pass


def handle_command(parser):
    args = parser.parse_args()

    sscm = SSCM(args.install, args.host, args.port, args.username, args.password)

    if args.command == "parse" and args.mainline and args.path:
        verify_surround_environment(sscm)
        database = create_database()
        cmd_parse(args.mainline, args.path, database, sscm)
    elif args.command == "export" and args.database:
        verify_surround_environment(sscm)
        database = sqlite3.connect(args.database)
        cmd_export(database, args.email, sscm, args.branch)
    elif args.command == "all" and args.mainline and args.path:
        # typical case
        verify_surround_environment(sscm)
        database = create_database()
        cmd_parse(args.mainline, args.path, database, sscm)
        cmd_export(database, args.email, sscm, args.branch)
    elif args.command == "verify" and args.mainline and args.path:
        # the 'verify' operation must take place after the export has completed.
        # as such, it will always be conducted as its own separate operation.
        verify_surround_environment(sscm)
        cmd_verify(args.mainline, args.path)
    else:
        parser.print_help()
        sys.exit(1)


def parse_arguments():
    parser = argparse.ArgumentParser(prog='export-surround-to-git.py', description='Exports history from Seapine Surround in a format parsable by `git fast-import`.', formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('-b', '--branch', default="main", help='default branch in the git repo')
    parser.add_argument('-m', '--mainline', help='Mainline branch containing history to export')
    parser.add_argument('-p', '--path', help='Path containing history to export')
    parser.add_argument('-d', '--database', help='Path to local database (only used when resuming an export)')
    parser.add_argument('-u', '--username', help='Username for the scm server')
    parser.add_argument('-pw', '--password', help='Password for the scm server')
    parser.add_argument('-i', '--install', default='sscm' ,help='Full path to sscm executable')
    parser.add_argument('-ho', '--host', help='Surround SCM server host address')
    parser.add_argument('-po', '--port', help='Surround SCM server port number')
    parser.add_argument('--email', help='Domain for the email address')
    parser.add_argument('--version', action='version', version='%(prog)s ' + VERSION)
    parser.add_argument('command', nargs='?', default='all')
    parser.epilog = "Example flow:\n\tgit init my-new-repo\n\tcd my-new-repo\n\texport-surround-to-git.py -m Sandbox -p \"Sandbox/Merge Test\" -f blah.txt | git fast-import --stats --export-marks=marks.txt\n\t...\n\tgit repack ..."
    return parser


def main():
    parser = parse_arguments()
    handle_command(parser)
    sys.exit(0)


if __name__ == "__main__":
    main()
