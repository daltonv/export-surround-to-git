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
# - dynamically find a tempory folder to store files. Python should have an os module for this
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


#
# globals
#

# temp directory in cwd, holds files fetched from Surround
scratchDir = "scratch"

# for efficiency, compile the history regex once beforehand
# TODO timestamp should match times more explicitly but I want to ensure timestamps are always printed the sameway from sscm
histRegex = re.compile(r"^(?P<action>[\w]+([^\[\]\r\n]*[\w]+)?)(\[(?P<data>[^\[\]\r\n]*?)( v\. [\d]+)?\]| from \[(?P<from>[^\[\]\r\n]*)\] to \[(?P<to>[^\[\]\r\n]*)\])?([\s]+)(?P<author>[\w]+([^\[\]\r\n]*[\w]+)?)([\s]+)(?P<version>[\d]+)([\s]+)(?P<timestamp>\d\d\/[^\[\]\r\n]*)$", re.MULTILINE | re.DOTALL)

# global "mark" number.  incremented before used, as 1 is minimum value allowed.
mark = 0

# local time zone
# TODO how detect this?  right now we assume EST.
timezone = "-0500"

sscm = "sscm"
username = ""
password = ""
host = ""
port = ""

# keeps track of snapshot name --> mark number pairing
tagDict = {}

# actions enumeration
class Actions:
    BRANCH_SNAPSHOT = 1
    BRANCH_BASELINE = 2
    FILE_MODIFY = 3
    FILE_DELETE = 4
    FILE_RENAME = 5

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
    SSCMFileAction.AddToBranch                      : None,
    SSCMFileAction.AddToBranch                      : Actions.FILE_MODIFY, # This doesn't feel like a modify. TODO investigate
    SSCMFileAction.AddFromBranch                    : Actions.FILE_MODIFY,
    SSCMFileAction.CheckIn                          : Actions.FILE_MODIFY,
    SSCMFileAction.Rebase                           : None,
    SSCMFileAction.RebaseWithMerge                  : None,
    SSCMFileAction.Label                            : None,
    SSCMFileAction.AttachToDefect                   : None,
    SSCMFileAction.Delete                           : Actions.FILE_DELETE,
    SSCMFileAction.Undelete                         : None,
    SSCMFileAction.PromoteToBranch                  : Actions.FILE_MODIFY,
    SSCMFileAction.PromoteFromBranchWithMerge       : Actions.FILE_MODIFY,
    SSCMFileAction.PromoteFromBranchWithOutMerge    : Actions.FILE_MODIFY,
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


def verify_surround_environment():
    # verify we have sscm client installed and in PATH
    cmd = sscm + " version"
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
    if stderrdata:
        sys.stderr.write('\n')
        sys.stderr.write('[*] sscm error from cmd ' + sscm_cmd + '\n')
        sys.stderr.write('[*]\t error = ' + stderrdata)
    return [real_line for real_line in stdoutdata.splitlines() if real_line]


def find_all_branches_in_mainline_containing_path(mainline, path):
    # use the -o command on lsbranch to get a full path definition of each
    # branch. This will help us parse later
    cmd = sscm + ' lsbranch -b"%s" -p"%s" -o ' % (mainline, path)
    if username and password:
        cmd = cmd + '-y"%s":"%s" ' % (username, password)

    # FTODO this command yields branches that don't include the path specified.
    # we can however filter out the branches by using the -o option to print
    # the full path of each branch and manually parse incorrect branches out
    # NOTE: don't use '-f' with this command, as it really restricts overall usage.
    branches = get_lines_from_sscm_cmd(cmd)

    our_branches = []
    # Parse the branches and find the branches in the path provided
    for branch in branches:
        if branch.startswith(path):
            # Since the branch currently shows the full path we need to get the
            # the branch name by getting only the last element in the path
            match = re.search(r'\/([^\/]+)\s\<.+>\s\((baseline|mainline|snapshot)\)', branch)
            our_branches.append(match.group(1))

    return our_branches


def find_all_files_in_branches_under_path(mainline, branches, path):
    fileSet = set()
    for branch in branches:
        sys.stderr.write("\n[*] Looking for files in branch '%s' ..." % branch)

        # use all lines from `ls` except for a few
        cmd = sscm + ' ls -b"%s" -p"%s" -r ' % (branch, path)
        if username and password:
            cmd = cmd + '-y"%s":"%s" ' % (username, password)
        #cmd = cmd + '| grep -v \'Total listed files\' | sed -r \'s/unknown status.*$//g\''
        # TODO why were they only looking for files with unkown status
        lines = get_lines_from_sscm_cmd(cmd)

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


def is_snapshot_branch(branch, repo):
    # TODO can we eliminate 'repo' as an argument to this function?
    cmd = sscm + ' branchproperty -b"%s" -p"%s" ' % (branch, repo)
    if username and password:
            cmd = cmd + '-y"%s":"%s" ' % (username, password)
    with open(os.devnull, 'w') as fnull:
        result = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=fnull).communicate()[0].decode("utf8")
    return result.find("snapshot") != -1


def get_file_rename(version, file, repo, branch):
    cmd = sscm + ' history "%s" -b"%s" -p"%s" -v"%d:%d" ' % (file, branch, repo, version, version)
    if username and password:
        cmd += '-y"%s":"%s" ' % (username, password)

    old = None
    new = None

    lines = get_lines_from_sscm_cmd(cmd)

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


def find_all_file_versions(mainline, branch, path):
    repo = path.parent
    file = path.name
    # The sscm history command is too difficult to parse corerectly so here we
    # use a tool created with the sscm API that we control
    sscmhist = pathlib.Path(sys.path[0]) / "sscmhist" / "sscmhist.exe"
    if not sscmhist.exists():
        raise Exception("sscmhist does not exit. Try compiling it")

    cmd = str(sscmhist) + ' %s %s ' % (host, port)
    if username and password:
        cmd += '%s %s ' % (username, password)
    else:
        # TODO handle this better
        cmd += 'NULL NULL '
    cmd += '"%s" "%s" "%s" "%s"' % (branch, branch, repo, file)

    lines = get_lines_from_sscm_cmd(cmd)

    versionList = []

    if lines:
        # TODO: use an actual condition in the while loop instead of relying on
        # the break.
        while 1:
            i = lines.index("--END_COMMENT--")

            lines_group = lines[:i]

            version = int(lines_group[0])
            # strip the seconds out of the time as it is too precise. Many
            # file changes only differ by a second as Surround alters each file
            # as part of a group checkin operation
            time_struct = time.localtime(int(lines_group[1]))
            time_string = time.strftime("%Y%m%d%H:%M:59", time_struct)
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
                (oldName, newName) = get_file_rename(version , file, repo, branch)
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
        c.execute('''UPDATE operations SET origPath=? WHERE action=? AND mainline=? AND branch=? AND path=? AND (origPath IS NULL OR origPath='') AND version<=?''', (record.origPath, Actions.FILE_MODIFY, record.mainline, record.branch, record.path, record.version))
        database.commit()


def cmd_parse(mainline, repo, database):
    sys.stderr.write("[+] Beginning parse phase...")

    branches = find_all_branches_in_mainline_containing_path(mainline, repo)

    # NOTE how we're passing branches, not branch.  this is to detect deleted files.
    filesToWalk = find_all_files_in_branches_under_path(mainline, branches, repo)

    for branch in branches:
        # Skip snapshot branches
        if is_snapshot_branch(branch, repo):
            continue

        sys.stderr.write("\n[*] Parsing branch '%s' ..." % branch)

        for fullPathWalk in filesToWalk:
            #sys.stderr.write("\n[*] \tParsing file '%s' ..." % fullPathWalk)

            pathWalk = fullPathWalk.parent
            fileWalk = fullPathWalk.name

            versions = find_all_file_versions(mainline, branch, fullPathWalk)
            #sys.stderr.write("\n[*] \t\tversions = %s" % versions)
            for timestamp, action, origPath, version, author, comment, data in versions:
                # branch operations don't follow the actionMap
                if action == SSCMFileAction.AddToBranch:
                    if is_snapshot_branch(data, pathWalk):
                        branchAction = Actions.BRANCH_SNAPSHOT
                    else:
                        branchAction = Actions.BRANCH_BASELINE
                    # each add to branch command happens once for a new branch, but will show up on each file
                    # that is a part of the branch added too. To ensure there are no duplicates use an empty
                    # string for origPath (its irrelevant in the export phase for this action) and set the version
                    # to one. We cant use None/NULL for these values as SQLITE doesnt consider NULL==NULL as a true
                    # statement.
                    add_record_to_database(DatabaseRecord((timestamp, branchAction, mainline, branch, repo, "NULL", 1, author, comment, data, repo)), database)
                else:
                    origFullPath = None
                    if origPath:
                        if action == SSCMFileAction.FileRenamed:
                            origFullPath = str(pathWalk / origPath)
                            data = str(pathWalk / data)
                        elif action == SSCMFileAction.FileMoved:
                            origFullPath = str(origPath / fileWalk)
                            data = str(data / fileWalk)
                    add_record_to_database(DatabaseRecord((timestamp, actionMap[action], mainline, branch, str(fullPathWalk), origFullPath, version, author, comment, data, repo)), database)

    sys.stderr.write("\n[+] Parse phase complete")


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
def print_blob_for_file(branch, fullPath, timestamp=None):
    global mark

    time_struct = time.localtime(timestamp)
    time_string = time.strftime("%Y%m%d%H:%M:%S", time_struct)

    path, file = os.path.split(fullPath)
    localPath = os.path.join(scratchDir, file)
    if os.path.isfile(localPath):
        os.remove(localPath)
    if timestamp:
        # get specified version. You would think the -v option would get the
        # version of the file you want, but this does not work for deleted files.
        # we need to use the time stamp with -s
        cmd = sscm + ' get "%s" -b"%s" -p"%s" -d"%s" -f -i -s"%s" -e ' % (file, branch, path, scratchDir, time_string)
        if username and password:
            cmd = cmd + '-y"%s":"%s" ' % (username, password)
    else:
        # get newest version
        cmd = sscm + ' get "%s" -b"%s" -p"%s" -d"%s" -f -i -e ' % (file, branch, path, scratchDir)
        if username and password:
            cmd = cmd + '-y"%s":"%s" ' % (username, password)
    with open(os.devnull, 'w') as fnull:
        subprocess.Popen(cmd, shell=True, stdout=fnull, stderr=fnull).communicate()

    # git fast-import is very particular about the format of the blob command.
    # The data must be given in raw bytes for it to parse the files correctly.
    mark = mark + 1
    sys.stdout.buffer.write(b'blob\n')
    sys.stdout.buffer.write(b'mark :%d\n' % mark)
    line = open(localPath, 'rb').read()
    sys.stdout.buffer.write(b'data %d\n' % len(line))
    sys.stdout.buffer.write(line)
    sys.stdout.buffer.write(b'\n')
    sys.stdout.flush()
    return mark


def process_database_record_group(c):
    global mark

    # will contain a list of the MODIFY, DELETE, and RENAME records in this
    # group to be processed later
    normal_records = []

    while r := c.fetchone():
        record = DatabaseRecord(r)

        if record.action == Actions.BRANCH_SNAPSHOT:
            # the basic idea here is to use a "TAG_FIXUP" branch, as recommended in the manpage for git-fast-import.
            # this is necessary since Surround version-controls individual files, and Git controls the state of the entire branch.
            # the purpose of this commit it to bring the branch state to match the snapshot exactly.

            sys.stdout.buffer.write(b"reset TAG_FIXUP\n")
            parentBranch =  record.branch
            if record.branch == record.mainline:
                parentBranch = "master"
            sys.stdout.buffer.write(("from refs/heads/%s\n" % translate_branch_name(parentBranch)).encode("utf-8"))

            # get all files contained within snapshot
            files = find_all_files_in_branches_under_path(record.mainline, [record.data], record.path)
            startMark = None
            for file in files:
                blobMark = print_blob_for_file(record.data, file)
                if not startMark:
                    # keep track of what mark represents the start of this snapshot data
                    startMark = blobMark

            mark = mark + 1
            sys.stdout.buffer.write(b"commit TAG_FIXUP\n")
            sys.stdout.buffer.write(b"mark :%d\n" % mark)
            # we don't have the legit email addresses, so we just use the author as the email address
            sys.stdout.buffer.write(("author %s <%s> %s %s\n" % (record.author, record.author, record.timestamp, timezone)).encode("utf-8"))
            sys.stdout.buffer.write(("committer %s <%s> %s %s\n" % (record.author, record.author, record.timestamp, timezone)).encode("utf-8"))
            if record.comment:
                comment = record.comment.encode("utf-8")
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
                parentBranch = "master"
            parentBranch = translate_branch_name(parentBranch)
            if is_snapshot_branch(parentBranch, os.path.split(record.path)[0]):
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

        else:
            raise Exception("Unknown record action")

        # Flush our buffer. We are going to print a lot, so this helps everything
        # stay in the right order.
        sys.stdout.flush()

    # Here we are going to combine all the "normal records" into a single commit
    if len(normal_records):
        unique_comments = {}

        for record in normal_records:
            if record.action == Actions.FILE_MODIFY:
                    blob_mark = print_blob_for_file(record.branch, record.path, record.timestamp)
                    record.set_blob_mark(blob_mark)
            if record.comment:
                if record.comment not in unique_comments:
                    unique_comments[record.comment] = []
                unique_comments[record.comment].append(record.path)

        mark = mark + 1
        branch = record.branch
        if branch == record.mainline:
            branch = "master"
        sys.stdout.buffer.write(("commit refs/heads/%s\n" % translate_branch_name(branch)).encode("utf-8"))
        sys.stdout.buffer.write(("mark :%d\n" % mark).encode("utf-8"))
        sys.stdout.buffer.write(("author %s <%s> %s %s\n" % (normal_records[0].author, normal_records[0].author, normal_records[0].timestamp, timezone)).encode("utf-8"))
        sys.stdout.buffer.write(("committer %s <%s> %s %s\n" % (normal_records[0].author, normal_records[0].author, normal_records[0].timestamp, timezone)).encode("utf-8"))
        if len(unique_comments):
            full_comment = ""
            for comment, files in unique_comments.items():
                full_comment += (comment + "\n")
                # If we're combining multiple comments lets tell the user which
                # file(s) each comment is associated with
                if len(unique_comments) > 1:
                    full_comment += "Above comment references the following files:\n"
                    for file in files:
                        full_comment += "- %s\n" % file
                    full_comment += "\n"
            sys.stdout.buffer.write(b"data %d\n" % len(full_comment))
            sys.stdout.buffer.write(full_comment.encode("utf-8"))
        else:
            sys.stdout.buffer.write(b"data 0\n")

        for record in normal_records:
            # fixup the paths so the root of the git repo matches the root
            # of the scm repo origonally passed in
            full_path = pathlib.PurePosixPath(record.path)
            repo = pathlib.PurePosixPath(record.repo)
            path = full_path.relative_to(repo)
            if record.origPath and record.origPath != "NULL":
                full_origPath = pathlib.PurePosixPath(record.origPath)
                origPath = full_origPath.relative_to(repo)

            if record.action == Actions.FILE_MODIFY:
                if record.origPath and record.origPath != "NULL":
                    # looks like there was a previous rename.  use the original name.
                    sys.stdout.buffer.write(("M 100644 :%d %s\n" % (record.blob_mark, origPath)).encode("utf-8"))
                else:
                    # no previous rename.  good to use the current name.
                    sys.stdout.buffer.write(("M 100644 :%d %s\n" % (record.blob_mark, path)).encode("utf-8"))
            elif record.action == Actions.FILE_DELETE:
                sys.stdout.buffer.write(("D %s\n" % path).encode("utf-8"))
            elif record.action == Actions.FILE_RENAME:
                # NOTE we're not using record.path here, as there may have been multiple renames in the file's history
                full_data_path = pathlib.PurePosixPath(record.data)
                data = full_data_path.relative_to(repo)
                sys.stdout.buffer.write(("R %s %s\n" % (origPath, data)).encode("utf-8"))
            else:
                raise Exception("Unknown record action")

        # Flush our buffer. We are going to print a lot, so this helps everything
        # stay in the right order.
        sys.stdout.flush()


def cmd_export(database):
    sys.stderr.write("\n[+] Beginning export phase...\n")

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
        process_database_record_group(c2)
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

    sys.stderr.write("\n[+] Export complete.  Your new Git repository is ready to use.\nDon't forget to run `git repack` at some future time to improve data locality and access performance.\n\n")


def cmd_verify(mainline, path):
    # TODO verify that all Surround baseline branches are identical to their Git counterparts
    # TODO verify that all Surround snapshot branches are identical to their Git counterparts
    # should be able to do this without database
    pass


def handle_command(parser):
    args = parser.parse_args()

    if args.install:
        global sscm
        sscm = args.install[0]

    if args.username and args.password:
        global username
        global password
        username = args.username[0]
        password = args.password[0]

    if args.host and args.port:
        global host
        global port
        host = args.host[0]
        port = args.port[0]

    if args.command == "parse" and args.mainline and args.path:
        verify_surround_environment()
        database = create_database()
        cmd_parse(args.mainline[0], args.path[0], database)
    elif args.command == "export" and args.database:
        verify_surround_environment()
        database = sqlite3.connect(args.database[0])
        cmd_export(database)
    elif args.command == "all" and args.mainline and args.path:
        # typical case
        verify_surround_environment()
        database = create_database()
        cmd_parse(args.mainline[0], args.path[0], database)
        cmd_export(database)
    elif args.command == "verify" and args.mainline and args.path:
        # the 'verify' operation must take place after the export has completed.
        # as such, it will always be conducted as its own separate operation.
        verify_surround_environment()
        cmd_verify(args.mainline[0], args.path[0])
    else:
        parser.print_help()
        sys.exit(1)


def parse_arguments():
    # TODO: fixup args to have required args
    parser = argparse.ArgumentParser(prog='export-surround-to-git.py', description='Exports history from Seapine Surround in a format parsable by `git fast-import`.', formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('-m', '--mainline', nargs=1, help='Mainline branch containing history to export')
    parser.add_argument('-p', '--path', nargs=1, help='Path containing history to export')
    parser.add_argument('-d', '--database', nargs=1, help='Path to local database (only used when resuming an export)')
    parser.add_argument('-u', '--username', nargs=1, help='Username for the scm server')
    parser.add_argument('-pw', '--password', nargs=1, help='Password for the scm server')
    parser.add_argument('-i', '--install', nargs=1, help='Full path to sscm executable')
    parser.add_argument('-ho', '--host', nargs=1, help='Surround SCM server host address')
    parser.add_argument('-po', '--port', nargs=1, help='Surround SCM server port number')
    parser.add_argument('--version', action='version', version='%(prog)s ' + VERSION)
    parser.add_argument('command', nargs='?', default='all')
    parser.epilog = "Example flow:\n\tsscm setclient ...\n\tgit init my-new-repo\n\tcd my-new-repo\n\texport-surround-to-git.py -m Sandbox -p \"Sandbox/Merge Test\" -f blah.txt | git fast-import --stats --export-marks=marks.txt\n\t...\n\tgit repack ..."
    return parser


def main():
    parser = parse_arguments()
    handle_command(parser)
    sys.exit(0)


if __name__ == "__main__":
    main()
