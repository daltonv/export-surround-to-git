import subprocess
import pathlib
import sys
import time
import os


class SSCM:
    def __init__(self, exe, host, port, username, password):
        self.exe = exe
        self.host = host
        self.port = port
        self.username = username
        self.password = password

        self.sscmhist = pathlib.Path(sys.path[0]) / "sscmhist" / "sscmhist.exe"
        if not self.sscmhist.exists():
            raise Exception("sscmhist does not exit. Try compiling it")

        self.__verify_surround_env__()

    def __verify_surround_env__(self):
        cmd = self.exe

        with open(os.devnull, "w") as fnull:
            p = subprocess.Popen(cmd, shell=True, stdout=fnull, stderr=fnull)
            p.communicate()
            if p.returncode != 1:
                raise Exception("%s failed to run. Check your -i argument." % cmd)

    def __get_sscm_output__(self, cmd, get_lines=True):
        # helper function to clean each item on a line since sscm has lots of
        # newlines
        p = subprocess.Popen(
            cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        stdoutdata, stderrdata = p.communicate()
        stdoutdata = stdoutdata.decode("utf8")
        stderrdata = (stderrdata.strip()).decode("utf8")

        if get_lines:
            output = [real_line for real_line in stdoutdata.splitlines() if real_line]
        else:
            output = stdoutdata

        return output, stderrdata

    def __fix_file_name__(self, file):
        # helper function to fix up any file names that will throw off the
        # sscm tool with escape sequences.
        fixed_file = file.replace("$", "\$")
        fixed_file = fixed_file.replace("~", "\~")
        return fixed_file

    def ls(self, branch, repo, get_lines=True):
        cmd = self.exe + ' ls -b"%s" -p"%s" -r ' % (branch, repo)
        if self.username and self.password:
            cmd += '-y"%s":"%s" ' % (self.username, self.password)

        output, stderrdata = self.__get_sscm_output__(cmd, get_lines)

        return output, stderrdata

    def lsbranch(self, mainline, get_lines=True):
        # lsbranch will give us every branch under a mainline if you give it
        # any repo in a mainline. use the -o option here to get a full path
        # definition of each branch. This will help us parse later
        cmd = self.exe + ' lsbranch -p"%s" -o ' % mainline
        if self.username and self.password:
            cmd += '-y"%s":"%s" ' % (self.username, self.password)

        output, stderrdata = self.__get_sscm_output__(cmd, get_lines)

        return output, stderrdata

    def lsremoved(self, item, branch, repo, get_lines=True):
        fixed_item = self.__fix_file_name__(item)

        cmd = self.exe + ' property "%s" -b"%s" -p"%s" -d ' % (fixed_item, branch, repo)
        if self.username and self.password:
            cmd += '-y"%s":"%s" ' % (self.username, self.password)

        output, stderrdata = self.__get_sscm_output__(cmd, get_lines)

        return output, stderrdata

    def branchhistory(self, branch, repo, get_lines=True):
        cmd = self.exe + ' branchhistory -b"%s" -p"%s" ' % (branch, repo)
        if self.username and self.password:
            cmd += '-y"%s":"%s" ' % (self.username, self.password)

        output, stderrdata = self.__get_sscm_output__(cmd, get_lines)

        return output, stderrdata

    def branchproperty(self, branch, repo, get_lines=True):
        cmd = self.exe + ' branchproperty -b"%s" -p"%s" ' % (branch, repo)
        if self.username and self.password:
            cmd += '-y"%s":"%s" ' % (self.username, self.password)

        output, stderrdata = self.__get_sscm_output__(cmd, get_lines)

        return output, stderrdata

    def history(
        self, file, branch, repo, version=None, recursive=False, get_lines=True
    ):
        fixed_file = self.__fix_file_name__(file)

        cmd = self.exe + ' history "%s" -b"%s" -p"%s" ' % (fixed_file, branch, repo)
        if self.username and self.password:
            cmd += '-y"%s":"%s" ' % (self.username, self.password)
        if version:
            cmd += '-v"%d:%d" ' % (version, version)
        if recursive:
            cmd += "-r "

        output, stderrdata = self.__get_sscm_output__(cmd, get_lines)

        return output, stderrdata

    def customhistory(self, file, branch, repo, get_lines=True):
        fixed_file = self.__fix_file_name__(file)

        cmd = str(self.sscmhist) + " %s %s " % (self.host, self.port)
        if self.username and self.password:
            cmd += "%s %s " % (self.username, self.password)
        else:
            # TODO handle this better
            cmd += "NULL NULL "
        cmd += '"%s" "%s" "%s" "%s"' % (branch, branch, repo, fixed_file)

        output, stderrdata = self.__get_sscm_output__(cmd, get_lines)

        return output, stderrdata

    def get(self, file, branch, repo, scratchDir, time_string=None, get_lines=True):
        fixed_file = self.__fix_file_name__(file)

        cmd = self.exe + ' get "%s" -b"%s" -p"%s" -d"%s" -f -i -e ' % (
            fixed_file,
            branch,
            repo,
            scratchDir,
        )
        if self.username and self.password:
            cmd += '-y"%s":"%s" ' % (self.username, self.password)
        if time_string:
            cmd += '-s"%s" ' % time_string

        output, stderrdata = self.__get_sscm_output__(cmd, get_lines)

        return output, stderrdata
