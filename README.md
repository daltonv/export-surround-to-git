export-surround-to-git
======================

Python script to export history from Surround Surround in a format parsable by `git fast-import`.

This method is capable of preserving complete history, timestamps, authors, comments, branches, snapshots, etc.


# Project Status

This project was last tested using the following environment:

```
#   * Python 3.8.5
#   * bash / git bash for windows
#   * sscm command-line client version:  2019.1.0 Windows
#   * Windows 10
#   * Ubuntu 20.04.2 LTS
```


# Usage
Currently the sscmhist.exe has to be manually compiled before running the
python script. A Makefile tailored to the Visual Studio Compiler is provided
under the sscmhist folder of this repo. Although you will have to tweak the
paths for the SCM dependencies.

```
usage: export-surround-to-git.py [-h] [-m MAINLINE] [-p PATH] [-d DATABASE] [-u USERNAME] [-pw PASSWORD] [-i INSTALL] [-ho HOST] [-po PORT] [--email EMAIL] [--version] [command]

Exports history from Seapine Surround in a format parsable by `git fast-import`.

positional arguments:
  command

optional arguments:
  -h, --help            show this help message and exit
  -m MAINLINE, --mainline MAINLINE
                        Mainline branch containing history to export
  -p PATH, --path PATH  Path containing history to export
  -d DATABASE, --database DATABASE
                        Path to local database (only used when resuming an export)
  -u USERNAME, --username USERNAME
                        Username for the scm server
  -pw PASSWORD, --password PASSWORD
                        Password for the scm server
  -i INSTALL, --install INSTALL
                        Full path to sscm executable
  -ho HOST, --host HOST
                        Surround SCM server host address
  -po PORT, --port PORT
                        Surround SCM server port number
  --email EMAIL         Domain for the email address
  --version             show program's version number and exit

Example flow:
        git init my-new-repo
        cd my-new-repo
        export-surround-to-git.py -m Sandbox -p "Sandbox/Merge Test" -f blah.txt | git fast-import --stats --export-marks=marks.txt
        ...
        git repack ...
```

## Example flow
```
git init my-new-repo
cd my-new-repo
export-surround-to-git.py -m Sandbox -p "Sandbox/Merge Test" | git fast-import --stats --export-marks=marks.txt
...
git repack ...
```


# Further Reading

See the [manpage for git fast-import](https://www.kernel.org/pub/software/scm/git/docs/git-fast-import.html).
