#!/usr/bin/env python
#
# rs - a repository surgeon.
#
import sys, os, getopt, commands

class GenericCommit:
    "Generic commit object."
    def __init__(self, timestamp, author, committer, comment, parents):
        self.timestamp = timestamp   # Primary key
        self.author = author         # Aujtor of commit
        self.committer = committer   # Person responsible for committing it.
        self.comment = comment       # Commit comment
        self.parents = parents       # List of parent nodes
        self.branch = branch         # branch name (deduced optimization hack)

class RepoSurgeonException:
    def __init__(self, msg):
        self.msg = msg

class GenericRepo:
    "Generic repository object."
    def __init__(self):
        self.commits = []   # A list of commit objects
        self.branches = []  # A list of branchname-to-commit mappings
        self.tags = []      # List of tag-to-commit
        self.map = []       # List of commit-to-parent mappings
        self.__marks = []
    def fast_import(fp):
        "Initialize repo object from fast import."
        os.mkdir(".rs")     # May throw os.error
        os.mkdir(".rs/history")
        mark = None
        for line in fp:
            if line.startswith("#") or line.startswith("checkpoint"):
                continue
            elif line.startswith("progress"):
                sys.stdout.write(line)
            elif line.startswith("options"):
                continue     # Might need real code here someday
            elif line.startswith("options"):
                continue     # Might need real code here someday
            elif line.startswith("blob"):
                continue     # FIXME
            elif line.startswith("commit"):
                continue     # FIXME
            elif line.startswith("reset"):
                continue     # FIXME
            elif line.startswith("tag"):
                continue     # FIXME
            else:
                raise RepoSurgeonException("unexpected line in import stream")

def act(cmd):
    (err, out) = commands.getstatusoutput(cmd)
    if err:
        raise RepoSurgeonException("'%s' failed" % cmd)
    else:
        return out

if __name__ == '__main__':
    #subcommand = sys.argv[1]
    #(options, arguments) = getopt.getopt(sys.argv[2:], "")
    print "No mainline code yet"
