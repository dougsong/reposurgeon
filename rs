#!/usr/bin/env python
#
# rs - a repository surgeon.
#
import sys, os, getopt, commands

class GenericCommit:
    "Generic commit object."
    def __init__(self, timestamp, cid, comment, branch, parents):
        self.timestamp = timestamp
        self.id = cid
        self.comment = comment
        self.branch = branch
        self.parents = parents

class GitSlicer:
    "Repo-slicing methods for the Git version-control system"
    def __init__(repo):
        pass

if __name__ == '__main__':
    #subcommand = sys.argv[1]
    #(options, arguments) = getopt.getopt(sys.argv[2:], "")
    print "No mainline code yet"
