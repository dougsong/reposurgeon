#!/usr/bin/env python
#
# rs - a repository surgeon.
#
import sys, os, getopt, commands

class GenericCommit:
    "Generic commit object."
    def __init__(self, timestamp, comment, parents):
        self.timestamp = timestamp   # Primary key
        self.comment = comment       # Commit comment
        self.parents = parents       # List of parent nodes
        self.branch = branch         # branch name (deduced optimization hack)

class GenericRepo:
    "Generic repository object."
    def __init__(self):
        self.commits = []   # A list of commit objects
        self.branches = []  # A list of branchname-to-commit mappings
        self.tags = []      # List of tag-to-commit
        self.map = []       # List of commit-to-parent mappings

class GitSlicer:
    "Repo-slicing methods for the Git version-control system"
    def __init__(repo):
        pass

if __name__ == '__main__':
    #subcommand = sys.argv[1]
    #(options, arguments) = getopt.getopt(sys.argv[2:], "")
    print "No mainline code yet"
