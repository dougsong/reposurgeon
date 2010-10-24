#!/usr/bin/env python
#
# rs - a repository surgeon.
#
import sys, os, getopt, commands, cStringIO

class Action:
    "Represents an instance pof a person acting on the repo."
    def __init__(self, name, email, when):
        self,name = name
        self.email = email
        self.when = when
    def __repr__(self):
        return self.name + " " + self.email + " " + self.when

class Commit:
    "Generic commit object."
    def __init__(self):
        self.mark = None             # Mark name of commit (may be None)
        self.author = None           # Author of commit
        self.committer = None        # Person responsible for committing it.
        self.comment = None          # Commit comment
        self.parents = None          # List of parent nodes
        self.branch = None           # branch name (deduced optimization hack)
        self.fileops = []            # blob and file operation list

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
        self.nmarks = 0
        self.import_line = 0
    def error(self, msg, atline=True):
        if atline:
            raise RepoSurgeonException(msg + (" at line " + `self.import_line`))
        else:
            raise RepoSurgeonException(msg)
    def fast_import(self, fp):
        "Initialize repo object from fast-import stream."
        try:
            os.mkdir(".rs")     # May throw OSError
        except OSError:
            self.error("can't create operating directory", atline=False)
        refs_to_marks = {}
        self.import_line = 0
        linebuffers = []
        currentbranch = "master"
        ncommits = 0
        def read_data(dp, line=None):
            if not line:
                line = readline()
            if line.startswith("data <<"):
                delim = line[7:]
                while True:
                    dataline = fp.readline()
                    if dataline == delim:
                        break
                    elif not dataline:
                        raise RepoSurgeonException("EOF while reading blob")
            elif line.startswith("data"):
                try:
                    count = int(line[5:])
                    dp.write(fp.read(count))
                except ValueSelf.Error:
                    raise self.error("bad count in data")
            else:
                raise self.error("malformed data header")
            return
        def readline():
            if linebuffers:
                return linebuffers.pop()
            else:
                self.import_line += 1
                return fp.readline()
        def pushback(line):
            self.linebuffers.append(line)
        while True:
            line = readline()
            if not line:
                break
            elif line.startswith("#") or line.startswith("checkpoint"):
                continue
            elif not line.strip():
                continue
            elif line.startswith("progress"):
                sys.stdout.write(line[9:])
            elif line.startswith("options"):
                continue     # Might need real code here someday
            elif line.startswith("options"):
                continue     # Might need real code here someday
            elif line.startswith("blob"):
                nextline = readline()
                if line.startswith("mark"):
                    mark = nextline[5:].strip()
                    read_data(open(".rs/blob-" + mark, "w")).close()
                    self.nmarks += 1
                else:
                    self.error("missing mark after blob")
            elif line.startswith("data"):
                self.error("unexpected data object")
            elif line.startswith("commit"):
                commit = Commit()
                commit.branch = currentbranch
                ncommits += 1
                inlinecount = 0
                while True:
                    nextline = readline()
                    if not line:
                        self.error("EOF after commit")
                    elif line.startswith("mark"):
                        self.mark = nextline[5:].strip()
                        self.nmarks += 1
                    elif line.startswith("author"):
                        try:
                            (name, email, when) = line.split()
                            commit.author = Action(name, email, when)
                        except ValueSelf.Error:
                            self.error("malformed author line")
                    elif line.startswith("committer"):
                        try:
                            (name, email, when) = line.split()
                            commit.committer = Action(name, email, when)
                        except ValueSelf.Error:
                            self.error("malformed committer line")
                    elif line.startswith("data"):
                        dp = self.read_data(cStringIO.StringIO(), line)
                        commit.comment = dp.getvalue()
                        dp.close()
                    elif line.startswith("from") or line.startswith("merge"):
                        commit.ancestors.append(line.split()[1])
                    elif line[0] in ("C", "D", "R"):
                        commit.filemap.append(line.strip().split())
                    elif line == "filedeletall\n":
                        commit.filemap.append("filedeleteall")
                    elif line[0] == "M":
                        (op, mode, ref, path) = line.split()
                        if ref[0] == ':':
                            fileop.append((op, mode, ref, path))
                        elif ref[0] == 'inline':
                            copyname = ".rs/inline-" + `inline_count`
                            self.read_data(open(copyname, "w")).close()
                            inline_count += 1
                            fileop.append((op, mode, ref, path, copyname))
                        else:
                            self.error("unknown content type in filemodify")
                    else:
                        pushback(line)
                        break
                self.commits.append(commit)
            elif line.startswith("reset"):
                currentbranch = line[4:].strip()
                nextline = readline()
                if nextline.startswith("from"):
                    refs_to_marks[currentbranch] = nextline[5:].strip()
                else:
                    self.error("missing from after reset")
            elif line.startswith("tag"):
                tagname = line[4:].strip()
                nextline = readline()
                if nextline.startswith("from"):
                    refs_to_marks[tagname] = nextline[5:].strip()
                else:
                    self.error("missing from after tag")
                self.read_data(open(".rs/tag-" + tagname, "w")).close()
            else:
                raise self.error("unexpected line in import stream")

def act(cmd):
    (err, out) = commands.getstatusoutput(cmd)
    if err:
        raise RepoSurgeonException("'%s' failed" % cmd)
    else:
        return out

def fatal(msg):
    print >>sys.stderr, "rs:", msg
    raise SystemExit, 1

def usage():
    print >>sys.stderr,"""\
usage: rs command [option..]

Commands are as follows

    help       -- emit this help message             
    load       -- prepare a repo for surgery
    clear      -- clear the operating theater
"""

if __name__ == '__main__':
    sys.argv.pop(0)
    if not sys.argv:
        usage()
        raise SystemExit, 0
    command = sys.argv.pop(0)
    (options, arguments) = getopt.getopt(sys.argv[2:], "")
    if command in ("help", "usage"):
        usage()
    elif command == "clear":
        os.system("rm -fr .rs")
    elif command == "load":
        repo = GenericRepo()
        try:
            if not arguments:
                repo.fast_import(sys.stdin)
            else:
                fatal("rs: unsupported load mode")
        except RepoSurgeonException, e:
            fatal(e.msg)
    else:
        print >>sys.stderr,"rs: unknown command"

# end
