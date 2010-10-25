#!/usr/bin/env python
#
# rs - a repository surgeon.
#
import sys, os, getopt, commands, cStringIO

class Action:
    "Represents an instance of a person acting on the repo."
    def __init__(self, person):
        person = person.replace(" <", "|").replace("> ", "|")
        (self.name, self.email, self.when) = person.strip().split("|")
    def __repr__(self):
        return self.name + " <" + self.email + "> " + self.when

class Tag:
    "Represents an annotated tag."
    def __init__(self, name, committish, tagger, content):
        self.name = name
        self.committish = tagger
        self.tagger = tagger
        self.comment = content
    def __repr__(self):
        return "tag %s\nfrom %s\ntagger %s\ndata %d\n%s\n\n" \
             % (self.name, self.committish, self.tagger, self.content)
        
class Commit:
    "Generic commit object."
    def __init__(self):
        self.mark = None             # Mark name of commit (may be None)
        self.author = None           # Author of commit
        self.committer = None        # Person responsible for committing it.
        self.comment = None          # Commit comment
        self.parents = []            # List of parent nodes
        self.branch = None           # branch name (deduced optimization hack)
        self.fileops = []            # blob and file operation list
    def __repr__(self):
        st = "commit %s\n" % self.branch
        if self.mark:
            st += "mark %s\n" % self.mark
        if self.author:
            st += "author %s\n" % self.author
        if self.committer:
            st += "committer %s\n" % self.committer
        st += "data %d\n%s\n"
        if self.parents:
            st += "from %s\n" % self.parents[0]
        for ancestor in parents[1:]:
            st += "merge %s\n" % self.parents[0]
        for op in fileops:
            if type(op) == type(""):
                st += op + "\n"
            else:
                str += " ".join(op) + "\n"
        return st + "\n"

class RepoSurgeonException:
    def __init__(self, msg):
        self.msg = msg

class Repository:
    "Generic repository object."
    def __init__(self):
        self.commits = []   # A list of commit objects
        self.branches = []  # A list of branchname-to-commit mappings
        self.tags = []      # List of tag-to-commit
        self.nmarks = 0
        self.import_line = 0
    def error(self, msg, atline=True):
        if atline:
            raise RepoSurgeonException(msg + (" at line " + `self.import_line`))
        else:
            raise RepoSurgeonException(msg)
    def fast_import(self, argv):
        "Initialize repo object from fast-import stream."
        verbose = False
        (options, arguments) = getopt.getopt(argv[1:], "v")
        for (opt, arg) in options:
            if opt == '-v':
                verbose = True
        if not arguments:
            fp = sys.stdin
        else:
            error("load subcommand does not take arguments", atline=False)
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
                raise self.error("malformed data header %s" % `line`)
            return dp
        def readline():
            if linebuffers:
                line = linebuffers.pop()
            else:
                self.import_line += 1
                line = fp.readline()
                if verbose:
                    print line.rstrip()
            return line
        def pushback(line):
            linebuffers.append(line)
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
                line = readline()
                if line.startswith("mark"):
                    mark = line[5:].strip()
                    read_data(open(".rs/blob-" + mark, "w")).close()
                    self.nmarks += 1
                else:
                    self.error("missing mark after blob")
            elif line.startswith("data"):
                self.error("unexpected data object")
            elif line.startswith("commit"):
                commit = Commit()
                commit.branch = line.split()[1]
                ncommits += 1
                inlinecount = 0
                while True:
                    line = readline()
                    if not line:
                        self.error("EOF after commit")
                    elif line.startswith("mark"):
                        self.mark = line[5:].strip()
                        self.nmarks += 1
                    elif line.startswith("author"):
                        try:
                            commit.author = Action(line[7:])
                        except ValueError:
                            self.error("malformed author line")
                    elif line.startswith("committer"):
                        try:
                            commit.committer = Action(line[10:])
                        except ValueError:
                            self.error("malformed committer line")
                    elif line.startswith("data"):
                        dp = read_data(cStringIO.StringIO(), line)
                        commit.comment = dp.getvalue()
                        dp.close()
                    elif line.startswith("from") or line.startswith("merge"):
                        commit.parents.append(line.split()[1])
                    elif line[0] in ("C", "D", "R"):
                        commit.fileops.append(line.strip().split())
                    elif line == "filedeletall\n":
                        commit.fileops.append("filedeleteall")
                    elif line[0] == "M":
                        (op, mode, ref, path) = line.split()
                        if ref[0] == ':':
                            commit.fileops.append((op, mode, ref, path))
                        elif ref[0] == 'inline':
                            copyname = ".rs/inline-" + `inline_count`
                            self.read_data(open(copyname, "w")).close()
                            inline_count += 1
                            commit.fileops.append((op, mode, ref, path, copyname))
                        else:
                            self.error("unknown content type in filemodify")
                    else:
                        pushback(line)
                        break
                self.commits.append(commit)
            elif line.startswith("reset"):
                currentbranch = line[4:].strip()
                line = readline()
                if line.startswith("from"):
                    refs_to_marks[currentbranch] = line[5:].strip()
                else:
                    pushback(line)
            elif line.startswith("tag"):
                tagname = line[4:].strip()
                line = readline()
                if line.startswith("from"):
                    referent = line[5:].strip()
                else:
                    self.error("missing from after tag")
                line = readline()
                if line.startswith("tagger"):
                        try:
                            tagger = Action(line[7:])
                        except ValueError:
                            self.error("malformed tagger line")
                else:
                    self.error("missing tagger after from in tag")
                dp = read_data(cStringIO.StringIO())
                self.tags.append(Tag(tagname,
                                     referent, tagger, dp.getvalue()))

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
    command = sys.argv[0]
    if command in ("help", "usage"):
        usage()
    elif command == "clear":
        os.system("rm -fr .rs")
    elif command == "load":
        try:
            repo = Repository()
            repo.fast_import(sys.argv)
        except RepoSurgeonException, e:
            fatal(e.msg)
    else:
        print >>sys.stderr,"rs: unknown command"

# end
