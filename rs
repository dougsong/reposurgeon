#!/usr/bin/env python
#
# rs - a repository surgeon.
#
import sys, os, getopt, commands, cStringIO, cmd, tempfile

#
# All knowledge about specific version-control systems lives in the
# following dictionary. The key is the subdirectory name that tells us
# we have a given VCS active.  The values in the tuple are,
# respectively:
#
# * Name of the SCM for diagnostic messages
# * Command to export from the SCM to the interchange format
# * Command to initialize a new repo
# * Command to import from the interchange format
# * Command to check out working copies of the repo files.
#
# Note that some of the commands used here are plugins or extenstions
# that are not part of the basic VCS. Thus these may fail when called;
# we need to be prepared to cope with that.
#
# Subversion/RCS/CVS aren't in this table because exporting from them
# requires fixups of usernames in the committer information to full
# email addresses.  Trying to handle that entirely inside this tool
# would be excessively messy, so we don't. Instead we let the user
# transform dump files and cope with the export/import himself.
#
vcstypes = [
     ("git",
      ".git",
      "git fast-export -M -C --all >%s",
      "git init",
      "git fast-import <%s",
      "git checkout"),
     # FIXME: hg and bzr methods are untested
     ("hg",
      ".hg",
      "hg-fast-export.sh %s",   # Not part of stock hg
      "hg init",
      "hg fast-import %s",      # Not part of stock hg
      "hg checkout"),
     ("bzr",
      ".bzr",
      "bzr-fast-export --plain %s",
      "bzr init",
      "bzr fast-import %s",
      "bzr checkout"),
    ]

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
             % (self.name, self.committish, self.tagger, len(self.comment), self.comment)
        
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
        st += "data %d\n%s\n" % (len(self.comment), self.comment) 
        if self.parents:
            st += "from %s\n" % self.parents[0]
        for ancestor in self.parents[1:]:
            st += "merge %s\n" % self.parents[0]
        for op in self.fileops:
            if type(op) == type(""):
                st += op + "\n"
            else:
                st += " ".join(op[:4]) + "\n"
                if op[2] == 'inline':
                    fp = open(op[4])
                    content = fp.read()
                    fp.close()
                    st += "data %d\n%s\n" % (len(content), content)
        return st + "\n"

class RepoSurgeonException:
    def __init__(self, msg):
        self.msg = msg

class Repository:
    "Generic repository object."
    def __init__(self):
        self.repotype = None
        self.commits = []   # A list of commit objects
        self.branches = []  # A list of branchname-to-commit mappings
        self.tags = []      # List of tag-to-commit
        self.nmarks = 0
        self.nblobs = 0
        self.import_line = 0
        self.subdir = ".rs"
    def error(self, msg, atline=True):
        if atline:
            raise RepoSurgeonException(msg + (" at line " + `self.import_line`))
        else:
            raise RepoSurgeonException(msg)
    def __del__(self):
        os.system("rm -fr %s" % (self.subdir,))
    def fast_import(self, fp, verbose=False):
        "Initialize repo object from fast-import stream."
        try:
            os.system("rm -fr %s; mkdir %s" % (self.subdir, self.subdir))
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
                    read_data(open(self.subdir + "/blob-" + mark, "w")).close()
                    self.nmarks += 1
                    self.nblobs += 1
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
                            copyname = self.subdir + "/blob-" + ref
                            commit.fileops.append((op, mode, ref, path, copyname))
                        elif ref[0] == 'inline':
                            copyname = self.subdir + "/inline-" + `inline_count`
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
    def fast_export(self, fp):
        "Dump the repo object in fast-export format."
        for commit in self.commits:
            for fileop in commit.fileops:
                if type(fileop) == type(()):
                    ref = fileop[2]
                    if ref[0] == ':':
                        dp = open(fileop[4])
                        content = dp.read()
                        dp.close()
                        fp.write("blob %s\ndata %d\n%s\n" % (ref, len(content), content))
            fp.write(repr(commit))
        for tag in self.tags:
            fp.write(repr(tag))

def read_repo(source):
    "Read a repository using fast-import."
    if source == '-':
        repo = Repository()
        repo.fast_import(sys.stdin)
    elif not os.path.exists(source):
        print "rs: %s does not exist" % source
        return None
    elif not os.path.isdir(source):
        repo = Repository()
        repo.fast_import(open(source))
    else:
        for (name, dirname, exporter, initializer, importer, checkout) in vcstypes:
            subdir = os.path.join(source, dirname)
            
            if os.path.exists(subdir) and os.path.isdir(subdir):
                break
        else:
            print "rs: could not find a repository under %s" % source
            return None
        print "rs: recognized %s repository under %s" % (name, source)
        try:
            repo = Repository()
            (tfdesc, tfname) = tempfile.mkstemp()
            cmd = "cd %s >/dev/null;" % source
            cmd += exporter % tfname
            act(cmd)
            tp = open(tfname)
            repo.fast_import(tp);
            tp.close()
        finally:
            os.remove(tfname)
    (repo.type, repo.initializer, repo.importer, repo.checkout) = (name,
                                                                   initializer,
                                                                   importer,
                                                                   checkout)
    return repo

def write_repo(repo, target):
    "Write a repository using fast-export."
    if target == '-':
        repo.fast_export(sys.stdout)
    # FIXME: Have to decide a policy here

def act(cmd):
    (err, out) = commands.getstatusoutput(cmd)
    if err:
        raise RepoSurgeonException("'%s' failed" % cmd)
    else:
        return out

def fatal(msg):
    print >>sys.stderr, "rs:", msg
    raise SystemExit, 1

class RepoSurgeon(cmd.Cmd):
    "Repository surgeon command interpreter."
    def __init__(self):
        cmd.Cmd.__init__(self)
        self.verbose = 0
        self.prompt = "rs# "
        self.repo = None
    def postcmd(self, stop, line):
        if line == "EOF":
            return True
    def do_verbose(self, line):
        "Set the interpreter's verbosity level."
        try:
            self.verbose = int(line)
        except ValueError:
            print "rs: verbosity value must be an integer"
    def do_read(self, line):
        "Read in a repository for surgery."
        if not line:
            line = '.';
        self.repo = read_repo(line)
        if self.verbose:
            print "rs: %d commits, %d blobs, %d marks, %d tags" % \
                  (len(self.repo.commits),
                   self.repo.nblobs,
                   self.repo.nmarks,
                   len(self.repo.tags))
    def do_write(self, line):
        "Write out the results of repo surgery."
        if not line:
            line = '-'
        write_repo(self.repo, line)
    def do_EOF(self, line):
        "Terminate the browser."
        return True

if __name__ == '__main__':
    try:
        interpreter = RepoSurgeon()
        if not sys.argv[1:]:
            sys.argv.append("-")
        for arg in sys.argv[1:]:
            for cmd in arg.split(";"):
                if cmd == '-':
                    interpreter.cmdloop()
                else:
                    interpreter.onecmd(cmd)
    except RepoSurgeonException, e:
        fatal(e.msg)
    except KeyboardInterrupt:
        print ""

# end
