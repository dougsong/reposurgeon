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
        self.nmarks = 0
    def fast_import(fp):
        "Initialize repo object from fast-import stream."
        os.mkdir(".rs")     # May throw OSError
        os.mkdir(".rs/history")
        tags_to_marks = {}
        import_line = 0
        def error(msg):
            raise RepoSurgeonException(msg + (" at line " + `import_line`)
        def read_data(dp):
            if line.startswith("data <<"):
                delim = line[7:]
                while True:
                    dataline = fp.readline()
                    if dataline == delim:
                        break
                    elif not dataline:
                        raise RepoSurgeonException("EOF while reading blob")
            else:
                try:
                    count = int(line[5:])
                    dp.write(fp.read(count))
                except ValueError:
                    raise error("bad count in data")
            else:
                    raise error("malformed data header")
            return
        for line in fp:
            import_line += 1
            if line.startswith("#") or line.startswith("checkpoint"):
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
                nextline = fp.readline()
                import_line += 1
                if readline.startwith("mark"):
                    mark = nextline[5:].strip()
                    read_data(open(".rs/blob" + mark, "w")).close()
                    self.nmarks += 1
                else:
                    error("missing mark after blob")
            elif line.startswith("data"):
                error("unexpected data object")
            elif line.startswith("commit"):
                continue     # FIXME
            elif line.startswith("reset"):
                tagname = line[4:].strip()
                nextline = fp.readline()
                import_line += 1
                if nextline.startswith("from"):
                    tags_to_marks[tagname] = nextline[5:].strip()
                else:
                    error("missing from after reset")
            elif line.startswith("tag"):
                tagname = line[4:].strip()
                nextline = fp.readline()
                import_line += 1
                if nextline.startswith("from"):
                    tags_to_marks[tagname] = nextline[5:].strip()
                else:
                    error("missing from after tag")
                self.read_data(open(".rs/tag" + tagname, "w")).close()
            else:
                raise error("unexpected line in import stream")

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
