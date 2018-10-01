package main

// This code is intended to be hackable to support for special-purpose or
// custom operations, though it's even better if you can come up with a new
// surgical primitive general enough to ship with the stock version.  For
// either case, here's a guide to the architecture.
//
// The core classes are largely about deserializing and reserializing
// import streams.  In between these two operations the repo state
// lives in a fairly simple object, Repository. The main part of
// Repository is just a list of objects implementing the Event
// interface - Commits, Blobs, Tags, Resets, and Passthroughs.
// These are straightforward representations of the command types in
// an import stream, with Passthrough as a way of losslessly conveying
// lines the parser does not recognize.
//
//  +-------------+    +---------+    +-------------+
//  | Deserialize |--->| Operate |--->| Reserialize |
//  +-------------+    +---------+    +-------------+
//
// The general theory of reposurgeon is: you deserialize, you do stuff
// to the event list that preserves correctness invariants, you
// reserialize.  The "do stuff" is mostly not in the core classes, but
// there is one major exception.  The primitive to delete a commit and
// squash its fileops forwards or backwards is seriously intertwined
// with the core classes and actually makes up almost 50% of Repository
// by line count.
//
// The rest of the surgical code lives outside the core classes. Most
// of it lives in the RepoSurgeon class (the command interpreter) or
// the RepositoryList class (which encapsulated by-name access to a list
// of repositories and also hosts surgical operations involving
// multiple repositories). A few bits, like the repository reader and
// builder, have enough logic that's independent of these
// classes to be factored out of it.
//
// In designing new commands for the interpreter, try hard to keep them
// orthogonal to the selection-set code. As often as possible, commands
// should all have a similar form with a (single) selection set argument.
//
// VCS is not a core class.  The code for manipulating actual repos is bolted
// on the the ends of the pipeline, like this:
//
//  +--------+    +-------------+    +---------+    +-----------+    +--------+
//  | Import |--->| Deserialize |--->| Operate |--->| Serialize |--->| Export |
//  +--------+    +-------------+ A  +---------+    +-----------+    +--------+
//       +-----------+            |
//       | Extractor |------------+
//       +-----------+
//
// The Import and Export boxes call methods in VCS.
//
// Extractor classes build the deserialized internal representation directly.
// Each extractor class is a set of VCS-specific methods to be used by the
// RepoStreamer driver class.  Key detail: when a repository is recognized by
// an extractor it sets the repository type to point to the corresponding
// VCS instance.

// This code was translated from Python. It retains, for internal
// documentation purposes the Pyton convention of using leading
// underscores on field names to flag fields tht should never be
// referenced ouside a method of the associated struct.
//
// Differences from the Python version
// 1. whoami() does not read .lynxrc files
// 2. No Python plugins.
// 3. Regular expressions use Go syntax rather than Python. Little
//    difference in practice; the biggest deal is lack of lookbehinds
// 4. Go and Python disagree on what RFC822 format is, and neither is compatible
//    with the Git log date format, which claims to be RFC822 but isn't.  So
//    screw it - we always dump timestamps in RFC3339 now.

import (
	"bufio"
	"bytes"
	"compress/gzip"
	"crypto/sha1"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"net/mail"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"reflect"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode"

	terminal "golang.org/x/crypto/ssh/terminal"
	ianaindex "golang.org/x/text/encoding/ianaindex"
)

// Go's panic/defer/recover feature is a weak primitive for catchable
// exceptions, but it's all we have. So we write a throw/catch pair;
// throw() must pass its exception payload to panic(), catch() can only be
// called in a defer hook either at the current level or further up the
// call stack and must take recover() as its second argument.
//
// Here are the defined error classes:
//
// parse = malformed fast-import stream or Subversion dump.  Recover
// by aborting the parse and backing out whatever operation relied on it.
//
// command = general command failure, no specific cleanup required, abort
// to interpreter read-eval loop.
//
// extractor = unexpected VCS command behavior inside an extractor class.
// Abort the attempt to build a repo.
//
// mailbox = malformed mailbox-style input.  Abort merging those changes.
//
// Unlabeled panics are presumed to be unrecoverable and intended to be
// full aborts indicating a serious internal error.  These will call a defer
// hook that nukes the on-disk storage for repositories.

type exception struct {
	class string
	message string
}

func (e exception) Error() string {
	return e.message
}

func throw(class string, msg string, args ...interface{}) *exception {
	// We could call panic() in here but we leave it at the callsite
	// to clue the compiler in that no return after is required.
	e := new(exception)
	e.class = class
	e.message = fmt.Sprintf(msg, args...)
	return e
}

func catch(accept string, x interface{}) *exception {
	// Because recover() returns interface{}.
	// Return us to the world of type safety.
	if x == nil {
		return nil
	}
	err := x.(*exception)
	if err.class == accept {
		return err
	}
	panic(x)
}

// Change these in the unlikely the event this is ported to Windows
const userReadWriteMode = 0775	// rwxrwxr-x

func exists(pathname string) bool {
	_, err := os.Stat(pathname)
	return !os.IsNotExist(err)
}

func isdir(pathname string) bool {
	st, err := os.Stat(pathname)
	return err == nil && st.Mode().IsDir()
}

func isfile(pathname string) bool {
	st, err := os.Stat(pathname)
	return err == nil && st.Mode().IsRegular()
}

func getsize(pathname string) int64 {
	st, err := os.Stat(pathname)
	if err != nil {
		return -1
	}
	return st.Size()
}

func min(a, b int) int {
    if a < b {
        return a
    }
    return b
}

// filecopy does what it says, returning bytes copied and an error indication
func filecopy(src, dst string) (int64, error) {
        sourceFileStat, err := os.Stat(src)
        if err != nil {
                return 0, err
        }

        if !sourceFileStat.Mode().IsRegular() {
                return 0, fmt.Errorf("%s is not a regular file", src)
        }

        source, err := os.Open(src)
        if err != nil {
                return 0, err
        }
        defer source.Close()

        destination, err := os.Create(dst)
        if err != nil {
                return 0, err
        }
        defer destination.Close()
        nBytes, err := io.Copy(destination, source)
        return nBytes, err
}

// This representation optimizes for small memory footprint at the expense
// of speed.  To make the opposite trade we would do the obvious thing with
// map[string] bool.
type stringSet []string

func newStringSet(elements ...string) stringSet {
	set := make([]string, 0)
	return append(set, elements...)
}

func (s stringSet) Contains(item string) bool {
	for _, el := range s {
		if item == el {
			return true
		}
	}
	return false
}

func (s *stringSet) Remove(item string) bool {
	for i, el := range *s {
		if item == el {
			// Zero out the deleted element so it's GCed
			copy((*s)[i:], (*s)[i+1:])
			(*s)[len(*s)-1] = ""
			*s = (*s)[:len(*s)-1]
			return true
		}
	}
	return false
}

func (s *stringSet) Add(item string) {
	for _, el := range *s {
		if el == item {
			return
		}
	}
	*s = append(*s, item)
}

func (s stringSet) Subtract(other stringSet) stringSet {
	var diff stringSet
	for _, outer := range s {
		for _, inner := range other {
			if outer == inner {
				goto dontadd
			}
		}
		diff = append(diff, outer)
	dontadd:
	}
	return diff
}

func (s stringSet) Intersection(other stringSet) stringSet {
	// Naive O(n**2) method - don't use on large sets if you care about speed
	var intersection stringSet
	for _, item := range s {
		if other.Contains(item) {
			intersection = append(intersection, item)
		}
	}
	return intersection
}

func (s stringSet) Union(other stringSet) stringSet {
	// Naive O(n**2) method - don't use on large sets if you care about speed
	var union stringSet
	union = s[:]
	for _, item := range other {
		if !s.Contains(item) {
			union = append(union, item)
		}
	}
	return union
}

func (s *stringSet) String() string {
	if len(*s) == 0 {
		return "{}"
	}
	rep := "{"
	for _, el := range *s {
		rep += "\""
		rep += el
		rep += "\", "
	}
	return rep[0:len(rep)-2] + "}"
}

// A copy of the stringSet code with the names changed to protect the innocent.
// Lack of generics is annoying.
type orderedIntSet []int

func newOrderedIntSet(elements ...int) orderedIntSet {
	set := make([]int, 0)
	return append(set, elements...)
}

func (s orderedIntSet) Contains(item int) bool {
	for _, el := range s {
		if item == el {
			return true
		}
	}
	return false
}

func (s *orderedIntSet) Remove(item int) bool {
	for i, el := range *s {
		if item == el {
			copy((*s)[i:], (*s)[i+1:])
			*s = (*s)[:len(*s)-1]
			return true
		}
	}
	return false
}

func (s *orderedIntSet) Add(item int) {
	for _, el := range *s {
		if el == item {
			return
		}
	}
	*s = append(*s, item)
}

func (s orderedIntSet) Subtract(other orderedIntSet) orderedIntSet {
	var diff orderedIntSet
	for _, outer := range s {
		for _, inner := range other {
			if outer == inner {
				goto dontadd
			}
		}
		diff = append(diff, outer)
	dontadd:
	}
	return diff
}

func (s orderedIntSet) Intersection(other orderedIntSet) orderedIntSet {
	// Naive O(n**2) method - don't use on large sets if you care about speed
	var intersection orderedIntSet
	for _, item := range s {
		if other.Contains(item) {
			intersection = append(intersection, item)
		}
	}
	return intersection
}

func (s orderedIntSet) Union(other orderedIntSet) orderedIntSet {
	// Naive O(n**2) method - don't use on large sets if you care about speed
	var union orderedIntSet
	union = s[:]
	for _, item := range other {
		if !s.Contains(item) {
			union = append(union, item)
		}
	}
	return union
}

func (s *orderedIntSet) String() string {
	if len(*s) == 0 {
		return "{}"
	}
	rep := "{"
	for _, el := range *s {
		rep += fmt.Sprintf("%d, ", el)
	}
	return rep[0:len(rep)-2] + "}"
}

/*
 * Encapsulation of VCS capabilities starts here
 */

// Most knowledge about specific version-control systems lives in the
// following class list. Exception; there's a git-specific hook in the
// repo reader; also see the extractor classes; also see the dump method
// in the Blob() class.
// The members are, respectively:
//
// * Name of its characteristic subdirectory.
// * Command to export from the VCS to the interchange format
// * Import/export style flags.
//     "no-nl-after-commit" = no extra NL after each commit
//     "nl-after-comment" = inserts an extra NL after each comment
//     "export-progress" = exporter generates its own progress messages,
//                         no need for baton prompt.
//     "import-defaults" = Import sets default ignores
// * Flag specifying whether it handles per-commit properties on import
// * Command to initialize a new repo
// * Command to import from the interchange format
// * Command to check out working copies of the repo files.
// * Default preserve set (e.g. config & hook files; parts can be directories).
// * Likely location for an importer to drop an authormap file
// * Command to list files under repository control.
//
// Note that some of the commands used here are plugins or extensions
// that are not part of the basic VCS. Thus these may fail when called;
// we need to be prepared to cope with that.
//
// %(tempfile)s in a command gets substituted with the name of a
// tempfile that the calling code will know to read or write from as
// appropriate after the command is done.  If your exporter can simply
// dump to stdout, or your importer read from stdin, leave out the
// %(tempfile)s; reposurgeon will popen(3) the command, and it will
// actually be slightly faster (especially on large repos) because it
// won't have to wait for the tempfile I/O to complete.
//
// %(basename) is replaced with the basename of the repo directory.

// VCS is a class representing a version-control system.
type VCS struct {
	name         string
	subdirectory string
	exporter     string
	styleflags   stringSet
	extensions   stringSet
	initializer  string
	lister       string
	importer     string
	checkout     string
	preserve     stringSet
	authormap    string
	ignorename   string
	dfltignores  string
	cookies      []regexp.Regexp
	project      string
	notes        string
}

// Constants needed in VCS class methods
const suffixNumeric = `[0-9]+\s`
const tokenNumeric = `\s` + suffixNumeric
const dottedNumeric = `\s[0-9]+(\.[0-9]+\s)`

func (vcs VCS) String() string {
	realignores := newStringSet()
	for _, item := range strings.Split(strings.Trim(vcs.dfltignores, "\n"), "\n") {
		if len(item) > 0 && !strings.HasPrefix(item, "# ") {
			realignores.Add(item)
		}
	}
	notes := strings.Trim(vcs.notes, "\t ")

	return fmt.Sprintf("         Name: %s\n", vcs.name) +
		fmt.Sprintf(" Subdirectory: %s\n", vcs.subdirectory) +
		fmt.Sprintf("     Exporter: %s\n", vcs.exporter) +
		fmt.Sprintf(" Export-Style: %s\n", vcs.styleflags.String()) +
		fmt.Sprintf("   Extensions: %s\n", vcs.extensions.String()) +
		fmt.Sprintf("  Initializer: %s\n", vcs.initializer) +
		fmt.Sprintf("       Lister: %s\n", vcs.lister) +
		fmt.Sprintf("     Importer: %s\n", vcs.importer) +
		fmt.Sprintf("     Checkout: %s\n", vcs.checkout) +
		fmt.Sprintf("     Preserve: %s\n", vcs.preserve.String()) +
		fmt.Sprintf("    Authormap: %s\n", vcs.authormap) +
		fmt.Sprintf("   Ignorename: %s\n", vcs.ignorename) +
		fmt.Sprintf("      Ignores: %s\n", realignores.String()) +
		fmt.Sprintf("      Project: %s\n", vcs.project) +
		fmt.Sprintf("        Notes: %s\n", notes)
}

// Used for pre-compiling regular expressions at module load time
func reMake(patterns ...string) []regexp.Regexp {
	regexps := make([]regexp.Regexp, 0)
	for _, item := range patterns {
		regexps = append(regexps, *regexp.MustCompile(item))
	}
	return regexps
}

func (vcs VCS) hasReference(comment []byte) bool {
	for _, v := range vcs.cookies {
		if v.Find(comment) != nil {
			return true
		}
	}
	return false
}

var vcstypes []VCS
var extractors []Extractor

func init() {
	vcstypes = []VCS{
		{
			name:         "git",
			subdirectory: ".git",
			exporter:     "git fast-export --signed-tags: verbatim --tag-of-filtered-object: drop --all",
			styleflags:   newStringSet(),
			extensions:   newStringSet(),
			initializer:  "git init --quiet",
			importer:     "git fast-import --quiet",
			checkout:     "git checkout",
			lister:       "git ls-files",
			preserve:     newStringSet(".git/config", ".git/hooks"),
			authormap:    ".git/cvs-authors",
			ignorename:   ".gitignore",
			dfltignores:  "",
			cookies:      reMake(`\b[0-9a-f]{6}\b`, `\b[0-9a-f]{40}\b`),
			project:      "http://git-scm.com/",
			notes:        "The authormap is not required, but will be used if present.",
		},
		{
			name:         "bzr",
			subdirectory: ".bzr",
			exporter:     "bzr fast-export --no-plain %(basename)s",
			styleflags: newStringSet(
				"export-progress",
				"no-nl-after-commit",
				"nl-after-comment"),
			extensions: newStringSet(
				"empty-directories",
				"multiple-authors", "commit-properties"),
			initializer: "",
			lister:      "",
			importer:    "bzr fast-import -",
			checkout:    "bzr checkout",
			preserve:    newStringSet(),
			authormap:   "",
			project:     "http://bazaar.canonical.com/en/",
			ignorename:  ".bzrignore",
			dfltignores: `
# A simulation of bzr default ignores, generated by reposurgeon.
*.a
*.o
*.py[co]
*.so
*.sw[nop]
*~
.#*
[#]*#
__pycache__
bzr-orphans
# Simulated bzr default ignores end here
`,
			cookies: reMake(tokenNumeric),
			notes:   "Requires the bzr-fast-import plugin.",
		},
		{
			name:         "hg",
			subdirectory: ".hg",
			exporter:     "",
			styleflags: newStringSet(
				"import-defaults",
				"nl-after-comment",
				"export-progress"),
			extensions:  newStringSet(),
			initializer: "hg init",
			lister:      "hg status -macn",
			importer:    "hg fastimport %(tempfile)s",
			checkout:    "hg checkout",
			preserve:    newStringSet(".hg/hgrc"),
			authormap:   "",
			ignorename:  ".hgignore",
			dfltignores: "",
			cookies:     reMake(tokenNumeric, `\b[0-9a-f]{40}\b`, `\b[0-9a-f]{12}\b`),
			project:     "http://mercurial.selenic.com/",
			notes: `The hg fastimport method is not part of stock Mercurial.

If there is no branch named 'master' in a repo when it is read, the hg 'default'
branch is renamed to 'master'.
`,
		},
		{
			// Styleflags may need tweaking for round-tripping
			name:         "darcs",
			subdirectory: "_darcs",
			exporter:     "darcs fastconvert export",
			styleflags:   newStringSet(),
			extensions:   newStringSet(),
			initializer:  "",
			lister:       "darcs show files",
			importer:     "darcs fastconvert import",
			checkout:     "",
			preserve:     newStringSet(),
			authormap:    "",
			ignorename:   "_darcs/prefs/boring",
			dfltignores: `
# A simulation of darcs default ignores, generated by reposurgeon.
# haskell (ghc) interfaces
*.hi
*.hi-boot
*.o-boot
# object files
*.o
*.o.cmd
# profiling haskell
*.p_hi
*.p_o
# haskell program coverage resp. profiling info
*.tix
*.prof
# fortran module files
*.mod
# linux kernel
*.ko.cmd
*.mod.c
*.tmp_versions
# *.ko files aren't boring by default because they might
# be Korean translations rather than kernel modules
# *.ko
# python, emacs, java byte code
*.py[co]
*.elc
*.class
# objects and libraries; lo and la are libtool things
*.obj
*.a
*.exe
*.so
*.lo
*.la
# compiled zsh configuration files
*.zwc
# Common LISP output files for CLISP and CMUCL
*.fas
*.fasl
*.sparcf
*.x86f
### build and packaging systems
# cabal intermediates
*.installed-pkg-config
*.setup-config
# standard cabal build dir, might not be boring for everybody
# dist
# autotools
autom4te.cache
config.log
config.status
# microsoft web expression, visual studio metadata directories
*.\\_vti_cnf
*.\\_vti_pvt
# gentoo tools
*.revdep-rebuild.*
# generated dependencies
.depend
### version control
# darcs
_darcs
.darcsrepo
*.darcs-temp-mail
-darcs-backup[[:digit:]]+
# gnu arch
+
,
vssver.scc
*.swp
MT
{arch}
*.arch-ids
# bitkeeper
BitKeeper
ChangeSet
### miscellaneous
# backup files
*~
*.bak
*.BAK
# patch originals and rejects
*.orig
*.rej
# X server
..serverauth.*
# image spam
\\#
Thumbs.db
# vi, emacs tags
tags
TAGS
# core dumps
core
# partial broken files (KIO copy operations)
*.part
# mac os finder
.DS_Store
# Simulated darcs default ignores end here
`,
			cookies: reMake(),
			project: "http://darcs.net/",
			notes:   "Assumes no boringfile preference has been set.",
		},
		{
			name:         "mtn",
			subdirectory: "_MTN",
			exporter:     "mtn git_export",
			styleflags:   newStringSet(),
			extensions:   newStringSet(),
			initializer:  "",
			lister:       "mtn list known",
			importer:     "",
			checkout:     "",
			preserve:     newStringSet(),
			authormap:    "",
			ignorename:   ".mtn_ignore", // Assumes default hooks
			dfltignores: `
*.a
*.so
*.o
*.la
*.lo
^core
*.class
*.pyc
*.pyo
*.g?mo
*.intltool*-merge*-cache
*.aux
*.bak
*.orig
*.rej
%~
*.[^/]**.swp
*#[^/]*%#
*.scc
^*.DS_Store
/*.DS_Store
^desktop*.ini
/desktop*.ini
autom4te*.cache
*.deps
*.libs
*.consign
*.sconsign
CVS
*.svn
SCCS
_darcs
*.cdv
*.git
*.bzr
*.hg
`,
			cookies: reMake(),
			project: "http://www.monotone.ca/",
			notes:   "Exporter is buggy, occasionally emitting negative timestamps.",
		},
		{
			// Styleflags may need tweaking for round-tripping
			// Export is experimental and doesn't round-trip
			name:         "svn",
			subdirectory: "locks",
			exporter:     "svnadmin dump .",
			styleflags:   newStringSet("import-defaults", "export-progress"),
			extensions:   newStringSet(),
			initializer:  "svnadmin create .",
			importer:     "svnadmin load .",
			checkout:     "",
			lister:       "",
			preserve:     newStringSet("hooks"),
			authormap:    "",
			ignorename:   "",
			// Note dangerous hack here: the leading
			// slashes are there to mark lines which
			// should *not* be anchored, and will be
			// removed later in processing.
			dfltignores: `
# A simulation of Subversion default ignores, generated by reposurgeon.
/*.o
/*.lo
/*.la
/*.al
/*.libs
/*.so
/*.so.[0-9]*
/*.a
/*.pyc
/*.pyo
/*.rej
/*~
/*.#*
/.*.swp
/.DS_store
# Simulated Subversion default ignores end here
`,
			cookies: reMake(`\b(?:SVN|svn|Subversion|subversion|rev|version)\s+`+suffixNumeric, "r"+suffixNumeric),
			project: "http://subversion.apache.org/",
			notes:   "Run from the repository, not a checkout directory.",
		},
		{
			name:         "cvs",
			subdirectory: "CVSROOT", // Can't be Attic, that doesn't always exist.
			exporter:     "find . -name '*,v' -print | cvs-fast-export --reposurgeon",
			styleflags:   newStringSet("import-defaults", "export-progress"),
			extensions:   newStringSet(),
			initializer:  "",
			importer:     "",
			checkout:     "",
			lister:       "",
			preserve:     newStringSet(),
			authormap:    "",
			ignorename:   "",
			dfltignores: `
# A simulation of cvs default ignores, generated by reposurgeon.
tags
TAGS
.make.state
.nse_depinfo
*~
#*
.#*
,*
_$*
*$
*.old
*.bak
*.BAK
*.orig
*.rej
.del-*
*.a
*.olb
*.o
*.obj
*.so
*.exe
*.Z
*.elc
*.ln
core
# Simulated cvs default ignores end here
`,
			cookies: reMake(dottedNumeric),
			project: "http://www.catb.org/~esr/cvs-fast-export",
			notes:   "Requires cvs-fast-export.",
		},
		{
			name:         "rcs",
			subdirectory: "RCS",
			exporter:     "find . -name '*,v' -print | cvs-fast-export --reposurgeon",
			styleflags:   newStringSet("export-progress"),
			extensions:   newStringSet(),
			initializer:  "",
			importer:     "",
			checkout:     "",
			lister:       "",
			preserve:     newStringSet(),
			authormap:    "",
			ignorename:   "",
			dfltignores:  "", // Has none
			cookies:      reMake(dottedNumeric),
			project:      "http://www.catb.org/~esr/cvs-fast-export",
			notes:        "Requires cvs-fast-export.",
		},
		{
			name:         "src",
			subdirectory: ".src",
			exporter:     "src fast-export",
			styleflags:   newStringSet(),
			extensions:   newStringSet(),
			initializer:  "src init",
			importer:     "",
			checkout:     "",
			lister:       "src ls",
			preserve:     newStringSet(),
			authormap:    "",
			ignorename:   "",
			dfltignores:  "", // Has none
			cookies:      reMake(tokenNumeric),
			project:      "http://catb.org/~esr/src",
			notes:        "",
		},
		{
			// Styleflags may need tweaking for round-tripping
			name:         "bk",
			subdirectory: ".bk",
			exporter:     "bk fast-export -q --no-bk-keys",
			styleflags:   newStringSet(),
			extensions:   newStringSet(),
			initializer:  "", // bk setup doesn't work here
			lister:       "bk gfiles -U",
			importer:     "bk fast-import -q",
			checkout:     "",
			preserve:     newStringSet(),
			authormap:    "",
			ignorename:   "BitKeeper/etc/ignore",
			dfltignores:  "",                    // Has none
			cookies:      reMake(dottedNumeric), // Same as SCCS/CVS
			project:      "https://www.bitkeeper.com/",
			// No tag support, and a tendency to core-dump
			notes: "Bitkeeper's importer is flaky and incomplete as of 7.3.1ce.",
		},
	}

	// More extractors go in this list
	extractors = []Extractor{*newGitExtractor(), *newHgExtractor()}
}

// Import and export filter methods for VCSes that use magic files rather
// than magic directories. So far there is only one of these.
//
// Each entry maps a read/write option to an (importer, exporter) pair.
// The input filter must be an *exporter from* that takes an alien file
// and emits a fast-import stream on standard output.  The exporter
// must be an *importer to* that takes an import stream on standard input
// and produces a named alien file.
//
var fileFilters = map[string]struct {
	importer string
	exporter string
}{
	"fossil": {"fossil export --git %s", "fossil import --git %s"},
}

// How to write extractor classes:
//
// Clone one of the existing ones and mutate.
//
// Significant fact: None of the get* methods for extracting information about
// a revision is called until after checkout has been called on that revision.
//
// Most methods take a native revision ID as argument. The value and type of the
// ID don't matter to any of the code that will call the extractor, except that
// IDs must be valid map keys.
//
// The 'name', 'subdirectory', and 'visible' members must be set. The
// subdirectory member is how an extractor recognizes what repositories
// it can consume.  If the visible member is false, the 'read' command
// will ignore the existence of the extractor.
//
// The strings returned by getCommitter() and getAuthors() should look like
//
// J. Random User <random@foobar> 2011-11-29T10:13:32Z
//
// that is, a free text name followed by an email ID followed by a date.
// The date specification can be anything Attribution() can parse; in
// particular, RFC3339 dates are good. and so is git's native
// integer-Unix-timestamp/timezone pairs.


// Commit-Meta is the extractor;s idea of per-commit metadata
type CommitMeta struct {
	ci string
	ai string
	branch string
}

// ExtractorMeta meeds to be composed into each extractor class as the
// place where its common data lives. The methods that have to be common
// to extractors are specified by the Extractor interface, next up.
type ExtractorMeta struct {
	name string			// extractor name
	vcs *VCS			// underlying VCS
	visible bool			// should it be selectable?
}

type Extractor interface {
	// Return meta-information about an extractor.
	getMeta() ExtractorMeta
        // Gather the topologically-ordered lists of revisions and the parent map
	// (revlist and parent members)
	gatherRevisionIDs(*RepoStreamer) error
        // Gather all other per-commit data except branch IDs
	// (ai and ci members in self.meta list elements)
	gatherCommitData(*RepoStreamer) error
        // Gather all branch heads and tags (refs and tags members)
	gatherAllReferences(*RepoStreamer) error
	// Color commits with their branch names
	colorBranches(*RepoStreamer) error
        // Hook for any cleanup actions required after streaming.
	postExtract(*Repository)
        // Return true if repo has no unsaved changes.
	isClean() bool
	// Check the directory out to a specified revision, return a manifest.	
	checkout(string) stringSet
        // Return a commit's change comment as a string.
	getComment(string) string
}

// How these are structured: RepoStreamer is the common code that
// sequences extractions. It expects to be able to call a VCS-specific 
// extractor class. Each of these extractors has the option of using
// ColorMixin, which can simulate Git's algorithm for branch-coloring
// commits.

type MixerCapable interface {
	gatherCommitTimestamps() error
	gatherChildTimestamps(*RepoStreamer) map[string]time.Time
}


// ColorMixer is a mixin class for simulating the git branch-coloring algorithm
type ColorMixer struct {
	base *RepoStreamer
        commitStamps map[string]time.Time	// icommit -> timestamp
        childStamps map[string]time.Time	// commit -> timestamp of latest child
}

func (cm *ColorMixer) colorMixerInit(base *RepoStreamer) {
	cm.base = base
	cm.commitStamps = make(map[string]time.Time)
        cm.childStamps = make(map[string]time.Time)
}

// simulateGitColoring colors branches in the order the tips occur.
func (cm *ColorMixer) simulateGitColoring(mc MixerCapable, base *RepoStreamer) {
        // This algorithm is intended to emulate git's coloring algorithm;
        // note that this includes emulating the fact that git's algorithm
        // is not lossless--that is, it is possible to construct a git
        // fast-import stream that git cannot reproduce on output with
        // git fast-export
        // First retrieve the commit timestamps, they are used in
	// branchColor below
        err := mc.gatherCommitTimestamps()
        if err != nil || cm.commitStamps  == nil {
		panic(throw("extractor", "Could not retrieve commit timestamps: %v", err))
	}
        // This will be used in _branchColor below
        cm.childStamps = mc.gatherChildTimestamps(base)
        for refname, refobj := range base.refs.dict {
		if base.branchesAreColored && strings.HasPrefix(refname, "refs/heads/") {
			return
		}
		cm._branchColor(refobj, refname)
	}
}

// Exact value of this constant is unimportant, it just needs to be
// absurdly far in the future so no commit can have a committer date
// that's greater.  In fact it is 292277026596-12-04 10:30:07 -0500 EST
var farFuture = time.Unix(1<<63-1, 0)

func (cm *ColorMixer) _branchColor(rev, color string) {
        // This ensures that a branch tip rev never gets colored over
        if _, ok := cm.childStamps[rev]; !ok {
		cm.childStamps[rev] = farFuture
	}
        // This is used below to ensure that a branch color is never colored
        // back to a tag
        isBranch := strings.HasPrefix(color, "refs/heads/")
        // No need for a condition here because we will only be starting
        // this while loop from an initial call with a branch tip or from
        // a recursive call with a parent we know we want to color; the
        // loop exit is controlled by filtering out the parents that are
        // already colored properly
	timestamp := cm.commitStamps[rev]
	cm.base.meta[rev].branch = color
	// We only want to color back to parents that don't have a branch
	// assigned or whose assigned branch was from an earlier commit
	// than the one we're coloring from now; this emulates the git
	// algorithm that assigns the color of the latest child commit to
	// a parent that has multiple children; note also that tags take
	// precedence over branches, so we never color back to a tag with
	// a branch color
	var parents []string
	for _, p := range cm.base.getParents(rev) {
		if cm.base.meta[p].branch == "" || ((!(isBranch && cm.base.isTag(p))) && (cm.childStamps[p].Before(timestamp))) {
			parents = append(parents, p)
		}
	}

	for _, parent := range parents {
		// Mark each parent with the timestamp of the child it is
		// being colored from
		cm.childStamps[parent] = timestamp
		cm._branchColor(parent, color)
	}
}

func findVCS(name string) *VCS {
	for _, vcs := range vcstypes {
		if vcs.name == name {
			return &vcs
		}
	}
	panic("reposurgeon: failed to find " + name + " in VCS types")
}

func lineByLine(rs *RepoStreamer, command string, errfmt string,
	hook func(string, *RepoStreamer) error) error {
        r, cmd, err1 := readFromProcess(command)
	if err1 != nil {
		return err1
	}
	//defer r.Close()
	for {
		line, err2 := r.ReadString(byte('\n'))
		if err2 == io.EOF {
			if cmd != nil {
				cmd.Wait()
			}
			break
		} else {
			return fmt.Errorf(errfmt, err2)
		}
		hook(line, rs)
	}
	return nil
}

// Repository extractor for the git version-control system
type GitExtractor struct {
	b ExtractorMeta
}

func newGitExtractor() *GitExtractor {
	// Regardless of what revision and branch was current at start,
	// after the git extractor runs the head revision on the master branch
	// will be checked out.
	//
	// The git extractor does not attempt to recover N ops,
	// symbolic links, gitlinks, or directory fileops.
	//
	// To be streamed, a git repo must have *local*
	// refs to all branches - in particular, local tracking branches
	// corresponding to all remotes.
	//
	// Some of these limitations could be fixed, but the git extractor
	// is not intended to replace git-fast-export; it only exists as a
	// test for the generic RepoStreamer code and a model for future
	// extractors.
	ge := new(GitExtractor)
	ge.b.name = "git-extractor"
	ge.b.vcs = findVCS("git")
	ge.b.visible = false
	return ge
}

func (ge GitExtractor) getMeta() ExtractorMeta {
	return ge.b
}

func (ge GitExtractor) gatherRevisionIDs(rs *RepoStreamer) error {
	hook := func(line string, rs *RepoStreamer) error {
		fields := strings.Fields(line)
                rs.revlist = append(rs.revlist, fields[0])
                rs.parents[fields[0]] = fields[1:]
		return nil
	}
	return lineByLine(rs,
		"git log --all --date-order --reverse --format='%H %P'",
		"git's gatherRevisionIDs: %v",
		hook)
}

func (ge GitExtractor) gatherCommitData(rs *RepoStreamer) error {
	hook := func(line string, rs *RepoStreamer) error {
		line = strings.Trim(line, "\n")
		fields := strings.Split(line, "|")
                rs.meta[fields[0]].ci = fields[1]
                rs.meta[fields[0]].ai = fields[2]
		return nil
	}
	return lineByLine(rs,
		"git log --all --reverse --date=raw --format='%H|%cn <%ce> %cd|%an <%ae> %ad'",
		"git's gatherCommitData: %v",
		hook)
}


func (ge GitExtractor) gatherAllReferences(rs *RepoStreamer) error {
	err := filepath.Walk(".git/refs", func(pathname string, info os.FileInfo, err error) error {
		if err != nil {
			// Prevent panic by handling failure accessing a path
			return err
		}
		if info.IsDir() {
			return nil
		}
		data, err := ioutil.ReadFile(pathname)
		if err != nil {
			return fmt.Errorf("while walking the refs tree: %v", err) 
		}
		// 5: strips off the.git/ prefix
		rs.refs.set(pathname[5:], strings.Trim(string(data), "\n"))
		return nil
	})
        rs.baton.twirl("")

        rf, cmd, err1 := readFromProcess("git tag -l")
	if err1 != nil {
		return fmt.Errorf("while listing tags: %v", err)
	}
	//defer rf.Close()
	for {
		fline, err2 := rf.ReadString(byte('\n'))
		if err2 == io.EOF {
			if cmd != nil {
				cmd.Wait()
			}
			break
		} else if err2 != nil {
			return err2
		}
		tag := strings.Trim(fline, "\n")
		taghash, terr := captureFromProcess("git rev-parse " + tag)
		if terr != nil {
			panic(throw("extractor", "Could not spawn git rev-parse: %v", terr))
		}
		taghash = strings.Trim(taghash, "\n")
		// Annotated tags are first-class objects with their
		// own hashes.  The hash of a lightweight tag is just
		// the commit it points to. Handle both cases.
		objecthash := taghash
		cf, cmd, err3 := readFromProcess("git cat-file -p " + tag)
		if err3 != nil {
			return fmt.Errorf("while auditing tag %q: %v", tag, err)
		}
		tagger := ""
		comment := ""
		for {
			line, err3 := cf.ReadString(byte('\n'))
			if err3 == io.EOF {
				if cmd != nil {
					cmd.Wait()
				}
				break
			} else if err3 != nil {
				return err3
			}
			comment = ""
			tagger = ""
			inBody := false
			line = strings.Trim(line, "\n")
			if strings.HasPrefix(line, "tagger ") {
				tagger = line[len("tagger "):]
			} else if strings.HasPrefix(line, "object") {
				objecthash = strings.Fields(line)[1]
			} else if comment == "" && line == "" {
				inBody = true
			} else if inBody {
				comment += line + "\n"
			}
		}
		rs.refs.set("refs/tags/" + tag, objecthash)
		if objecthash != taghash {
			// committish isn't a mark; we'll fix that later
			tagobj := *newTag(nil, tag, objecthash, nil, 
				newAttribution(tagger),
				comment)
			rs.tags = append(rs.tags, tagobj)
		}
		rs.baton.twirl("")
	}
	return nil
}

// colorBranches colors all commits with their branch name.
func (ge GitExtractor) colorBranches(rs *RepoStreamer) error {
        // This is really cheating since fast-export could give us the
        // whole repo, but it's the only way I've found to get the correct
        // mapping of commits to branches, and we still want to test the
        // rest of the extractor logic independently, so here goes...
	file, err1 := ioutil.TempFile(".", "rse")
	if err1 != nil {
	    return err1
	}
	defer os.Remove(file.Name())
	markfile, err2 := os.Open(file.Name())
	if err2 != nil {
	    return err1
	}
	data, err3 := captureFromProcess("git fast-export --all --export-marks=" + file.Name())
	if err3 != nil {
		panic(throw("extractor", "Couldn't spawn git-fast-export: %v", err3))
	}
	rf := bufio.NewReader(markfile)
	rs.baton.twirl("")
	marks := make(map[string]string)
	for {
		fline, err3 := rf.ReadString(byte('\n'))
		if err3 == io.EOF {
			break
		} else if err3 != nil {
			return err3
		}
		fields := strings.Fields(fline)
		marks[fields[0]] = fields[1]
	}
        branch := ""
        for _, line := range strings.Split(data, "\n") {
		fields := strings.Fields(line)
		if len(fields) != 2 {
			// The lines we're interested in will always have
			// exactly 2 fields: commit <ref> or mark <id>; so
			// all other lines can be ignored
			continue
		} else if fields[0] == "commit" {
			branch = fields[1]
		} else if (fields[0] == "mark") && (branch != "") {
			h := marks[fields[1]]
			// This is a valid (commit hash, branch name) pair
			rs.meta[h].branch = branch
			branch = ""
		} else if branch != "" {
			// The mark line for a commit should always be the
			// next line after the commit line, so this should
			// never happen, but we put it in just in case
			panic(throw("extractor", "Could not parse branch information"))
		}
	}
	return nil
}

func (ge GitExtractor) _metadata(rev string, format string) string {
        line, err := captureFromProcess(fmt.Sprintf("git log -1 --format='%s' %s", format, rev))
	if err != nil {
		panic(throw("extractor", "Couldn't spawn git log: %v", err))
	}
	if line[len(line)-1] == '\n' {
		line = line[:len(line)-1]
	}
	return line
}

func (ge GitExtractor) postExtract(_repo *Repository) {
        exec.Command("git", "checkout", "--quiet", "master").Run()
}

// isClean is a predicate;  return true if repo has no unsaved changes.
func (ge GitExtractor) isClean() bool {
        data, err := captureFromProcess("git ls-files --modified")
	if err != nil {
		panic(throw("extractor", "Couldn't spawn git ls-files --modified: %v", err))
	}
	return data == ""
}

// checkout checks the repository out to a specified revision.
func (ge GitExtractor) checkout(rev string) stringSet {
        exec.Command("git", "checkout", "--quiet",  rev).Run()
        data, err := captureFromProcess("git ls-files")
	if err != nil {
		panic(throw("extractor", "Couldn't spawn git ls-files in checkout: %v", err))
	}
        manifest := strings.Split(data, "\n")
	if manifest[len(manifest)-1] == "" {
		manifest = manifest[:len(manifest)-1]
	}
        return newStringSet(manifest...)
}

// getComment returns a commit's change comment as a string.
func (ge GitExtractor) getComment(rev string) string {
        return ge._metadata(rev, "%B")
}

// Repository extractor for the hg version-control system
type HgExtractor struct {
	b ExtractorMeta
	ColorMixer
        tagsFound bool
        bookmarksFound bool
}

func newHgExtractor() *HgExtractor {
	// Regardless of what revision and branch was current at
	// start, after the hg extractor runs the tip (most recent
	// revision on any branch) will be checked out.
	ge := new(HgExtractor)
	ge.b.name = "hg-extractor"
	ge.b.vcs = findVCS("hg")
	ge.b.visible = true
	return ge
}

func (he HgExtractor) getMeta() ExtractorMeta {
	return he.b
}

//gatherRevisionIDs gets the topologically-ordered list of revisions and parents.
func (he HgExtractor) gatherRevisionIDs(rs *RepoStreamer) error {
        // hg changesets can only have up to two parents
        // we have to use short (12-nibble) hashes because that's all "hg tags"
        // and "hg branches" give us.  Hg's CLI is rubbish.
	hook := func(line string, rs *RepoStreamer) error {
		fields := strings.Fields(line)
		rs.revlist = append(rs.revlist, fields[0])
                // non-existent parents are given all-0s hashes.
                // Did I mention that the Hg CLI is rubbish?
		parents := make([]string, 0)
		for _, f := range fields[1:] {
			if f != "000000000000" {
				parents = append(parents, f)
			}
		}
		rs.parents[fields[0]] = parents
		return nil
	}
	err := lineByLine(rs,
		"hg log --template {node|short} {p1node|short} {p2node|short}\\n",
		"hg's gatherRevisionIDs: %v",
		hook)
	// No way to reverse the log order, so it has to be done here
	for i := len(rs.revlist)/2-1; i >= 0; i-- {
		opp := len(rs.revlist)-1-i
		rs.revlist[i], rs.revlist[opp] = rs.revlist[opp], rs.revlist[i]
	}
	
	return err	
}

// gatherCommitData gets all other per-commit data except branch IDs
func (he HgExtractor) gatherCommitData(rs *RepoStreamer) error {
	hook := func(line string, rs *RepoStreamer) error {
		fields := strings.Fields(line)
		hash := fields[0]
		ci := fields[1]
                // Because hg doesn't store separate author and committer info,
                // we just use the committer for both.  Alternate possibility,
		// just set the committer - I (ESR) believe git does that
		// defaulting itself.  But let's not count on it, since we
		// might be handing the history stream to somebody's importer
		// that handles that edge case differently.
		rs.meta[hash].ci = ci
		rs.meta[hash].ai = ci
		return nil
	}
	return lineByLine(rs,
		`{node|short}|{sub(r"<([^>]*)>", "", author|person)} <{author|email}> {date|rfc822date}\n`,
		"hg's gatherCommitData: %v",
		hook)
}

// gatherCommitTimestamps updates the ColorMixer mapping of hash -> timestamp
func (he HgExtractor) gatherCommitTimestamps() error {
	hook := func(line string, rs *RepoStreamer) error {
		fields := strings.Fields(line)
		d, err := newDate(fields[1] + " " + fields[2])
		if err != nil {
			panic(throw("unrecognized date format in %q: %v", line, err))
		}
		he.commitStamps[fields[0]] = d.timestamp
		return nil
	}

	return lineByLine(nil,
		"log --template {node|short} {date|hgdate}\\n",
		"hg's gatherCommitTimestamps",
		hook)
}

// gatherAllReferences finds all branch heads and tags
func (he HgExtractor) gatherAllReferences(rs *RepoStreamer) error {
	// Some versions of mercurial can return an error for showconfig
	// when the config is not present. This isn't an error.
	bookmarkRef, errcode := captureFromProcess("hg showconfig reposurgeon.bookmarks")
	if errcode != nil {
		bookmarkRef = ""
	} else {
		bookmarkRef = strings.TrimSpace(bookmarkRef)
	}

	// both branches and tags output "name      num:hash" lines
	// branches may also append " (inactive)"
	hook1 := func(line string, rs *RepoStreamer) error {
		fields := strings.Fields(line)
		if len(fields[0]) < 1 {
			panic(throw("extractor",
				"Empty 'hg branches' line: %q", line))
		}
		n := string(fields[0])
		seqref := strings.Split(fields[1], ":")
		if len(fields[0]) < 2 {
			panic(throw("extractor",
				"Missing colon in 'hg branches' line: %q", line))
		}
		h := string(seqref[1])
		rs.refs.set("refs/heads/" + n, h)
		return nil
	}
	err := lineByLine(rs, 
		"hg branches --closed",
		"fetching hg branches",
		hook1)
	if err != nil {
		panic(throw("extractor", "while fetching hg branches: %v", err))
	}

	if bookmarkRef != "" {
		hook2 := func(line string, rs *RepoStreamer) error {
			fields := strings.Fields(line)
			if len(fields[0]) < 1 {
				panic(throw("extractor",
					"Empty 'hg bookmarks' line: %q", line))
			}
			n := string(fields[0])
			seqref := strings.Split(fields[1], ":")
			if len(fields[0]) < 2 {
				panic(throw("extractor",
					"Missing colon in 'hg bookmarks' line: %q", line))
			}
			h := string(seqref[1])
			rs.refs.set("refs/" + bookmarkRef + n, h)
			he.bookmarksFound = true
			return nil
		}
		err = lineByLine(rs, 
			"hg bookmarks",
			"fetching hg bookmarks",
			hook2)
		if err != nil {
			panic(throw("extractor", "while fetching hg bookmarks: %v", err))
		}
	}
	hook3 := func(line string, rs *RepoStreamer) error {
		// In Python this was:
		/* n, h = tuple(map(polystr, line.strip().rsplit(b'\t', 1))) */
		line = strings.TrimSpace(line)
		fields := strings.Split(line, "\t")
		h := fields[len(fields)-1]
		n := strings.Join(fields[:len(fields)-1], "\t")
                if n == "tip" {		// pseudo-tag for most recent commit
			return	nil	// We don't want it
		}
		rs.refs.set("refs/tags/" + n, h[:12])
		return nil
	}
	he.tagsFound = true
	err = lineByLine(rs,
		"log --rev=tag() --template={tags}\t{node}\n",
		"fetching hg tags",
		hook3)
	if err != nil {
		panic(throw("extractor", "while fetching hg tags: %v", err))
	}
        // We have no annotated tags, so he.tags = []
        // Conceivably it might be better to treat the commit message that
        // creates the tag as an annotation, but that's a job for the surgeon
        // later, not the extractor now.
	return nil
}

func (he HgExtractor) _hg_branch_items() map[string]string {
	out := make(map[string]string)
	err := lineByLine(nil, 
		"hg log --template {node|short} {branch}\\n",
		"in _hg_branch_items: %v",
		func(line string, rs *RepoStreamer) error {
			fields := strings.Fields(line)
			out[fields[0]] = "refs/heads/" + fields[1]
			return nil
		})
	if err != nil {
		panic(throw("extractor", "in _hg_branch_items: %v", err))
	}
	return out
}

// Return initial mapping of commit hash -> timestamp of child it is colored from
func (he HgExtractor) gatherChildTimestamps(rs *RepoStreamer) map[string]time.Time {
        results := make(map[string]time.Time)
        for h, branch := range he._hg_branch_items() {
		// Fill in the branch as a default; this will ensure
		// that any commit that is not in the ancestor tree of
		// a tag will get the correct hg branch name, even if
		// the hg branch coloring is not compatible with the
		// git coloring algorithm
		rs.meta[h].branch = branch
		// Fill in the branch tips with child timestamps to
		// ensure that they can't be over-colored (other
		// commits in the ancestor tree of a branch can be
		// over-colored if they are in a tag's ancestor tree,
		// so we don't fill in any child timestamp for them
		// here)
		if rs.refs.get(branch) == h {
			results[h] = farFuture
		}
	}
	rs.branchesAreColored = true
        return results
}


func (he HgExtractor) _branchColorItems() map[string]string {
        if !he.tagsFound && !he.bookmarksFound {
		// If we didn't find any tags or bookmarks, we can
		// safely color all commits using hg branch names,
		// since hg stores them with commit metadata; note,
		// however, that the coloring this will produce might
		// not be reproducible if the repo is written to a
		// fast-import stream and used to construct a git
		// repo, because hg branches can store colorings that
		// do not match the git coloring algorithm
		return he._hg_branch_items()
	}
        // Otherwise we have to use the emulated git algorithm to color
        // any commits that are tags or the ancestors of tags, since git
        // prioritizes tags over branches when coloring; we will color
        // commits that are not in the ancestor tree of any tag in
        // gatherChildTimestamps below, using the hg branch names
	return nil
}

// colorBanches assigns branches to commits in an extracted repository
func (he HgExtractor) colorBranches(rs *RepoStreamer) error {
        color_items := he._branchColorItems()
        if color_items != nil {
		// If the repo will give us a complete list of (commit
		// hash, branch name) pairs, use that to do the coloring
		for h, color := range color_items {
			rs.meta[h].branch = color
		}
        } else {
		// Otherwise we have to emulate the git coloring algorithm
		he.simulateGitColoring(he, rs)
	}
	return nil
}


func (he HgExtractor) postExtract(repo *Repository) {
        he.checkout("tip")
        if !repo.branchset().Contains("refs/heads/master") { 
		for _, event := range repo.events {
			switch event.(type) {
			case *Commit:
				if event.(*Commit).branch == "refs/heads/default" {
					event.(*Commit).branch = "refs/heads/master"
				}
			case *Reset:
				event.(*Reset).ref = "refs/heads/master"
			}
		}
	}
}
			
// isClean returns true if repo has no unsaved changes
func (he HgExtractor) isClean() bool {
        data, err := captureFromProcess("hg status --modified")
	if err != nil {
		panic(throw("extractor", "Couldn't spawn hg status --modified: %v", err))
	}
	return data == ""
}

func mustChdir(directory string, errorclass string) {
	err := os.Chdir(directory)
	if err != nil {
		panic(throw(errorclass,
			"In %s, could not change working directory to %s: %v",
			errorclass, directory, err))
	}
}

func mustCaptureFromProcess(command string, errorclass string) string {
	data, err := captureFromProcess(command)
	if err != nil {
		panic(throw(errorclass,
			"In %s, command %s failed: %v",
			errorclass, command, err))
	}
	return data
}

// checkout checka the directory out to a specified revision, return a manifest.
func (he HgExtractor) checkout(rev string) stringSet {
        pwd, err := os.Getwd()
	if err != nil {
		panic(throw("extractor", "Could not get working directory: %v", err))
	}
        _, errcode := captureFromProcess("hg update -C " + rev)
	if errcode != nil {
		panic(throw("extractor", "Could not check out: %v", errcode))
	}
        // 'hg update -C' can delete and recreate the current working
        // directory, so cd to what should be the current directory
	mustChdir(pwd, "extractor") 
	
        // Sometimes, hg update can fail because of missing subrepos. When that
        // happens, try really hard to fake it. This is safe because subrepos
        // don't work in any case, so it's always safe to ignore them.
        //
        // There are tons of problems with this parsing. It doesn't safely
        // handle subrepositories with special chars like spaces, quotes or that
        // sort of thing. It also doesn't handle comments or other rarely used
        // stuff in .hgsub files. This is documented poorly at best so it's
        // unclear how things should work ideally.
        if errcode != nil {
		subrepoTxt, subcatErr := captureFromProcess("hg cat -r" + rev + " .hgsub")
		subrepoArgs := make([]string, 0)
		if subcatErr == nil {
			// If there's a subrepository file, try to parse the
			// names from it.
			for _, subrepoLine := range strings.Split(subrepoTxt, "\n") {
				parsed := strings.SplitN(subrepoLine, "=", 1)
				if len(parsed) > 1 {
					subrepoArgs = append(subrepoArgs, "--exclude")
					subrepoArgs = append(subrepoArgs, strings.TrimSpace(parsed[0]))
				}
			}
		}
		// Since all is not well, clear everything and try from zero.
		// Sidesteps some issues with problematic checkins.
		// Remove checked in files.
		captureFromProcess("hg update -C null")
		mustChdir(pwd, "extractor")
		// Remove extraneous files.
		captureFromProcess("hg purge --config extensions.purge= --all")
		mustChdir(pwd, "extractor") 

		// The Python version of this code had a section
		// beginning with the comment "Remove everything
		// else. Purge is supposed to do this, but doesn't."
		// But I tested under hg 4.5.3 and it seems to actually
		// do that now. Which is good because the way Go's
		// filepath.Walk interface is designed it would have been a
		// been a serious PITA to replicate the old behavior:
		// nuke everything *including directories* except the top
		// level .hg/.  The issue is that filepath.Walk just walks
		// the tree in lexical order, which means directories
		// are at inconvenient places in the sequence.

		// If there are subrepos, use revert to fake an
		// update, but exclude the subrepo paths, which are
		// probably borken.
		if len(subrepoArgs) > 0 {
			captureFromProcess("hg revert --all --no-backup -r " + rev + strings.Join(subrepoArgs, " "))
			mustChdir(pwd, "extractor")
			mustCaptureFromProcess("hg debugsetparents " + rev, "extracror")
			mustChdir(pwd, "extractor")
			mustCaptureFromProcess("hg debugrebuilddirstate", "extractor")
			mustChdir(pwd, "extractor")
		} else {
			reupTxt, reupErr := captureFromProcess("update -C" + rev)
			if reupErr != nil {
				panic(throw("extractor", "Failed to update to revision %s: %s", rev, reupTxt))
			}
			mustChdir(pwd, "extractor")
		}
        }
	data := mustCaptureFromProcess("hg manifest", "extractor")
        manifest := strings.Trim(data, "\n")
        return newStringSet(strings.Split(manifest, "\n")...)
}

// getComment returns a commit's change comment as a string.
func (he HgExtractor) getComment(rev string) string {
        data, err := captureFromProcess("hg log -r " + rev + " --template {desc}\\n")
	if err != nil {
		panic(throw("extractor", "Couldn't spawn hg log: %v", err))
	}
	return data
}

// Repository factory driver class for all repo analyzers.
type RepoStreamer struct {
        revlist []string		// commit identifiers, oldest first
        parents map[string][]string	// commit -> [parent-commit, ...]
        meta map[string]*CommitMeta	// commit -> committer/author/branch
        refs OrderedMap			// 'refs/class/name' -> commit
        tags []Tag			// Tag objects (annotated tags only)
        tagseq int
        commitMap map[string]*Commit
        visibleFiles map[string]map[string]signature
        hashToMark map[[sha1.Size]byte]string
	branchesAreColored bool
        baton *Baton
	extractor Extractor
}

func newRepoStreamer(extractor Extractor) *RepoStreamer {
	rs := new(RepoStreamer)
        rs.revlist = make([]string, 0)
        rs.parents = make(map[string][]string)
        rs.meta = make(map[string]*CommitMeta)
        rs.refs = newOrderedMap()
        rs.tags = make([]Tag, 0)
        rs.tagseq = 0
        rs.commitMap = make(map[string]*Commit)
        rs.visibleFiles = make(map[string]map[string]signature)
        rs.hashToMark = make(map[[sha1.Size]byte]string)
	rs.extractor = extractor
	return rs
}

// getParents returns the list of commit IDs of a commit's parents.
func (be *RepoStreamer) getParents(rev string) []string {
        return be.parents[rev]
}

// isTag ia a previcate; does rev refer to a tag?
func (be *RepoStreamer) isTag(rev string) bool {
        return strings.HasPrefix(be.meta[rev].branch, "refs/tags/")
}

// getCommitter returns the committer's ID/date as a string.
func (be *RepoStreamer) getCommitter(rev string) string {
        return be.meta[rev].ci
}

// getAuthors returns a string list of the authors' names and email addresses.
func (be *RepoStreamer) getAuthors(rev string) []string {
        return []string{be.meta[rev].ai}
}

// fileSetAt returns the set of all files visible at a revision
func (rs *RepoStreamer) fileSetAt(revision string) stringSet {
	var fs stringSet
	for key, _ := range rs.visibleFiles[revision] {
		fs.Add(key)
	}
	// Warning: order is nondeterministic 
	return fs
}


func (rs *RepoStreamer) extract(repo *Repository, progress bool) (*Repository, error) {
        if !rs.extractor.isClean() {
		return nil, fmt.Errorf("repository directory has unsaved changes.")
	}

	rs.baton = newBaton("Extracting", "", progress)
	defer rs.baton.exit("")

	var err error
	defer func(r **Repository, e *error) {
		if thrown := catch("extractor", recover()); thrown != nil {
			if strings.HasPrefix(thrown.class, "extractor") {
				complain(thrown.message)
				*e = errors.New(thrown.message)
				*r = nil
			}
		}
	}(&repo, &err)

	meta := rs.extractor.getMeta()
        repo.makedir()
	front := fmt.Sprintf("#reposurgeon sourcetype %s\n", meta.vcs.name)
	repo.addEvent(newPassthrough(repo, front))

	err = rs.extractor.gatherRevisionIDs(rs)
	if err != nil {
		return nil, fmt.Errorf("while gathering revisions: %v", err)
	}
	rs.baton.twirl("")
	err = rs.extractor.gatherCommitData(rs)
	if err != nil {
		return nil, fmt.Errorf("while gathering commit data: %v", err)
	}
	rs.baton.twirl("")
	err = rs.extractor.gatherAllReferences(rs)
	if err != nil {
		return nil, fmt.Errorf("while gathering tag/branch refs: %v", err)
	}
	rs.baton.twirl("")
	// Sort branch/tag references by target revision ID, earliest first
	// Needs to be done before branch coloring because the simu;ation
	// of the Git branch-coloring alorithm needs it.  Also controls the
	// order in which annotated tags and resets are output.
	rs.refs.valueLess = func(a string, b string) bool {
		for _, item := range rs.revlist {
			if item == a {
				return true
			} else if item == b {
				return false
			}
		}
		panic(throw("extractor", "Did not find revision IDs in revlist"))
	}
	sort.Sort(rs.refs)
	rs.baton.twirl("")
	rs.extractor.colorBranches(rs)

	var uncolored []string
	for _, revision := range rs.revlist {
		if rs.meta[revision].branch == "" {
			uncolored = append(uncolored, revision)
		}
	}

        if len(uncolored) > 0 {
		if verbose >= 1 {
			return nil, fmt.Errorf("missing branch attribute for %v", uncolored)
		} else {
			return nil, fmt.Errorf("some branches do not have local ref names.")
		}
	}
	rs.baton.twirl("")

	consume := make([]string, len(rs.revlist))
	copy(consume, rs.revlist)
	for _, revision  := range consume {
                commit := newCommit(repo)
		commit.setMark(repo.newmark())
                rs.baton.twirl("")
                present := rs.extractor.checkout(revision)
                parents := rs.getParents(revision)
		commit.committer = *newAttribution(rs.getCommitter(revision))
		for _, a := range rs.getAuthors(revision) {
			commit.authors = append(commit.authors,
				*newAttribution(a))
		}
		for _, rev := range parents{
			commit.addParentCommit(rs.commitMap[rev])
		}
                commit.setBranch(rs.meta[revision].branch)
                commit.comment = rs.extractor.getComment(revision)
                if debugEnable(debugEXTRACT) {
			msg := strconv.Quote(commit.comment)
			announce(debugEXTRACT,
				"r%s: comment '%s'", revision, msg)
		}
                // Git fast-import constructs the tree from the first parent only
                // for a merge commit; fileops from all other parents have to be
                // added explicitly
                for _, rev := range parents[:1] {
			for k,v := range rs.visibleFiles[rev] {
				rs.visibleFiles[revision][k] = v
			}
		}

                if len(present) > 0 {
			removed := rs.fileSetAt(revision).Subtract(present)
			for _, pathname := range present {
				if isdir(pathname) {
					continue
				}
				if !exists(pathname) {
					complain("r%s: expected path %s does not exist!",
						revision, pathname)
					continue
				}
				newsig := newSignature(pathname)
				if rs.hashToMark[newsig.hashval] == "" {
					//if debugEnable(debugEXTRACT) {
					//    announce(debugSHOUT, "r%s: %s has old hash",
					//             revision, pathname)
					// }
					// The file's hash corresponds
					// to an existing blob;
					// generate modify, copy, or
					// rename as appropriate.
					if _, ok := rs.visibleFiles[revision][pathname]; !ok || rs.visibleFiles[revision][pathname]!=*newsig {
						announce(debugEXTRACT, "r%s: update for %s", revision, pathname)
						found := false
						var deletia []string
						for oldpath, oldsig := range rs.visibleFiles[revision] {
							if oldsig == *newsig {
								found = true		
								if removed.Contains(oldpath) {
									op := newFileOp(repo)
									op.construct("R", oldpath, pathname)
									commit.appendOperation(*op)
									deletia = append(deletia, oldpath)
								} else if oldpath != pathname {
									op := newFileOp(repo)
									op.construct("C", oldpath, pathname)
									commit.appendOperation(*op)
								}
								break
							}
						}
						// Avoid deleting
						// items from map
						// while iterating
						// through it.
						for _, item := range deletia {
							delete(rs.visibleFiles[revision], item)
						}
						if found {
							op := newFileOp(repo)
							op.construct("M",
								newsig.perms,
								rs.hashToMark[newsig.hashval],
								pathname)
							commit.appendOperation(*op)
						}
					}
				} else {
					// Content hash doesn't match
					// any existing blobs
					announce(debugEXTRACT, "r%s: %s has new hash",
						revision, pathname)
					blobmark := repo.newmark()
					rs.hashToMark[newsig.hashval] = blobmark
					// Actual content enters the representation
					blob := newBlob(repo)
					blob.setMark(blobmark)
					filecopy(blob.getBlobfile(true),pathname)
					blob.addalias(pathname)
					repo.addEvent(blob)
					// Its new fileop is added to the commit
					op := newFileOp(repo)
					op.construct("M", newsig.perms, blobmark, pathname)
					commit.appendOperation(*op)
				}
				rs.visibleFiles[revision][pathname] = *newsig
			}
			for _, tbd := range removed {
				op := newFileOp(repo)
				op.construct("D", tbd)
				commit.appendOperation(*op)
				delete(rs.visibleFiles[revision], tbd)
			}
                }
                if len(parents) == 0 { // && commit.branch != "refs/heads/master"
			reset := newReset(repo, commit.branch, "", commit)
			repo.addEvent(reset)
                }
		commit.sortOperations()
		commit.legacyID = revision
		commit.properties = newOrderedMap()
		rs.commitMap[revision] = commit
		announce(debugEXTRACT, "r%s: gets mark %s (%d ops)", revision, commit.mark, len(commit.operations()))
	}
	// Now append reset objects
	// Note: we time-sorted the resets when they were picked up;
	// this is to ensure that the ordering is (a) deterministic,
	// and (b) easily understood.
	for resetname, revision := range rs.refs.dict {
		if strings.Index(resetname, "/tags/") == -1 {
			// FIXME: what if revision is unknown?
			// keep previous behavior for now
			reset := newReset(repo, resetname, "", rs.commitMap[revision])
			reset.ref = resetname
			repo.addEvent(reset)
		}
	}
	// Last, append tag objects. Sort by tagger-date first
	sort.Slice(rs.tags, func(i, j int) bool {
		return rs.tags[i].tagger.date.Before(rs.tags[j].tagger.date) 
	})
	for _, tag := range rs.tags {
		// Hashes produced by the GitExtractor are turned into proper
		// committish marks here.
		c, ok := rs.commitMap[tag.committish]
		if !ok {
			tag.remember(repo, "", c)
		} else {
			return nil, fmt.Errorf("no commit corresponds to %s", tag.committish)
		}
	}
	rs.extractor.postExtract(repo)
	repo.vcs = meta.vcs
	return repo, err
}

// No user-serviceable parts below this line

/*
 * Baton machinery
 */

// Baton is the state of a progess meter that ships indications to stdout.
type Baton struct {
	prompt    string
	endmsg    string
	lastlen   int
	erase     bool
	counter   int
	countfmt  string
	stream    *os.File
	starttime time.Time
	lastfrac  float64
}

func newBaton(prompt string, endmsg string, enable bool) *Baton {
	me := new(Baton)
	me.prompt = prompt
	me.endmsg = endmsg
	if enable {
		me.stream = os.Stdout
		me.stream.Write([]byte(me.prompt + "...[\b"))
		if me.isatty() {
			me.stream.Write([]byte(" \b"))
		}
		me.counter = 0
		me.starttime = time.Now()
	}
	return me
}

func (baton *Baton) isatty() bool {
	return terminal.IsTerminal(int(baton.stream.Fd()))
}

func (baton *Baton) startcounter(countfmt string, initial int) {
	baton.countfmt = countfmt
	baton.counter = initial
}

func (baton *Baton) bumpcounter() {
	if baton.stream == nil {
		return
	}
	if baton.isatty() {
		if baton.countfmt != "" {
			update := fmt.Sprintf(baton.countfmt, baton.counter)
			baton.stream.Write([]byte(update + strings.Repeat("\b", len(update))))
			//baton.stream.Flush()
		} else {
			baton.twirl("")
		}
	}
	baton.counter++
}

func (baton *Baton) endcounter() {
	if baton.stream != nil {
		w := len(fmt.Sprintf(baton.countfmt, baton.counter))
		baton.stream.Write([]byte(strings.Repeat(" ", w) + strings.Repeat("\b", w)))
		//baton.stream.Flush()
	}
	baton.countfmt = ""
}

// twirl spins the baton
func (baton *Baton) twirl(ch string) {
	if baton.stream == nil {
		return
	}
	if baton.erase {
		baton.stream.Write([]byte(strings.Repeat("\b", baton.lastlen)))
		baton.stream.Write([]byte(strings.Repeat(" ", baton.lastlen)))
		baton.stream.Write([]byte(strings.Repeat("\b", baton.lastlen)))
		baton.erase = true
	}
	if baton.isatty() {
		if ch != "" {
			baton.lastlen = len(ch)
			baton.stream.Write([]byte(ch))
			//baton.stream.Flush()
			baton.erase = strings.Index(ch, "%") != -1
			if baton.erase {
				time.Sleep(100 * time.Millisecond)
			}
		} else {
			baton.lastlen = 1
			baton.erase = false
			if baton.counter > 0 && (baton.counter%(100*1000)) == 0 {
				baton.stream.Write([]byte("!"))
			} else if baton.counter > 0 && (baton.counter%(10*1000)) == 0 {
				baton.stream.Write([]byte("*"))
			} else if baton.counter > 0 && (baton.counter%(1*1000)) == 0 {
				baton.stream.Write([]byte("+"))
			} else {
				baton.stream.Write([]byte{"-/|\\"[baton.counter%4]})
				baton.erase = true
				baton.counter++
			}
		}
	}
}

func (baton *Baton) exit(override string) {
	if override != "" {
		baton.endmsg = override
	}
	if baton.stream != nil {
		baton.stream.Write([]byte(fmt.Sprintf("]\b...(%s) %s.\n",
			time.Since(baton.starttime), baton.endmsg)))
	}
}

func (baton *Baton) readProgress(ccount int64, filesize int64) {
	frac := float64(ccount) / float64(filesize)
	if frac > baton.lastfrac+0.01 {
		baton.twirl(fmt.Sprintf("%f%%", frac*100))
		baton.lastfrac = frac
	}
	baton.twirl("")
}

/*
 * Debugging and utility
 */

var verbose = 0

const debugSHOUT = 0    // Unconditional
const debugSVNDUMP = 2  // Debug Subversion dumping
const debugTOPOLOGY = 2 // Debug repo-extractor logic (coarse-grained)
const debugEXTRACT = 2  // Debug repo-extractor logic (fine-grained)
const debugFILEMAP = 3  // Debug building of filemaps
const debugDELETE = 3   // Debug canonicalization after deletes
const debugIGNORES = 3  // Debug ignore generation
const debugSVNPARSE = 4 // Lower-level Subversion parsing details
const debugEMAILIN = 4  // Debug round-tripping through mailbox_{out|in}
const debugSHUFFLE = 4  // Debug file and directory handling
const debugCOMMANDS = 5 // Show commands as they are executed
const debugUNITE = 5    // Debug mark assignments in merging
const debugLEXER = 6    // Debug selection-language parsing
var quiet = false

// Boolean option false is represented by key not in option map,
// true is represented by an empty stringlist value. 
var globalOptions map[string]stringSet

func haveGlobalOption(name string) bool {
	_, ok := globalOptions[name]
	return ok
}

func globalOption(name string) stringSet {
	d, _ := globalOptions[name]
	return d	// Should be nil if not present
}

func setGlobalOption(name string, value stringSet) {
	globalOptions[name] = value
}

// whoami - ask various programs that keep track of who you are
func whoami() (string, string) {
	if haveGlobalOption("testmode") {
		return "Fred J. Foonly", "foonly@foo.com"
	}
	// Git version-control system
	out1, err1 := exec.Command("git", "config", "user.name").CombinedOutput()
	out2, err2 := exec.Command("git", "config", "user.email").CombinedOutput()
	if err1 == nil && len(out1) != 0 && err2 == nil && len(out2) != 0 {
		return strings.Trim(string(out1), "\n"), strings.Trim(string(out2), "\n")
	}

	// Mercurial version control system
	out3, err3 := exec.Command("hg", "config", "ui.username").CombinedOutput()
	if err3 == nil && len(out3) != 0 {
		e, err := mail.ParseAddress(strings.Trim(string(out3), "\n"))
		if err != nil {
			log.Fatal(err)
		}
		return e.Name, e.Address
	}

	// Out of alternatives
	log.Fatal("can't deduce user identity!")
	return "", ""
}

// screenwidth returns the current width of the terminal window.
func screenwidth() int {
	width, _, err := terminal.GetSize(0)
	if err != nil {
		log.Fatal(err)
	}
	return width
}

/*
 * Debugging and utility
 */

// debugEnable is a hook to set up debug-message filtering.
func debugEnable(level int) bool {
	return verbose >= level
}

// nuke removed a (large) directory, reporting elapsed time.
func nuke(directory string, legend string) {
	baton := newBaton(legend, "", debugEnable(debugSHUFFLE))
	defer baton.exit("")
	// FIXME: Redo with filepath.Walk and a more granular baton
	os.RemoveAll(directory)
}

func complain(msg string, args ...interface{}) {
	content := fmt.Sprintf(msg, args...)
	os.Stderr.Write([]byte("reposurgeon: " + content + "\n"))
}

func announce(lvl int, msg string, args ...interface{}) {
	if debugEnable(lvl) {
		content := fmt.Sprintf(msg, args...)
		os.Stdout.Write([]byte("reposurgeon: " + content + "\n"))
	}
}

// emptyComment says whether comment info should be considered disposable?
func emptyComment(c string) bool {
	if c == "" {
		return true
	}
	c = strings.TrimSpace(c)
	// A CVS artifact from ancient times.
	if c == "" || c == "*** empty log message ***" {
		return true
	}
	return false
}

// OrderedMap is a map witn preserved key order
type OrderedMap struct {
	keys []string
	dict map[string]string
	valueLess func(string, string) bool
}

func newOrderedMap() OrderedMap {
	d := new(OrderedMap)
	d.keys = make([]string, 0)
	d.dict = make(map[string]string)
	return *d
}

func (d *OrderedMap) get(hd string) string {
	payload, ok := d.dict[hd]
	if !ok {
		return ""
	}
	return payload
}

func (d *OrderedMap) has(hd string) bool {
	_, ok := d.dict[hd]
	return ok
}

func (d *OrderedMap) set(hd string, data string) {
	d.dict[hd] = data
	d.keys = append(d.keys, hd)
}

func (d *OrderedMap) delete(hd string) bool {
	delete(d.dict, hd)
	for i, el := range d.keys {
		if hd == el {
			// Zero out the deleted element so it's GCed
			copy(d.keys[i:], d.keys[i+1:])
			d.keys[len(d.keys)-1] = ""
			d.keys = d.keys[:len(d.keys)-1]
			return true
		}
	}
	return false
}

func (d OrderedMap) Len() int {
	return len(d.keys)
}

func (d OrderedMap) String() string {
	var out = "{"
	for _, el := range d.keys {
		out += el + ":" + d.dict[el] + ","
	}
	return out[:len(out)-1] + "}"
}

// Less returns true if the sort method says the value for key i is
// less than the value for key j. Useful with the Go library sort.
func (d OrderedMap) Less(i int, j int) bool {
	return d.valueLess(d.dict[d.keys[i]], d.dict[d.keys[j]])
}

// Swap interchanges key i and j. Useful with the Go library sort.
func (d OrderedMap) Swap(i int, j int) {
	keep := d.keys[j]
	d.keys[j] = d.keys[i]
	d.keys[i] = keep
}

/*
 * RFC2822 message blocks
 *
 * This is how we serialize comments so they can be modified in an editor.
 */

// MessageBlockDivider is the separator between messages in a comment mailbox.
var MessageBlockDivider = bytes.Repeat([]byte("-"), 78)

// MessageBlock is similar to net/mail's type, but the body is pulled inboard
// as a string.  This is appropriate because change comments are normally short.
type MessageBlock struct {
	hdnames stringSet
	header map[string]string
	body   string
}

// newMessageBlock is like net/mail ReadMessage but with a special delimiter.
// Also, we preserve the order of headers read in.
func newMessageBlock(bp *bufio.Reader) (*MessageBlock, error) {
	msg := new(MessageBlock)
	msg.hdnames = make([]string, 0)
	msg.header = make(map[string]string)

	headerize := func(data string) bool {
		if data == "\n" {
			return false
		}
		colon := strings.Index(data, ":")
		if colon == -1 {
			panic(throw("mailbox", "Ill-formed line in mail message"))
		}
		key := data[0:colon]
		payload := strings.TrimSpace(data[colon+1:len(data)])
		msg.hdnames = append(msg.hdnames, key)
		msg.header[key] = payload
		return true
	}
	
	if bp != nil {
		inBody := false
		firstline, err := bp.ReadBytes('\n')
		if err != nil {
			return nil, err
		} else if !bytes.HasPrefix(firstline, MessageBlockDivider) {
			headerize(string(firstline))
		}
		for {
			line, err := bp.ReadBytes('\n')
			if err == io.EOF {
				break
			} else if err != nil {
				return nil, err
			}
			if !inBody && (line[0] == ' ' || line[0] == '\t') {
				// RFC822 continuation
				if len(msg.hdnames) >= 1 {
					lasthdr := msg.hdnames[len(msg.hdnames)-1]
					msg.setHeader(lasthdr,
						msg.getHeader(lasthdr) + string(line))
				}
			} else if !inBody && !headerize(string(line)) {
				inBody = true
				continue
			} else if inBody {
				// check for delimiter
				if bytes.HasPrefix(line, MessageBlockDivider) {
					break
				}
				// undo byte-stuffing *after* the delimiter check
				if bytes.HasPrefix(line, []byte(".")) {
					line = line[1:len(line)-1]
				}
				msg.body += string(line)
			}
		}

		return msg, err
	}

	return msg, nil
}

func (msg *MessageBlock) getPayload() string {
	return msg.body
}

func (msg *MessageBlock) setPayload(data string) {
	msg.body = data
}

func (msg *MessageBlock) getHeader(hd string) string {
	hdrs, ok := msg.header[hd]
	if !ok {
		return ""
	}
	return hdrs
}

func (msg *MessageBlock) setHeader(hd string, data string) {
	msg.header[hd] = string(data)
	msg.hdnames = append(msg.hdnames, hd)
}

func (msg *MessageBlock) deleteHeader(hd string) {
	delete(msg.header, hd)
	msg.hdnames.Remove(hd)
}

func (msg *MessageBlock) String() string {
	hd := ""
	for _, k := range msg.hdnames {
		if v := msg.header[k]; v != "" {
			hd += fmt.Sprintf("%s: %s\n", k, v)
		}
	}

	body := ""
	for _, line := range strings.Split(msg.body, "\n") {
		// byte stuffing so we can protect instances of the delimiter
		// within message bodies.
		if strings.HasPrefix(line, ".") || strings.HasPrefix(line, string(MessageBlockDivider)) {
			body += "."
		}
		body += line + "\n"
	}
	return hd + "\n" + body[0:len(body)-1]
}

/*
 * Time, date, and zone handling
 */

var isocodeToZone = make(map[string]string)

// zoneFromEmail attempts to deduce an IANA time zone from an email address.
// Only works when the TLD is an ISO country code that has exactly one entry
// in the IANA timezone database; it's a big fail for com/edu/org/net and
// big countries like the US.
func zoneFromEmail(addr string) string {
	if len(isocodeToZone) == 0 {
		file, err := os.Open("/usr/share/zoneinfo/zone.tab")
		if err != nil {
			fmt.Fprint(os.Stderr, "reposurgeon: no country-code to timezone mapping")
		} else {
			defer file.Close()

			firstpass := make(map[string][]string)

			scanner := bufio.NewScanner(file)
			for scanner.Scan() {
				line := scanner.Text()
				if strings.HasPrefix(line, "#") {
					continue
				}
				fields := strings.Fields(line)
				code := strings.ToLower(fields[0])
				zone := fields[2]
				_, ok := firstpass[code]
				if !ok {
					firstpass[code] = make([]string, 0)
				}
				firstpass[code] = append(firstpass[code], zone)
			}
			for k, v := range firstpass {
				if len(v) == 1 {
					isocodeToZone[k] = v[0]
				}
			}

			if err := scanner.Err(); err != nil {
				log.Fatal(err)
			}
		}
	}

	fields := strings.Split(addr, ".")
	toplevel := fields[len(fields)-1]

	// If the top-level domain is an ISO country code that implies a
	// single IANA timezine, we're good.
	return isocodeToZone[toplevel]
}

// rfc3339 makes a UTC RFC3339 string from a system timestamp.
// Go's format rules document that this will end with Z, not an 00:00 timezone.
func rfc3339(t time.Time) string {
	return t.UTC().Format(time.RFC3339)
}

var gitDateRE = regexp.MustCompile(`[0-9]+\s*[+-][0-9]+$`)
var zoneOffsetRE = regexp.MustCompile(`^([-+]?[0-9]{2})([0-9]{2})$`)

// locationFromZoneOffset makes a Go location object from a hhhmmm string.
// It is rather a strained hack. We don't get an actual TZ from a
// Git-format date, just a [+-]hhmm offset. Fortunately that
// is usually all we need to dump. Make a location from which
// we can get back the offset string, by storing it as the zone name.
func locationFromZoneOffset(offset string) (*time.Location, error) {
	m := zoneOffsetRE.FindSubmatch([]byte(offset))
	if m == nil || len(m) != 3 {
		return nil, errors.New("ill-formed timezone offset " + string(offset))
	}
	hours, _ := strconv.Atoi(string(m[1]))
	mins, _ := strconv.Atoi(string(m[2]))
	if hours < -14 || hours > 13 || mins > 59 {
		// According to RFC2822 we could put "-0000" in here to
		// indicate invalid zone information.
		return nil, errors.New("dubious zone offset " + string(offset))
	}
	tzname := intern(offset)
	tzoff := (hours*60 + mins) * 60
	return time.FixedZone(tzname, tzoff), nil
}

// Date wraps a system time object, giving it various serializarion and
// deserialization capabilities.
type Date struct {
	timestamp time.Time
}

// GitLogFormat - which git falsely claims is RFC2822-conformant.
// In reality RFC2822 would be "Mon, 02 Aug 2006 15:04:05 -0700",
// which is Go's RFC1123Z format. (We're ignoring obsolete variants
// with letter zones and two-digit years.)
//
// FIXME: Alas, we cannot yet support this due to an apparent bug in time.Parse()
// For bug-isolation purposes we're currently faking it with a format
// Go can handle but that has the tz and year swapped.
//const GitLogFormat = "Mon Jan 02 15:04:05 2006 -0700"
const GitLogFormat = "Mon Jan 02 15:04:05 -0700 2006"

// newDate exists mainly to wrap a parser to recognize date formats that
// exporters or email programs might emit
func newDate(text string) (Date, error) {
	var t Date
	// Special case: we may want current time in UTC
	if len(text) == 0 {
		t.timestamp = time.Now()
		return t, nil
	}
	// Otherwise, look for git's preferred format, which is a timestamp
	// in UTC followed by an offset to be used as a hint for what
	// timezone to display the date in when converting to other
	// formats
	text = strings.TrimSpace(text)
	if gitDateRE.Find([]byte(text)) != nil {
		fields := strings.Fields(text)
		n, err := strconv.Atoi(fields[0])
		if err != nil {
			return t, err
		}
		loc, err2 := locationFromZoneOffset(fields[1])
		if err2 != nil {
			return t, err2
		}
		t.timestamp = time.Unix(int64(n), 0).In(loc)
		return t, nil

	}
	// RFC3339 - because it's the presentation format I prefer
	// RFC3339Nano - so we parse Subversion dates with fractional seconds
	// RFC1123Z - we use it in message-block headers
	// GitLog - git log emits this format
	for _, layout := range []string{time.RFC3339, time.RFC3339Nano, time.RFC1123Z, GitLogFormat} {
		trial, err3 := time.Parse(layout, string(text))
		if err3 == nil {
			t.timestamp = trial.Round(1 * time.Second)
			return t, nil
		}
	}
	return t, errors.New("not a valid timestamp: " + string(text))
}

// isZero tells us if this is an uninitialized date object
func (date *Date) isZero() bool {
	return date.timestamp.IsZero()
}

func (date *Date) clone() Date {
	out := *date
	return out
}

func (date Date) rfc3339() string {
	return rfc3339(date.timestamp)
}

func (date Date) gitlog() string {
	return date.timestamp.Format(GitLogFormat)
}

func (date Date) rfc2822() string {
	// Alas, the format Go calls RFC822 is archaic
	return date.timestamp.Format(time.RFC1123Z)
}

func (date Date) delta(other Date) time.Duration {
	return other.timestamp.Sub(date.timestamp)
}

// String formats a Date object as an internal Git date (Unix time in seconds
// and a hhmm offset).  The tricky part here is what we do if the
// time's location is not already a +-hhmm string.
func (date *Date) String() string {
	var hhmm string
	loc := date.timestamp.Location()
	zone := loc.String()
	if len(zone) > 0 && (zone[0] == byte('+') || zone[0] == byte('-')) {
		hhmm = zone
	} else {
		_, offs := date.timestamp.Zone()
		sign := "+"
		if offs < 0 {
			offs *= -1
			sign = "-"
		}
		hhmm = fmt.Sprintf("%s%02d%02d", sign, offs/60, offs%60)
	}

	return fmt.Sprintf("%d %s", date.timestamp.Unix(), hhmm)
}

func (date *Date) setTZ(zone string) {
	loc, err := time.LoadLocation(zone)
	if err == nil {
		date.timestamp = date.timestamp.In(loc)
	}
}

// Equal tests equality of Date objects 
func (date *Date) Equal(other Date) bool {
	return date.timestamp.Equal(other.timestamp)
}

// Before tests time ordering of Date objects 
func (date *Date) Before(other Date) bool {
	return date.timestamp.Before(other.timestamp)
}

// After tests rime ordering of Date objects 
func (date *Date) After(other Date) bool {
	return date.timestamp.After(other.timestamp)
}

/*
 * Attributions
 */

// Attribution represents pins a reposiory event to a person and time.
type Attribution struct {
	fullname  string
	email string
	date  Date
}

var attributionRE = regexp.MustCompile(`([^<]*\s*)<([^>]*)>(\s*.*)`)

// parseAttributionLine parses a Git attribution line into its fields
func parseAttributionLine(line string) (string, string, string, error) {
	m := attributionRE.FindSubmatch(bytes.TrimSpace([]byte(line)))
	if m != nil {
		name := string(bytes.TrimSpace(m[1]))
		address := string(bytes.TrimSpace(m[2]))
		date := string(bytes.TrimSpace(m[3]))
		return name, address, date, nil
	}
	err := fmt.Errorf("Malformed attribution on '%s'\n", line)
	return "", "", "", err
}

func (attr *Attribution) address() (string, string) {
	return attr.fullname, attr.email
}

// newAttribution makes an Attribution from an author or committer line
func newAttribution(attrline string) *Attribution {
	attr := new(Attribution)

	if attrline != "" {
		fullname, email, datestamp, err1 := parseAttributionLine(attrline)
		if err1 != nil {
			panic(throw("parse", "in neWAttribution: %v", err1))
		}
		parsed, err2 := newDate(datestamp)
		if err2 != nil {
			panic(throw("parse", "Malformed attribution date '%s' in '%s': %v",
				datestamp, attrline, err2))
		}
		// Deal with a cvs2svn artifact
		if fullname == "(no author)" {
			fullname = "no-author"
		}
		attr.fullname = intern(fullname)
		attr.email = intern(email)
		attr.date = parsed
	}
	return attr
}

func (attr Attribution) String() string {
	return attr.fullname + " <" + attr.email + "> " + attr.date.String()
}

func (attr *Attribution) clone() *Attribution {
	mycopy := newAttribution("")
	mycopy.fullname = attr.fullname
	mycopy.email = attr.email
	mycopy.date = attr.date.clone()
	return mycopy
}

// emailOut updates a message-block object with a representation of this
// attribution object.
func (attr *Attribution) emailOut(modifiers stringSet, msg *MessageBlock, hdr string) {
	msg.setHeader(hdr, attr.fullname+" <"+attr.email+">")
	msg.setHeader(hdr+"-Date", attr.date.rfc3339())
}

// Equal compares attributions
func (attr *Attribution) Equal(other *Attribution) bool {
	return attr.fullname == other.fullname && attr.email == other.email && attr.date.Equal(other.date)
}

func (attr *Attribution) actionStamp() string {
	return attr.date.rfc3339() + "!" + attr.email
}

func (attr *Attribution) userid() string {
	return strings.Split(attr.email, "@")[0]
}

func (attr *Attribution) who() string {
	return attr.fullname + " <" + attr.email + ">"
}

// Remap changes the attribution fullname/email according to a map of author entries.
func (attr *Attribution) remap(authors map[string]Contributor) {
	matches := func(attr *Attribution, local string, ae Contributor) bool {
		nlower := strings.ToLower(attr.fullname)
		elower := strings.ToLower(attr.email)
		return strings.HasPrefix(elower, local+"@") || elower == local || (attr.email == "" && nlower == local)
	}

	for local, ae := range authors {
		if matches(attr, local, ae) {
			attr.fullname = intern(ae.fullname)
			attr.email = intern(ae.email)
			if ae.timezone != "" {
				attr.date.setTZ(ae.timezone)
			}
			break
		}
	}
}

/*
 * Repository objects.  All satisfy the Event interface.
 */

// Blob represents a detached blob of data referenced by a mark.
type Blob struct {
	repo       *Repository
	blobseq	   int
	mark       string
	pathlist   []string	// In-repo paths associated with this blob
	colors     []string	// Scratch space for grapg coloring algorithms
	cookie     [2]string	// CVS/SVN cookie analyzed out of this file
	start      int64	// Seek start if this blob refers into a dump
	size       int64	// length start if this blob refers into a dump
	abspath    string
	deleteflag bool
}

var blobseq int

func newBlob(repo *Repository) *Blob {
	b := new(Blob)
	b.repo = repo
	b.pathlist = make([]string, 0)	// These have an implied sequence.
	b.colors = newStringSet()
	b.start = -1
	b.blobseq = blobseq
	blobseq++
	return b
}

// idMe IDs this blob for humans.
func (b Blob) idMe() string {
        return fmt.Sprintf("blob@%s", b.mark)
}

// pathlist is implemented for uniformity with commits and fileops."
func (b *Blob) paths(_pathtype string) []string {
        return b.pathlist
}

func (b *Blob) addalias(argpath string) {
	for _, el := range b.pathlist {
		if el == argpath {
			return
		}
	}
	b.pathlist = append(b.pathlist, argpath)
}

func (b *Blob) setBlobfile(argpath string) {
        b.abspath = argpath
}

// getBloobfile returns the path where the blob's content lives.
func (b *Blob) getBlobfile(create bool) string {
        if b.abspath != "" {
		return b.abspath
	}
	stem := fmt.Sprintf("%09d", b.blobseq)
	// The point of the breaking up the ID into multiple sections is to use
	// the filesystem to speed up lookup time.
	parts := strings.Split(filepath.FromSlash(b.repo.subdir("")), "/")
	parts = append(parts,  		
		[]string{"blobs", stem[0:3], stem[3:6], stem[6:len(stem)]}...)
	if create {
		dir := strings.Join(parts[0:len(parts)-1], "/")
		err := os.MkdirAll(filepath.FromSlash(dir), userReadWriteMode)
		if err != nil {
			panic(fmt.Errorf("Blob creation: %v", err))
		}
	}
	return filepath.FromSlash(strings.Join(parts[0:len(parts)], "/"))
}
	
// hasfile answers the question: "Does this blob have its own file?"
func (b *Blob)  hasfile() bool {
        return b.repo.seekstream != nil || b.start != -1
}

// getContent gets the content of the blob as a string.
func (b *Blob) getContent() string {
        if !b.hasfile() {
		var data = make([]byte, b.size)
		_, err := b.repo.seekstream.ReadAt(data, b.start)
		if err != nil {
			panic(fmt.Errorf("Blob fetch: %v", err))
		}
		return string(data)
	}
	var file io.ReadCloser
	var err error
	var buf bytes.Buffer
        if haveGlobalOption("compressblobs") {
		file, err = gzip.NewReader(&buf)
	} else {
		file, err = os.Open(b.getBlobfile(false))
	}
	if err != nil {
		panic(fmt.Errorf("Blob creation: %v", err))
	}
	defer file.Close()
        data, err := ioutil.ReadAll(file)
	if err != nil {
		panic(fmt.Errorf("Blob write: %v", err))
	}
	return string(data)
}

// setContent sets the content of the blob from a string.
func (b *Blob) setContent(text string, tell int64) {
        b.start = tell
        b.size = int64(len(text))
        if b.hasfile() {
		var file io.WriteCloser
		var err error
		var buf bytes.Buffer
		if haveGlobalOption("compressblobs") {
			file = gzip.NewWriter(&buf)
		} else {
			file, err = os.OpenFile(b.getBlobfile(true),
				os.O_WRONLY | os.O_CREATE, userReadWriteMode)
		}
		if err != nil {
			panic(fmt.Errorf("Blob update: %v", err))
		}
		defer file.Close()
		_, err = io.WriteString(file, text)
		if err != nil {
			panic(fmt.Errorf("Blob write: %v", err))
		}
	}
}

// materialize stores this content as a separate file, if it isn't already.
func (b *Blob) materialize() string {
        if !b.hasfile() {
		b.setContent(b.getContent(), 0)
	}
        return b.getBlobfile(false)
}

// sha returns the SHA-1 hash of the blob content. Used only for indexing,
// does not need to be crypto-quality
func (b *Blob) sha() string {
	return fmt.Sprintf("%x", sha1.Sum([]byte(b.getContent())))
}

// getMark returns the blob's identifying mark
func (b Blob) getMark() string {
	return b.mark
}

// setMark sets the blob's mark and clears the mark lookup cache.
func (b *Blob) setMark(mark string) string {
        b.mark = mark
	if b.repo != nil {
		b.repo._eventByMark = nil
	}
        return mark
}

// forget de-links this commit from its repo.
func (b *Blob) forget() {
        b.repo = nil
}

// moveto changes the repo this blob is associated with."
func (b *Blob) moveto(repo *Repository) *Blob {
	if b.hasfile() {
		oldloc := b.getBlobfile(false)
		b.repo = repo
		newloc := b.getBlobfile(true)
		announce(debugSHUFFLE,
			"blob rename calls os.rename(%s, %s)", oldloc, newloc)
		os.Rename(oldloc, newloc)
	}
        return b
}

// clone makes a copy of this blob, pointing at the same file."
func (b *Blob) clone(repo *Repository) *Blob {
        c := newBlob(repo)
        c.colors = newStringSet()
        if b.hasfile() {
		announce(debugSHUFFLE,
			"blob clone for %s (%s) calls os.Link(): %s -> %s", b.mark, b.pathlist, b.getBlobfile(false), c.getBlobfile(false))
		err := os.Link(b.getBlobfile(false), c.getBlobfile(true))
		if err != nil {
			panic(fmt.Errorf("Blob clone: %v", err))
		}
	}
        return c
}


func (b Blob) String() string {
        if b.hasfile() {
		fn := b.getBlobfile(false)
		if !exists(fn)  {
			return ""
		}
	}
	content := b.getContent()
	data := fmt.Sprintf("blob\nmark %s\ndata %d\n",	b.mark, len(content))
	return data + content + "\n"
}

type Tag struct {
	repo *Repository
	name string
	color string
	committish string
	target *Commit
	tagger *Attribution
	comment string
	deletehook bool
	legacyID string
}

func newTag(repo *Repository,
	name string, committish string,
	target *Commit, tagger *Attribution, comment string) *Tag {
	t := new(Tag)
	t.name = name
	t.tagger = tagger
	t.comment = comment
	t.remember(repo, committish, target)
	return t
}

// getMark returns the tag's identifying mark
// Not actually used, needed to satisfy Event interface
func (t Tag) getMark() string {
	return ""
}

// remember records an attachment to a repo and commit.
func (t *Tag) remember(repo *Repository, committish string, target *Commit) {
        t.repo = repo
	t.target = target
        if t.target != nil {
		t.committish = target.getMark()
        } else {
		t.committish = committish
	}
	if t.target != nil {
		t.target.attach(t)
	}
}

// forget removes this tag's attachment to its commit and repo.
func (t *Tag) forget() {
        if t.target != nil {
                t.target.detach(t)
		t.target = nil
	}
        t.repo = nil
}

// index returns our 0-origin index in our repo.
func (t *Tag) index() int {
        return t.repo.index(t)
}

// idMe IDs this tag for humans."
func (t Tag) idMe() string {
	suffix := ""
	if t.legacyID != "" {
		suffix = "=<" + t.legacyID + ">"
	}
        return fmt.Sprintf("tag@%s%s (%s)", t.committish, suffix, t.name)
}

// actionStamp controls how a tag stamp is made
func (t *Tag) actionStamp() string {
        return t.tagger.actionStamp()
}

// showlegacy yields a legacy ID in the expected form for the ancestral system.
func (t *Tag) showlegacy() string {
        if t.legacyID == "" {
		return ""
	}
        // Special case for Subversion
        if t.repo != nil && t.repo.vcs != nil && t.repo.vcs.name == "svn" {
		return "r" + t.legacyID
        } else {
		return t.legacyID
	}
}

// tags enables do_tags() to report tags.
func (t *Tag) tags(modifiers stringSet, eventnum int, _cols int) string {
        return fmt.Sprintf("%6d\ttag\t%s", eventnum+1, t.name)
}

// emailOut enables do_mailbox_out() to report tag metadata
func (t *Tag) emailOut(modifiers stringSet, eventnum int,
	filterRegexp *regexp.Regexp) string {
        msg, _ := newMessageBlock(nil)
        msg.setHeader("Event-Number", fmt.Sprintf("%d", eventnum+1))
	msg.setHeader("Tag-Name", t.name)
	msg.setHeader("Target-Mark", t.committish)
        if t.tagger != nil {
            t.tagger.emailOut(modifiers, msg, "Tagger")
	}
        if t.legacyID != "" {
		msg.setHeader("Legacy-ID", t.legacyID)
	}
	check := strings.Split(t.comment, "\n")[0]
	if len(check) > 64 {
		check = check[0:64]
	}
        msg.setHeader("Check-Text", check)
        msg.setPayload(t.comment)
        if t.comment != "" && !strings.HasSuffix(t.comment, "\n") {
            complain("in tag %s, comment was not LF-terminated.", t.name)
	}
        if filterRegexp != nil{
		for key, _ := range msg.header {
			if len(filterRegexp.Find([]byte(key + ":"))) > 0 {
				msg.deleteHeader(key)
			}
		}
	}

	return msg.String()
}


// emailIn updates this Tag from a parsed message block.
func (t *Tag) emailIn(msg *MessageBlock, fill bool) bool {
        tagname := msg.getHeader("Tag-Name")
        if tagname == ""  {
		panic(throw("mailbox", "update to tag %s is malformed", t.name))
	}
        modified := false
        if t.name != tagname {
		announce(debugEMAILIN,
			"in tag %s, Tag-Name is modified %q -> %q",
			msg.getHeader("Event-Number"), t.name, tagname)
		t.name = tagname
		modified = true
	}
        if target := msg.getHeader("Target-Mark"); target != "" && target != t.committish {
                modified = true
		t.committish = target
	}
	if newtagger := msg.getHeader("Tagger"); newtagger != "" {
                newname, newemail, _, err := parseAttributionLine(newtagger)
		if err != nil || newname == "" || newemail == "" {
			panic(throw("mailbox", "Can't recognize address in Tagger: " + newtagger))
		} else if t.tagger.fullname != newname || t.tagger.email != newemail {
			t.tagger.fullname, t.tagger.email = newname, newemail
			announce(debugEMAILIN,
				"in tag %s, Tagger is modified",
				msg.getHeader("Event-Number"))
			modified = true
		}
		if taggerdate := msg.getHeader("Tagger-Date"); taggerdate != "" {
			candidate := msg.getHeader("Tagger-Date")
			date, err := newDate(candidate)
			if err != nil {
				panic(throw("mailbox", "Malformed date %s in tag message: %v",
					candidate, err))
			}
			if t.tagger.date.isZero() || !date.timestamp.Equal(t.tagger.date.timestamp) {
				// Yes, display this unconditionally
				if t.repo != nil {
					announce(debugSHOUT, "in %s, Tagger-Date is modified '%v' -> '%v' (delta %v)",
						t.idMe(),
						t.tagger.date, taggerdate,
						date.timestamp.Sub(t.tagger.date.timestamp))
					t.tagger.date = date
					modified = true
				}
			}
		}
	}

        if legacy := msg.getHeader("Legacy-ID"); legacy != "" && legacy != t.legacyID {
                modified = true
		t.legacyID = legacy
	}
        newcomment := msg.getPayload()
        if haveGlobalOption("canonicalize") {
		newcomment = strings.TrimSpace(newcomment)
		newcomment = strings.Replace(newcomment, "\r\n", "\n", 1)
		newcomment += "\n"
	}
        if newcomment != t.comment {
		announce(debugEMAILIN, "in tag %s, comment is modified %q -> %q",
			msg.getHeader("Event-Number"), t.comment, newcomment)
		modified = true
		t.comment = newcomment
	}

        if fill && t.tagger.fullname == "" {
		t.tagger.fullname, t.tagger.email = whoami()
		modified = true
	}
	
	return modified
}

// ianaDecode tells if a string has undecodable i18n sequences in it.
// http://www.iana.org/assignments/character-sets/character-sets.xhtml
func ianaDecode (data, codec string) (string, bool, error) {
	// This works around a bug in the ianaindex package.
	// It should return a copying decoder if the name is a synonym for ASCII
	// but does not.
	var asciiNames = stringSet{
		"US-ASCII",
		"iso-ir-6",
		"ANSI_X3.4-1968",
		"ANSI_X3.4-1986",
		"ISO_646.irv:1991",
		"ISO646-US",
		"us",
		"IBM367",
		"cp367",
		"csASCII",
		"ascii",	// Unaccountably not an IANA name
	}
	if asciiNames.Contains(codec) {
		for _, c := range data {
			if c > 127 {
				return data, false, nil
			}
		}
		return data, true, nil
	}
	enc, err1 := ianaindex.IANA.Encoding(codec)
	if err1 != nil {
		return data, false, err1
	}
	dec := enc.NewDecoder()
	decoded, err2 := dec.Bytes([]byte(data))
	return string(decoded), err2 == nil, err2
}

func (t *Tag) undecodable(codec string) bool {
	_, f1, err1 := ianaDecode(t.name, codec)
	if !f1 || err1 == nil {
		return false
	}
	_, f2, err2 := ianaDecode(t.tagger.fullname, codec)
	if !f2 || err2 == nil {
		return false
	}
	_, f2, err2 = ianaDecode(t.tagger.email, codec)
	if !f2 || err2 == nil {
		return false
	}
	_, f3, err3 := ianaDecode(t.comment, codec)
	if !f3 || err3 == nil {
		return false
	}
	return true
}

// branchname returns the full branch reference corresponding to a tag.
func branchname(tagname string) string {
	fulltagname := tagname
        if strings.Count(tagname, "/") == 0 {
		fulltagname = "tags/" + fulltagname
	}
        if !strings.HasPrefix(fulltagname, "refs/") {
		fulltagname = "refs/" + fulltagname
	}
        return fulltagname
}
	
// stamp enables do_stamp() to report action stamps
func (t *Tag) stamp(_modifiers stringSet, _eventnum int, cols int) string {
        report := "<" + t.tagger.actionStamp() + "> " + strings.Split(t.comment, "\n")[0]
        if cols > 0 {
		report = report[0:cols]
	}
        return report
}

// String dumps this tag in import-stream format
func (t Tag) String() string {
        parts := []string{fmt.Sprintf("tag %s\n", t.name)}
        if t.legacyID != "" {
		id := fmt.Sprintf("#legacy-id %s\n", t.legacyID)
		parts = append(parts, id)
	}
        parts = append(parts, fmt.Sprintf("from %s\n", t.committish))
        if t.tagger != nil {
		tagger := fmt.Sprintf("tagger %s\n", t.tagger)
		parts = append(parts, tagger)
	}
	comment := t.comment
        if t.comment != "" && t.repo.writeOptions.Contains("--legacy") && t.legacyID != "" {
		comment += fmt.Sprintf("\nLegacy-ID: %s\n", t.legacyID)
		parts = append(parts, comment)
	}
	data := fmt.Sprintf("data %d\n", len(comment))
        parts = append(parts, data)
        return strings.Join(parts, "") + comment + "\n"
}

// Reset represents a branch creation."
type Reset struct {
        repo *Repository
        ref string
        committish string
        target *Commit
        deletehook bool
        color string
}

func newReset(repo *Repository, ref string, committish string, target *Commit) *Reset {
	reset := new(Reset)
	reset.repo = repo
	reset.ref = ref
	reset.committish = committish
	reset.target = target
	reset.remember(repo, committish, target)
	return reset
}

// idMe IDs this reset for humans.
func (reset Reset) idMe() string {
        return fmt.Sprintf("reset-%s@%d", reset.ref, reset.repo.index(reset))
}

// getMark returns the reset's identifying mark
// Not actually used, needed to satisfy Event interface
func (reset Reset) getMark() string {
	return ""
}

// remember records an attachment to a repo and commit.
func (reset *Reset) remember(repo *Repository, committish string, target *Commit) {
        reset.repo = repo
        if target != nil {
		reset.target = target
		reset.committish = target.getMark()
        } else {
		reset.committish = committish
		if reset.repo != nil && committish != ""{
			reset.target = reset.repo.markToEvent(reset.committish).(*Commit)
		}
	}
	if reset.target != nil {
		reset.target.attach(reset)
	}
}

// forget loses this reset's attachment to its commit and repo.
func (reset *Reset) forget() {
        if reset.target != nil {
		reset.target.detach(reset)
		reset.target = nil
	}
        reset.repo = nil
}

// moveto changes the repo this reset is associated with."
func (reset *Reset) moveto(repo *Repository) {
	reset.repo = repo
}

// tags enables do_tags() to report resets."
func (reset Reset) tags(modifiers stringSet, eventnum int, _cols int) string {
        return fmt.Sprintf("%6d\treset\t%s", eventnum+1, reset.ref)
}

// String dumps this reset in import-stream format
func (reset Reset) String() string {
        if reset.repo.realized != nil {
		var branch string = reset.ref
		if strings.Index(reset.ref, "^") != -1 {
			branch = strings.Split(reset.ref, "^")[0]
		}
		reset.repo.realized[branch] = true
	}
        st := fmt.Sprintf("reset %s\n", reset.ref)
        if reset.committish == "" {
		return st
	}
        return st + fmt.Sprintf("from %s\n\n", reset.committish)
}

type FileOp struct {
        repo *Repository
        op string
        committish string
        source string
        target string
        mode string
        path string
        ref string
        inline string
}


func newFileOp(repo *Repository) *FileOp {
	op := new(FileOp)
	op.repo = repo
	return op
}

func (fileop *FileOp) setOp(op string) {
	fileop.op = op
}

// Thiis is a space-optimization hack.  We count on the compiler to
// put each of these in the text segment and pass around just one reference each.
// If we ever think the implementation has changed to falsify this assumption,
// we'll change these to var declarations and intern these strings explicitly.
const opM	= "M"
const opD	= "D"
const opR	= "R"
const opC	= "C"
const opN	= "N"
const deleteall = "deleteall"

func (fileop *FileOp) construct(opargs ...string) *FileOp {
        if opargs[0] == "M" {
		fileop.op = opM
		fileop.mode = opargs[1]
		fileop.ref = opargs[2]
		fileop.path = opargs[3]
        } else if opargs[0] == "D" {
		fileop.op = opD
		fileop.path = opargs[1]
        } else if opargs[0] == "N" {
		fileop.op = opN
		fileop.ref = opargs[1]
		fileop.path = opargs[2]
        } else if opargs[0] == "R" {
		fileop.op = opR
		fileop.source = opargs[1]
		fileop.target = opargs[2]
        } else if opargs[0] == "C" {
		fileop.op = opC
		fileop.source = opargs[1]
		fileop.target = opargs[2]
        } else if opargs[0] == "deleteall" {
		fileop.op = deleteall
        } else {
		panic(throw("parse", "unexpected fileop " + opargs[0]))
	}
        return fileop
}


// stringScan extracts tokens from a text line.  Tokens maky be
// "-quoted, in which the bounding quotes are stripped and C-style
// backslashes interpreted in the interior. Meant to mimic the
// behavior of git-fast-import.
func stringScan(input string) []string {
	bufs := make([][]byte, 0)
	state := 0
	tokenStart := func() {
		//fmt.Fprintf(os.Stderr, "New token\n")
		bufs = append(bufs, make([]byte, 0))
	}
	tokenContinue := func(c byte) {
		//fmt.Fprintf(os.Stderr, "%c: appending\n", c)
		bufs[len(bufs)-1] = append(bufs[len(bufs)-1], c)
	}
	toState := func(c byte, i int) int {
		//fmt.Fprintf(os.Stderr, "%c: %d -> %d\n", c, state, i)
		return i
	}
	for i, _ := range input {
		c := input[i]
		//fmt.Fprintf(os.Stderr, "State %d, byte %c\n", state, c)
		switch state {
		case 0:	// ground state, in whitespace
			if unicode.IsSpace(rune(c)) {
				continue
			} else if c == '"' {
				state = toState(c, 2)
				tokenStart()
				tokenContinue(c)
			} else {
				state = toState(c, 1)
				tokenStart()
				tokenContinue(c)
			}
		case 1:	// in token
			if unicode.IsSpace(rune(c)) {
				state = toState(c, 0)
			} else {
				tokenContinue(c)
			}
		case 2:	// in string
			if c == '"' {
				tokenContinue(c)
				state = toState(c, 0)
			} else if c == '\\' {
				state = toState(c, 3)
			} else {
				tokenContinue(c)
			}
		case 3:	// after \ in string
			state = toState(c, 2)
			tokenContinue(c)
		}
	}
	

	out := make([]string, len(bufs))
	for i, tok := range(bufs) {
		s := string(tok)
		if s[0] == '"' {
			s, _ = strconv.Unquote(s)
		}
		out[i] = s
	}
	return out
}

var modifyRE = regexp.MustCompile(`(M) ([0-9]+) (\S+) (.*)`)

// parse interprets a fileop dump line
func (fileop *FileOp) parse(opline string) *FileOp {
	fields := stringScan(opline)
	if len(fields) == 0 {
		panic(throw("parse", "Empty fileop line %q", opline))
	}
        if strings.HasPrefix(opline, "M ") {
		if len(fields) != 4 {
			panic(throw("parse", "Bad format of M line: %q", opline))
		}
		fileop.op = opM
		fileop.mode = string(fields[1])
		fileop.ref = string(fields[2])
		fileop.path = intern(string(fields[3]))
	} else if strings.HasPrefix(opline, "N ") {
		if len(fields) != 3 {
			panic(throw("parse", "Bad format of N line: %q", opline))
		}
		fileop.op = opN
		fileop.ref = string(fields[1])
		fileop.path = intern(string(fields[2]))
	} else if strings.HasPrefix(opline, "D ") {
		if len(fields) != 2 {
			panic(throw("parse", "Bad format of D line: %q", opline))
		}
		fileop.op = opD
		fileop.path = intern(string(fields[1]))
	} else if strings.HasPrefix(opline, "R ") {
		if len(fields) != 3 {
			panic(throw("parse", "Bad format of R line: %q", opline))
		}
		fileop.op = opR
		fileop.source = intern(fields[1])
		fileop.target = intern(fields[2])
	} else if strings.HasPrefix(opline, "C ") {
		if len(fields) != 3 {
			panic(throw("parse", "Bad format of C line: %q", opline))
		}
		fileop.op = opC
		fileop.source = intern(fields[1])
		fileop.target = intern(fields[2])
	} else if opline == "deleteall" {
		fileop.op = deleteall
	} else {
		panic(throw("parse", "Unexpected fileop while parsing %q", opline))
	}
        return fileop
}

// paths returns the set of all paths touched by this file op
func (fileop *FileOp) paths(pathtype stringSet) stringSet {
        if pathtype == nil {
		pathtype = stringSet{opM, opD, opR, opC, opN}
	}
        if !pathtype.Contains(fileop.op) {
		return stringSet{}
	}
        if fileop.op == opM || fileop.op == opD || fileop.op == opN {
		return stringSet{fileop.path}
	}
        if fileop.op == opR || fileop.op == opC {
		return stringSet{fileop.source, fileop.target}
	}
        // Ugh...this isn't right for deleteall, but since we don't expect
        // to see that except at branch tips we'll ignore it for now.
        if fileop.op == deleteall {
		return stringSet{}
	}
        panic("Unknown fileop type " + fileop.op)
}

// relevant tells if two fileops touch any of the same filesthe same file(s)
func (fileop *FileOp) relevant(other *FileOp) bool {
        if fileop.op == deleteall || other.op == deleteall {
		return true
	}
	return len(fileop.paths(nil).Intersection(other.paths(nil))) > 0
}

// String dumps this fileop in import-stream format
func (fileop FileOp) String() string {
	quotifyIfNeeded := func(cpath string) string {
		if len(strings.Split(cpath, " \t")) > 1 {
			return strconv.Quote(cpath)
		} else {
			return cpath
		}
	}
        if fileop.op == opM {
		parts := fileop.op + " " + fileop.mode + " " + fileop.ref
		parts += " " + quotifyIfNeeded(fileop.path) + "\n"
		if fileop.ref == "inline" {
			parts += fmt.Sprintf("data %d\n", len(fileop.inline))
			parts += fileop.inline + "\n"
		}
		return parts
        } else if fileop.op == opN {
		parts := "N " + fileop.ref 
		parts += " " + quotifyIfNeeded(fileop.path) + "\n"
		if fileop.ref == "inline" {
			parts += fmt.Sprintf("data %d\n", len(fileop.inline))
			parts += fileop.inline + "\n"
		}
		return parts
        } else if fileop.op == opD {
		return "D " + quotifyIfNeeded(fileop.path) + "\n"
	} else if fileop.op == opR || fileop.op == opC {
		return fmt.Sprintf(`%s %s %s`, fileop.op,
			quotifyIfNeeded(fileop.source),
			quotifyIfNeeded(fileop.target)) + "\n"
        } else if fileop.op == deleteall {
		return fileop.op + "\n"
        } else {
		panic(throw("Unexpected op %s while writing", fileop.op))
	}
}


// Callout is a stub object for callout marks in incomplete repository segments.
type Callout struct {
	mark string
	branch string
	_childNodes []string
}

func newCallout(mark string) *Callout {
	callout := new(Callout)
        callout.mark = mark
        callout._childNodes = make([]string, 0)
	return callout
}

func (callout Callout) callout() string {
        return callout.mark
}

func (callout Callout) getMark() string {
        return callout.mark
}

func (callout Callout) idMe() string {
        return fmt.Sprintf("callout-%s", callout.mark)
}

// Stub to satisfy Event interface - should never be used
func (callout Callout) String() string {
        return fmt.Sprintf("callout-%s", callout.mark)
}

type ManifestEntry struct {
	mode string
	ref string
	inline string
}

func (m ManifestEntry) String() string {
	return fmt.Sprintf("<entry mode=%q ref=%q inline=%q>",
		m.mode, m.ref, m.inline)
}

// Commit represents a commit event in a fast-export stream
type Commit struct {
        repo *Repository
        mark string                 // Mark name of commit (may be None)
        authors []Attribution       // Authors of commit
        committer Attribution       // Person responsible for committing it.
        comment string              // Commit comment
        branch string               // branch name
        fileops []FileOp            // blob and file operation list
        properties OrderedMap	    // commit properties (extension)
        _manifest map[string]*ManifestEntry
        color string                // Scratch storage for graph-coloring 
        legacyID string             // Commit's ID in an alien system
        common string               // Used only by the Subversion parser
        deleteflag bool             // Flag used during deletion operations
        attachments []Event         // Tags and Resets pointing at this commit
        _parentNodes []CommitLike   // list of parent nodes
        _childNodes []CommitLike    // list of child nodes
        _pathset stringSet
}

func (commit Commit) getMark() string {
        return commit.mark
}

func newCommit(repo *Repository) *Commit {
	commit := new(Commit)
	commit.repo = repo
	commit.authors = make([]Attribution, 0)
	commit.fileops = make([]FileOp, 0)
	commit.properties = newOrderedMap()
	commit.attachments = make([]Event, 0)
	commit._childNodes = make([]CommitLike, 0)
	commit._parentNodes = make([]CommitLike, 0)
	//commit._pathset = nil
	return commit
}

func (commit *Commit) detach(event Event) bool {
	for i, el := range commit.attachments {
		if event == el {
			// Zero out the deleted element so it's GCed
			copy(commit.attachments[i:], commit.attachments[i+1:])
			commit.attachments[len(commit.attachments)-1] = nil
			commit.attachments = commit.attachments[:len(commit.attachments)-1]
			return true
		}
	}
	return false
}

func (commit *Commit) attach(event Event) {
	commit.attachments = append(commit.attachments, event)
}

// index gives the commit's 0-origin index in our repo.
func (commit *Commit) index() int {
        return commit.repo.index(commit)
}

// idMe IDs this commit for humans.
func (commit Commit) idMe() string {
        myid := fmt.Sprintf("commit@%s", commit.mark)
        if commit.legacyID != "" {
		myid += fmt.Sprintf("=<%s>", commit.legacyID)
	}
        return myid
}

// when returns an imputed timestamp for sorting after unites.
func (commit *Commit) when() time.Time {
        return commit.committer.date.timestamp
}

// date returns the commit date, for purpose of display and reference
func (commit *Commit) date() Date {
        if commit.authors != nil {
		return commit.authors[0].date
	}
        return commit.committer.date
}

// setBranch sets the repo's branch field.
func (commit *Commit) setBranch(branch string) {
        commit.branch = intern(branch)
}

// operations returns a list of ileops associated with this commit;
// it hides how this is represented.
func (commit *Commit) operations() []FileOp {
        return commit.fileops
}

// setOperations replaces the set of fileops associated with this commit.
func (commit *Commit) setOperations(ops []FileOp) {
        commit.fileops = ops
        commit.invalidatePathsetCache()
	commit.invalidateManifests()
}

// appendOperation appends to the set of fileops associated with this commit.
func (commit *Commit) appendOperation(op FileOp) {
        commit.fileops = append(commit.fileops, op)
        commit.invalidatePathsetCache()
	commit.invalidateManifests()
}

// prependOperation prepends to the set of fileops associated with this commit.
func (commit *Commit) prependOperation(op FileOp) {
        commit.fileops = append([]FileOp{op}, commit.fileops...)
        commit.invalidatePathsetCache()
	commit.invalidateManifests()
}

// sortOperations sorts fileops on a commit the same way git-fast-export does
func (commit *Commit) sortOperations() {
	const sortkeySentinel = "@"
	pathpart := func(fileop FileOp) string {
		if fileop.path != "" {
			return fileop.path
		}
		if fileop.source != "" {
			return fileop.path
		}
		return ""
	}
        // As it says, 'Handle files below a directory first, in case they are
        // all deleted and the directory changes to a file or symlink.'
        // First sort the renames last, then sort lexicographically
        // We append a sentinel to make sure "a/b/c" < "a/b" < "a".
	lessthan :=  func(i, j int) bool {
		if commit.fileops[i].op != "R" && commit.fileops[j].op == "R" {
			return true
		}
		left := pathpart(commit.fileops[i]) + sortkeySentinel
		right := pathpart(commit.fileops[j]) + sortkeySentinel
		return left < right
	}
        sort.Slice(commit.fileops, lessthan)
        commit.invalidatePathsetCache()
}

// bump increments the timestamps on this commit to avoid time collisions.
func (commit *Commit) bump(i int) {
	delta := time.Second * time.Duration(i)
        commit.committer.date.timestamp.Add(delta)
        for _, author := range commit.authors {
		author.date.timestamp.Add(delta)
	}
}

// clone replicates this commit, without its fileops, color, children, or tags.
func (commit *Commit) clone(repo *Repository) *Commit {
        c := newCommit(repo)
        c.committer = commit.committer
        c.authors = make([]Attribution, len(commit.authors))
	// FIXME: Test this against Python, which does a deeper copy.
	// It might alter the behavior of the split operation.
	copy(c.authors, commit.authors)
	c.comment = commit.comment
	c.mark = commit.mark
	c.branch = commit.branch
        return c
}

// showlegacy returns a legacy ID in the expected form for the ancestral system.
func (commit *Commit) showlegacy() string {
        if commit.legacyID == "" {
		return ""
	}
        // Special case for Subversion
        if commit.repo != nil && commit.repo.vcs != nil && commit.repo.vcs.name == "svn" {
		return "r" + commit.legacyID
	}
	return commit.legacyID
}

// lister enables do_list() to report commits.
func (commit *Commit) lister(_modifiers stringSet, eventnum int, cols int) string {
        topline := strings.Split(commit.comment, "\n")[0]
        summary := fmt.Sprintf("%6d %s %6s ",
		eventnum+1, commit.date().rfc3339(), commit.mark)
        if commit.legacyID != "" {
		legacy := fmt.Sprintf("<%s>", commit.legacyID)
		summary += fmt.Sprintf("%6s ", legacy)
	}
        report := summary + topline
        if cols > 0 {
		report = report[:cols]
	}
        return report
}

// stamp enables do_stamp() to report action stamps.
func (commit *Commit) stamp(modifiers stringSet, _eventnum int, cols int) string {
        report := "<" + commit.actionStamp() + "> " + strings.Split(commit.comment, "\n")[0]
        if cols > 0 {
		report = report[:cols]
	}
        return report
}

// tags enables do_tags() to report tag tip commits.
func (commit *Commit) tags(_modifiers stringSet, eventnum int, _cols int) string {
        if commit.branch == "" || strings.Index(commit.branch, "/tags/") == -1 {
		return ""
	}
	if commit.hasChildren() {
		successorBranches := newStringSet()
		for _, child := range commit.children() {
			switch child.(type) {
			case *Commit:
				successorBranches.Add(child.(Commit).branch)
			case *Callout:
				complain("internal error: callouts do not have branches: %s",
					child.idMe())
			default:
				panic("In tags method, unexpected type in child list")
			}
		}
		if len(successorBranches) == 1 && successorBranches[0] == commit.branch {
			return ""
		}
	}
        return fmt.Sprintf("%6d\tcommit\t%s", eventnum+1, commit.branch)
}

// emailOut enables do_mailbox_out() to report commit metadata.
func (commit *Commit) emailOut(modifiers stringSet,
	eventnum int, filterRegexp *regexp.Regexp) string {
        msg, _ := newMessageBlock(nil)
        msg.setHeader("Event-Number", fmt.Sprintf("%d", eventnum+1))
        msg.setHeader("Event-Mark", commit.mark)
        msg.setHeader("Branch", commit.branch)
        msg.setHeader("Parents", strings.Join(commit.parentMarks(), " "))
        if commit.authors != nil && len(commit.authors) > 0 {
		commit.authors[0].emailOut(modifiers, msg, "Author")
		for i, coauthor := range commit.authors[1:] {
			coauthor.emailOut(modifiers, msg, "Author" + fmt.Sprintf("%d", 2+i))
		}
		commit.committer.emailOut(modifiers, msg, "Committer")
	}
        if commit.legacyID != "" {
		msg.setHeader("Legacy-ID", commit.legacyID)
	}
        if len(commit.properties.keys) > 0 {
		for _, name := range commit.properties.keys {
			hdr := ""
			for _, s := range strings.Split(name, "-") {
				hdr += strings.Title(s)
			}
			value := commit.properties.get(name)
			value = strings.Replace(value, "\n", `\n`, 0)
			value = strings.Replace(value, "\t", `\t`, 0)
			msg.setHeader("Property-" + hdr, value)
		}
	}
	check := strings.Split(commit.comment, "\n")[0]
	if len(check) > 54 {
		check = check[0:54]
	}
        msg.setHeader("Check-Text", check)
        msg.setPayload(commit.comment)
        if !strings.HasSuffix(commit.comment, "\n") {
		complain("in commit %s, comment was not LF-terminated.",
			commit.mark)
	}
        if filterRegexp != nil {
		for _, key := range msg.hdnames {
			if len(filterRegexp.Find([]byte(key + ":"))) > 0 {
			msg.deleteHeader(key)
		}
	    }
	}
	return msg.String()
}

// actionStamp controls how a commit stamp is made.
func (commit *Commit) actionStamp() string {
        // Prefer the author stamp because that doesn't change when patches
        // are replayed onto a repository, while the commit stamp will.
        if commit.authors != nil && len(commit.authors) > 0 {
		return commit.authors[0].actionStamp()
	}
        return commit.committer.actionStamp()
}

func stringSliceEqual(a, b []string) bool {
	// If one is nil, the other must also be nil.
	if (a == nil) != (b == nil) { 
		return false; 
	}

	if len(a) != len(b) {
		return false
	}

	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}

	return true
}

var authorRE = regexp.MustCompile("Author[0-9]*$")

// emailIn updates this commit from a parsed email message.
func (commit *Commit) emailIn(msg *MessageBlock, fill bool) bool {
        modified := false
	newbranch := msg.getHeader("Branch")
        if newbranch != "" && commit.branch != newbranch {
		modified = true
		commit.setBranch(newbranch)
	}
	newparents := msg.getHeader("Parents") 
        if newparents != "" {
		newParentList := strings.Split(newparents, " ")
		if !stringSliceEqual(commit.parentMarks(), newParentList) {
			modified = true
			commit.setParentMarks(newParentList)
		}
	}
	c := &commit.committer
	newcommitter := msg.getHeader("Committer")
        if newcommitter != "" {
		var err2 error
                newfullname, newemail, _, err2 := parseAttributionLine(newcommitter)
		if err2 != nil {
			panic(throw("mailbox", "bad attribution: %v", err2))
		}
                if c.fullname != newfullname || c.email != newemail {
			c.fullname, c.email = newfullname, newemail
			if commit.repo != nil {
				announce(debugEMAILIN, "in %s, Committer is modified", commit.idMe())
			}
			modified = true
		}
	}
	newcommitdate, err := newDate(msg.getHeader("Committer-Date"))
	if err != nil {
		panic(throw("mailbox", "Bad Committer-Date: %v", err))
	}
        if newcommitdate.isZero() && !newcommitdate.Equal(c.date) {
                if commit.repo != nil {
			announce(debugEMAILIN, "in %s, Committer-Date is modified '%s' -> '%s' (delta %d)",
				commit.idMe(),
				c.date, newcommitdate,
				c.date.delta(newcommitdate))
		}
                c.date = newcommitdate
                modified = true
	}
	newauthor := msg.getHeader("Author")
        if  newauthor != "" {
		authorkeys := []string{} 
		for _, hd := range msg.hdnames {
			if len(authorRE.Find([]byte(hd))) > 0 {
				authorkeys = append(authorkeys, hd)
			}
		}
		// Potential minor bug here if > 10 authors;
		// lexicographic sort order doesn't match numeric
		// msg is *not* a dict so the .keys() is correct
		sort.Strings(authorkeys)
		for i := 0; i < len(authorkeys) - len(commit.authors); i++ {
			commit.authors = append(commit.authors, *newAttribution(authorkeys[i]))
		}
		// Another potential minor bug: permuting the set of authors
		// will look like a modification, as old and new authors are
		// compaired pairwise rather than set equality being checked.
		// Possibly a feature if one thinks order is significant, but
		// I just did it this way because it was easier.
		for i, hdr := range authorkeys {
			c := &commit.authors[i]
			newfullname, newemail, _, err := parseAttributionLine(msg.getHeader(hdr))
			if err != nil {
				panic(throw("mailbox", "bad attribution: %v", err))
			}
			if c.fullname != newfullname || c.email != newemail {
				c.fullname, c.email = newfullname, newemail
				announce(debugEMAILIN,
					"in commit %s, Author #%d is modified",
					msg.getHeader("Event-Number"), i+1)
				modified = true
			}
			newdate := msg.getHeader(hdr + "-Date")
			if newdate != "" {
				date, err := newDate(newdate)
				if err != nil {
					panic(throw("mailbox", "Bad Author-Date: %v", err))
				}
				if c.date.isZero() || !date.Equal(c.date) {
					eventnum := msg.getHeader("Event-Number")
					if commit.repo != nil && eventnum != "" {
						announce(debugEMAILIN,
							"in event %s, %s-Date #%d is modified",
							eventnum, hdr, i+1)
					}
					c.date = date
					modified = true
				}
			}
		}
	}
	newlegacy := msg.getHeader("Legacy-ID")
        if newlegacy != "" && newlegacy != commit.legacyID {
                modified = true
                commit.legacyID = newlegacy
	}
        newprops := newOrderedMap()
        for _, prophdr := range msg.hdnames {
		if !strings.HasPrefix(prophdr, "Property-") {
			continue
		}
		propkey := strings.ToLower(prophdr[9:])
		propval := msg.getHeader(prophdr)
		if propval == "True" || propval == "False" {
			newprops.set(propkey, propval)
		} else {
			newprops.set(propkey, strconv.Quote(propval))
		}
	}
	propsModified := !reflect.DeepEqual(newprops, commit.properties)
	if propsModified {
		commit.properties = newprops
		modified = true
	}
        newcomment := msg.getPayload()
	if haveGlobalOption("canonicalize") {
		newcomment = strings.TrimSpace(newcomment)
		newcomment = strings.Replace(newcomment, "\r\n", "\n", 1)
		newcomment += "\n"
	}
        if newcomment != commit.comment {
		announce(debugEMAILIN, "in %s, comment is modified %q -> %q",
			commit.idMe(), commit.comment, newcomment)
		modified = true
		commit.comment = newcomment
	}
        if fill {
		modified = true
		if commit.committer.date.isZero() {
			d, _ := newDate("")
			commit.committer.date = d
		}
		if commit.committer.fullname == "" {
			commit.committer.fullname, commit.committer.email = whoami()
		}
	}
        return modified
}

// setMark sets the commit's mark and clears the lookup cache.
func (commit *Commit) setMark(mark string) string {
        commit.mark = mark
	if commit.repo != nil {
		commit.repo._eventByMark = nil
	}
        return mark
}

// forget de-links this commit from its parents.
func (commit *Commit) forget() {
        commit.setParents([]CommitLike{})
        for _, fileop := range commit.operations() {
            if fileop.op == opN {
		    commit.repo.inlines -=1
	    }
	}
        commit.repo = nil
}

// moveto changes the repo this commit is associated with.
func (commit *Commit) moveto(repo *Repository) {
        for _, fileop := range commit.operations() {
		fileop.repo = repo
		if fileop.op == opN {
			commit.repo.inlines -=1
			repo.inlines += 1
		}
	}
        commit.repo = repo
}

// parents gets a list of this commit's parents.
func (commit *Commit) parents() []CommitLike {
        return commit._parentNodes
}

// invalidateManifests cleans out manifess in this commit and all descendants
func (commit *Commit) invalidateManifests() {
	commit._manifest = nil
	for _, c := range commit.children() {
		switch c.(type) {
		case *Commit:
			c.(*Commit).invalidateManifests()
		case *Callout:
			/* do nothing */
		default:
			panic("InvalidateManifests found unexpected type in child list")
		}
	}
}

// parentMarks hides the parent list behind a wrapper, so that we
// can memoize the computation, which is very expensive and frequently
// performed.
func (commit *Commit) parentMarks() []string {
	var out []string
	for _, x := range commit._parentNodes {
		out = append(out, x.getMark())
	}
	return out
}

// commitRemove removes all instances of a commit/callout pointer from a list
func commitRemove(commitlist []CommitLike, event Event) []CommitLike {
	for i, el := range commitlist {
		if event == el {
			// Zero out the deleted element so it's GCed
			copy(commitlist[i:], commitlist[i+1:])
			commitlist[len(commitlist)-1] = nil
			commitlist = commitlist[:len(commitlist)-1]
		}
	}
	return commitlist
}

func (commit *Commit) setParents(parents []CommitLike) {
        for _, parent := range commit._parentNodes {
		// remove all occurrences of self in old parent's children cache
		switch parent.(type) {
		case (Commit):
			parent.(*Commit)._childNodes = commitRemove(parent.(*Commit)._childNodes, commit)
		case (Callout):
			complain("not removing callout %s", parent.(Callout).mark)
		}
	}
        commit._parentNodes = parents
        for _, parent := range commit._parentNodes {
		switch parent.(type) {
		case *Commit:
			parent.(*Commit)._childNodes = append(parent.(*Commit)._childNodes, commit)
		case *Callout:
			/* do nothing */
		}
	}
        commit.invalidateManifests()
}

func (commit *Commit) setParentMarks(marks []string) {
	var clist []CommitLike
	for _, m := range marks {
		clist = append(clist, commit.repo.markToEvent(m).(CommitLike)) 
	}
	commit.setParents(clist)
}

func (commit *Commit) addParentCommit(newparent *Commit) {
        commit._parentNodes = append(commit._parentNodes, newparent)
        newparent._childNodes = append(newparent._childNodes, commit)
        commit.invalidateManifests()
}

func (commit *Commit) addParentByMark(mark string) {
	newparent := commit.repo.markToEvent(mark).(*Commit)
        if newparent == nil {
		panic("Ill-formed stream: cannot resolve " + mark)
	}
	commit.addParentCommit(newparent)
}


// callout generates a callout cookie for this commit.
func (commit Commit) callout() string {
        return commit.actionStamp()
}

// is_callot tells if the specified mark field a callout?"
func isCallout(mark string) bool {
        return strings.Index(mark, "!") != -1
}

func (commit *Commit) addCallout(mark string) {
        commit._parentNodes = append(commit._parentNodes, newCallout(mark))
}

func (commit *Commit) insertParent(idx int, mark string) {
        newparent := commit.repo.markToEvent(mark)
	if newparent == nil {
		complain("invalid mark %s passed to insertParent", mark)
		return
	}
	// Stupid slice tricks: https://github.com/golang/go/wiki/SliceTricks
        commit._parentNodes = append(commit._parentNodes[:idx], append([]CommitLike{newparent.(*Commit)}, commit._parentNodes[idx:]...)...)
	switch newparent.(type) {
	case *Commit:
		newparent.(*Commit)._childNodes = append(newparent.(*Commit)._childNodes, commit)
	}
        commit.invalidateManifests()
}

func (commit *Commit) removeParent(event *Commit) {
        // remove *all* occurences of event in parents
        commit._parentNodes = commitRemove(commit._parentNodes, event)
        // and all occurences of self in event's children
        event._childNodes = commitRemove(event._childNodes, commit)
        commit.invalidateManifests()
}

func (commit *Commit) replaceParent(e1, e2 *Commit) {
	for i, item := range commit._parentNodes {
		if item == e1 {
			commit._parentNodes[i] = e2
			commitRemove(e1._childNodes, commit)
			e2._childNodes = append(e2._childNodes, commit)
			commit.invalidateManifests()
			return
		}
	}
        commit.invalidateManifests()
}

func (commit *Commit) hasParents() bool {
	    return len(commit._parentNodes) > 0
}

func (commit *Commit) hasCallouts() bool {
	for _, c := range commit._parentNodes {
		switch c.(type) {
		case Callout:
			return true
		}
	}
		
	return false
}

// children gets a list of this commit's children (Commits or Callouts)."
func (commit *Commit) children() []CommitLike {
        return commit._childNodes	
}

func (commit *Commit) childMarks() []string {
	var out []string
	for _, x := range commit._childNodes {
		out = append(out, x.getMark())
	}
	return out
}

// hasChildren is a predicate - does this commit have children?"
func (commit *Commit) hasChildren() bool {
	return len(commit._childNodes) > 0
}

// firstChild gets the first child of this commit, or None if not hasChildren()."
func (commit *Commit) firstChild() *Commit {
	if len(commit._childNodes) == 0 {
		return nil
	}
        return commit._childNodes[0].(*Commit)
}

// descendedFrom tells if this commit a descendent of the specified other?
func (commit *Commit) descendedFrom(other *Commit) bool {
        if !commit.hasParents() {
            return false
	}
	for _, item := range commit.parents() {
		if item == other {
			return true
		}
	}
	for _, item := range commit.parents() {
		switch item.(type) {
		case *Commit:
			if item.(*Commit).descendedFrom(other) {
				return true
			}
		}
	}

	return false
}

// cliques returns a dictionary mapping filenames to associated M cliques.
// Change in behavior from Python: the map keys are not ordered.
func (commit *Commit) cliques() map[string][]int {
	cliques := make(map[string][]int)
        for i, fileop := range commit.operations() {
		if fileop.op == opM {
			_, ok := cliques[fileop.path]
			if !ok {
				cliques[fileop.path] = make([]int, 0)
			}
			cliques[fileop.path] = append(cliques[fileop.path], i)
		}
	}
        return cliques
}

// fileopDump reports file ops without data or inlines; used for debugging only.
func (commit *Commit) fileopDump() {
	banner := fmt.Sprintf("commit %d, mark %s:\n", commit.repo.find(commit.mark)+1, commit.mark)
        os.Stdout.Write([]byte(banner))
	for i, op := range commit.operations() {
		report := fmt.Sprintf("%d: %-20s\n", i, op.String())
		os.Stdout.Write([]byte(report))
	}
}


// paths returns the set of all paths touched by this commit.
func (commit *Commit) paths(pathtype stringSet) stringSet {
        if commit._pathset == nil {
		commit._pathset = newStringSet()
		for _, fileop := range commit.operations() {
			for _, item := range fileop.paths(pathtype) {
				commit._pathset.Add(item)
					
			}
		}
	}
        return commit._pathset
}

// invalidatePathsetCache forces a rebuild on the next call to paths().
func (commit *Commit) invalidatePathsetCache() {
        commit._pathset = nil
}

// visible tells if a path is modified and not deleted in the ancestors
func (commit *Commit) visible(argpath string) *Commit {
        ancestor := commit
        for {
		parents := ancestor.parents()
		if len(parents) == 0 {
			break
		}  else {
			switch parents[0].(type) {
			case *Callout:
				break
			}
			ancestor = parents[0].(*Commit)
			// This loop assumes that the op sequence has no
			// M/C/R foo after D foo pairs. If this condition
			// is violated it can throw false negatives.
			for _, fileop := range ancestor.operations() {
				if fileop.op == opD && fileop.path == argpath {
					return nil
				} else if fileop.op == opM && fileop.path == argpath {
					return ancestor
				} else if (fileop.op == opR || fileop.op == opC) && fileop.target == argpath {
					return ancestor
				}
			}
		}
	}
	return nil
}

// manifest returns a map from all pathnames visible at this commit
// to ManifestEntry structures. The map contents is shared as much as
// possible with manifests from previous commits to keep working-set
// size to a minimum.  Note, if the working set blows up horribly
// anyway, the map overhead here is a thing to suspect - we might
// have to something like the copy-on-write structure in the ancestral
// Python.
func (commit *Commit) manifest() map[string]*ManifestEntry {
	// yeah, baby this operation is *so* memoized...
        if commit._manifest != nil {
		return commit._manifest
	}
	commit._manifest = make(map[string]*ManifestEntry)
	if commit.hasParents() {
		p := commit.parents()[0]
		switch p.(type) {
		case *Commit:
			// Magic recursion, force fetch or recompute
			// of manifest back to the root commit.
			// Git only inherits files from the first parent. 
			m := p.(*Commit).manifest()
			for k, v := range m {
				// map entries are pointers so that
				// generations will share the actual
				// entries.
				commit._manifest[k] = v
			}
		case *Callout:
			complain("internal error: can't get through a callout")
		default:
			panic("manifest() found unexpected type in parent list")
		}
	}
        // Take own fileops into account.
        for _, fileop := range commit.operations() {
		if fileop.op == opM {
			commit._manifest[fileop.path] = &ManifestEntry{fileop.mode, fileop.ref, fileop.inline}
		} else if fileop.op == opD {
			delete(commit._manifest, fileop.path)
		} else if fileop.op == opC {
			commit._manifest[fileop.target] = commit._manifest[fileop.source]
		} else if fileop.op == opR {
			commit._manifest[fileop.target] = commit._manifest[fileop.source]
			delete(commit._manifest, fileop.source)
		} else if fileop.op == "deleteall" {
			commit._manifest = make(map[string]*ManifestEntry)
		}
	}
        return commit._manifest
}

// canonicalize replaces fileops by a minimal set of D and M with same result.
func (commit *Commit) canonicalize() {
	if len(commit.fileops) == 0 {
		return
	}
	// Discard everything before the last deletall
	lastdel := 0
	for i, op := range commit.operations() {
		if op.op == deleteall {
			lastdel = i 
		}
	}
	commit.fileops = commit.fileops[lastdel:len(commit.fileops)]
	if len(commit.fileops) < 2 {
		return
	}
        // Get paths touched by non-deleteall operations.
	commit.invalidatePathsetCache()
        paths := commit.paths(nil)
        // Full canonicalization is very expensive on large
        // repositories. Try an inexpensive check for cases it needn't
        // be done. If all ops are Ms and Ds, and every path in a commit
        // is unique, don't do it.  The .gitignores guard is required
        // because these are sometimes generated.
	md := 0
	for _, op := range commit.operations() {
		if op.op == opM || op.op == opD {
			md++
		}
	}
	gi := 0
	all := 0
	for _, cpath := range commit.paths(nil) {
		all++
		if path.Base(cpath) == ".gitignore" {
			gi++
		}
	}
        if md > 1 && (all != md || gi > 0){
		// Fetch the tree state before us...
		var previous map[string]*ManifestEntry
		if !commit.hasParents() {
			previous = make(map[string]*ManifestEntry)
		} else {
			p := commit.parents()[0]
			switch p.(type) {
			case *Commit:
				previous = p.(*Commit).manifest()
			case *Callout:
				complain("internal error: can't get through a callout")
				return
			default:
				panic("manifest() found unexpected type in parent list")
			}
		}
		current := commit.manifest()
		newops := make([]FileOp, 0)
		// Generate needed D fileops.
		if commit.fileops[0].op != deleteall {
			// Only files touched by non-deleteall ops might disappear.
			for _, cpath := range paths {
				_, old := previous[cpath]
				_, new := current[cpath]
				if old && !new {
					fileop := newFileOp(commit.repo)
					fileop.construct("D", cpath)
					newops = append(newops, *fileop)
				}
			}
		}
		// Generate needed M fileops.
		// Only paths touched by non-deleteall ops can be changed.
		for _, cpath := range paths {
			oe, _ := previous[cpath]
			ne, newok := current[cpath]
			if newok && ne != oe {
				fileop := newFileOp(commit.repo)
				fileop.construct(opM, ne.mode, ne.ref, cpath)
				if ne.ref == "inline" {
					fileop.inline = ne.inline
				}
				newops = append(newops, *fileop)
			}
		}
		commit.setOperations(newops)
	}
        // Finishing touches.  Sorting always has to be done
        commit.sortOperations()
        commit._pathset = nil
}

// alldeletes is a predicate: is this an all-deletes commit?
func (commit *Commit) alldeletes(killset stringSet) bool {
        if killset == nil {
		killset = stringSet{opD, deleteall}
	}
	for _, fileop := range commit.operations() {
		if !killset.Contains(fileop.op) {
			return false
		}
	}
	
        return true
}

// checkout makes a directory with links to files in a specified checkout.
// FIXME: function needs unit test.
func (commit *Commit) checkout(directory string) string {
        if directory == "" {
		directory = filepath.FromSlash(commit.repo.subdir("") + "/" + commit.mark)
	}
	if !exists(directory) {
		os.Mkdir(directory, userReadWriteMode)
	}

	defer func () {
		if r := recover(); r != nil {
			complain("could not create checkout directory or files: %v.", r)
		}
	}()

	for cpath, entry := range commit.manifest() {
                fullpath := filepath.FromSlash(directory +
			"/" + cpath + "/" + entry.ref)
                if !exists(fullpath) {
			parts := strings.Split(fullpath, "/")
			// os.MkdirAll is broken and rpike says they
			// won't fix it.
			// https://github.com/golang/go/issues/22323
			var dpath string
			for i, _ := range parts[0:len(parts)-1] {
				dpath = filepath.FromSlash(strings.Join(parts[:i], "/"))
				err := os.Mkdir(dpath, userReadWriteMode)
				if err != nil {
					panic(fmt.Errorf("Directory creation failed during checkout: %v", err))
				}

			}
			rawmode, err2 := strconv.ParseUint(entry.mode, 8, 32)
			if err2 != nil {
				panic(err2)
			}
			mode := os.FileMode(rawmode)
			blob := commit.repo.markToEvent(entry.ref).(*Blob)
			if entry.ref == "inline" {
				file, err3 := os.OpenFile(blob.getBlobfile(true),
					os.O_WRONLY | os.O_CREATE, mode)
				if err3 != nil {
					panic(fmt.Errorf("File creation for inline failed during checkout: %v", err3))
				}
				file.Write([]byte(entry.inline))
				file.Close()
			} else {
				if blob.hasfile() {
					os.Link(blob.getBlobfile(false), fullpath)
				} else {
					file, err4 := os.OpenFile(blob.getBlobfile(true),
						os.O_WRONLY | os.O_CREATE, mode)
					if err4 != nil {
						panic(fmt.Errorf("File creation failed during checkout: %v", err4))
					}
					file.Write([]byte(blob.getContent()))
					file.Close()
				}
			}
		}
	}
	return directory
}

// head returns the branch to which this commit belongs.
func (commit *Commit) head() string {
        if strings.HasPrefix(commit.branch, "refs/heads/") || !commit.hasChildren() {
		return commit.branch
	}
	// FIXME: We need a unit test for the nontrivial case
        rank := 0
	var child Event
	for rank, child = range commit.children() {
		switch child.(type) {
		case *Commit:
			if child.(*Commit).branch == commit.branch {
				return child.(*Commit).head()
			}
		case *Callout:
			complain("internal error: callouts do not have branches: %s",
				child.idMe())
		}
	}
        if rank == 0 {
		switch child.(type) {
		case *Commit:
			child.(*Commit).head() // there was only one child
		case *Callout:
			complain("internal error: callouts do not have branches: %s",
				child.idMe())
		}
	}
        panic(throw("command", "Can't deduce a branch head for %s", commit.mark))
}

// tip enables do_tip() to report deduced branch tips.
func (commit *Commit) tip(_modifiers stringSet, eventnum int, cols int) string {
        summary := fmt.Sprintf("%6d %s %6s ",
		eventnum+1, commit.date().rfc3339(), commit.mark)
        report := summary + commit.head()
        if cols > 0 {
		report = report[:cols]
	}
        return report
}

// reference answers whether this commit references a specified blob mark.
func (commit *Commit) references(mark string) bool {
        for _, fileop := range commit.operations() {
		if fileop.op == opM && fileop.ref == mark {
			return true
		}
	}
        return false
}

// blobByName looks up file content by name
func (commit *Commit) blobByName(pathname string) (string, bool) {
	entry, ok := commit.manifest()[pathname]
        if !ok {
		 return "", false
	}
	if entry.ref == "inline" {
		return entry.inline, true
	}
	retrieved := commit.repo.markToEvent(entry.ref)
	switch retrieved.(type) {
	case *Blob:
		return retrieved.(*Blob).getContent(), true
	default:
		errmsg := fmt.Sprintf("Unexpected type while attempting to fetch %s content at %s", pathname, entry.ref)
		panic(errmsg)
	}
}

// undecodable tells whether this commit has undecodable i18n sequences in it?
// FIXME: Needs unit test
func (commit *Commit) undecodable(codec string) bool {
	_, f1, err1 := ianaDecode(commit.committer.fullname, codec)
	if !f1 || err1 == nil {
		return false
	}
	_, f1, err1 = ianaDecode(commit.committer.email, codec)
	if !f1 || err1 == nil {
		return false
	}
	for _, attr := range commit.authors {
		_, f2, err2 := ianaDecode(attr.fullname, codec)
		if !f2 || err2 == nil {
			return false
		}
		_, f3, err3 := ianaDecode(attr.email, codec)
		if !f3 || err3 == nil {
			return false
		}
	}
	_, f4, err4 := ianaDecode(commit.comment, codec)
	if !f4 || err4 == nil {
		return false
	}
	return true
}

// delete severs this commit from its repository.
func (commit *Commit) delete(policy stringSet) {
        //commit.repo.delete([]int{commit.index()}, policy)	FIXME
}

// dump reports this commit in import-stream format.
func (commit Commit) String() string {
	vcs := commit.repo.preferred
        if vcs == nil && commit.repo.vcs != nil && commit.repo.vcs.importer != "" {
		vcs = commit.repo.vcs
	}
        parts := make([]string, 0)
        incremental := false
        if !commit.repo.writeOptions.Contains("--noincremental") {
		if commit.repo.realized != nil  && commit.hasParents() {
			if _, ok := commit.repo.realized[commit.branch]; !ok {
				parent := commit.parents()[0]
				switch parent.(type) {
				case *Commit:
					pbranch := parent.(*Commit).branch
					if !commit.repo.realized[pbranch] {
						incremental = true
					}
				}
			}
		}
	}
        if incremental {
		parts = append(parts, fmt.Sprintf("reset %s^0\n\n", commit.branch))
	}
        parts = append(parts, fmt.Sprintf("commit %s\n", commit.branch))
        if commit.legacyID != "" {
		parts = append(parts, fmt.Sprintf("#legacy-id %s\n", commit.legacyID))
	}
        if commit.repo.realized != nil {
		commit.repo.realized[commit.branch] = true
	}
        if commit.mark != "" {
		parts = append(parts, fmt.Sprintf("mark %s\n", commit.mark))
	}
        if len(commit.authors) > 0 {
		for _, author := range commit.authors {
			parts = append(parts, fmt.Sprintf("author %s\n", author))
		}
	}
        if commit.committer.fullname != ""{
		parts = append(parts, fmt.Sprintf("committer %s\n", commit.committer))
	}
        // As of git 2.13.6 (possibly earlier) the comment fields of
        // commit is no longer optional - you have to emit data 0 if there
        // is no comment, otherwise the importer gets confused.
        comment := commit.comment
        if commit.repo.writeOptions.Contains("--legacy") && commit.legacyID != "" {
		comment += fmt.Sprintf("\nLegacy-ID: %s\n", commit.legacyID)
	}
        parts = append(parts, fmt.Sprintf("data %d\n%s", len(comment), comment))
        if commit.repo.exportStyle().Contains("nl-after-comment") {
		parts = append(parts, "\n")
	}
        parents := commit.parents()
        if len(parents) > 0 {
		ancestor := parents[0]
		if !incremental || commit.repo.internals.Contains(ancestor.getMark()) {
			parts = append(parts, fmt.Sprintf("from %s\n", ancestor.getMark()))
		} else if commit.repo.writeOptions.Contains("--callout") {
			parts = append(parts, fmt.Sprintf("from %s\n", ancestor.callout()))
		}
		for _, ancestor := range parents[1:] {
			var nugget string
			if commit.repo.internals == nil || commit.repo.internals.Contains(ancestor.getMark()) {
				nugget = ancestor.getMark()
			} else {
				nugget = ancestor.callout()
			}
			parts = append(parts, fmt.Sprintf("merge %s\n", nugget))
		}
	}
	if vcs != nil && vcs.extensions.Contains("commit-properties") {
		if len(commit.properties.keys) > 0 {
			for _, name := range commit.properties.keys {
				value := commit.properties.get(name)
				if value == "true" || value == "false" {
					if value != "" {
						parts = append(parts, fmt.Sprintf("property %s\n", name))
					}
				} else {
					parts = append(parts,
						fmt.Sprintf("property %s %d %s\n", name, len(value), value))
				}
			}
		}
	}
	for _, op := range commit.operations() {
		parts = append(parts, op.String())
	}
        if !commit.repo.exportStyle().Contains("no-nl-after-commit") {
		parts = append(parts, "\n")
	}
        return strings.Join(parts, "")
}

//Passthrough represents a passthrough line.
type Passthrough struct {
	repo *Repository
	text string
	deleteflag bool
	color string
}

func newPassthrough(repo *Repository, line string) *Passthrough {
	p := new(Passthrough)
        p.repo = repo
        p.text = line
	// Don't do this!  These sometimes need to be added to the front.
	//if repo != nil {
	//	repo.events = append(repo.events, p)
	//}
	return p
}

// emailOut enables do_mailbox_out() to report these.
func (p *Passthrough) emailOut(_modifiers stringSet,
	eventnum int, _filterRegexp *regexp.Regexp) string {
        msg, _ := newMessageBlock(nil)
        msg.setHeader("Event-Number", fmt.Sprintf("%d", eventnum+1))
        msg.setPayload(p.text)
        return msg.String()
}

func (p *Passthrough) emailIn(msg *MessageBlock) {
        p.text = msg.getPayload()
}

// idMe IDs this passthrough for humans."
func (p Passthrough) idMe() string {
        return fmt.Sprintf("passthrough@%d", p.repo.index(p))
}

//getMark is a stub required for the Event interface
func (p Passthrough) getMark() string {
        return ""
}

// String reports this passthrough in import-stream format.
func (p Passthrough) String() string {
        return p.text
}
	
// Generic extractor code begins here

// signature is a file signature - path, hash value of content and permissions."
type signature struct {
	pathname string
	hashval [sha1.Size]byte
	perms string
}

func newSignature(path string) *signature {
	file, err1 := os.Open(path)
	defer file.Close()
	if err1 != nil {
		panic(throw("extractor", "Can't open %q\n", path))
	}
	st, err2 := file.Stat()
	if err2 != nil {
		panic(throw("extractor", "Can't stat %q\n", path))
	}

	ps := new(signature)
        ps.pathname = path
	if !st.IsDir() {
		h := sha1.New()
		if _, err := io.Copy(h, file); err != nil {
			log.Fatal(err)
		}
		perms := st.Mode()
		// Map to the restricted set of modes that are allowed in
		// the stream format.
		if (perms & 0100700) == 0100700 {
			perms = 0100755
		} else if (perms & 0100600) == 0100600 {
			perms = 0100644
		}
		ps.perms = fmt.Sprintf("%6o", perms)
	}
	return ps
}

func (s signature) String() string {
        return fmt.Sprintf("<%s:%s:%s>",
		s.pathname, s.perms, s.hashval)
}

func (s signature) Equal(other signature) bool {
	return s.pathname == other.pathname &&
		s.hashval == other.hashval &&
		s.perms == other.perms
}

// capture runs a specified command, capturing the output.
func captureFromProcess(command string) (string, error) {
	announce(debugCOMMANDS, "%s: capturing %s", rfc3339(time.Now()), command)
	cmd := exec.Command("sh", "-c", command)
	content, err := cmd.CombinedOutput()
	if debugEnable(debugCOMMANDS) {
		os.Stderr.Write([]byte(content))
	}
	return string(content), err
}

// branchbase returns the branch minus refs/heads or refs/tags.
func branchbase(branch string) string {
	for _, p := range []string{"refs/heads/", "refs/tags/"} {
		if strings.HasPrefix(branch, p) {
			return branch[len(p):]
		}
	}
	return filepath.Base(branch)
}

// Stream parsing
//
// The Subversion dumpfile format is documented at
//
// https://svn.apache.org/repos/asf/subversion/trunk/notes/dump-load-format.txt

// Use numeric codes rather than (un-interned) strings
// to reduce working-set size.
const sdNONE = 0	// Must be integer zero
const sdFILE = 1
const sdDIR = 2
const sdADD = 1
const sdDELETE = 3
const sdCHANGE = 4
const sdREPLACE = 5
const sdNUKE = 6	// Not part of the Subversion data model

// If these don't match the constants above, havoc will ensue
var ActionValues = []string{"none", "add", "delete", "change", "replace"}
var PathTypeValues = []string{"none", "file", "dir", "ILLEGAL-TYPE"}

// Native Subversion properties that we don't suppress: svn:externals
// The reason for these suppressions is to avoid a huge volume of
// junk file properties - cvs2svn in particular generates them like
// mad.  We want to let through other properties that might carry
// useful information.
var IgnoreProperties = []string {
	"svn:executable",  // We special-case this one elsewhere
	"svn:ignore",      // We special-case this one elsewhere
	"svn:special",     // We special-case this one elsewhere
	"svn:mime-type",
	"svn:keywords",
	"svn:needs-lock",
	"svn:eol-style",   // Don't want to suppress, but cvs2svn floods these.
}

type NodeAction struct {
	// These are set during parsing.  Can all initially have zero values
	revision int
	path string
	kind int
	action int	// initially sdNONE
	fromRev int
	fromPath string
	contentHash [sha1.Size]byte
	fromHash [sha1.Size]byte
	blob *Blob
	props OrderedMap
	propchange bool
	// These are set during the analysis phase
	//fromSet = None FIXME: PathMap
	blobmark string
	generated bool
}

func (action NodeAction) String() string {
	out := "<NodeAction: "
	out += fmt.Sprintf("%d", action.revision)
	out += " " + ActionValues[action.action]
	out += " " + PathTypeValues[action.kind]
	out += " '" + action.path + "'"
	if action.fromRev != 0 {
		out += fmt.Sprintf("%d", action.fromRev) + "~" + action.fromPath
	}
	//if len(action.fromSet) > 0 {
	//	out += "sources=" + action.fromSet.String()
	//}
	if action.generated {
		out += " generated"
	}
	if action.props.Len() > 0 {
		out += action.props.String()
	}
	return out + ">"
}

type RevisionRecord struct {
	nodes []NodeAction
	log string
	date string
	author string
	props OrderedMap
}

func newRevisionRecord(nodes []NodeAction, props OrderedMap) *RevisionRecord {
	rr := new(RevisionRecord)
	rr.nodes = nodes
	// Following four members are so we can avoid having a hash
	// object in every single node instance...those are expensive.
	rr.log = props.get("svn:log")
	props.delete("svn:log")
	rr.author = props.get("svn:author")
	props.delete("svn:author")
	rr.date = props.get("svn:date")
	props.delete("svn:date")
	rr.props = props
	return rr
}

// Cruft recognizers
var cvs2svnTagRE = regexp.MustCompile("This commit was manufactured by cvs2svn to create tag.*'([^']*)'")
var cvs2svnBranchRE = regexp.MustCompile("This commit was manufactured by cvs2svn to create branch.*'([^']*)'")
const SplitSep = '.'

// StreamParser parses a fast-import stream or Subversion dump to
// populate a Repository.
type StreamParser struct {
        repo *Repository
        fp io.Reader		// Can't be os.File, unit tests will fail
        importLine int
        ccount int64
        linebuffers []string
        warnings []string
        // Everything below here is Subversion-specific
        branches map[string]*Commit	// Points to branch root commits
        branchlink stringSet
        branchdeletes stringSet
        branchcopies stringSet
        generatedDeletes []*Commit
        revisions []RevisionRecord
        hashmap map[string]string
        propertyStash map[string]OrderedMap
        fileopBranchlinks stringSet
        directoryBranchlinks stringSet
        activeGitignores map[string]string
        large bool
        propagate map[string]string
}


// newSteamParser parses a fast-import stream or Subversion dump to a Repository.
func newStreamParser(repo *Repository) *StreamParser {
	sp := new(StreamParser)
        sp.repo = repo
        sp.linebuffers = make([]string, 0)
        sp.warnings = make([]string, 0)
	sp.ccount = -1
        // Everything below here is Subversion-specific
        sp.branches = make(map[string]*Commit)
        sp.branchlink = newStringSet()
        sp.branchdeletes = newStringSet()
        sp.branchcopies = newStringSet()
        sp.generatedDeletes = make([]*Commit, 0)
        sp.revisions = make([]RevisionRecord, 0)
        sp.hashmap = make(map[string]string)
        sp.propertyStash = make(map[string]OrderedMap)
        sp.fileopBranchlinks = newStringSet()
        sp.directoryBranchlinks = newStringSet()
        sp.activeGitignores = make(map[string]string)
        sp.propagate = make(map[string]string)
	return sp
}

func (sp *StreamParser) error(msg string) {
        // Throw fatal error during parsing.
        panic(throw("parse", "%s at line %d", msg, sp.importLine))
}

func (sp *StreamParser)  warn(msg string) {
        // Display a parse warning associated with a line.
        if sp.importLine > 0 {
		complain("%s at line %d", msg, sp.importLine)
        } else {
		complain(msg)
        }
}

func (sp *StreamParser) gripe(msg string) {
        // Display or queue up an error message.
        if verbose < 2 {
		sp.warnings = append(sp.warnings, msg)
        } else {
		complain(msg)
        }
}

func (sp *StreamParser) read(n int) string {
	// Read possibly binary data
	cs := make([]byte, n)
	m, err := sp.fp.Read(cs)
	if err != nil {
		sp.error(fmt.Sprintf("in readline(): %v", err))
	} else if m < n {
		sp.error(fmt.Sprintf("short read in readline"))
	}
	sp.ccount += int64(n)
	sp.importLine = bytes.Count(cs, []byte{'\n'})
        return string(cs)	
}

func (sp *StreamParser) readline() string {
	// Read a newline-terminated string, returning "" at EOF
	var line []byte
        if len(sp.linebuffers) > 0 {
		line = []byte(sp.linebuffers[0])
		sp.linebuffers = sp.linebuffers[1:]
        } else {
		cs := make([]byte, 1)
		for {
			_, err := sp.fp.Read(cs)
			if err != nil {
				if err == io.EOF {
					line = []byte{}
					break
				} else {
					panic(throw("parse", "in readline(): %v", err))
				}
			}
			line = append(line, cs[0])
			if cs[0] == '\n' {
				break
			}
		}
        }
        sp.ccount += int64(len(line))
        sp.importLine++
        return string(line)
}

func (sp *StreamParser) tell() int64 {
        // Return the current read offset in the source stream.
	return sp.ccount
}

func (sp *StreamParser)  pushback(line string) {
        sp.ccount -= int64(len(line))
        sp.importLine--
        sp.linebuffers = append(sp.linebuffers, line)
    }

    // Helpers for import-stream files

func (sp *StreamParser) fiReadline() string {
        // Read a line, stashing comments as we go.
        for {
		line := sp.readline()
		if len(line) > 0 && strings.HasPrefix(line, "#") && !strings.HasPrefix(line, "#legacy-id") {
			sp.repo.addEvent(newPassthrough(sp.repo, line))
			if strings.HasPrefix(line, "#reposurgeon") {
				// Extension command generated by some exporter's
				// --reposurgeon mode.
				fields := strings.Fields(line)
				if fields[1] == "sourcetype" && len(fields) == 3 {
					sp.repo.hint(fields[2], "", true)
				}
			}
			continue
		} else {
			return line
		}
        }
}

func (sp *StreamParser) fiReadData(line string) (string, int64) {
        // Read a fast-import data section.
        if line == "" {
		line = sp.fiReadline()
        }
	var data string
	var start int64
        if strings.HasPrefix(line, "data <<") {
		delim := line[7:]
		data = ""
		start = sp.tell()
		for {
			dataline := sp.readline()
			if dataline == delim {
				break
			} else if dataline == "" {
				sp.error("EOF while reading blob")
			} else {
				data += dataline
			}
		}
        } else if strings.HasPrefix(line, "data") {
                count, err := strconv.Atoi(strings.TrimSpace(line[5:]))
		if err != nil{
			sp.error("bad count in data: " + line[5:])
		}
                start = sp.tell()
		buf := make([]byte, count)
		var n int
		n, err = sp.fp.Read(buf)
		if err != nil || count != n {
			sp.error("bad read in data")
		}
		data = string(buf)
        } else if strings.HasPrefix(line, "property") {
		line = line[9:]                    // Skip this token
		line = line[strings.Index(line, " "):]      // Skip the property name
		nextws := strings.Index(line, " ")
		count, err := strconv.Atoi(strings.TrimSpace(line[:nextws-1]))
		if err != nil{
			sp.error("bad count in property")
		}
		start = sp.tell()
		buf := make([]byte, count) 
		var n int
		n, err = sp.fp.Read(buf)
		if err != nil || n != count {
			sp.error("bad read in property")
		}
		data = line[nextws:] + string(buf)
        } else {
		sp.error("malformed data header")
        }
        line = sp.readline()
        if line != "\n" {
		sp.pushback(line) // Data commands optionally end with LF
        }
        return data, start
}

func (sp *StreamParser) fiParseFileop(fileop *FileOp) {
        // Read a fast-import fileop
        if fileop.ref[0] == ':' {
		return
        } else if fileop.ref == "inline" {
		data, _ := sp.fiReadData("")
		// FIXME: Python said data[0] here - probably a bug, test it.
		fileop.inline = data
        } else {
		sp.error("unknown content type in filemodify")
	}
}

// General helpers

func parseInt(s string) int {
	n, err := strconv.Atoi(s)
	if err != nil {
		panic(throw("parse", "malformed integer literal: %v", err))
	}
	return n		
}

// Helpers for Subversion dumpfiles

func sdBody(line string) string {
        // Parse the body from a Subversion header line
        return strings.TrimSpace(strings.SplitN(line, ":", 2)[1])
}

func (sp *StreamParser) sdRequireHeader(hdr string) string {
        // Consume a required header line
        line := sp.readline()
        sp.ccount += int64(len(line))
        if !strings.HasPrefix(line, hdr) {
		sp.error("required header missing: " + hdr)
        }
        return sdBody(line)
}

func (sp *StreamParser) sdRequireSpacer() {
        line := sp.readline()
        if strings.TrimSpace(line)!= "" {
		sp.error("found "+strconv.Quote(line)+" expecting blank line" )
        }
}

func (sp *StreamParser)  sdReadBlob(length int) string {
        // Read a Subversion file-content blob.
	buf := make([]byte, length+1)
        n, _ := sp.fp.Read(buf)
        if n != length + 1 || buf[length] != '\n' {
            sp.error("EOL not seen where expected, Content-Length incorrect")
        }
	content := string(buf[:length])
        sp.importLine += strings.Count(content, "\n") + 1
        sp.ccount += int64(len(content)) + 1
        return content
}

func (sp *StreamParser) sdReadProps(target string, checklength int) OrderedMap {
        // Parse a Subversion properties section, return as an OrderedMap.
        props := newOrderedMap()
        start := sp.ccount
        for sp.ccount - start < int64(checklength) {
		line := sp.readline()
		announce(debugSVNPARSE, "readprops, line %d: %r",
			sp.importLine, line)
		if strings.HasPrefix(line, "PROPS-END") {
			// This test should be !=, but I get random
			// off-by-ones from real dumpfiles - I don't
			// know why.
			if sp.ccount - start < int64(checklength) {
				sp.error(fmt.Sprintf("expected %d property chars, got %d",
					checklength, sp.ccount - start))

			}
			break
		} else if strings.TrimSpace(line) == "" {
			continue
		} else if line[0] == 'K' {
			payloadLength := func(s string) int {
				n, _ := strconv.Atoi(strings.Fields(s)[1])
				return n
			}
			key := sp.sdReadBlob(payloadLength(line))
			line := sp.readline()
			if line[0] != 'V' {
				sp.error("property value garbled")
			}
			value := sp.sdReadBlob(payloadLength(line))
			props.set(key, value)
			announce(debugSVNPARSE,
				"readprops: on %s, setting %s = %q",
				target, key, value)
		}
	}
        return props
}

	
func (sp *StreamParser) branchlist() []string  {
        //The branch list in deterministic order, most specific branches first.
	out := make([]string, 0)
	for key, _ := range sp.branches {
		out = append(out, key)
	}
	sort.Slice(out, func(i, j int) bool {
		if len(out[i]) > len(out[j]) {
			return true
		}
		return out[i] > out [j]
	})
        return out
}

func (sp *StreamParser) timeMark(label string) {
	sp.repo.timings = append(sp.repo.timings, TimeMark{label, time.Now()})
}

func (sp *StreamParser) parseSubversion(options stringSet, baton *Baton, filesize int64) {
	hashcopy := func(hash *[sha1.Size]byte, src string) {
		for i := 0; i < sha1.Size && i < len(src); i++ {
			hash[i] = src[i]
		}
	}
        trackSymlinks := newStringSet()
	for {
		line := sp.readline()
		if line == "" {
			break
		} else if strings.TrimSpace(line) == "" {
			continue
		} else if strings.HasPrefix(line, " # reposurgeon-read-options:") {
			payload := strings.Split(line, ":")[1]
			options = options.Union(newStringSet(strings.Fields(payload)...))
		} else if strings.HasPrefix(line, "UUID:") {
			sp.repo.uuid = sdBody(line)
		} else if strings.HasPrefix(line, "Revision-number: ") {
			// Begin Revision processing
			announce(debugSVNPARSE, "revision parsing, line %d: begins", sp.importLine)
			revision, rerr := strconv.Atoi(sdBody(line))
			if rerr != nil {
				panic(throw("parse", "ill-formed revision number: " + line))
			}
			plen := parseInt(sp.sdRequireHeader("Prop-content-length"))
			sp.sdRequireHeader("Content-length")
			sp.sdRequireSpacer()
			props := sp.sdReadProps("commit", plen)
			// Parsing of the revision header is done
			var node *NodeAction
			nodes := make([]NodeAction, 0)
			plen = -1
			tlen := -1
			// Node list parsing begins
			for {
				line = sp.readline()
				announce(debugSVNPARSE, "node list parsing, line %d: %q",
					sp.importLine, line)
				if len(line) == 0 {
					break
				} else if strings.TrimSpace(line) == "" {
					if node == nil {
						continue
					} else {
						if plen > -1 {
							node.props = sp.sdReadProps(node.path, plen)
							node.propchange = true
						}
						if tlen > -1 {
							start := sp.tell()
							// This is a
							// crock. It
							// is
							// justified
							// only by the
							// fact that
							// we get -1
							// back from
							// sp.tell()
							// only when
							// the parser
							// input is
							// coming from
							// an inferior
							// process
							// rather than
							// a file. In
							// this case
							// the start
							// offset can
							// be any
							// random
							// garbage,
							// because
							// we'll never
							// try to use
							// it for
							// seeking
							// blob
							// content.
							if start == -1 {
								start = 0
							}
							text := sp.sdReadBlob(tlen)
							node.blob = newBlob(sp.repo)
							node.blob.setContent(text, start)
							// Ugh - cope
							// with
							// strange
							// undocumented
							// Subversion
							// format for
							// storing
							// links.
							// Apparently
							// the dumper
							// puts "link
							// " in front
							// of the path
							// && the
							// loader (or
							// at least
							// git-svn)
							// removes it.
							// But the
							// link op is
							// on;y marked
							// with
							// property
							// svn:special
							// on
							// creation,
							// !on
							// modification.
							// So we have
							// to track
							// which paths
							// are
							// currently
							// symlinks,
							// && take off
							// that mark
							// when a path
							// is deleted
							// in case it
							// later gets
							// recreated
							// as a
							// non-sym
							// link.
							if strings.HasPrefix(text, "link ") {
								if node.props.has("svn:special") {
									trackSymlinks.Add(node.path)
								}
							if trackSymlinks.Contains(node.path)  {
									node.blob.setContent(
										text[5:], start+5)
								}
							}
						}
						node.revision = revision
						// If there are
						// property changes on
						// this node, stash
						// them so they will
						// be propagated
						// forward on later
						// nodes matching this
						// path but with no
						// property fields of
						// their own.
						if node.propchange {
							sp.propertyStash[node.path] = node.props
						} else if node.action == sdADD && node.fromPath != "" {
							for _, oldnode := range sp.revisions[node.fromRev].nodes {
								if oldnode.path == node.fromPath {
									sp.propertyStash[node.path] = oldnode.props
								}
							}
							//os.Stderr.write(fmt.Sprintf("Copy node %s:%s stashes %s\n", node.revision, node.path, sp.propertyStash[node.path]))
						}
						if node.action == sdDELETE {
							if _, ok := sp.propertyStash[node.path]; ok {
								delete(sp.propertyStash, node.path)
							}
						} else {
							// The forward propagation.
							node.props = sp.propertyStash[node.path]
						}
						// This guard filters
						// out the empty nodes
						// produced by format
						// 7 dumps.
						if !(node.action == sdCHANGE && len(node.props.keys) == 0 && node.blob == nil && node.fromRev == 0) {
							nodes = append(nodes, *node)
						}
						node = nil
					}
				} else if strings.HasPrefix(line, "Revision-number: ") {
					sp.pushback(line)
					break
				} else if strings.HasPrefix(line, "Node-path: ") {
					// Node processing begins
					// Normal case
					if node == nil {
						node = new(NodeAction)
					}
					node.path = intern(sdBody(line))
					plen = -1
					tlen = -1
				} else if strings.HasPrefix(line, "Node-kind: ") {
					// svndumpfilter sometimes emits output
					// with the node kind first
					if node == nil {
						node = new(NodeAction)
					}
					kind := sdBody(line)
					for i, v := range PathTypeValues {
						if v == kind {
							node.kind = i
						}
					}
					if node.kind == sdNONE {
						sp.error(fmt.Sprintf("unknown kind %s", kind))
					}
				} else if strings.HasPrefix(line, "Node-action: ") {
					if node == nil {
						node = new(NodeAction)
					}
					action := sdBody(line)
					for i, v := range ActionValues {
						if v == action {
							node.action = i
						}
					}
					if node.action == sdNONE {
						sp.error(fmt.Sprintf("unknown action %s", action))
					}
					if node.action == sdDELETE {
						if trackSymlinks.Contains(node.path) {
							trackSymlinks.Remove(node.path)
						}
					}
				} else if strings.HasPrefix(line, "Node-copyfrom-rev: ") {
					if node == nil {
						node = new(NodeAction)
					}
					node.fromRev = parseInt(sdBody(line))
				} else if strings.HasPrefix(line, "Node-copyfrom-path: ") {
					if node == nil {
						node = new(NodeAction)
					}
					node.fromPath = intern(sdBody(line))
				} else if strings.HasPrefix(line, "Text-copy-source-md5: ") {
					if node == nil {
						node = new(NodeAction)
					}
					hashcopy(&node.fromHash, sdBody(line))
				} else if strings.HasPrefix(line, "Text-content-md5: ") {
					hashcopy(&node.contentHash, sdBody(line))
				} else if strings.HasPrefix(line, "Text-content-sha1: ") {
					continue
				} else if strings.HasPrefix(line, "Text-content-length: ") {
					tlen = parseInt(sdBody(line))
				} else if strings.HasPrefix(line, "Prop-content-length: ") {
					plen = parseInt(sdBody(line))
				} else if strings.HasPrefix(line, "Content-length: ") {
					continue
				} else {
					announce(debugSVNPARSE, "node list parsing, line %d: uninterpreted line %q", sp.importLine, line)
					continue
				}
				// Node processing ends
			}
			// Node list parsing ends
			sp.revisions[revision] = *newRevisionRecord(nodes, props)
			sp.repo.legacyCount += 1
			announce(debugSVNPARSE, "revision parsing, line %d: ends",  sp.importLine)
			// End Revision processing
			baton.readProgress(sp.ccount, filesize)
		}
	}
}

var dollarId = regexp.MustCompile(`\$Id *:([^$]+)\$`)
var dollarRevision = regexp.MustCompile(`\$Revision *: *([^$]*)\$`)

func (sp *StreamParser) parseFastImport(options stringSet, baton *Baton, filesize int64) {
	// Beginning of fast-import stream parsing
	commitcount := 0
	for {
		line := sp.fiReadline()
		if line == "" {
			break
		} else if strings.TrimSpace(line) == "" {
			continue
		} else if strings.HasPrefix(line, "blob") {
			blob := newBlob(sp.repo)
			line = sp.fiReadline()
			if strings.HasPrefix(line, "mark") {
				sp.repo.markseq += 1
				blob.setMark(strings.TrimSpace(line[5:]))
				blobcontent, blobstart := sp.fiReadData("")
				// Parse CVS && Subversion $-headers
				// There'd better not be more than one of these.
				for _, m := range dollarId.FindAllStringSubmatch(blobcontent, 0) {
					fields := strings.Fields(m[0])
					if len(fields) < 2 {
						sp.gripe(fmt.Sprintf("malformed $-cookie '%s'", m[0]))
					} else {
						// Save file basename && CVS version
						if strings.HasSuffix(fields[1], ",v") {
							// CVS revision
							rid := fields[1]
							blob.cookie = [2]string{rid[:len(rid)-2], fields[2]}
							sp.repo.hint("$Id$", "cvs", false)
						} else {
							// Subversion revision
							blob.cookie = [2]string{fields[1], ""}
							if sp.repo.hint("$Id$", "svn", false) {
								announce(debugSHOUT, "$Id$ header hints at svn.")
							}
						}
					}
				}
				for _, m := range dollarRevision.FindAllStringSubmatch(blobcontent, 0) {
					rev := strings.TrimSpace(m[1])
					if strings.Index(rev, ".") == -1 {
						// Subversion revision
						blob.cookie = [2]string{rev, ""}
						if sp.repo.hint("$Revision$", "svn", false) {
							announce(debugSHOUT, "$Revision$ header hints at svn.")
						}
					}
				}
				blob.setContent(blobcontent, blobstart)
			} else {
				sp.error("missing mark after blob")
			}
			sp.repo.addEvent(blob)
			baton.twirl("")
		} else if strings.HasPrefix(line, "data") {
			sp.error("unexpected data object")
		} else if strings.HasPrefix(line, "commit") {
			baton.twirl("")
			commitbegin := sp.importLine
			commit := newCommit(sp.repo)
			commit.setBranch(strings.Fields(line)[1])
			for {
				line = sp.fiReadline()
				if line == "" {
					break
				} else if strings.HasPrefix(line, "#legacy-id") {
					// reposurgeon extension, expected to
					// be immediately after "commit" if present
					commit.legacyID = strings.Fields(line)[1]
					if sp.repo.vcs != nil {
						sp.repo.legacyMap[strings.ToUpper(sp.repo.vcs.name) + ":" + commit.legacyID] = commit
					} else {
						sp.repo.legacyMap[commit.legacyID] = commit
					}
				} else if strings.HasPrefix(line, "mark") {
					sp.repo.markseq += 1
					commit.setMark(strings.TrimSpace(line[5:]))
				} else if strings.HasPrefix(line, "author") {
					attrib := *newAttribution(line[7:])
					commit.authors = append(commit.authors, attrib)
					sp.repo.tzmap[attrib.email] = attrib.date.timestamp.Location()
				} else if strings.HasPrefix(line, "committer") {
					attrib := *newAttribution(line[10:])
					commit.committer = attrib
					sp.repo.tzmap[attrib.email] = attrib.date.timestamp.Location()
				} else if strings.HasPrefix(line, "property") {
					commit.properties = newOrderedMap()
					fields := strings.Split(line, " ")
					if len(fields) < 3 {
						sp.error("malformed property line")
					} else if len(fields) == 3 {
						commit.properties.set(fields[1], "true")
					} else {
						name := fields[1]
						length := parseInt(fields[2])
						value := strings.Join(fields[3:], " ")
						if len(value) < length {
							value += sp.read(length-len(value))
							if sp.read(1) != "\n" {
								sp.error("trailing junk on property value")
							}
						} else if len(value) == length + 1 {
							value = value[:len(value)-1] // Trim '\n'
						} else {
							value += sp.read(length - len(value))
							if sp.read(1) != "\n" {
								sp.error("newline not found where expected")
							}
						}
						commit.properties.set(name, value)
						// Generated by cvs-fast-export
						if name == "cvs-revisions" {
							if !sp.repo.stronghint {
								announce(debugSHOUT, "cvs_revisions property hints at CVS.")
							}
							sp.repo.hint("cvs", "", true)
							for _, line := range strings.Split(value, "\n") {
								if line != "" {
									sp.repo.legacyMap["CVS:"+line] = commit
								}
							}
						}
					}
				} else if strings.HasPrefix(line, "data") {
					d, _ := sp.fiReadData(line)
					commit.comment = d
					if haveGlobalOption("canonicalize") {
						commit.comment = strings.Replace(strings.TrimSpace(commit.comment), "\r\n", "\n", -1) + "\n"
					}
				} else if strings.HasPrefix(line, "from") || strings.HasPrefix(line, "merge") {
					mark := strings.Fields(line)[1]
					if isCallout(mark) {
						commit.addCallout(mark)
					} else {
						commit.addParentByMark(mark)
					}
				} else if line[0]=='C' || line[0]=='D' || line[0]=='R' {
					commit.appendOperation(*newFileOp(sp.repo).parse(line))
				} else if line == "deleteall\n" {
					commit.appendOperation(*newFileOp(sp.repo).parse(deleteall))
				} else if line[0] == opM[0] {
					fileop := newFileOp(sp.repo).parse(line)
					if fileop.ref != "inline" {
						ref := sp.repo.markToEvent(fileop.ref)
						if ref != nil {
							ref.(*Blob).addalias(fileop.path)
						} else {
							// Crap out on
							// anything
							// but a
							// submodule
							// link.
							if fileop.mode != "160000" {
								sp.error(fmt.Sprintf("ref %s could not be resolved", fileop.ref))
							}
						}
					}
					commit.appendOperation(*fileop)
					if fileop.mode == "160000" {
						// This is a submodule
						// link.  The ref
						// field is a SHA1
						// hash && the path is
						// an external
						// reference name.
						// Don't try to
						// collect data, just
						// pass it through.
						sp.warn("submodule link")
					} else {
						// 100644, 100755, 120000.
						sp.fiParseFileop(fileop)
					}
				} else if line[0] == opN[0] {
					fileop := newFileOp(sp.repo).parse(line)
					commit.appendOperation(*fileop)
					sp.fiParseFileop(fileop)
					sp.repo.inlines += 1
				} else if strings.TrimSpace(line) == "" {
					// This handles slightly broken
					// exporters like the bzr-fast-export
					// one that may tack an extra LF onto
					// the end of data objects.  With it,
					// we don't drop out of the
					// commit-processing loop until we see
					// a *nonblank* line that doesn't match
					// a commit subpart.
					continue
				} else {
					// Dodgy bzr autodetection hook...
					if sp.repo.vcs == nil {
						if commit.properties.has("branch-nick") {
							sp.repo.hint("bzr", "", true)
						}
					}
					sp.pushback(line)
					break
				}
			}
			if !(commit.mark != "" && commit.committer.fullname != "") {
				sp.importLine = commitbegin
				sp.error("missing required fields in commit")
			}
			if commit.mark == "" {
				sp.warn("unmarked commit")
			}
			sp.repo.addEvent(commit)
			commitcount += 1
			baton.twirl("")
		} else if strings.HasPrefix(line, "reset") {
			reset := newReset(sp.repo, "", "", nil)
			reset.ref = strings.TrimSpace(line[6:])
			line = sp.fiReadline()
			if strings.HasPrefix(line, "from") {
				committish := strings.TrimSpace(line[5:])
				reset.remember(sp.repo, committish, nil)
			} else {
				sp.pushback(line)
			}
			sp.repo.addEvent(reset)
			baton.twirl("")
		} else if strings.HasPrefix(line, "tag") {
			var tagger *Attribution
			tagname := strings.TrimSpace(line[4:])
			line = sp.fiReadline()
			legacyID := ""
			if strings.HasPrefix(line, "#legacy-id ") {
				// reposurgeon extension, expected to
				// be immediately after "tag" line if
				// present
				legacyID = strings.Fields(line)[1]
				line = sp.fiReadline()
			}
			var referent string
			if strings.HasPrefix(line, "from") {
				referent = strings.TrimSpace(line[5:])
			} else {
				sp.error("missing from after tag")
			}
			line = sp.fiReadline()
			if strings.HasPrefix(line, "tagger") {
				tagger = newAttribution(line[7:])
			} else {
				sp.warn("missing tagger after from in tag")
				sp.pushback(line)
			}
			d, _ := sp.fiReadData("")
			tag := newTag(sp.repo, tagname, referent, nil, tagger, d)
			tag.legacyID = legacyID
			sp.repo.addEvent(tag)
		} else {
			// Simply pass through any line we don't understand.
			sp.repo.addEvent(newPassthrough(sp.repo, line))
		}
		baton.readProgress(sp.ccount, filesize)
	}
}


//
// The main event
//
// FIXME: When we have signal notifications, fire the defer on signal.

func (sp *StreamParser) fastImport(fp io.Reader,
	options stringSet, progress bool, source string) {
	// Initialize the repo from a fast-import stream or Subversion dump.
	sp.repo.makedir()
	sp.timeMark("start")
	var filesize int64 = -1
	sp.fp = fp
	fileobj, ok := fp.(*os.File)
	// Optimization: if we're reading from a plain stream dump,
	// no need to clone all the blobs.
	if ok && isfile(fileobj.Name()) {
		sp.repo.seekstream = fileobj
		filesize = getsize(sp.repo.seekstream.Name())
	}
        pwd, err := os.Getwd()
	if err != nil {
		sp.error(fmt.Sprintf("Could not get working directory: %v", err))
	}
	if source == "" && sp.repo.seekstream != nil {
		source, err = filepath.Rel(pwd, sp.repo.seekstream.Name())
		if err != nil {
			sp.error(fmt.Sprintf("Could not compute relative path: %v", err))
		}
	}
	baton := newBaton(fmt.Sprintf("reposurgeon: from %s", source), "", progress)
	commitcount := 0
	sp.repo.legacyCount = 0
	// First, determine the input type
	line := sp.readline()
	if strings.HasPrefix(line, "SVN-fs-dump-format-version: ") {
		body := sdBody(line)
		if body != "1" && body !="2" {
			sp.error("unsupported dump format version " + body)
		}
		// Beginning of Subversion dump parsing
		sp.parseSubversion(options, baton, filesize)
		// End of Subversion dump parsing
		sp.timeMark("parsing")
		sp.svnProcess(options, baton)
		elapsed := time.Since(baton.starttime)
		baton.twirl(fmt.Sprintf("...%d svn revisions (%d/s)",
			sp.repo.legacyCount,
			int(sp.repo.legacyCount/int(elapsed))))
	} else {
		sp.pushback(line)
		sp.parseFastImport(options, baton, filesize)
		sp.timeMark("parsing")
		if sp.repo.stronghint {
			baton.twirl(fmt.Sprintf("%d %s commits", commitcount, sp.repo.vcs.name))
		} else {
			baton.twirl(fmt.Sprintf("%d commits", commitcount))
		}
	}
	baton.exit("")
	baton = nil
	sp.importLine = 0
	if len(sp.repo.events) == 0 {
		sp.error("ignoring empty repository")
	}
	for _, warning := range sp.warnings {
		complain(warning)
	}

	// FIXME: When we have signal notifications, fire the defer on signal.
	defer func() {
		if e := catch("parse", recover()); e != nil {
			if baton != nil {
				baton.exit("interrupted by error")
			}
			complain(e.message)
			nuke(sp.repo.subdir(""), fmt.Sprintf("import interrupted, removing %s", sp.repo.subdir("")))
		}
		if sp.repo.seekstream != nil {
			sp.repo.seekstream.Close()
		}
	}()
}
	
//
// The rendezvous between parsing and object building for import
// streams is pretty trivial and best done inline in the parser
// because reposurgeon's internal structures are designed to match
// those entities. For Subversion dumpfiles, on the other hand,
// there's a fair bit of impedance-matching required.  That happens
// in the following functions.
//
func nodePermissions(node NodeAction) string {
    // Fileop permissions from node properties
	if node.props.has("svn:executable") {
		return "100755"
	} else if node.props.has("svn:special") {
		// Map to git symlink, which behaves the same way.
		// Blob contents is the path the link should resolve to.
		return "120000"
    }
    return "100644"
}

func (sp *StreamParser) isBranch(pathname string) bool {
	_, ok := sp.branches[pathname]
	return ok
}


// Path separator as found in Subversion dump files. Isolated because
// it might be "\" on OSes not to be mentioned in polite company. 
const svnSep = "/"

func (sp *StreamParser) svnProcess(options stringSet, baton *Baton) {
        // Subversion actions to import-stream commits.
        sp.repo.addEvent(newPassthrough(sp.repo, "#reposurgeon sourcetype svn\n"))
        announce(debugEXTRACT, "Pass 0: dead-branch deletion")
        if !options.Contains("--preserve") {
		// Identify Subversion tag/branch directories with
		// tipdeletes && nuke them.  Happens well before tip
		// deletes are tagified, the behavior if --preserve is on.
		// This pass doesn't touch trunk - any tipdelete on trunk
		// we presume to be some kind of operator error that needs
		// to show up under lint && be manually corrected
		deadbranches := newStringSet()
		for i, _ := range sp.revisions {
			backup := len(sp.revisions) - i
			for i, _ := range sp.revisions[backup].nodes {
				node := &sp.revisions[backup].nodes[i]
				if !strings.HasPrefix(node.path, "tags") && !strings.HasPrefix(node.path, "branches") {
					continue
				}
				if node.action == sdDELETE && node.kind == sdDIR {
					deadbranches = append(deadbranches, node.path)
					announce(debugSHOUT, fmt.Sprintf("r%d~%s nuked by tip delete", backup, node.path))
				}
				if deadbranches.Contains(node.path) {
					node.action = sdNUKE
				}
				for _, deadwood := range deadbranches {
					if strings.HasPrefix(node.path, deadwood + "/") {
						node.action = sdNUKE
						break
					}
				}
			}
		}
		// Actual deletion logic.  This does no new allocation;
		// trick from https://github.com/golang/go/wiki/SliceTricks
		for revision, record := range sp.revisions {
			newnodes := record.nodes[:0]
			for _, node := range record.nodes {
				if node.action != sdNUKE {
					newnodes = append(newnodes, node)
				}
			}
			sp.revisions[revision].nodes = newnodes 
		}
        }
	// no-preserve ends begins here

        // Find all copy sources && compute the set of branches
        announce(debugEXTRACT, "Pass 1: compute copy sets and branches")
        nobranch := options.Contains("--nobranch")
        copynodes := make([]*NodeAction, 0)
        for i, record := range sp.revisions {
		for j, node := range record.nodes {
			if node.fromPath != "" {
				copynodes = append(copynodes, &sp.revisions[i].nodes[j])
				announce(debugEXTRACT, fmt.Sprintf("copynode at %s", node))
			}
			np := node.path + svnSep
			if node.action == sdADD && node.kind == sdDIR &&  !sp.isBranch(np) && !nobranch {
				for _, trial := range globalOption("svn_branchify") {
					if strings.Index(trial, "*") != -1 && trial == node.path {
						sp.branches[np] = nil
					} else if strings.HasSuffix(trial, svnSep + "*") && filepath.Dir(trial) == filepath.Dir(node.path) && !globalOption("svn_branchify").Contains(np + "*") {
						sp.branches[np] = nil
					} else if trial == "*" && !globalOption("svn_branchify").Contains(np + "*") && strings.Count(node.path, svnSep) < 1 {
						sp.branches[np] = nil
					}
				}
				if _, ok := sp.branches[np]; ok && debugEnable(debugTOPOLOGY) {
					announce(debugSHOUT, "%s recognized as a branch", np)
				}
			}
		}
		// Per-commit spinner disabled because this pass is fast
		//baton.twirl("")
        }
        sort.Slice(copynodes, func(i int, j int) bool {
		return copynodes[i].fromRev < copynodes[j].fromRev
	})

	timeit := func (tag string) {
		sp.timeMark("tag")
		if haveGlobalOption("bigprofile") {
			e := len(sp.repo.timings)-1
			baton.twirl(fmt.Sprintf("%s:%v...", tag, sp.repo.timings[e].stamp.Sub(sp.repo.timings[e-1].stamp)))
		} else {
			baton.twirl("")
		}
	}

        timeit("copynodes")

	/* FIXME: Most of this function is not yet translated.  See near EOF. */
}

// Generic repository-manipulation code begins here

// Event is an operation in a repository's time sequence of modifications.
type Event interface {
	idMe() string
	getMark() string
	String() string
}

// CommitLike is a Commit or Callout
type CommitLike interface {
	idMe() string
	getMark() string
	callout() string
	String() string
}

// Contributor - associate a username with a DVCS-style ID and timezone
type Contributor struct {
	local     string
	fullname string
	email    string
	timezone string
}

// ContributorID identifies a contributor for purposes of aliasing
type ContributorID struct {
	fullname     string
	email        string
}

func (c Contributor) isEmpty() bool {
	return c.local == ""
}

// Time mark for profiling
type TimeMark struct {
	label string
	stamp time.Time
}

// Repository is the entire state of a version-control repository
type Repository struct {
	name string
        readtime time.Time
        vcs *VCS
        stronghint bool
        hintlist []Hint
        sourcedir string
        seekstream *os.File
        events []Event    // A list of the events encountered, in order
        //_commits = None
        _markToIndex map[string]int
        _eventByMark map[string]Event
        _namecache map[string][]int
        preserveSet stringSet
        caseCoverage stringSet
        basedir string
        uuid string
        write_legacy bool
        //dollarMap = None        // From dollar cookies in files
        legacyMap map[string]*Commit    // From anything that doesn't survive rebuild
        legacyCount int
        timings []TimeMark
        assignments map[string]orderedIntSet
        inlines int
        //uniqueness = None
        markseq int
        authormap map[string]Contributor
        tzmap map[string]*time.Location	// most recent email address to timezone
        aliases map[ContributorID]ContributorID
	// Write control - set, if required, before each dump
	preferred *VCS			// overrides vcs slot for writes
	realized map[string]bool	// clear and remake this before each dump
	writeOptions stringSet		// options requested on this write
	internals stringSet		// export code computes this itself
}

func newRepository(name string) *Repository {
	repo := new(Repository)
	repo.name = name
	repo.readtime = time.Now()
	repo.hintlist = make([]Hint, 0)
	repo.preserveSet = newStringSet()
	repo.caseCoverage = newStringSet()
        repo.legacyMap = make(map[string]*Commit)
	repo.assignments = make(map[string]orderedIntSet)
	repo.timings = make([]TimeMark, 0)
	repo.authormap = make(map[string]Contributor)
	repo.tzmap = make(map[string]*time.Location)
	repo.aliases = make(map[ContributorID]ContributorID)
	d, err := os.Getwd()
	if err != nil {
		panic(throw("command", "During repository creation: %v", err))
	}
	repo.basedir = d
	return repo
}

func (repo *Repository) subdir(name string) string {
        if name == "" {
		name = repo.name
        }
	head := fmt.Sprintf("%s/.rs%d", repo.basedir, os.Getpid())
	if name != "" {
		head += "-" + name
        }
	return filepath.FromSlash(head)
}

// cleanup releases disk storage associated with this repo
func (repo *Repository) cleanup() {
        nuke(repo.subdir(""),
		fmt.Sprintf("reposurgeon: cleaning up %s", repo.subdir("")))
}

// markToEvent finds an object by mark
func (repo *Repository) markToEvent(mark string) Event {
        if repo._eventByMark == nil {
		repo._eventByMark = make(map[string]Event)
		for _, event := range repo.events {
			key := event.getMark()
			if key != "" {
				repo._eventByMark[key] = event
			}
		}
	}
	d, ok := repo._eventByMark[mark]
	if ok {
		return d
	}
	return nil
}

// index returns the index of the specified object in the main even list
func (repo *Repository) index(obj Event) int {
	for ind, event := range repo.events {
                if event == obj {
			return ind
		}
	}
	panic(throw("Internal error: object not matched in repository %s", repo.name))
}

// find gets an object index by mark
func (repo *Repository) find(mark string) int {
        if repo._markToIndex == nil {
		repo._markToIndex = make(map[string]int)
		for ind, event := range repo.events {
			mark = event.getMark()
			if mark != "" {
				repo._markToIndex[mark] = ind+1
			}
		}
	}
	// return -1 if not found
	// Python version returned None
        return repo._markToIndex[mark]-1
}

func (repo *Repository) newmark() string {
        repo.markseq++
        mark := ":" + fmt.Sprintf("%d", repo.markseq)
        return mark
}

func (repo *Repository) makedir() {
	target := repo.subdir("")
	announce(debugSHUFFLE, "repository fast import creates " + target)
	if _, err1 := os.Stat(target); os.IsNotExist(err1) {
                err2 := os.Mkdir(target, userReadWriteMode)
		if err2 != nil {
			panic("Can't create repository directory")
		}
	} else if err1 != nil {
		panic(fmt.Errorf("Can't stat %s: %v", target, err1))
	}
}

type Hint struct {
	cookie string
	vcs string
}

func (repo *Repository) hint(clue1 string, clue2 string, strong bool) bool {
        // Hint what the source of this repository might be.
	newhint := false
	for _, item := range repo.hintlist {
		if item.cookie == clue1 && item.vcs == clue2 {
			newhint = false
			break
		}
	}
        if newhint && repo.stronghint && strong {
		announce(debugSHOUT, "new hint %s conficts with old %s",
			clue1, repo.hintlist[len(repo.hintlist)-1])
            return false
        }
        if !repo.stronghint {
                repo.vcs = findVCS(clue2)
	}
	if newhint {
		repo.hintlist = append(repo.hintlist, Hint{clue1, clue2})
	}
        notify := newhint && !repo.stronghint
        repo.stronghint = repo.stronghint || strong
        return notify
}
	
func (repo *Repository) size() int {
	// Return the size of this import stream, for statistics display.
	var sz int
	for _, e := range repo.events {
		sz += len(e.String())
	}
	return sz
}


func (repo *Repository) branchset() stringSet {
	// branchset returns a set of all branchnames appearing in this repo.
        branches := newStringSet()
        for _, e := range repo.events {
		switch e.(type) {
		case *Reset:
			if e.(*Reset).committish != "" {
				branches.Add(e.(*Reset).ref)
			}
		case *Commit:
			branches.Add(e.(*Commit).branch)
		}
	}
	return branches
}

func (repo *Repository) branchmap() map[string]string {
	// Return a map of branchnames to terminal marks in this repo.
	brmap := make(map[string]string)
	for _, e := range repo.events {
		switch e.(type) {
		case *Reset:
			if e.(*Reset).committish == "" {
				delete(brmap, e.(*Reset).ref)
			} else {
				brmap[e.(*Reset).ref] = e.(*Reset).committish
			}
		case *Commit:
			brmap[e.(*Commit).branch] = e.(*Commit).mark
		}
	}
	return brmap
}

func (repo *Repository) all() []int {
        // Return a set that selects the entire repository.
	s := make([]int, len(repo.events))
        for i, _ := range repo.events {
		s[i] = i
	}
	return s
}

func (repo *Repository) __buildNamecache() {
	// Avoid repeated O(n**2) lookups.
	repo._namecache = make(map[string][]int) 
	commitcount := 0
	for i, event := range repo.events {
		switch event.(type) {
		case *Commit:
			commitcount += 1
			repo._namecache[fmt.Sprintf("#%d", commitcount)] = []int{i}
			commit := event.(*Commit)
			legacyID := commit.legacyID
			if legacyID != "" {
				repo._namecache[legacyID] = []int{i}
			}
			var key string
			if len(commit.authors) > 0 {
				key = commit.authors[0].actionStamp()
				if _, ok := repo._namecache[key]; !ok {
					repo._namecache[key] = []int{i}
				} else {
					repo._namecache[key] = append(repo._namecache[key], i)
				}
			}
			key = commit.committer.actionStamp()
			if _, ok := repo._namecache[key]; !ok {
				repo._namecache[key] = []int{i}
			} else{
				repo._namecache[key] = append(repo._namecache[key], i)
			}
		case *Tag:
			repo._namecache[event.(*Tag).name] = []int{i}
		case *Reset:
			repo._namecache["reset@" + filepath.Base(event.(*Reset).ref)] = []int{i}
		}
	}
}

func (repo *Repository) invalidateNamecache() {
    repo._namecache = nil
}

// FIXME: Needs more unit tests, can't do yet withot assignment logic 
func (repo *Repository) named(ref string) orderedIntSet {
        // Resolve named reference in the context of this repository.
        selection := newOrderedIntSet()
        // For matches that require iterating across the entire event
        // sequence, building an entire name lookup table is !much
        // more expensive in time than doing a single lookup. Avoid
        // lots of O(n**2) searches by building a lookup cache, at the
        // expense of increased working set for the hash table.
        lookup, ok := repo.assignments[ref]
        if ok {
		return lookup
        }
        if repo._namecache == nil {
		repo.__buildNamecache()
        }
        if v, ok := repo._namecache[ref]; ok {
		return v
        }
        // No hit in the name cache or assignments? Then search branches.
        for _, symbol := range repo.branchset() {
		if ref == branchbase(symbol) {
			loc := -1
			// Find the last commit with this branchname
			for i, event := range repo.events {
				switch event.(type) {
				case *Commit:
					if event.(*Commit).branch == symbol {
						loc = i
					}
				}
			}
			if loc == -1 {
				panic(throw("command", "branch name %s points to hyperspace", symbol))
				return nil
			} else {
				return newOrderedIntSet(loc)
			}
                }
	}
        // Might be a date or action stamp (though action stamps should
        // be in the name cache already).  First, peel off an optional
	// ordinal suffix.
	var ordinal int = -1
	stamp := ref
	m := regexp.MustCompile("#[0-9]+$").Find([]byte(ref))
	if m != nil {
		n, _ := strconv.Atoi(string(m[1:]))
		ordinal = n
		stamp = ref[:len(ref)- len(m)]
	}
	// Now look for action stamp or date
	dateEnd := len(stamp)
	bang := strings.Index(stamp, "!")
	if bang >= 0 {
		dateEnd = min(bang, dateEnd)
	}
	datestr := ref[:dateEnd]
	date, err2 := newDate(datestr)
	var datematch func(u Date) bool 
	if err2 == nil {
		datematch = func(u Date) bool {
			return u.timestamp.Equal(date.timestamp)
		}
	} else {
		daymark, err3 := time.Parse("2006-01-02", datestr)
		if err3 != nil {
			datematch = func(u Date) bool {
				d := daymark.Sub(u.timestamp).Hours()
				return d < -24 || d > 24
			}
		} else {
			complain("unparseable date in " + ref)
			return nil
		}
	}
	emailID := ""
	if err2 == nil && bang > -1 {
		emailID = ref[bang+1:]
	}
	matches := newOrderedIntSet()
	if datematch !=  nil {
		for ei, event := range repo.events {
			switch event.(type) {
			case *Commit:
				commit := event.(*Commit)
				if !datematch(commit.committer.date) {
					continue
				}
				// FIXME: Recognize aliases here
				if commit.committer.email != emailID {
					continue
				} else {
					matches.Add(ei)
				}
			case *Tag:
				tag := event.(*Tag)
				// FIXME: Recognize aliases here
				if !datematch(tag.tagger.date) {
					continue
				} else if tag.tagger.email != emailID {
					continue
				} else {
					matches = append(matches, ei)
				}
			}
		}
		if len(matches) < 1 {
			complain("no events match %s", ref)
			return nil
		} else if len(matches) > 1 {
			if ordinal != -1 && ordinal <= len(matches) {
				selection.Add(matches[ordinal-1])
			} else {
				selection = selection.Union(matches)
			}
		} else {
			selection.Add(matches[0])
		}
		if len(selection) > 0 {
			return selection
		}
	}
	// More named-reference formats can go here.
	// Otherwise, return nil to signal invalid selection.
	return nil
}

func (repo *Repository) invalidateObjectMap() {
    // Force an object-map rebuild on the next lookup.
    repo._eventByMark = nil
}

func (repo *Repository) readAuthorMap(selection orderedIntSet, fp io.Reader) error {
	// Read an author-mapping file and apply it to the repo.
	scanner := bufio.NewScanner(fp)
	var principal Contributor
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line  == "" ||  strings.HasPrefix(line, "#") {
			continue
		}
		if strings.Index(line, "=") > -1 {
			fields := strings.Split(line, "=")
			local := strings.TrimSpace(fields[0])
			netwide := strings.TrimSpace(fields[1])
			name, mail, timezone, err := parseAttributionLine(netwide)
			if err != nil {
				return fmt.Errorf("in readAuthorMap: %v", err)
			}
			if mail == "" {
				return fmt.Errorf("can't recognize address in '%s'", netwide)
			}
			if timezone != "" {
				loc, err2 := time.LoadLocation(timezone)
				if err2 != nil {
					loc, err2 = locationFromZoneOffset(timezone)
					if err2 != nil {
						return fmt.Errorf("in readAuthorMap entry lookup: %v", err2)
					}
				}
				repo.tzmap[mail] = loc
			}
			key := strings.ToLower(local)
			principal = Contributor{local,name,mail,timezone}
			repo.authormap[key] = principal
		}
		// Process aliases gathered from Changelog entries
		if line[0] == '+' {
			if principal.isEmpty() {
				return fmt.Errorf("alias entry before any principal")
			}
			line = strings.TrimSpace(line[1:])
			aname, aemail, atimezone, aerr := parseAttributionLine(line)
			if aerr != nil {
				return fmt.Errorf("bad contributor alias: %v", aerr)
			}
			repo.aliases[ContributorID{aname, aemail}] = ContributorID{principal.fullname, principal.email}
			if atimezone != "" {
				loc, err2 := time.LoadLocation(atimezone)
				if err2 != nil {
					loc, err2 = locationFromZoneOffset(atimezone)
					if err2 != nil {
						return fmt.Errorf("in readAuthorMap alias lookup: %v", err2)
					}
				}
				repo.tzmap[aemail] = loc
			}
		}
	}

	for _, ei := range selection {
		event := repo.events[ei]
		switch event.(type) {
		case *Commit:
			event.(*Commit).committer.remap(repo.authormap)
			for _, author := range event.(*Commit).authors {
				author.remap(repo.authormap)
			}
		case *Tag:
			event.(*Tag).tagger.remap(repo.authormap)
		}
	}
	// Email addresses have changed.
	// Force rebuild of action-stamp mapping on next lookup
	repo.invalidateNamecache()

	return nil
}

/*

func writeAuthorMap(self, selection, fp):
        "List the identifiers we need."
        contributors = {}
        for ei in selection:
            event = repo.events[ei]
            if isinstance(event, Commit):
                contributors[event.committer.userid()] = event.committer.who()
                for author in event.authors:
                    contributors[author.userid()] = author.who()
            else if isinstance(event, Tag):
                contributors[event.tagger.userid()] = event.tagger.who()
        for (userid, cid) in contributors.items():
            fp.write("%s = %s\n" % (userid, cid))
    func read_legacymap(fp):
        "Read a legacy-references dump and initialize the repo's legacy map."
        commitMap = {}
        for event in self.commits():
            key = (event.committer.date.timestamp, event.committer.email)
            if key not in commitMap:
                commitMap[key] = []
            commitMap[key].append(event)
        try:
            matched = unmatched = 0
            for line in fp:
                (legacy, stamp) = line.split()
                (timefield, person) = stamp.split('!')
                if ':' in person:
                    (person, seq) = person.split(':')
                    seq = int(seq) - 1
                else:
                    seq = 0
                assert legacy && timefield && person
                when_who = (Date(timefield).timestamp, person)
                if when_who in commitMap:
                    self.legacyMap[legacy] = commitMap[when_who][seq]
                    if legacy.startswith("SVN:"):
                        commitMap[when_who][seq].legacyID = legacy[4:]
                    matched += 1
                else:
                    unmatched += 1
            if verbose >= 1:
                announce(debugSHOUT, "%d matched, %d unmatched, %d total"\
                         % (matched, unmatched, matched+unmatched))
            del commitMap
        except ValueError:
            raise Recoverable("bad syntax in legacy map.")
    func write_legacymap(self, fp):
        "Dump legacy references."
        for cookie, commit in sorted(
                self.legacyMap.items(),
                key=lambda f: (f[1].committer.date.timestamp, f[0])):
            if "SVN" in cookie and StreamParser.SplitSep in cookie:
                serial = ':' + cookie.split(StreamParser.SplitSep)[1]
            else:
                serial = ''
            # The markToEvent test is needed in case this repo is an expunge
            # fragment with a copied legacy map.  It's a simple substitute
            # for partitioning the map at expunge time.
            if self.markToEvent(commit.mark) && commit.legacyID:
                fp.write("%s\t%s!%s%s\n" % (cookie,
                                           commit.committer.date.rfc3339(),
                                           commit.committer.email,
                                           serial))
    func tagify(self, commit, name, target, legend="", delete=true):
        "Turn a commit into a tag."
        if debugEnable(debugEXTRACT):
            commit_id = commit.mark
            if commit.legacyID:
                commit_id += " <%s>" % commit.legacyID
            announce(debugSHOUT, "tagifying: %s -> %s" % (commit_id, name))
        if commit.operations():
            raise Fatal("Attempting to tagify a commit with fileops.")
        if not commit.comment:
            pref = ""
        else:
            pref = commit.comment
            if legend or not pref.endswith("\n"):
                pref += "\n"
        tag = Tag(commit.repo,
                  name=name,
                  target=target,
                  tagger=commit.committer,
                  comment=pref + legend)
        tag.legacyID = commit.legacyID
        #self.addEvent(tag)
        if delete: commit.delete(["--tagback"])
    func tagify_empty(self, commits = None,
                           tipdeletes = false,
                           tagify_merges = false,
                           canonicalize = true,
                           name_func = lambda _: None,
                           legend_func = lambda _: "",
                           create_tags = true,
                           gripe = complain
                          ):
        """Turn into tags commits without (meaningful) fileops.
            Arguments: * commits:       None, or an iterable of event indices
                                        tagify_empty() ignores non-commits
                       * tipdeletes:    whether tipdeletes should be tagified
                       * canonicalize:  whether to canonicalize fileops first
                       * name_func:     custom function for choosing the tag
                                        name; if it returns a false value like
                                        None, a default scheme is used
                       * legend_func:   custom function for choosing the legend
                                        of a tag; no fallback is provided. By
                                        default it always returns "".
                       * create_tags    whether to create tags."""
        # Default scheme for tag names
        func default_name(commit):
            if commit.operations():
                branch = commit.branch
                if branch[-1] == svnSep: branch = branch[:-1]
                return "tipdelete-" + branchbase(branch)
            if commit.legacyID:
                return "emptycommit-" + commit.legacyID
            else if commit.mark:
                return "emptycommit-mark" + commit.mark[1:]
            else:
                return "emptycommit-index" + commit.index()
        # Use a separate loop because delete() invalidates manifests.
        if canonicalize:
            for _, commit in self.iterevents(commits, types=Commit):
                commit.canonicalize()
        # Tagify commits without fileops
        usednames = {e.name for e in self.events if isinstance(e, Tag)}
        if tipdeletes:
            is_tipdelete = lambda c: c.alldeletes(killset={FileOp.deleteall}) \
                                     && not c.hasChildren()
        else:
            is_tipdelete = lambda _: false
        deletia = []
        for index, commit in self.iterevents(commits, types=Commit):
            #os.Stdout.write("Examining: %s (%s), %s %s\n" % (commit.mark, commit.comment,
            #                                      commit.operations(), is_tipdelete(commit)))
            if (not commit.operations()) or is_tipdelete(commit):
                if commit.hasParents():
                    if len(commit.parents()) > 1 && not tagify_merges:
                        continue
                    name = name_func(commit) or default_name(commit)
                    for i in itertools.count():
                        suffix = ".{}".format(i) if i else ""
                        if name + suffix not in usednames: break
                    usednames.add(name + suffix)
                    legend = legend_func(commit)
                    if commit.operations():
                        commit.setOperations([])
                    if create_tags:
                        self.tagify(commit,
                                    name + suffix,
                                    commit.parents()[0],
                                    legend,
                                    delete = false)
                    deletia.append(index)
                else:
                    msg = []
                    if commit.legacyID:
                        msg.append("r%s:" % commit.legacyID)
                    else if commit.mark:
                        msg.append("'%s':" % commit.mark)
                    msg.append("deleting parentless")
                    if commit.operations():
                        msg.append("tip delete of %s." % commit.branch)
                    else:
                        msg.append("zero-op commit on %s." % commit.branch)
                    gripe(" ".join(msg))
                    deletia.append(index)
        self.delete(deletia, ["--tagback", "--tagify"])
    func fastImport(self, fp, options, progress=false, source=None):
        "Read a stream file and use it to populate the repo."
        StreamParser().fastImport(fp, options, progress, source=source)
        self.readtime = time.time()
    func parse_dollar_cookies():
        "Extract info about legacy references from CVS/SVN header cookies."
        if self.dollarMap is not None:
            return
        # The goal here is to throw away CVS and Subversion header
        # information still fossilized into $Id$ and $Subversion$
        # headers after conversion to a later version. For each
        # cookie, all but the earliest blob containing it has it
        # as a fossil which should be removed.  Then, the earliest
        # commit referencing that blob gets a legacy property set;
        # later references will be branching artifacts.
        self.dollarMap = {}
        seen = set()
        for event in self.events:
            if isinstance(event, Blob) && event.cookie:
                if event.cookie in seen:
                    continue
                else:
                    # The first commit immediately after this blob
                    for ei in range(self.find(event.mark), len(self.events)):
                        if isinstance(self.events[ei], Commit):
                            commit = self.events[ei]
                            break
                    seen.add(event.cookie)
                    if commit.properties && "legacy" in commit.properties:
                        complain("legacy property of %s overwritten" \
                                 % commit.mark)
                    if isinstance(event.cookie, str):
                        svnkey = "SVN:" + event.cookie
                        self.dollarMap[svnkey] = commit
                    else:
                        (basename, cvsref) = event.cookie
                        for fileop in commit.operations():
                            if fileop.op == opM && fileop.ref == event.mark:
                                if not os.path.basename(fileop.path).endswith(basename):
                                    # Usually the harmless result of a
                                    # file move or copy that cvs2svn or
                                    # git-svn didn't pick up on.
                                    complain("mismatched CVS header path '%s' in %s vs '%s' in %s"
                                             % (fileop.path, commit.mark, basename, event.mark))
                                cvskey = "CVS:%s:%s" % (fileop.path, cvsref)
                                self.dollarMap[cvskey] = commit
    func check_uniqueness(self, verbosely, announcer=announce):
        "Audit the repository for uniqueness properties."
        self.uniqueness = None
        timecheck = {}
        time_collisions = {}
        for event in self.commits():
            when = event.when()
            if when in timecheck:
                if when not in time_collisions:
                    time_collisions[when] = [timecheck[when]]
                time_collisions[when].append(event)
            timecheck[when] = event
        if not time_collisions:
            self.uniqueness = "committer_date"
            if verbosely:
                announcer("All commit times in this repository are unique.")
            return
        announcer("These timestamps have multiple commits: %s" \
                 % " ".join(map(rfc3339, time_collisions.keys())))
        stamp_collisions = set()
        for clique in time_collisions.values():
            stampcheck = {}
            for event in clique:
                if event.actionStamp() in stampcheck:
                    stamp_collisions.add(stampcheck[event.actionStamp()])
                    stamp_collisions.add(event.mark)
                stampcheck[event.actionStamp()] = event.mark
        if not stamp_collisions:
            self.uniqueness = "committer_stamp"
            announcer("All commit stamps in this repository are unique.")
            return
        announcer("These marks are in stamp collisions: %s" \
                  % " ".join(stamp_collisions))
*/

// exportStyle says how we should we tune the export dump format.
func (repo *Repository) exportStyle() stringSet {
        if repo.vcs != nil {
            return repo.vcs.styleflags
        }
	// Default to git style
	return stringSet{"nl-after-commit"}
}

/*
    func fast_export(self, selection, fp, options, target=None, progress=false):
        "Dump the repo object in Subversion dump or fast-export format."
	self.writeOptions = options
	self.preferred = target
        if target && target.name == "svn":
            SubversionDumper().dump(selection, fp, progress)
            return
        if selection != self.all():
            implied = set(selection)
            for ei in selection:
                event = self.events[ei]
                if isinstance(event, Commit):
                    for fileop in event.operations():
                        if fileop.op == opM:
                            if fileop.ref != "inline":
                                implied.add(self.find(fileop.ref))
                    for tag in event.attachments:
                        implied.add(self.find(tag.committish))
            selection = list(implied)
            selection.sort()
	self.realized = make(map[string]bool)	// Track what branches are made 
        with Baton("reposurgeon: exporting", enable=progress) as baton:
            try:
                self.realized = {}
                selection_marks = [self.events[i].mark for i in selection if hasattr(self.events[i], "mark")]
		self.internals = selection.marks
                for ei in selection:
                    baton.twirl("")
                    event = self.events[ei]
                    if isinstance(event, Passthrough):
                        # Support writing bzr repos to plain git if they don't
                        # actually have the extension features their export
                        # streams declare.  Without this check git fast-import
                        # barfs on declarations for unused features.
                        if event.text.startswith("feature") && event.text.split()[1] not in target.extensions:
                            continue
                    if debugEnable(debugUNITE):
                        if hasattr(event, "mark"):
                            announce(debugSHOUT, "writing %d %s %s" % (ei, event.mark, event.__class__.__name__))
                    fp.write(event.String())
            except IOError as e:
                raise Fatal("export error: %s" % e)
    func preserve(self, filename):
        "Add a path to the preserve set, to be copied back on rebuild."
        if os.path.exists(filename):
            self.preserveSet.add(filename)
        else:
            raise Recoverable("%s doesn't exist" % filename)
    func unpreserve(self, filename):
        "Remove a path from the preserve set."
        if filename in self.preserveSet:
            self.preserveSet.remove(filename)
        else:
            raise Recoverable("%s doesn't exist" % filename)
    func preservable():
        "Return the repo's preserve set."
        return self.preserveSet
    func rename(self, newname):
        "Rename the repo."
        try:
            # Can fail if the target directory exists.
            announce(debugSHUFFLE, "repository rename %s->%s calls os.rename(%s, %s)" % (self.name, newname, repr(self.subdir()), repr(self.subdir(newname))))
            os.rename(self.subdir(), self.subdir(newname))
            self.name = newname
        except OSError as e:
            raise Fatal("repo rename %s -> %s failed: %s"
                                       % (self.subdir(), self.subdir(newname), e))
    func insertEvent(self, event, where=None, legend=""):
        "Insert an event just before the specified index."
        if where is not None:
            self.events.insert(where, event)
        else if self.events && isinstance(self.events[-1], Passthrough) && self.events[-1].text == "done":
            self.events.insert(-1, event)
        else:
            self.events.append(event)
        self.declare_sequence_mutation(legend)
*/

func (repo *Repository) addEvent(event Event) {
	repo.events = append(repo.events, event)
}

/*

    @memoized_iterator("_commits")
    func commits():
        "Iterate through the repository commit objects."
        return (e for e in self.events if isinstance(e, Commit))
    func filter_assignments(self, f):
        "Filter assignments, warning if any of them goes empty."
        for (name, values) in self.assignments.items():
            newassigns = []
            dc = 0
            for (i, e) in enumerate(self.events):
                if f(e):
                    dc += 1
                else if i in values:
                    newassigns.append(i - dc)
            if values && not newassigns:
                complain("sequence modification left %s empty" % name)
            self.assignments[name] = newassigns
    func declare_sequence_mutation(self, warning=None):
        "Mark the repo event sequence modified."
        self._commits = None
        self._markToIndex = nil
        self._namecache = {}
        if self.assignments && warning:
            self.assignments = {}
            complain("assignments invalidated by " + warning)
    func earliest_commit():
        "Return the earliest commit."
        return next(self.commits())
    func earliest():
        "Return the date of earliest commit."
        return next(self.commits()).committer.date
    func ancestors(self, ei):
        "Return ancestors of an event, in reverse order."
        trail = []
        while true:
            if not self.events[ei].hasParents():
                break
            else:
                efrom = self.find(self.events[ei].parentMarks()[0])
                trail.append(efrom)
                ei = efrom
        return trail

    #
    # Delete machinery begins here
    #
    func ancestor_count(self, event, path):
        "Count modifications of a path in this commit and its ancestors."
        count = 0
        while true:
            for fileop in event.operations():
                if fileop && fileop.op == opM && fileop.path == path:
                    count += 1
                    break
            # 0, 1, and >1 are the interesting cases
            if count > 1:
                return count
            try:
                event = event.parents()[0]
            except IndexError:
                break
        return count
    func __compose(self, event, left, right):
        "Compose two relevant fileops."
        # Here's what the fields in the return value mean:
        # 0: Was this a modification
        # 1: Op to replace the first with (None means delete)
        # 2: Op to replace the second with (None means delete)
        # 3: If not None, a warning to emit
        # 4: Case number, for coverage analysis
        pair = (left.op, right.op)
        #
        # First op M
        #
        if pair == (opM, opM):
            # Leave these in place, they get handled later.
            return (false, left, right, None, 0)
        # M a + D a -> D a
        # Or, could reduce to nothing if M a was the only modify..
        else if left.op == opM and right.op in opD:
            if self.ancestor_count(event, left.path) == 1:
                return (true, None, None, None, 1)
            else:
                return (true, right, None, None, 2)
        else if left.op == opM and right.op == opR:
            # M a + R a b -> R a b M b, so R falls towards start of list
            if left.path == right.source:
                if self.ancestor_count(event, left.path) == 1:
                    # M a has no ancestors, preceding R can be dropped
                    left.path = right.target
                    return (true, left, None, None, 3)
                else:
                    # M a has ancestors, R is still needed
                    left.path = right.target
                    return (true, right, left, None, 4)
            # M b + R a b can't happen.  If you try to generate this with
            # git mv it throws an error.  An ordinary mv results in D b M a.
            else if left.path == right.target:
                return(true, right, None, "M followed by R to the M operand?", -1)
        # Correct reduction for this would be M a + C a b -> C a b + M a + M b,
        # that is we'd have to duplicate the modify. We'll leave it in place
        # for now.
        else if left.op == opM and right.op == opC:
            return (false, left, right, None, 5)
        #
        # First op D or deleteall
        #
        # Delete followed by modify undoes delete, since M carries whole files.
        else if pair == (opD, opM):
            return (true, None, right, None, 6)
        # But we have to leave deletealls in place, since they affect right ops
        else if pair == (FileOp.deleteall, opM):
            return (false, left, right, None, 7)
        # These cases should be impossible.  But cvs2svn actually generates
        # adjacent deletes into Subversion dumpfiles which turn into (D, D).
        else if left.op == FileOp.deleteall and right.op != opM:
            return (false, left, right,
                    "Non-M operation after deleteall?", -1)
        else if left.op == opD and right.op == opD:
            return (true, left, None, None, -2)
        else if left.op == opD and right.op in (opR, opC):
            if left.path == right.source:
                return (false, left, right,
                        "R or C of %s after deletion?" % left.path, -3)
            else:
                return (false, left, right, None, 8)
        #
        # First op R
        #
        else if pair == (opR, opD):
            if left.target == right.path:
                # Rename followed by delete of target composes to source delete
                right.path = left.source
                return (true, None, right, None, 9)
            else:
                # On rename followed by delete of source discard the delete
                # but user should be warned.
                return (false, left, None,
                        "delete of %s after renaming to %s?" % (right.path, left.source), -4)
        # Rename followed by deleteall shouldn't be possible
        else if pair == (opR, FileOp.deleteall) and left.target == right.path:
            return (false, None, right,
                    "rename before deleteall not removed?", -5)
        # Leave rename or copy followed by modify alone
        else if pair == (opR, opM) or pair == (opC, opM):
            return (false, left, right, None, 10)
        # Compose renames where possible
        else if left.op == opR and right.op == opR:
            if left.target == right.source:
                left.target = right.target
                return (true, left, None, None, 11)
            else:
                return (false, left, right,
                        "R %s %s is inconsistent with following operation" \
                        % (left.source, left.target), -6)
        # We could do R a b + C b c -> C a c + R a b, but why?
        if left.op == opR and right.op == opC:
            return (false, left, right, None, 12)
        #
        # First op C
        #
        else if pair == (opC, opD):
            if left.source == right.path:
                # Copy followed by delete of the source is a rename.
                left.setOp(opR)
                return (true, left, None, None, 13)
            else if left.target == right.path:
                # This delete undoes the copy
                return (true, None, None, None, 14)
        else if pair == (opC, opR):
            if left.source == right.source:
                # No reduction
                return (false, left, right, None, 15)
            else:
                # Copy followed by a rename of the target reduces to single copy
                if left.target == right.source:
                    left.target = right.target
                    return (true, left, None, None, 16)
        else if pair == (opC, opC):
            # No reduction
            return (false, left, right, None, 17)
        #
        # Case not covered
        #
        raise Fatal("can't compose op '%s' and '%s'" % (left, right))
    func canonicalize(self, commit):
        "Canonicalize the list of file operations in this commit."
        coverage = set()
        # Handling deleteall operations is simple
        lastdeleteall = None
        for (i, a) in enumerate(commit.operations()):
            if a.op == FileOp.deleteall:
                lastdeleteall = i
        if lastdeleteall is not None:
            announce(debugDELETE, "removing all before rightmost deleteall")
            commit.setOperations(commit.operations()[lastdeleteall:])
            commit.invalidatePathsetCache()
        # Composition in the general case is trickier.
        while true:
            # Keep making passes until nothing mutates
            mutated = false
            for i in range(len(commit.operations())):
                for j in range(i+1, len(commit.operations())):
                    a = commit.operations()[i]
                    b = commit.operations()[j]
                    if a is not None and b is not None and a.relevant(b):
                        (modified, newa, newb, warn, case) = self.__compose(commit, a, b)
                        announce(debugDELETE, "Reduction case %d fired on %s" % (case, (i,j)))
                        if modified:
                            mutated = true
                            commit.operations()[i] = newa
                            commit.operations()[j] = newb
                            if debugEnable(debugDELETE):
                                announce(debugDELETE, "During canonicalization:")
                                commit.fileopDump()
                            if warn:
                                complain(warn)
                            coverage.add(case)
            if not mutated:
                break
            commit.setOperations([x for x in commit.operations() if x is not None])
            commit.invalidatePathsetCache()
        return coverage
    func squash(self, selected, policy):
        "Delete a set of events, or rearrange it forward or backwards."
        announce(debugDELETE, "Deletion list is %s" % [self.events[x].idMe() for x in selected])
        for qualifier in policy:
            if qualifier not in ["--complain",
                                 "--coalesce",
                                 "--delete",
                                 "--empty-only",
                                 "--pushback",
                                 "--pushforward",
                                 "--tagify",
                                 "--tagback",
                                 "--tagforward",
                                 "--quiet"]:
                raise Recoverable("no such deletion modifier as " + qualifier)
        # For --pushback, it is critical that deletions take place from lowest
        # event number to highest since --pushback often involves re-ordering
        # events even as it is iterating over the 'selected' list (see
        # 'swap_indices' below). Only events earlier than the event currently
        # being processed are re-ordered, however, so the operation is safe as
        # long as events are visited lowest to highest. (For --pushforward,
        # iteration order is immaterial since it does no event re-ordering and
        # actual deletion is delayed until after iteration is finished.)
        selected = sorted(selected)
        dquiet = "--quiet" in policy
        delete = "--delete" in policy
        tagify = "--tagify" in policy
        tagback = "--tagback" in policy
        tagforward = "--tagforward" in policy or (not delete and not tagback)
        pushback = "--pushback" in policy
        pushforward = "--pushforward" in policy or (not delete and not pushback)
        # Sanity checks
        if not dquiet:
            for ei in selected:
                event = self.events[ei]
                if  isinstance(event, Commit):
                    if delete:
                        speak = "warning: commit %s to be deleted has " % event.mark
                        if '/' in event.branch and '/heads/' not in event.branch:
                            complain(speak + "non-head branch attribute %s" % event.branch)
                        if not event.alldeletes():
                            complain(speak + "non-delete fileops.")
                    if not delete:
                        if pushback and not event.hasParents():
                            complain("warning: "
                                     "pushback of parentless commit %s" \
                                     % event.mark)
                        if pushforward and not event.hasChildren():
                            complain("warning: "
                                     "pushforward of childless commit %s" \
                                     % event.mark)
        altered = []
        # Here are the deletions
        for e in self.events:
            e.deleteflag = false
        for ei in selected:
            event = self.events[ei]
            if isinstance(event, Blob):
                # Never delete a blob except as a side effect of
                # deleting a commit.
                event.deleteflag = false
            else if isinstance(event, (Tag, Reset, Passthrough)):
                event.deleteflag = ("--delete" in policy)
            else if isinstance(event, Commit):
                event.deleteflag = true
                # Decide the new target for tags
                filter_only = true
                if tagforward and event.hasChildren():
                    filter_only = false
                    new_target = event.firstChild()
                else if tagback and event.parents():
                    filter_only = false
                    new_target = event.parents()[0]
                # Reparent each child
                func compose_comment(a, b):
                    "Concatenate comments, ignoring empty-log-message markers."
                    if a == b:
                        return a
                    a_empty = emptyComment(a)
                    b_empty = emptyComment(b)
                    if a_empty and b_empty:
                        return ""
                    else if a_empty and not b_empty:
                        return b
                    else if not a_empty and b_empty:
                        return a
                    else:
                        return a + '\n' + b
                for child in list(event.children()):
                    # Insert event's parents in place of event in child's
                    # parent list. We keep existing duplicates in case they
                    # are wanted, but ensure we don't introduce new ones.
                    old_parents = list(child.parents())
                    event_pos = old_parents.index(event)
                    # Start with existing parents before us,
                    # including existing duplicates
                    new_parents = old_parents[:event_pos]
                    # Add our parents, with possible duplicates, but not if
                    # already present before.
                    to_add = [p for p in event.parents() if p not in new_parents]
                    new_parents.extend(to_add)
                    # Avoid duplicates due to event.parents() insertion.
                    new_parents.extend(
                            p
                            for p in itertools.islice(old_parents,
                                                      event_pos+1, None)
                            if p not in to_add)
                    # Prepend a copy of this event's file ops to
                    # all children with the event as their first
                    # parent, and mark each such child as needing
                    # resolution.
                    if pushforward and child.parents()[0] == event:
                        child.setOperations(copy.copy(event.operations()) + child.operations())
                        child.invalidatePathsetCache()
                        # Also prepend event's comment, ignoring empty
                        # log messages.
                        if "--empty-only" in policy and not emptyComment(child.comment):
                            complain("--empty is on and %s comment is nonempty" % child.idMe())
                        child.comment = compose_comment(event.comment,
                                                        child.comment)
                        altered.append(child)
                    # Really set the parents to the newly constructed list
                    child.setParents(new_parents)
                    # If event was the first parent of child yet has no parents
                    # of its own, then child's first parent has changed.
                    # Prepend a deleteall to child's fileops to ensure it
                    # starts with an empty tree (as event does) instead of
                    # inheriting that of its new first parent.
                    if event_pos == 0 and not event.parents():
                        fileop = FileOp()
                        fileop.construct("deleteall")
                        child.prependOperation(fileop)
                        child.invalidatePathsetCache()
                        altered.append(child)
                # We might be trying to hand the event's fileops to its
                # primary parent.
                if pushback and event.hasParents():
                    # Append a copy of this event's file ops to its primary
                    # parent fileop list and mark the parent as needing
                    # resolution.
                    parent = event.parents()[0]
                    parent.setOperations(parent.operations() + copy.copy(event.operations()))
                    parent.invalidatePathsetCache()
                    # Also append child's comment to its parent's
                    if "--empty-only" in policy and not emptyComment(parent.comment):
                        complain("--empty is on and %s comment is nonempty" % parent.idMe())
                    parent.comment = compose_comment(parent.comment,
                                                     event.comment)
                    altered.append(parent)
                    # We need to ensure all fileop blobs are defined before the
                    # corresponding fileop, in other words ensure that the blobs
                    # appear before the primary parent in the stream.
                    earliest = parent.index()
                    swap_indices = set()
                    for fileop in event.operations():
                        if fileop.op == opM:
                            blob_index = self.find(fileop.ref)
                            if blob_index > earliest: swap_indices.add(blob_index)
                    if swap_indices:
                        last = max(swap_indices)
                        neworder = itertools.chain(
                                swap_indices, # first take the blobs
                                # then all others
                                itertools.ifilterfalse(swap_indices.__contains__,
                                         range(earliest, last+1)) )
                        self.events[earliest:last+1] = list(map(
                                self.events.__getitem__, neworder))
                        self.declare_sequence_mutation("squash pushback")
                # Move tags and attachments
                if filter_only:
                    for e in event.attachments:
                        e.deleteflag = true
                else:
                    if not tagify and event.branch and "/tags/" in event.branch \
                            and new_target.branch != event.branch:
                        # By deleting the commit, we would lose the fact that
                        # it moves its branch (to create a lightweight tag for
                        # instance): replace it by a Reset which will save this
                        # very information. The following loop will take care
                        # of moving the attachment to the new target.
                        reset = Reset(self, ref = event.branch,
                                            target = event)
                        self.events[ei] = reset
                    # use a copy of attachments since it will be mutated
                    for t in list(event.attachments):
                        t.forget()
                        t.remember(self, target=new_target)
                # And forget the deleted event
                event.forget()
        # Preserve assignments
        self.filter_assignments(lambda e: e.deleteflag)
        # Do the actual deletions
        self.events = [e for e in self.events if not e.deleteflag]
        self.declare_sequence_mutation()
        # Canonicalize all the commits that got ops pushed to them
        if not delete:
            for event in altered:
                if event.deleteflag: continue
                if debugEnable(debugDELETE):
                    announce(debugDELETE, "Before canonicalization:")
                    event.fileopDump()
                self.caseCoverage |= self.canonicalize(event)
                if debugEnable(debugDELETE):
                    announce(debugDELETE, "After canonicalization:")
                    event.fileopDump()
                # Now apply policy in the mutiple-M case
                cliques = event.cliques()
                if ("--coalesce" not in policy and not delete) \
                        or debugEnable(debugDELETE):
                    for (path, oplist) in cliques.items():
                        if len(oplist) > 1 and not dquiet:
                            complain("commit %s has multiple Ms for %s"
                                    % (event.mark, path))
                if "--coalesce" in policy:
                    # Only keep last M of each clique, leaving other ops alone
                    event.setOperations( \
                           [op for (i, op) in enumerate(event.operations())
                            if (op.op != opM) or (i == cliques[op.path][-1])])
                    event.invalidatePathsetCache()
                if debugEnable(debugDELETE):
                    announce(debugDELETE, "Commit %d, after applying policy:" % (ei + 1,))
                    event.fileopDump()
        # Cleanup
        for e in self.events:
            del e.deleteflag
        self.gc_blobs()
    func delete(self, selected, policy=None):
        "Delete a set of events."
        policy = policy or []
        self.squash(selected, ["--delete", "--quiet"] + policy)
    func dedup(self, dup_map):
        """Replace references to duplicate blobs according to the given dup_map,
        which maps marks of duplicate blobs to canonical marks"""
        for event in self.events:
            if isinstance(event, Commit):
                for fileop in event.operations():
                    if fileop.op == opM and fileop.ref in dup_map:
                        fileop.ref = dup_map[fileop.ref]
        self.gc_blobs()
    func gc_blobs():
        "Garbage-collect blobs that no longer have references."
        backreferences = collections.Counter()
        for event in self.events:
            if isinstance(event, Commit):
                for fileop in event.operations():
                    if fileop.op == opM:
                        backreferences[fileop.ref] += 1
        func eligible(e):
            return isinstance(e, Blob) and not backreferences[e.mark]
        self.filter_assignments(eligible)
        self.events = [e for e in self.events if not eligible(e)]
        self.invalidateManifests()     # Might not be needed
        self.declare_sequence_mutation()
    func __delitem__(self, index):
        # To make Repository a proper container (and please pylint)
        self.squash([index], ["--delete", "--quiet", "--tagback"])
    #
    # Delete machinery ends here
    #
    func front_events():
        "Return options, features."
        return [e for e in self.events \
                if isinstance(e, Passthrough) \
                and (e.text.startswith("option") or e.text.startswith("feature"))]

    func resort():
        """Topologically sort the events in this repository.

        Reorder self.events so that objects referenced by other
        objects appear first.  The sort is stable to avoid unnecessary
        churn.
        """

        class dag_edges(object):
            func __init__():
                self.eout = set()
                self.ein = set()

        dag = {}
        start = set(range(len(self.events)))

        # helper for constructing the dag
        func handle(x, ymark):
            assert(ymark is not None)
            if ymark == 'inline':
                return
            assert(ymark[0] == ':')
            if ymark is not None and ymark[0] == ':':
                y = self.find(ymark)
                assert(y is not None)
                assert(x != y)
                start.discard(x)
                dag.setdefault(x, dag_edges()).eout.add(y)
                dag.setdefault(y, dag_edges()).ein.add(x)

        # construct the dag
        for n, node in enumerate(self.events):
            edges = dag.setdefault(n, dag_edges())
            if isinstance(node, Commit):
                for parent in node.parents():
                    p = self.index(parent)
                    assert(n != p)
                    start.discard(n)
                    edges.eout.add(p)
                    dag.setdefault(p, dag_edges()).ein.add(n)
                for o in node.operations():
                    if o.op == opM:
                        handle(n, o.ref)
                    else if o.op == opN:
                        handle(n, o.ref)
                        handle(n, o.committish)
            else if isinstance(node, Blob):
                pass
            else if isinstance(node, Tag):
                handle(n, node.committish)
            else if isinstance(node, Reset):
                if node.target is not None:
                    t = self.index(node.target)
                    assert(n != t)
                    start.discard(n)
                    edges.eout.add(t)
                    dag.setdefault(t, dag_edges()).ein.add(n)
            else if isinstance(node, Passthrough):
                pass
            else:
                raise ValueError('unexpected event type')

        # now topologically sort the dag, using a priority queue to
        # provide a stable topological sort (each event's priority is
        # its original index)
        s = list(start)
        heapq.heapify(s)
        tsorted = []
        old_index_to_new = {}
        while len(s):
            n = heapq.heappop(s)
            assert n not in old_index_to_new
            old_index_to_new[n] = len(tsorted)
            tsorted.append(n)
            ein = dag[n].ein
            while len(ein):
                m = ein.pop()
                medges = dag[m]
                medges.eout.remove(n)
                if not len(medges.eout):
                    heapq.heappush(s, m)

        orig = range(len(self.events))
        if tsorted != orig:
            t = set(tsorted)
            assert len(t) == len(tsorted)
            o = set(orig)
            assert len(t - o) == 0
            leftout = o - t
            if (len(leftout)):
                complain('event re-sort failed due to one or more dependency' \
                         + ' cycles involving the following events: ' \
                         + ', '.join(str(x+1) for x in sorted(leftout)))
                return
            self.events = [self.events[i] for i in tsorted]
            if verbose:
                announce(debugSHOUT, 're-sorted events')
            # assignments will be fixed so don't pass anything to
            # declare_sequence_mutation() to tell it to warn about
            # invalidated assignments
            self.declare_sequence_mutation()
            self.assignments = {
                name:[old_index_to_new[i] for i in selection]
                for name, selection in self.assignments.items()}

    func reorder_commits(self, v, bequiet):
        "Re-order a contiguous range of commits."
        func validate_operations(events, bequiet):
            "Check if fileops still make sense after re-ordering events."
            # Also check events one level beyond re-ordered range; anything
            # beyond that is the user's responsibility.
            for x in events + events[-1].children():
                ops = []
                for op in x.operations():
                    path = None
                    if op.op == opD:
                        path = op.path
                    else if op.op in (opR, opC):
                        path = op.source
                    if path is not None and not x.visible(path):
                        if not bequiet:
                            complain("%s '%s' fileop references non-existent '%s' after re-order" %
                                     (x.idMe(), op.op, path))
                        continue
                    ops.append(op)
                if ops != x.operations():
                    x.setOperations(ops)
                    x.invalidatePathsetCache()
                    if not bequiet and len(ops) == 0:
                        complain("%s no fileops remain after re-order" % x.idMe())

        if len(v) <= 1:
            return
        events = [self.events[i] for i in v]
        sorted_events = [self.events[i] for i in sorted(v)]
        for e in sorted_events[1:]:
            if len(e.parents()) > 1:
                raise Recoverable("non-linear history detected: %s" % e.idMe())
        for e in sorted_events[:-1]:
            if len(e.children()) > 1:
                raise Recoverable("non-linear history detected: %s" % e.idMe())
        if any(not sorted_events[i+1].hasParents() or
               x not in sorted_events[i+1].parents()
               for i,x in enumerate(sorted_events[:-1])):
            raise Recoverable("selected commit range not contiguous")
        if events == sorted_events:
            complain("commits already in desired order")
            return
        events[0].setParents(list(sorted_events[0].parents()))
        for x in list(sorted_events[-1].children()):
            x.replaceParent(sorted_events[-1], events[-1])
        for i,e in enumerate(events[:-1]):
            events[i+1].setParents([e])
        validate_operations(events, bequiet)
        self.resort()
    func renumber(self, origin=1, baton=None):
        "Renumber the marks in a repo starting from a specified origin."
        markmap = {}
        func remark(m, e):
            try:
                return ":" + repr(markmap[m])
            except KeyError:
                raise Fatal("unknown mark %s in %s cannot be renumbered!" % \
                            (m, e.idMe()))
        if baton:
            count = len(self.events)
            baton.startcounter(" %%%dd of %s" % (len(str(count)), count))
        self.markseq = 0
        for event in self.events:
            if hasattr(event, "mark"):
                if event.mark is None:
                    continue
                else if not event.mark.startswith(":"):
                    raise Fatal("field not in mark format")
                else:
                    markmap[event.mark] = origin + self.markseq
                    self.markseq += 1
        for event in self.events:
            for fld in ("mark", "committish"):
                try:
                    old = getattr(event, fld)
                    if old is not None:
                        new = remark(old, event)
                        announce(debugUNITE, "renumbering %s -> %s in %s.%s" % (old, new,
                                                                        event.__class__.__name__,
                                                                        fld))
                        setattr(event, fld, new)
                except AttributeError:
                    pass
        for commit in self.commits():
            for fileop in commit.operations():
                if fileop.op == opM and fileop.ref.startswith(":"):
                    new = remark(fileop.ref, fileop)
                    announce(debugUNITE, "renumbering %s -> %s in fileop" % (fileop.ref, new))
                    fileop.ref = new
            if baton:
                baton.bumpcounter()
        # Prevent result from having multiple 'done' trailers.
        orig_len = len()
        self.events = [x for x in self.events if not (isinstance(x, Passthrough) and x.text == "done\n")]
        if len(self.events) != orig_len:
            self.events.append(Passthrough("done\n", self))
            self.declare_sequence_mutation()
        # Previous maps won't be valid
        self.invalidateObjectMap()
        self._markToIndex = nil
        if baton:
            baton.endcounter()
    func uniquify(self, color, persist=None):
        "Disambiguate branches, tags, and marks using the specified label."
        for event in self.events:
            for (objtype, attr) in ((Commit, "branch"),
                                    (Reset, "ref"),
                                    (Tag, "name"),):
                if isinstance(event, objtype):
                    oldname = getattr(event, attr)
                    newname = None
                    if persist is None:
                        # we're not trying to preserve names
                        if objtype == Tag:
                            newname = color + "-" + oldname
                        else:
                            newname = oldname + "-" + color
                    else if oldname not in persist:
                        # record name as belonging to this repo
                        persist[oldname] = color
                        continue
                    else if persist.get(oldname) == color:
                        # name belongs here, do nothing
                        continue
                    else:
                        # collision - oldname belongs to a different repo
                        if objtype == Tag:
                            newname = color + "-" + oldname
                        else:
                            newname = oldname + "-" + color
                    if newname:
                        setattr(event, attr, newname)
                        announce(debugUNITE, "moving %s -> %s in %s.%s"
                                     % (oldname, newname,
                                        objtype.__name__,
                                        attr))
                        if persist is not None:
                            persist[newname] = color
             # Disambiguate defining marks.
            for fld in ("mark", "committish"):
                if hasattr(event, fld):
                    old = getattr(event, fld)
                    if old is None:
                        continue
                    else if not old.startswith(":"):
                        raise Fatal("field not in mark format")
                    else:
                        new = old + "-" + color
                        announce(debugUNITE, "moving %s -> %s in %s.%s"
                                     % (old, new,
                                        event.__class__.__name__,
                                        fld))
                        setattr(event, fld, new)
            self.invalidateObjectMap()
            # Now marks in fileops
            if isinstance(event, Commit):
                for fileop in event.operations():
                    if fileop.op == opM and fileop.ref.startswith(":"):
                        new = fileop.ref + "-" + color
                        announce(debugUNITE, "moving %s -> %s in fileop"
                                     % (fileop.ref, new))
                        fileop.ref = new
        return persist
    func absorb(self, other):
        "Absorb all events from the repository OTHER into SELF."
        # Only vcstype, sourcedir, and basedir are not copied here
        self.preserveSet |= other.preserveSet
        self.caseCoverage |= other.caseCoverage
        # Strip feature events off the front, they have to stay in front.
        while isinstance(other[0], Passthrough):
            lenfront = sum(1 for x in self.events if isinstance(x, Passthrough))
            self.events.insert(lenfront, other.events.pop(0))
        # Merge in the non-feature events and blobs
        self.events += other.events
        self.declare_sequence_mutation("absorb")
        # Transplant in fileops, blobs, and other impedimenta
        for event in other:
            if hasattr(event, "moveto"):
                event.moveto(repo)
        other.events = []
        other.cleanup()
        #del other
    func graft(self, graft_repo, graft_point, options):
        "Graft a repo on to this one at a specified point."
        if graft_point is None:
            persist = {}
        else:
            persist = None
            where = self.events[graft_point]
            if not isinstance(where, Commit):
                raise Recoverable("%s in %s is not a commit." % \
                                  (where.mark, self.name))
        # Errors aren't recoverable after this
        graft_repo.uniquify(graft_repo.name, persist)
        if graft_point is not None:
            graftroot = graft_repo.earliest_commit()
        self.absorb(graft_repo)
        if graft_point:
            graftroot.addParentByMark(where.mark)

        if "--prune" in options:
            # Prepend a deleteall. Roots have nothing upline to preserve.
            delop = FileOp()
            delop.construct("deleteall")
            graftroot.prependOperation(delop)

        # Resolve all callouts
        for commit in graft_repo.commits():
            for (idx, parent) in enumerate(commit.parents()):
                if Commit.isCallout(parent.mark):
                    attach = self.named(parent.mark)
                    if len(attach) == 0:
                        raise Recoverable("no match for %s in %s" \
                                          % (parent.mark, graft_repo.name))
                    else if len(attach) >= 2:
                        raise Recoverable("%s is ambiguous in %s" \
                                          % (parent.mark, graft_repo.name))
                    else:
                        commit.removeParent(parent)
                        newparent = self.events[list(attach)[0]]
                        commit.insertParent(idx, newparent.mark)
        self.renumber()
    func __last_modification(self, commit, path):
        "Locate the last modification of the specified path before this commit."
        ancestors = commit.parents()
        while ancestors:
            backto = []
            # pylint: disable=useless-else-on-loop
            for ancestor in ancestors:
                # This is potential trouble if the file was renamed
                # down one side of a merge bubble but not the other.
                # Might cause an internal-error message, but no real
                # harm will be done.
                for (i, fileop) in enumerate(ancestor.operations()):
                    if fileop.op == opR and fileop.target == path:
                        path = fileop.source
                    else if fileop.op == opM and fileop.path == path:
                        return (ancestor, i)
                else:
                    backto += ancestor.parents()
            ancestors = backto
        return None
    func move_to_rename():
        "Make rename sequences from matched delete-modify pairs."
        # TODO: Actually use this somewhere...
        rename_count = 0
        # pylint: disable=unpacking-non-sequence
        for commit in self.commits():
            renames = []
            for (d, op) in enumerate(commit.operations()):
                if op.op == opD:
                    previous = self.__last_modification(commit, op.path)
                    if not previous:
                        raise Recoverable("internal error looking for renames of %s" % op.path)
                    else:
                        (ancestor, i) = previous
                        for (m, op2) in enumerate(commit.operations()):
                            if op2.op == opM and \
                               ancestor.operations()[i].mode == op2.mode and \
                               ancestor.operations()[i].ref == op2.ref:
                                renames.append((d, m))
                                rename_count += 1
                                break
            for (d, m) in renames:
                commit.operations()[d].source = commit.operations()[d].path
                commit.operations()[d].target = commit.operations()[m].path
                del commit.operations()[d].path
                commit.operations()[d].op = opR
                commit.operations().pop(m)
                commit.invalidatePathsetCache()
        return rename_count
    func path_walk(self, selection, hook=lambda path: path):
        "Apply a hook to all paths, returning the set of modified paths."
        modified = set()
        for ei in selection:
            event = self.events[ei]
            if isinstance(event, Commit):
                for fileop in event.operations():
                    if fileop.op in (opM, opD):
                        newpath = hook(fileop.path)
                        if newpath != fileop.path:
                            modified.add(newpath)
                        fileop.path = newpath
                    else if fileop.op in (opR, opC):
                        newpath = hook(fileop.source)
                        if newpath != fileop.source:
                            modified.add(newpath)
                        fileop.source = newpath
                        newpath = hook(fileop.target)
                        if newpath != fileop.target:
                            modified.add(newpath)
                        fileop.target = newpath
                event.invalidatePathsetCache()
        return sorted(modified)
    func split_commit(self, where, splitfunc):
        event = self.events[where]
        # Fileop split happens here
        (fileops, fileops2) = splitfunc(event.operations())
        if fileops and fileops2:
            self.events.insert(where+1, event.clone())
            self.declare_sequence_mutation("commit split")
            event2 = self.events[where+1]
            # need a new mark
            assert(event.mark == event2.mark)
            event2.setMark(event.repo.newmark())
            self.invalidateObjectMap()
            # Fix up parent/child relationships
            for child in list(event.children()):
                child.replaceParent(event, event2)
            event2.setParents([event])
            # and then finalize the ops
            event2.setOperations(fileops2)
            event2.invalidatePathsetCache()
            event.setOperations(fileops)
            event.invalidatePathsetCache()
            # Avoid duplicates in the legacy-ID map
            if event2.legacyID:
                event2.legacyID += ".split"
            return true
        return false
    func split_commit_by_index(self, where, splitpoint):
        return self.split_commit(where,
                                 lambda ops: (ops[:splitpoint],
                                              ops[splitpoint:]))
    func split_commit_by_prefix(self, where, prefix):
        return self.split_commit(where,
                                 lambda ops: ([op for op in ops if not op.path.startswith(prefix)],
                                              [op for op in ops if (op.path or op.target) and
                                                                   (op.path or op.target).startswith(prefix)]))

    func blob_ancestor(self, commit, path):
        "Return blob for the nearest ancestor to COMMIT of the specified PATH."
        ancestor = commit
        while true:
            back = ancestor.parents()
            if not back:
                break
            ancestor = back[0]
            for op in ancestor.operations():
                if hasattr(op, "path") and op.path == path:
                    if op.op == opD:
                        # Path had no ancestor after last delete
                        return None
                    else if op.op in (opR, opC):
                        path = op.source
                    else if op.op == opM:
                        # Buglet: if this path has multiple ops,
                        # we'd probably prefer the last to the first.
                        return self.markToEvent(op.ref)
        return None

    func dumptimes():
        total = self.timings[-1][1] - self.timings[0][-1]
        commit_count = sum(1 for _ in self.commits())
        if self.legacyCount is None:
            os.Stdout.write("        commits: %d\n" % commit_count)
        else:
            os.Stdout.write("        commits: %d (from %d)\n" % (commit_count, self.legacyCount))
        for (i, (phase, _interval)) in enumerate(self.timings):
            if i > 0:
                interval = self.timings[i][1] - self.timings[i-1][1]
                os.Stdout.write("%15s: %s (%2.2f%%)\n" % (phase,
                                              humanize(interval),
                                              (interval * 100)/total))
        os.Stdout.write("          total: %s (%d/sec)\n" % (humanize(total), int((self.legacyCount or commit_count))/total))

    # Sequence emulation methods
    func __len__():
        return len(self.events)
    func __getitem__(self, i):
        return self.events[i]
    func __setitem__(self, i, v):
        self.events[i] = v
    func iterevents(self, indices=None, types=None):
        "Iterate over events matching conditions."
        if indices is None:
            events = lambda: self.events
            withindices = list(enumerate(self.events))
        else:
            events = lambda: itertools.imap(self.events.__getitem__, indices)
            withindices = list(itertools.izip(indices, events()))
        if types is None: return withindices
        isinstances = itertools.imap(isinstance,
                                     events(), itertools.repeat(types))
        return itertools.compress(withindices, isinstances)
    func __del__():
        if self.seekstream:
            self.seekstream.close()

func read_repo(source, options, preferred):
    "Read a repository using fast-import."
    if debugEnable(debugSHUFFLE):
        if preferred:
            announce(debugSHOUT, "looking for a %s repo..." % preferred.name)
        else:
            announce(debugSHOUT, "reposurgeon: looking for any repo at %s..." % \
                     os.path.abspath(source))
    hitcount = 0
    extractor = vcs = None
    for possible in vcstypes:
        if preferred and possible.name != preferred.name:
            continue
        subdir = os.path.join(source, possible.subdirectory)
        if os.path.exists(subdir) and os.path.isdir(subdir) and possible.exporter:
            vcs = possible
            hitcount += 1
    for possible in extractors:
        if preferred and possible.name not in [preferred.name, preferred.name + "-extractor"]:
            continue
        subdir = os.path.join(source, possible.subdirectory)
        if os.path.exists(subdir) and os.path.isdir(subdir):
            if possible.visible or preferred \
                   and possible.name == preferred.name:
                extractor = possible
                hitcount += 1
    if hitcount == 0:
        raise Recoverable("couldn't find a repo under %s" % os.path.relpath(source))
    else if hitcount > 1:
        raise Recoverable("too many repos under %s" % os.path.relpath(source))
    else if debugEnable(debugSHUFFLE):
        announce(debugSHUFFLE, "found %s repository" % getattr(vcs or extractor, "name"))
    repo = Repository()
    repo.sourcedir = source
    if vcs:
        repo.hint(vcs.name, strong=true)
        repo.preserveSet = vcs.preserve
        showprogress = (verbose > 0) and "export-progress" not in repo.exportStyle()
        context = {"basename": os.path.basename(repo.sourcedir)}
    try:
        here = os.getcwd()
        os.Chdir(repo.sourcedir)
        # We found a matching VCS type
        if vcs:
            if "%(tempfile)s" in repo.vcs.exporter:
                try:
                    (tfdesc, tfname) = tempfile.mkstemp()
                    assert tfdesc > -1    # pacify pylint
                    context["tempfile"] = tfname
                    do_or_die(repo.vcs.exporter % context, "repository export")
                    with open(tfname, "rb") as tp:
                        repo.fastImport(tp, options, progress=showprogress, source=source)
                finally:
                    os.remove(tfname)
                    os.close(tfdesc)
            else:
                with popenOrDie(repo.vcs.exporter % context, "repository export") as tp:
                    repo.fastImport(make_wrapper(tp), options, progress=showprogress, source=source)
            if repo.vcs.authormap and os.path.exists(repo.vcs.authormap):
                announce(debugSHOUT, "reading author map.")
                with open(repo.vcs.authormap, "rb") as fp:
                    repo.readAuthorMap(range(len(repo.events)), make_wrapper(fp))
            legacyMap = os.path.join(vcs.subdirectory, "legacy_map")
            if os.path.exists(legacy_map):
                with open(legacyMap, "rb") as rfp:
                    repo.read_legacymap(make_wrapper(rfp))
            if vcs.lister:
                func fileset(exclude):
                    allfiles = []
                    for root, dirs, files in os.walk("."):
                        allfiles += [os.path.join(root, name)[2:] for name in files]
                        for exdir in exclude:
                            if exdir in dirs:
                                dirs.remove(exdir)
                    return set(allfiles)
                with popenOrDie(vcs.lister) as fp:
                    repofiles = set(polystr(fp.read()).split())
                allfiles = fileset([vcs.subdirectory] + glob.glob(".rs*"))
                repo.preserveSet |= (allfiles - repofiles)
            # kluge: git-specific hook
            if repo.vcs.name == "git":
                if os.path.exists(".git/cvs-revisions"):
                    announce(debugSHOUT, "reading cvs-revisions map.")
                    pathrev_to_hash = {}
                    # Pass 1: Get git's path/revision to hash mapping
                    with open(".git/cvs-revisions", "r") as fp:
                        for line in fp:
                            (path, rev, hashv) = line.split()
                            pathrev_to_hash[(path, rev)] = hashv
                    # Pass 2: get git's hash to (time,person) mapping
                    hash_to_action = {}
                    stamp_set = set({})
                    with popenOrDie("git log --all --format='%H %ct %ce'", "r") as fp:
                        for line in fp:
                            (hashv, ctime, cperson) = polystr(line).split()
                            stamp = (int(ctime), cperson)
                            if stamp in stamp_set:
                                complain("more than one commit matches %s!%s (%s)" \
                                         % (rfc3339(int(ctime)), cperson, hashv))
                                if stamp in hash_to_action:
                                    del hash_to_action[hashv]
                            else:
                                hash_to_action[hashv] = stamp
                                stamp_set.add(stamp)
                        # Pass 3: build a (time,person) to commit mapping
                        action_to_mark = {}
                        for commit in repo.commits():
                            action_to_mark[(commit.committer.date.timestamp, commit.committer.email)] = commit
                        # Pass 4: use it to set commit properties
                        for ((path, rev), value) in pathrev_to_hash.items():
                            if value in hash_to_action:
                                (ctime, cperson) = hash_to_action[value]
                                action_to_mark[(ctime, cperson)].legacyID = "CVS:%s:%s" % (path, rev)
                        del pathrev_to_hash
                        del hash_to_action
                        del stamp_set
        # We found a matching custom extractor
        if extractor:
            repo.stronghint=true
            streamer = newRepoStreamer(extractor)
            streamer.extract(repo, progress=verbose>0)
    finally:
        os.Chdir(here)
    return repo

class CriticalRegion:
    "Encapsulate operations to try and make us un-interruptible."
    # This number is magic. Python sets a much higher signal.NSIG
    # value, but under Linux the signal calls start to trigger
    # runtime errors at this value and above.
    NSIG = 32
    func __init__():
        self.handlers = None    # Pacifies pylint
    func __enter__():
        "Begin critical region."
        if debugEnable(debugCOMMANDS):
            complain("critical region begins...")
        # Alas that we lack sigblock support
        self.handlers = [None]*(CriticalRegion.NSIG+1)
        for sig in range(1, CriticalRegion.NSIG):
            if sig not in (signal.SIGKILL, signal.SIGSTOP):
                self.handlers[sig] = signal.signal(sig, signal.SIG_IGN)
    func __exit__(self, extype_unused, value_unused, traceback_unused):
        "End critical region."
        for sig in range(1, CriticalRegion.NSIG):
            if sig not in (signal.SIGKILL, signal.SIGSTOP):
                signal.signal(sig, self.handlers[sig])
        if debugEnable(debugCOMMANDS):
            complain("critical region ends.")
        return false

func rebuild_repo(repo, target, options, preferred):
    "Rebuild a repository from the captured state."
    if not target and repo.sourcedir:
        target = repo.sourcedir
    if target:
        target = os.path.abspath(target)
    else:
        raise Recoverable("no default destination for rebuild")
    vcs = preferred or repo.vcs
    if not vcs:
        raise Recoverable("please prefer a repo type first")
    if not hasattr(vcs, "exporter") or vcs.importer is None:
        raise Recoverable("%s repositories are supported for read only." \
                          % preferred.name)

    if os.path.join("refs", "heads", "master") not in repo.branchset():
        complain("repository has no branch named master. git will have no HEAD commit after the import; consider using the branch command to rename one of your branches to master.")

    # Create a new empty directory to do the rebuild in
    if not os.path.exists(target):
        staging = target
        try:
            os.mkdir(target)
        except OSError:
            raise Recoverable("target directory creation failed")
    else:
        staging = target + "-stage" + str(os.getpid())
        assert(os.path.isabs(target) and os.path.isabs(staging))
        try:
            os.mkdir(staging)
        except OSError:
            raise Recoverable("staging directory creation failed")

    # Try the rebuild in the empty staging directory
    here = os.getcwd()
    try:
        os.Chdir(staging)
        if vcs.initializer:
            do_or_die(vcs.initializer, "repository initialization")
        parameters = {"basename": os.path.basename(target)}
        if "%(tempfile)s" in vcs.importer:
            try:
                (tfdesc, tfname) = tempfile.mkstemp()
                assert tfdesc > -1    # pacify pylint
                with open(tfname, "wb") as tp:
                    repo.fast_export(range(len(repo)), make_wrapper(tp), options, progress=verbose>0, target=preferred)
                parameters["tempfile"] = tfname
                do_or_die(vcs.importer % parameters, "import")
            finally:
                os.remove(tfname)
                os.close(tfdesc)
        else:
            with popenOrDie(vcs.importer % parameters, "import", mode="w") as tp:
                repo.fast_export(range(len(repo)), make_wrapper(tp), options,
                                 target=preferred,
                                 progress=verbose>0)
        if repo.write_legacy:
            try:
                legacyfile = os.path.join(vcs.subdirectory, "legacy-map")
                with open(legacyfile, "wb") as wfp:
                    repo.write_legacymap(make_wrapper(wfp))
            except IOError:
                raise Recoverable("legacy-map file %s could not be written." \
                                  % legacyfile)

        if vcs.checkout:
            do_or_die(vcs.checkout, "repository_checkout")
        else:
            complain("checkout not supported for %s skipping" % vcs.name)

        if verbose:
            announce(debugSHOUT, "rebuild is complete.")

        os.Chdir(here)
        if staging != target:
            # Rebuild succeeded - make an empty backup directory
            backupcount = 1
            while true:
                savedir = target + (".~%d~" % backupcount)
                if os.path.exists(savedir):
                    backupcount += 1
                else:
                    break
            assert(os.path.abspath(savedir))
            os.mkdir(savedir)

            # This is a critical region.  Ignore all signals until we're done.
            with CriticalRegion():
                # Move the unmodified repo contents in target to the
                # backup directory.  Then move the staging contents to the
                # target directory.  Finally, restore designated files
                # from backup to target.
                for sub in os.listdir(target):
                    os.rename(os.path.join(target, sub),
                              os.path.join(savedir, sub))
                if verbose:
                    announce(debugSHOUT, "repo backed up to %s." % os.path.relpath(savedir))
                for sub in os.listdir(staging):
                    os.rename(os.path.join(staging, sub),
                              os.path.join(target, sub))
                if verbose:
                    announce(debugSHOUT, "modified repo moved to %s." % os.path.relpath(target))
            if repo.preserveSet:
                for sub in repo.preserveSet:
                    src = os.path.join(savedir, sub)
                    dst = os.path.join(target, sub)
                    if os.path.exists(src):
                        if os.path.exists(dst) and os.path.isdir(dst):
                            shutil.rmtree(dst)
                        if os.path.isdir(src):
                            shutil.copytree(src, dst)
                        else:
                            dstdir = os.path.dirname(dst)
                            if not os.path.exists(dstdir):
                                os.makedirs(dstdir)
                            shutil.copy2(src, dst)
                if verbose:
                    announce(debugSHOUT, "preserved files restored.")
            else if verbose:
                announce(debugSHOUT, "no preservations.")
    finally:
        os.Chdir(here)
        if staging != target:
            nuke(staging, "reposurgeon: removing staging directory")

func do_or_die(dcmd, legend=""):
    "Either execute a command or raise a fatal exception."
    if legend:
        legend = " "  + legend
    announce(debugCOMMANDS, "executing '%s'%s" % (dcmd, legend))
    try:
        retcode = subprocess.call(dcmd, shell=true, stderr=os.Stderr)
        if retcode < 0:
            raise Fatal("child was terminated by signal %d." % -retcode)
        else if retcode != 0:
            raise Fatal("child returned %d." % retcode)
    except (OSError, IOError) as e:
        raise Fatal("execution of %s%s failed: %s" % (dcmd, legend, e))

*/

func readFromProcess(command string) (*bufio.Reader, *exec.Cmd, error) {
	cmd := exec.Command("sh", "-c", command + " 2>&1")
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return nil, nil, err
	}
	r := bufio.NewReader(stdout)
	if debugEnable(debugCOMMANDS) {
		fmt.Fprintf(os.Stderr, "%s: reading from '%s'\n",
			rfc3339(time.Now()), command)
	}
	err = cmd.Start()
	if err != nil {
		return nil, nil, err
	}
	// Pass back cmd so we can call Wait on it and get the error status.
	return r, cmd, err
}

/*

class RepositoryList:
    "A repository list with selection and access by name."
    func __init__():
        self.repo = None
        self.repolist = []
        self.cut_index = None
    func chosen():
        return self.repo
    func choose(self, repo):
        self.repo = repo
    func unchoose():
        self.repo = None
    func reponames():
        "Return a list of the names of all repositories."
        return [r.name for r in self.repolist]
    func uniquify(self, name):
        "Uniquify a repo name in the repo list."
        if name.endswith(".fi"):
            name = name[:-3]
        else if name.endswith(".svn"):
            name = name[:-4]
        if name in self.reponames():
            # repo "foo" is #1
            seq = 2
            while name + str(seq) in self.reponames():
                seq += 1
            return name + str(seq)
        return name
    func repo_by_name(self, name):
        "Retrieve a repo by name."
        try:
            return self.repolist[self.reponames().index(name)]
        except ValueError:
            raise Recoverable("no repository named %s is loaded." % name)
    func remove_by_name(self, name):
        "Remove a repo by name."
        if self.repo and self.repo.name == name:
            self.unchoose()
        self.repolist.pop(self.reponames().index(name))
    func cut_conflict(self, early, late):
        "Apply a graph-coloring algorithm to see if the repo can be split here."
        self.cut_index = late.parentMarks().index(early.mark)
        late.removeParent(early)
        func do_color(commit, color):
            commit.color = color
            for fileop in commit.operations():
                if fileop.op == opM and fileop.ref != "inline":
                    blob = self.repo.find(fileop.ref)
                    assert isinstance(self.repo[blob], Blob)
                    self.repo[blob].colors.append(color)
        do_color(early, "early")
        do_color(late, "late")
        conflict = false
        keepgoing = true
        while keepgoing and not conflict:
            keepgoing = false
            for event in self.repo.commits():
                if event.color:
                    for neighbor in itertools.chain(event.parents(), event.children()):
                        if neighbor.color is None:
                            do_color(neighbor, event.color)
                            keepgoing = true
                            break
                        else if neighbor.color != event.color:
                            conflict = true
                            break
        return conflict
    func cut_clear(self, early, late):
        "Undo a cut operation and clear all colors."
        late.insertParent(self.cut_index, early.mark)
        for event in self.repo:
            if hasattr(event, "color"):
                event.color = None
            if hasattr(event, "colors"):
                event.colors = []
    func cut(self, early, late):
        "Attempt to topologically cut the selected repo."
        if self.cut_conflict(early, late):
            self.cut_clear(early, late)
            return false
        # Repo can be split, so we need to color tags
        for t in self.repo.events:
            if isinstance(t, Tag):
                for c in self.repo.events:
                    if isinstance(c, Commit):
                        if c is t.target:
                            t.color = c.color
        # Front events go with early segment, they'll be copied to late one.
        for event in self.repo.front_events():
            event.color = "early"
        assert all(hasattr(x, "color") or hasattr(x, "colors") or isinstance(x, Reset) for x in self.repo)
        # Resets are tricky.  One may have both colors.
        # Blobs can have both colors too, through references in
        # commits on both sides of the cut, but we took care
        # of that earlier.
        trackbranches = {"early": set(), "late": set()}
        for commit in self.repo.commits():
            if commit.color is None:
                complain("%s is uncolored!" % commit.mark)
            else:
                trackbranches[commit.color].add(commit.branch)
        # Now it's time to do the actual partitioning
        early = Repository(self.repo.name + "-early")
        os.mkdir(early.subdir())
        late = Repository(self.repo.name + "-late")
        os.mkdir(late.subdir())
        for event in self.repo:
            if isinstance(event, Reset):
                if event.ref in trackbranches["early"]:
                    early.addEvent(copy.copy(event))
                if event.ref in trackbranches["late"]:
                    late.addEvent(copy.copy(event))
            else if isinstance(event, Blob):
                if "early" in event.colors:
                    early.addEvent(event.clone(early))
                if "late" in event.colors:
                    late.addEvent(event.clone(late))
            else:
                if event.color == "early":
                    if hasattr(event, "moveto"):
                        event.moveto(early)
                    early.addEvent(event)
                else if event.color == "late":
                    if hasattr(event, "moveto"):
                        event.moveto(late)
                    late.addEvent(event)
                else:
                    # TODO: Someday, color passthroughs that aren't fronted.
                    raise Fatal("coloring algorithm failed on %s" % event)
        # Options and features may need to be copied to the late fragment.
        late.events = copy.copy(early.front_events()) + late.events
        late.declare_sequence_mutation("cut operation")
        # Add the split results to the repo list.
        self.repolist.append(early)
        self.repolist.append(late)
        self.repo.cleanup()
        self.remove_by_name(self.repo.name)
        return true
    func unite(self, factors, options):
        "Unite multiple repos into a union repo."
        for x in factors:
            if not list(x.commits()):
                raise Recoverable("empty factor %s" % x.name)
        factors.sort(key=operator.methodcaller("earliest"))
        roots = [x.earliest_commit() for x in factors]
        union = Repository("+".join(r.name for r in factors))
        os.mkdir(union.subdir())
        factors.reverse()
        persist = {}
        for factor in factors:
            persist = factor.uniquify(factor.name, persist)
        factors.reverse()
        for factor in factors:
            union.absorb(factor)
            self.remove_by_name(factor.name)
        # Renumber all events
        union.renumber()
        # Sort out the root grafts. The way we used to do this
        # involved sorting the union commits by timestamp, but this
        # fails because in real-world repos timestamp order may not
        # coincide with mark order - leading to "mark not defined"
        # errors from the importer at rebuild time. Instead we graft
        # each root just after the last commit in the dump sequence
        # with a date prior to it.  This method gives less intuitive
        # results, but at least means we never need to reorder
        # commits.
        for root in roots[1:]:
            # Get last commit such that it and all before it are earlier.
            # Never raises IndexError since union.earliest_commit() is root[0]
            # which satisfies earlier() thanks to factors sorting.
            eligible = collections.deque(
                itertools.takewhile(lambda e: root.when() > e.when(), union.commits()),
                    maxlen = 1)
            if eligible:
                most_recent = eligible.pop()
            else:
                # Weird case - can arise if you unite two or more copies
                # of the same commit.
                most_recent = union.earliest_commit()
            if most_recent.mark is None:
                # This should never happen either.
                raise Fatal("can't link to commit with no mark")
            root.addParentByMark(most_recent.mark)
            # We may not want files from the ancestral stock to persist
            # in the grafted branch unless they have modify ops in the branch
            # root.
            if "--prune" in options:
                deletes = []
                for path in most_recent.manifest():
                    fileop = FileOp()
                    fileop.construct("D", path)
                    deletes.append(fileop)
                root.setOperations(deletes + root.operations())
                root.canonicalize()
        # Put the result on the load list
        self.repolist.append(union)
        self.choose(union)
    func expunge(self, selection, matchers):
        "Expunge a set of files from the commits in the selection set."
        func digest(toklist):
            digested = []
            notagify = false
            for s in toklist:
                if s.startswith('/') and s.endswith('/'):
                    digested.append("(?:" + s[1:-1] + ")")
                else if s == '--notagify':
                    notagify = true
                else:
                    digested.append("^" + re.escape(s) + "$")
            return regexp.MustCompile("|".join(digested).encode('ascii')), notagify
        try:
            # First pass: compute fileop deletions
            alterations = []
            expunge, notagify = digest(matchers)
            for ei in selection:
                event = self.repo[ei]
                deletia = []
                if hasattr(event, "fileops"):
                    for (i, fileop) in enumerate(event.operations()):
                        if debugEnable(debugDELETE):
                            os.Stdout.write(polystr(fileop) + "\n")
                        if fileop.op in "DM":
                            if expunge.search(polybytes(fileop.path)):
                                deletia.append(i)
                        else if fileop.op in "RC":
                            fileop.sourcedelete = expunge.search(polybytes(fileop.source))
                            fileop.targetdelete = expunge.search(polybytes(fileop.target))
                            if fileop.sourcedelete:
                                deletia.append(i)
                                announce(debugSHOUT, "following %s of %s to %s" %
                                         (fileop.op,
                                          fileop.source,
                                          fileop.target))
                                if fileop.op == opR:
                                    try:
                                        matchers.remove("^" + fileop.source + "$")
                                    except ValueError:
                                        pass
                                matchers.append("^" + fileop.target + "$")
                                expunge, notagify = digest(matchers)
                            else if fileop.targetdelete:
                                if fileop.op == opR:
                                    fileop.op = opD
                                else if fileop.op == opC:
                                    deletia.append(i)
                                matchers.append("^" + fileop.target + "$")
                                expunge, notagify = digest(matchers)
                alterations.append(deletia)
        except re.error:
            raise Recoverable("you confused the regexp processor!")
        # Second pass: perform actual fileop expunges
        expunged = Repository(self.repo.name + "-expunges")
        expunged.seekstream = self.repo.seekstream
        expunged.makedir()
        for event in self.repo:
            event.deletehook = None
        for (ei, deletia) in zip(selection, alterations):
            if not deletia: continue
            event = self.repo[ei]
            keepers = []
            blobs = []
            for i in deletia:
                fileop = event.operations()[i]
                if fileop.op == opD:
                    keepers.append(fileop)
                    if verbose:
                        announce(debugSHOUT, "at %d, expunging D %s" \
                                 % (ei+1, fileop.path))
                else if fileop.op == opM:
                    keepers.append(fileop)
                    if fileop.ref != 'inline':
                        bi = self.repo.find(fileop.ref)
                        blob = self.repo[bi]
                        assert(isinstance(blob, Blob))
                        blobs.append(blob)
                    if verbose:
                        announce(debugSHOUT, "at %d, expunging M %s" \
                                 % (ei+1, fileop.path))
                else if fileop.op in (opR, opC):
                    assert(fileop.sourcedelete or fileop.targetdelete)
                    if fileop.sourcedelete and fileop.targetdelete:
                        keepers.append(fileop)
            event.setOperations([op for (i, op) in enumerate(event.operations())
                                  if i not in set(deletia)])
            event.invalidatePathsetCache()
            # If there are any keeper fileops, hang them them and
            # their blobs on keeps, cloning the commit() for them.
            if keepers:
                newevent = event.clone(expunged)
                newevent.setOperations(keepers)
                newevent.invalidatePathsetCache()
                for blob in blobs:
                    blob.deletehook = blob.clone(expunged)
                event.deletehook = newevent
        # Build the new repo and hook it into the load list
        expunged.events = copy.copy(self.repo.front_events())
        expunged.declare_sequence_mutation("expunge operation")
        expunged_branches = expunged.branchset()
        for event in self.repo:
            if event.deletehook:
                expunged.addEvent(event.deletehook)
                event.deletehook = None
            else if isinstance(event, Reset):
                if event.target is not None:
                    if event.target.deletehook:
                        expunged.addEvent(copy.deepcopy(event))
                else if isinstance(event, Reset) and event.ref in expunged_branches:
                    newreset = copy.copy(event)
                    newreset.repo = expunged
                    expunged.addEvent(newreset)
            else if isinstance(event, Tag) and \
                    event.target is not None and \
                    event.target.deletehook:
                expunged.addEvent(copy.deepcopy(event))
        for event in itertools.chain(self.repo.events, expunged.events):
            if hasattr(event, "deletehook"):
                delattr(event, "deletehook")
        expunged_marks = set(event.mark for event in expunged.events if hasattr(event, "mark"))
        for event in expunged.events:
            if hasattr(event, "parents"):
                # Parents still are Commits in the non-expunged repository
                # We use setParentMarks so that the correct parents are
                # searched in the expunged repository.
                event.setParentMarks(m for m in event.parentMarks()
                                         if m in expunged_marks)
        keeper_marks = set(event.mark for event in self.repo.events if hasattr(event, "mark"))
        for event in self.repo.events:
            if hasattr(event, "parents"):
                event.setParents([e for e in event.parents() if e.mark in keeper_marks])
        backreferences = collections.Counter()
        for event in self.repo.events:
            if isinstance(event, Commit):
                for fileop in event.operations():
                    if fileop.op == opM:
                        backreferences[fileop.ref] += 1
        # Now remove commits that no longer have fileops, and released blobs.
        # Announce events that will be deleted.
        if debugEnable(debugDELETE):
            to_delete = [i+1 for i,e in enumerate(self.repo.events)
                    if (isinstance(e, Blob) and not backreferences[e.mark])
                    or (isinstance(e, Commit) and not e.operations())]
            if not to_delete:
                announce(debugSHOUT, "deletion set is empty.")
            else:
                announce(debugSHOUT, "deleting blobs and empty commits %s" % to_delete)
            del to_delete
        # First delete the blobs.
        self.repo.events = [e for e in self.repo.events
                              if (not isinstance(e, Blob))
                              or backreferences[e.mark]]
        # Then tagify empty commits.
        self.repo.tagify_empty(canonicalize = false, create_tags = not notagify)
        # And tell we changed the manifests and the event sequence.
        self.repo.invalidateManifests()
        self.repo.declare_sequence_mutation("expunge cleanup")
        # At last, add the expunged repository to the loaded list.
        self.repolist.append(expunged)

func debug_lexer(f):
    """Function decorator to debug SelectionParser selection parsing methods."""
    @functools.wraps(f)
    func wrapper(self, *args):
        if not debugEnable(debugLEXER):
            return f(self, *args)
        try:
            stack = getattr(self, '_debug_lexer_stack')
        except AttributeError:
            stack = []
            setattr(self, '_debug_lexer_stack', stack)
        v = args[0] if self.line is None else ''
        s = ": {0}".format(repr(self.line)) if self.line is not None else ''
        announce(debugSHOUT, "{0}{1}({2}){3}".format(' ' * len(stack), f.__name__, v, s))
        stack.append(f.__name__)
        try:
            ret = f(self, *args)
        except Exception as e:
            ret = e
            raise
        finally:
            x = "lambda" if callable(ret) else repr(ret)
            s = ", left = {0}".format(repr(self.line)) if self.line is not None else ''
            announce(debugSHOUT, "{0}{1} <- {2}(){3}".format(
                ' ' * len(stack), x, stack.pop(), s))
        return ret
    return wrapper

class SelectionParser(object):
    """Selection set parser."""
    func __init__():
        self.line = None
        self.allitems = []
    func compile(self, line):
        "Compile expression; return remainder of line with expression removed."
        orig_line = line
        self.line = line
        machine = self.parse_expression()
        line = self.line.lstrip()
        self.line = None
        if line == orig_line.lstrip():
            machine = None
        return (machine, line)
    func evaluate(self, machine, allitems):
        """Evaluate a pre-compiled selection query against item list."""
        if machine is not None:
            self.allitems = allitems
            selection = list(machine(orderedIntSet(self.allitems)))
            self.allitems = None
            return selection
        return None
    func parse(self, line, allitems):
        """Parse selection; return remainder of line with selection removed."""
        machine, rest = self.compile(line)
        return (self.evaluate(machine, allitems), rest)
    func peek():
        return self.line and self.line[0]
    func pop():
        if not self.line:
            return ''
        else:
            c = self.line[0]
            self.line = self.line[1:]
            return c
    # this should only be called from a @debug_lexer function (it
    # depends on state set up by that decorator)
    func _debug_lexer(self, msg):
        """log a debug message from a lexer function"""
        if debugEnable(debugLEXER):
            stack = getattr(self, '_debug_lexer_stack')
            announce(debugSHOUT, "{0}{1}(): {2}".format(' ' * len(stack), stack[-1], msg))
    @debug_lexer
    func parse_expression():
        self.line = self.line.lstrip()
        return self.parse_disjunct()
    @debug_lexer
    func parse_disjunct():
        "Parse a disjunctive expression (| has lowest precedence)"
        self.line = self.line.lstrip()
        op = self.parse_conjunct()
        while true:
            self.line = self.line.lstrip()
            if self.peek() != '|':
                break
            self.pop()
            op2 = self.parse_conjunct()
            if op2 is None:
                break
            op = lambda p, lop=op, rop=op2: self.eval_disjunct(p, lop, rop)
        return op
    @debug_lexer
    func eval_disjunct(self, preselection, op1, op2):
        "Evaluate a disjunctive expression"
        selected = orderedIntSet()
        conjunct = op1(preselection)
        if conjunct is not None:
            selected |= conjunct
            conjunct = op2(preselection)
            if conjunct is not None:
                selected |= conjunct
        return selected
    @debug_lexer
    func parse_conjunct():
        "Parse a conjunctive expression (& has higher precedence)"
        self.line = self.line.lstrip()
        op = self.parse_term()
        if op is None:
            return lambda p: self.eval_conjunct(p, lambda q: None, None)
        while true:
            self.line = self.line.lstrip()
            if self.peek() != '&':
                break
            self.pop()
            op2 = self.parse_term()
            if op2 is None:
                break
            op = lambda p, lop=op, rop=op2: self.eval_conjunct(p, lop, rop)
        return op
    @debug_lexer
    func eval_conjunct(self, preselection, op1, op2):
        "Evaluate a conjunctive expression"
        # assign term before intersecting with preselection so
        # that the order specified by the user's first term is
        # preserved
        conjunct = op1(preselection)
        if conjunct is None:
            conjunct = preselection
        else:
            # this line is necessary if the user specified only
            # polyranges because eval_polyrange() ignores the
            # preselection
            conjunct &= preselection
            term = op2(preselection)
            if term is not None:
                conjunct &= term
        return conjunct
    @debug_lexer
    func parse_term():
        self.line = self.line.lstrip()
        if self.peek() == '~':
            self.pop()
            op = self.parse_expression()
            term = lambda p: self.eval_term_negate(p, op)
        else if self.peek() == '(':
            self.pop()
            term = self.parse_expression()
            self.line = self.line.lstrip()
            if self.peek() != ')':
                raise Recoverable("trailing junk on inner expression")
            else:
                self.pop()
        else:
            term = self.parse_visibility()
            if term is None:
                term = self.parse_polyrange()
                if term is None:
                    term = self.parse_textsearch()
                    if term is None:
                        term = self.parse_funcall()
        return term
    @debug_lexer
    func eval_term_negate(self, preselection, op):
        pacify_pylint(preselection)
        allitems = orderedIntSet(self.allitems)
        return allitems - orderedIntSet(op(allitems))
    @debug_lexer
    func parse_visibility():
        "Parse a visibility spec."
        self.line = self.line.lstrip()
        if not hasattr(self, 'visibility_typeletters'):
            visibility = None
        else if self.peek() != "=":
            visibility = None
        else:
            typeletters = self.visibility_typeletters()
            visible = set()
            self.pop()
            while self.peek() in typeletters:
                visible.add(self.pop())
            # We need a special check here because these expressions
            # could otherwise run onto the text part of the command.
            if self.peek() not in "()|& ":
                raise Recoverable("garbled type mask at %s" % repr(self.line))
            self._debug_lexer("visibility set is %s with %s left" % (
                visible, repr(self.line)))
            visibility = lambda p: self.eval_visibility(p, visible)
        return visibility
    @debug_lexer
    func eval_visibility(self, preselection, visible):
        "Evaluate a visibility spec."
        self._debug_lexer("visibility set is %s" % visible)
        typeletters = self.visibility_typeletters()
        visible = [typeletters[c] for c in visible]
        visibility = orderedIntSet()
        for i in preselection:
            if any(predicate(self.allitems[i]) for predicate in visible):
                visibility.add(i)
        return visibility
    func polyrange_initials():
        return ("0","1","2","3","4","5","6","7","8","9","$")
    func possible_polyrange():
        "Does the input look like a possible polyrange?"
        return self.peek() in self.polyrange_initials()
    @debug_lexer
    func parse_polyrange():
        "Parse a polyrange specification (list of intervals)."
        self.line = self.line.lstrip()
        if not self.possible_polyrange():
            polyrange = None
        else:
            selection = []
            while self.peek() in self.polyrange_initials() + (".", ","):
                sel = self.parse_atom()
                if sel is not None:
                    selection.append(sel)
            # Sanity checks
            if selection:
                if selection[0] == '..':
                    raise Recoverable("start of span is missing")
                if selection[-1] == '..':
                    raise Recoverable("incomplete range expression.")
            polyrange = lambda p: self.eval_polyrange(p, selection)
        return polyrange
    @debug_lexer
    func eval_polyrange(self, _preselection, ops):
        "Evaluate a polyrange specification (list of intervals)."
        # preselection is not used since it is perfectly legal to have range
        # bounds be outside of the reduced set.
        selection = []
        for op in ops:
            sel = op(_preselection)
            if sel is not None:
                selection.extend(sel)
        self._debug_lexer("location list is %s" % selection)
        # Resolve spans
        resolved = []
        last = None
        spanning = false
        for elt in selection:
            if elt == '..':
                if last is None:
                    raise Recoverable("start of span is missing")
                spanning = true
            else:
                if spanning:
                    resolved.extend(range(last+1, elt+1))
                    spanning = false
                else:
                    resolved.append(elt)
                last = elt
        selection = resolved
        self._debug_lexer("resolved list is %s" % selection)
        # Sanity checks
        if spanning:
            raise Recoverable("incomplete range expression.")
        for elt in selection:
            if elt < 0 or elt > len(self.allitems)-1:
                raise Recoverable("element %s out of range" % (elt+1))
        return orderedIntSet(selection)
    @debug_lexer
    func parse_atom():
        self.line = self.line.lstrip()
        selection = None
        # First, literal command numbers (1-origin)
        match = re.match(r"[0-9]+".encode('ascii'), polybytes(self.line))
        if match:
            number = polystr(match.group())
            selection = lambda p: [int(number)-1]
            self.line = self.line[len(number):]
        # $ means last commit, a la ed(1).
        else if self.peek() == "$":
            selection = lambda p: [len(self.allitems)-1]
            self.pop()
        # Comma just delimits a location spec
        else if self.peek() == ",":
            self.pop()
        # Following ".." means a span
        else if self.line[:2] == "..":
            selection = lambda p: [".."]
            self.line = self.line[2:]
        else if self.peek() == ".":
            raise Recoverable("malformed span")
        return selection
    @debug_lexer
    func parse_textsearch():
        "Parse a text search specification."
        self.line = self.line.lstrip()
        if not hasattr(self, 'eval_textsearch'):
            return None
        if self.peek() != '/':
            return None
        else if '/' not in self.line[1:]:
            raise Recoverable("malformed text search specifier")
        else:
            assert(self.pop() == '/')
            endat = self.line.index('/')
            try:
                match =  self.line[:endat]
                if str is not bytes:
                    match = match.encode(master_encoding)
                search = regexp.MustCompile(match).search
            except re.error:
                raise Recoverable("invalid regular expression")
            self.line = self.line[endat+1:]
            modifiers = set()
            while self.line and self.line[0].isalpha():
                modifiers.add(self.line[0])
                self.line = self.line[1:]
            return lambda p: self.eval_textsearch(p, search, modifiers)
        return None	# Deconfuse pylint
    @debug_lexer
    func parse_funcall():
        "Parse a function call."
        self.line = self.line.lstrip()
        if self.peek() != "@":
            return None
        self.pop()
        funname = ""
        while self.peek().isalpha() or self.peek() == '_':
            funname += self.pop()
        if not funname or self.peek() != '(':
            return None
        # The '(' and ')' after the function name are different than
        # the parentheses used to override operator precedence, so we
        # must handle them here.  If we let parse_expression() handle
        # the parentheses, it will process characters beyond the
        # closing parenthesis as if they were part of the function's
        # argument.  For example, if we let parse_expression() handle
        # the parentheses, then the following expression:
        #     @max(~$)|$
        # would be processed as if this was the argument to max():
        #     (~$)|$
        # when the actual argument is:
        #     ~$
        self.pop()
        subarg = self.parse_expression()
        self.line = self.line.lstrip()
        if self.peek() != ')':
            raise Recoverable("missing close parenthesis for function call")
        self.pop()
        try:
            func = getattr(self, funname + "_handler")
        except AttributeError:
            raise Recoverable("no such function as @%s()" % funname)
        return lambda p: func(subarg(p))
    @debug_lexer
    func min_handler(self, subarg):
        "Minimum member of a selection set."
        try:
            return orderedIntSet([min(subarg)])
        except ValueError:
            raise Recoverable("cannot take minimum of empty set")
    @debug_lexer
    func max_handler(self, subarg):
        "Maximum member of a selection set."
        try:
            return orderedIntSet([max(subarg)])
        except ValueError:
            raise Recoverable("cannot take maximum of empty set")
    @debug_lexer
    func amp_handler(self, subarg):
        "Amplify - map empty set to empty, nonempty set to all."
        if subarg:
            return orderedIntSet(self.allitems)
        else:
            return subarg
    @debug_lexer
    func pre_handler(self, subarg):
        "Predecessors function; all elements previous to argument set."
        if not subarg or min(subarg) == 0:
            return orderedIntSet()
        else:
            return orderedIntSet(range(0, min(subarg)))
    @debug_lexer
    func suc_handler(self, subarg):
        "Successors function; all elements following argument set."
        if not subarg or max(subarg) >= len(self.allitems) - 1:
            return orderedIntSet()
        else:
            return orderedIntSet(range(max(subarg)+1, len(self.allitems)))
    @debug_lexer
    func srt_handler(self, subarg):
        "Sort the argument set."
        return orderedIntSet(sorted(subarg))
    func rev_handler(self, subarg):
        "Reverse the argument set."
        return list(reversed(subarg))

class AttributionEditor(object):
    "Inspect and edit committer, author, tagger attributions."
    class A(object):
        func __init__(self, attribution):
            self.attribution = attribution
        func __getattr__(self, name):
            if name in self.__dict__:
                return super(AttributionEditor.A, self).__getattr__(name)
            return getattr(self.attribution, name)
        func String():
            return self.attribution.String()
        func desc():
            return self.__class__.__name__.lower()
        func assign(self, name, emailaddr, date):
            if name is not None:
                self.attribution.name = name
            if emailaddr is not None:
                self.attribution.email = emailaddr
            if date is not None:
                self.attribution.date = date
        func delete(self, event):
            pacify_pylint(event)
            raise Recoverable("unable to delete %s (1 needed)" % self.desc())
        func insert(self, after, event, newattr):
            pacify_pylint(after)
            pacify_pylint(event)
            pacify_pylint(newattr)
            raise Recoverable("unable to add %s (only 1 allowed)" % self.desc())
    class Committer(A):
        pass
    class Author(A):
        func __init__(self, attribution, pos):
            AttributionEditor.A.__init__(self, attribution)
            self.pos = pos
        func delete(self, event):
            del event.authors[self.pos]
            if not event.authors:
                event.authors = None
        func insert(self, after, event, newattr):
            event.authors.insert(self.pos + (1 if after else 0), newattr)
    class Tagger(A):
        pass
    class SelParser(SelectionParser):
        func __init__():
            SelectionParser.__init__()
            self.attributions = None
        func evaluate(self, machine, attributions):
            self.attributions = attributions
            sel = super(AttributionEditor.SelParser, self).evaluate(
                machine, range(len(self.attributions)))
            self.attributions = None
            return sel
        func visibility_typeletters():
            return {
                "C" : lambda i: isinstance(self.attributions[i], AttributionEditor.Committer),
                "A" : lambda i: isinstance(self.attributions[i], AttributionEditor.Author),
                "T" : lambda i: isinstance(self.attributions[i], AttributionEditor.Tagger)
            }
        @debug_lexer
        func eval_textsearch(self, preselection, search, modifiers):
            if not modifiers:
                check_name = check_email = true
            else:
                check_name = check_email = false
                for m in modifiers:
                    if m == 'n':
                        check_name = true
                    else if m == 'e':
                        check_email = true
                    else:
                        raise Recoverable("unknown textsearch flag")
            found = orderedIntSet()
            for i in preselection:
                a = self.attributions[i]
                if ((check_name and search(polybytes(a.name))) or
                    (check_email and search(polybytes(a.email)))):
                    found.add(i)
            return found
    func __init__(self, events, machine):
        self.events = events
        self.machine = machine
    func attributions(self, event):
        try:
            v = [AttributionEditor.Committer(event.committer)]
            if event.authors is not None:
                v.extend([AttributionEditor.Author(a,i)
                          for i,a in enumerate(event.authors)])
        except AttributeError:
            v = [AttributionEditor.Tagger(event.tagger)]
        return v
    func indices(self, v, types):
        return [i for i,x in enumerate(v) if isinstance(x, types)]
    func mark(self, event):
        try:
            mark = event.mark or '-'
        except AttributeError:
            mark = '-'
        return mark
    func apply(self, f, **extra):
        for i, event in self.events:
            attributions = self.attributions(event)
            try:
                sel = self.machine(attributions)
            except Recoverable as e:
                raise Recoverable("%s (event %d, mark %s)" %
                                  (e.msg, i+1, self.mark(event)))
            f(event=event, attributions=attributions, sel=sel, eventno=i, **extra)
    func infer(self, attributions, preferred, name, emailaddr, date):
        if name is None and emailaddr is None:
            raise Recoverable("unable to infer missing name and email")
        if preferred is not None:
            attributions = [attributions[preferred]] + attributions
        if name is None:
            for a in attributions:
                if a.email == emailaddr:
                    name = a.name
                    break
            if name is None:
                raise Recoverable("unable to infer name for %s" % emailaddr)
        if emailaddr is None:
            for a in attributions:
                if a.name == name:
                    emailaddr = a.email
                    break
            if emailaddr is None:
                raise Recoverable("unable to infer email for %s" % name)
        if date is None:
            if attributions:
                date = attributions[0].date
            else:
                raise Recoverable("unable to infer date")
        return name, emailaddr, date
    func glean(self, args):
        name = emailaddr = date = None
        for x in args:
            try:
                d = Date(x)
                if date is not None:
                    raise Recoverable("extra timestamp: %s" % x)
                date = d
                continue
            except Fatal:
                pass
            if '@' in x:
                if emailaddr is not None:
                    raise Recoverable("extra email: %s" % x)
                emailaddr = x
            else:
                if name is not None:
                    raise Recoverable("extra name: %s" % x)
                name = x
        return name, emailaddr, date
    func inspect(self, stdout):
        self.apply(self.do_inspect, stdout=stdout)
    func do_inspect(self, eventno, event, attributions, sel, stdout):
        mark = self.mark(event)
        if sel is None:
            sel = range(len(attributions))
        for i in sel:
            a = attributions[i]
            stdout.write("%6d %6s %2d:%-9s %s\n" % (eventno+1, mark, i+1, a.desc(), a))
    func assign(self, args):
        name, emailaddr, date = self.glean(args)
        self.apply(self.do_assign, name=name, emailaddr=emailaddr, date=date)
    func do_assign(self, attributions, sel, name, emailaddr, date, **extra):
        pacify_pylint(extra)
        if sel is None:
            raise Recoverable("no attribution selected")
        for i in sel:
            attributions[i].assign(name, emailaddr, date)
    func delete():
        self.apply(self.do_delete)
    func do_delete(self, event, attributions, sel, **extra):
        pacify_pylint(extra)
        if sel is None:
            sel = self.indices(attributions, AttributionEditor.Author)
        for i in sorted(sel, reverse=true):
            attributions[i].delete(event)
    func insert(self, args, after):
        name, emailaddr, date = self.glean(args)
        self.apply(self.do_insert, after=after, name=name, emailaddr=emailaddr, date=date)
    func do_insert(self, event, attributions, sel, after, name, emailaddr, date, **extra):
        pacify_pylint(extra)
        if not sel:
            sel = self.indices(attributions, AttributionEditor.Author)
        basis = sel[-1 if after else 0] if sel else None
        a = Attribution()
        a.name, a.email, a.date = self.infer(
            attributions, basis, name, emailaddr, date)
        if basis is not None:
            attributions[basis].insert(after, event, a)
        else:
            try:
                assert(event.authors is None)
                event.authors = [a]
            except AttributeError:
                raise Recoverable("unable to add author to %s" %
                                  event.__class__.__name__.lower())
    func resolve(self, stdout, label):
        self.apply(self.do_resolve, stdout=stdout, label=label)
    func do_resolve(self, eventno, event, sel, stdout, label, **extra):
        pacify_pylint(extra)
        if sel is None:
            raise Recoverable("no attribution selected")
        if label:
            stdout.write("%s: " % label)
        stdout.write("%6d %6s %s\n" %
                     (eventno+1, self.mark(event), [x+1 for x in sel]))

class RepoSurgeon(cmd.Cmd, RepositoryList, SelectionParser):
    "Repository surgeon command interpreter."
    OptionFlags = (
        ("canonicalize", """\
    If set, import stream reads and mailbox_in and edit will canonicalize
comments by replacing CR-LF with LF, stripping leading and trailing whitespace,
and then appending a LF.
"""),
        ("compressblobs", """\
    Use compression for on-disk copies of blobs. Accepts an increase
in repository read and write time in order to reduce the amount of
disk space required while editing; this may be useful for large
repositories. No effect if the edit input was a dump stream; in that
case, reposurgeon doesn't make on-disk blob copies at all (it points
into sections of the input stream instead).
"""),
        ("testmode", """\
Disable some features that cause output to be vary depending on wall time
and the ID of the invoking user. Use in regression-test loads.
"""),
        ("bigprofile", """\
Extra profiling for large repositories.  Mainly of interest to reposurgeon
developers.
"""),
        )
    unclean = regexp.MustCompile("[^\n]*\n[^\n]".encode('ascii'))
    class LineParse:
        "Parse a command line implementing shell-like syntax."
        func __init__(self, interpreter, line, capabilities=None):
            self.interpreter = interpreter
            self.line = line
            self.capabilities = capabilities or []
            self.stdin = sys.stdin
            self.infile = None
            self.stdout = os.Stdout
            self.outfile = None
            self.redirected = false
            self.options = set([])
            self.closem = []
        func __enter__():
            # Input redirection
            m = re.search(r"<\S+".encode('ascii'), polybytes(self.line))
            if m:
                if "stdin" not in self.capabilities:
                    raise Recoverable("no support for < redirection")
                self.infile = polystr(m.group(0)[1:])
                if self.infile and self.infile != '-':
                    try:
                        self.stdin = make_wrapper(open(self.infile, "rb"))
                        self.closem.append(self.stdin)
                    except (IOError, OSError):
                        raise Recoverable("can't open %s for read" \
                                          % self.infile)
                self.line = self.line[:m.start(0)] + self.line[m.end(0)+1:]
                self.redirected = true
            # Output redirection
            m = re.search(r">>?\S+".encode('ascii'), polybytes(self.line))
            if m:
                if "stdout" not in self.capabilities:
                    raise Recoverable("no support for > redirection")
                self.outfile = polystr(m.group(0)[m.group(0).count(b'>'):])
                if self.outfile and self.outfile != '-':
                    if os.path.exists(self.outfile) and os.path.isdir(self.outfile):
                        raise Recoverable("can't redirect output to directory")
                    try:
                        RepoSurgeon.write_notify(self.interpreter, self.outfile)
                        if m.group(0).count(b'>') > 1:
                            mode = "ab"
                        else:
                            mode = "wb"
                        self.stdout = make_wrapper(open(self.outfile, mode))
                        self.closem.append(self.stdout)
                    except (IOError, OSError):
                        raise Recoverable("can't open %s for write" \
                                          % self.outfile)
                self.line = self.line[:m.start(0)] + self.line[m.end(0)+1:]
                self.redirected = true
            # Options
            while true:
                m = re.search(r"--\S+".encode('ascii'), polybytes(self.line))
                if not m:
                    break
                else:
                    self.options.add(polystr(m.group(0).strip()))
                    self.line = polystr(polybytes(self.line)[:m.start(0)] + polybytes(self.line)[m.end(0)+1:])
            # Dash redirection
            if not self.redirected and self.line.strip() == '-':
                if "stdin" not in self.capabilities and "stdout" not in self.capabilities:
                    raise Recoverable("no support for - redirection")
                else:
                    self.line = ""
                    self.redirected = true
            self.line = self.line.strip()
            return self
        func __exit__(self, extype_unused, value_unused, traceback_unused):
            for fp in self.closem:
                fp.close()
        func tokens():
            "Return the argument token list after the parse for redirects."
            return self.line.split()
        func optval(self, optname):
            for option in self.options:
                if option.startswith(optname + "="):
                    return int(option.split("=")[0])
            return None
    func write_notify(self, filename):
        "Unstreamify any repo about to be written."
        for repo in self.repolist:
            if repo.name == filename or repo.name + "." in filename:
                for event in repo.events:
                    if isinstance(event, Blob):
                        event.materialize()
    func __init__():
        cmd.Cmd.__init__()
        RepositoryList.__init__()
        SelectionParser.__init__()
        self.use_rawinput = true
        self.echo = 0
        self.prompt = "reposurgeon% "
        self.prompt_format = "reposurgeon%% "
        self.preferred = None
        self.ignorename = None
        self.selection = []
        self.history = []
        self.callstack = []
        self.definitions = {}
        self.profile_log = None
        self.capture = None
        self.start_time = time.time()
        for option in dict(RepoSurgeon.OptionFlags):
            globalOptions[option] = []
        globalOptions['svn_branchify'] = ['trunk', 'tags/*', 'branches/*', '*']
        globalOptions['svn_branchify_mapping'] = []
    #
    # Housekeeping hooks.
    #
    func onecmd(self, line):
        "Execute one command, fielding interrupts for recoverable exceptions."
        try:
            cmd.Cmd.onecmd(self, line)
        except Recoverable as e:
            complain(e.msg)
    func postcmd(self, _unused, line):
        try:
            self.prompt = self.prompt_format % {"chosen":self.chosen() and self.chosen().name}
        except ValueError:
            announce(debugSHOUT, "bad prompt format - remember, literal % must be doubled.")
        if line == "EOF":
            return true
        return false
    func emptyline():
        pass
    func precmd(self, line):
        "Pre-command hook."
        if self.capture is not None:
            if line.startswith("}"):
                self.capture = None
            else:
                self.capture.append(line)
            return ""
        self.history.append(line.rstrip())
        if self.echo:
            os.Stdout.write(line.rstrip()+"\n")
        self.selection = None
        if line.startswith("#"):
            return ""
        m = regexp.MustCompile("\s+#".encode('ascii'))
        if m:
            line = polystr(m.split(polybytes(line))[0])
        # This is the only place in the implementation that knows
        # whether the syntax is VSO or SVO.
        if self.chosen():
            try:
                line = self.set_selection_set(line)
            except Recoverable as e:
                complain(e.msg)
                line = ""
        return line
    func do_shell(self, line):
        "Execute a shell command."
        os.Stdout.Flush()
        os.Stderr.Flush()
        if os.system(line):
            raise Recoverable("'shell %s' returned error." % line)
    func do_EOF(self, _unused):
        "Terminate reposurgeon."
        os.Stdout.write("\n")
        return true
    func cleanup():
        "Tell all the repos we're holding to clean up."
        announce(debugSHUFFLE, "interpreter cleanup called.")
        for repo in self.repolist:
            repo.cleanup()
    func selected(self, types=None):
        "Iterate over the selection set."
        return self.chosen().iterevents(indices=self.selection, types=types)
    #
    # The selection-language parsing code starts here.
    #
    func set_selection_set(self, line):
        "Implement object-selection syntax."
        # Returns the line with the selection removed
        self.selection = None
        if not self.chosen():
            return line
        try:
            if self.chosen().named(line):
                line = "<" + line + ">"
        except Recoverable:
            pass
        self.selection, line = self.parse(line, self.chosen().all())
        return line
    @debug_lexer
    func parse_expression():
        value = super(RepoSurgeon, self).parse_expression()
        while true:
            c = self.peek()
            if c != '?':
                break
            self.pop()
            value = lambda p, orig=value: self.eval_neighborhood(p, orig)
        return value
    @debug_lexer
    func eval_neighborhood(self, preselection, subject):
        value = subject(preselection)
        add_set = orderedIntSet()
        remove_set = orderedIntSet()
        for ei in value:
            event = self.chosen().events[ei]
            if isinstance(event, Commit):
                for parent in event.parents():
                    add_set.add(self.chosen().find(parent.mark))
                for child in event.children():
                    add_set.add(self.chosen().find(child.mark))
            else if isinstance(event, Blob):
                remove_set.add(ei) # Don't select the blob itself
                for i in preselection:
                    event2 = self.chosen().events[i]
                    if isinstance(event2, Commit):
                        for fileop in event2.operations():
                            if fileop.op == opM and fileop.ref==event.mark:
                                add_set.add(i)
            else if isinstance(event, (Tag, Reset)):
                if event.target:
                    add_set.add(event.target.index())
        value |= add_set
        value -= remove_set
        value = list(value)
        value.sort()
        value = orderedIntSet(value)
        return value
    @debug_lexer
    func parse_term():
        term = super(RepoSurgeon, self).parse_term()
        if term is None:
            term = self.parse_pathset()
        return term
    func has_reference(self, event):
        "Does an event contain something that looks like a legacy reference?"
        self.chosen().parse_dollar_cookies()
        if hasattr(event, "comment"):
            text = event.comment
        else if hasattr(event, "text"):
            text = event.text
        else:
            return false
        if self.chosen().vcs is None or not self.chosen().vcs.cookies:
            return false
        for pattern in self.chosen().vcs.cookies:
            if re.search(pattern.encode('ascii'), polybytes(text)):
                return true
        return false
    func visibility_typeletters():
        func e(i):
            return self.chosen().events[i]
        # Available: AEGJKQSVWXY
        return {
            "B" : lambda i: isinstance(e(i), Blob),
            "C" : lambda i: isinstance(e(i), Commit),
            "T" : lambda i: isinstance(e(i), Tag),
            "R" : lambda i: isinstance(e(i), Reset),
            "P" : lambda i: isinstance(e(i), Passthrough),
            "H" : lambda i: isinstance(e(i), Commit) and not e(i).hasChildren(),
            "O" : lambda i: isinstance(e(i), Commit) and not e(i).hasParents(),
            "U" : lambda i: isinstance(e(i), Commit) and e(i).hasCallouts(),
            "Z" : lambda i: isinstance(e(i), Commit) and len(e(i).operations())==0,
            "M" : lambda i: isinstance(e(i), Commit) and len(e(i).parents()) > 1,
            "F" : lambda i: isinstance(e(i), Commit) and len(e(i).children()) > 1,
            "L" : lambda i: isinstance(e(i), Commit) and RepoSurgeon.unclean.match(polybytes(e(i).comment)),
            "I" : lambda i: hasattr(e(i), 'undecodable') and e(i).undecodable(),
            "D" : lambda i: hasattr(e(i), 'alldeletes') and e(i).alldeletes(),
            "N" : lambda i: self.has_reference(e(i))
            }
    func polyrange_initials():
        return super(RepoSurgeon, self).polyrange_initials() + (":", "<")
    func possible_polyrange():
        "Does the input look like a possible polyrange?"
        if not super(RepoSurgeon, self).possible_polyrange():
            return false
        # Avoid having an input redirect mistaken for the start of a literal.
        # This might break if a command can ever have both input and output
        # redirects.
        if self.peek() == "<" and ">" not in self.line:
            return false
        return true
    @debug_lexer
    func parse_atom():
        selection = super(RepoSurgeon, self).parse_atom()
        if selection is None:
            # Mark references
            match = re.match(r":[0-9]+".encode('ascii'), polybytes(self.line))
            if match:
                markref = polystr(match.group())
                self.line = self.line[len(markref):]
                selection = lambda p: self.eval_atom_mark(p, markref)
            else if self.peek() == ':':
                raise Recoverable("malformed mark")
            else if self.peek() == "<":
                self.pop()
                closer = self.line.find('>')
                if closer == -1:
                    raise Recoverable("reference improperly terminated. '%s'" % self.line)
                ref = self.line[:closer]
                self.line = self.line[closer+1:]
                selection = lambda p: self.eval_atom_ref(p, ref)
        return selection
    @debug_lexer
    func eval_atom_mark(self, preselection, markref):
        pacify_pylint(preselection)
        selection = []
        for (i, event) in enumerate(self.chosen()):
            if hasattr(event, "mark") and event.mark == markref:
                selection.append(i)
                break
            else if hasattr(event, "committish") and event.committish == markref:
                selection.append(i)
                break
        else:
            raise Recoverable("mark %s not found." % markref)
        return selection
    @debug_lexer
    func eval_atom_ref(self, preselection, ref):
        pacify_pylint(preselection)
        selection = []
        lookup = self.chosen().named(ref)
        if lookup:
            # Choose to include *all* commits matching the date.
            # Alas, results in unfortunate behavior when a date
            # with multiple commits ends a span.
            selection += list(lookup)
        else:
            raise Recoverable("couldn't match a name at <%s>" % ref)
        return selection
    @debug_lexer
    func eval_textsearch(self, preselection, search, modifiers):
        "Perform a text search of items."
        matchers = orderedIntSet()
        searchable_attrs = {"a":"author",          # commit
                            "b":"branch",          # commit
                            "c":"comment",         # commit or tag
                            "C":"committer",       # commit
                            "r":"committish",      # tag or reset
                            "p":"text",            # passthrough
                            "t":"tagger",          # tag
                            "n":"name"             # tag
                            }
        search_in = searchable_attrs.values()
        extractor_lambdas = {
            "author": lambda x: x.authors[0].who(),
            "branch": lambda x: x.branch,
            "comment": lambda x: x.comment,
            "committer": lambda x: x.committer.who(),
            "committish": lambda x: x.committish,
            "text": lambda x: x.text,
            "tagger": lambda x: x.tagger.who(),
            "name": lambda x: x.name,
            }
        check_authors = false
        check_blobs = false
        check_branch = false
        if modifiers:
            search_in = []
            for m in modifiers:
                if m == 'a':
                    check_authors = true
                else if m == 'B':
                    check_blobs = true
                else if m in searchable_attrs.keys():
                    search_in.append(searchable_attrs[m])
                    if m == 'b':
                        check_branch = true
                else:
                    raise Recoverable("unknown textsearch flag")
        for i in preselection:
            e = self.chosen().events[i]
            if check_branch:
                if isinstance(e, Tag):
                    e = e.target
                else if isinstance(e, Blob):
                    events = self.chosen().events
                    for ci in range(i, len(events)):
                        possible = events[ci]
                        if isinstance(possible, Commit) and possible.references(e.mark):
                            # FIXME: Won't find multiple references
                            e = possible
                            break
            for searchable in search_in:
                if hasattr(e, searchable):
                    key = extractor_lambdas[searchable](e)
                    if key is not None and search(polybytes(key)):
                        matchers.add(i)
            if check_authors and isinstance(e, Commit):
                for ai in range(len(e.authors)):
                    if search(polybytes(str(e.authors[ai]))):
                        matchers.add(i)
                        break
            if check_blobs and isinstance(e, Blob) and search(polybytes(e.getContent())):
                matchers.add(i)
        return matchers
    @debug_lexer
    func parse_pathset():
        "Parse a path name to evaluate the set of commits that refer to it."
        self.line = self.line.lstrip()
        if self.peek() != "[":
            return None
        self.pop()
        depth = 1
        for (i, c) in enumerate(self.line):
            if c == '[':
                depth += 1
            else if c == ']':
                depth -= 1
            if depth == 0:
                matcher = self.line[:i]
                self.line = self.line[i+1:]
                break
        else:
            raise Recoverable("malformed path matcher")
        if matcher.startswith('/'):
            flags = set()
            while matcher[-1] in ("a", "c", "D", "M", "R", "C", "N"):
                flags.add(matcher[-1])
                matcher = matcher[:-1]
            if matcher[-1] != '/':
                raise Recoverable("regexp matcher missing trailing /")
            try:
                search = regexp.MustCompile(matcher[1:-1].encode('ascii')).search
            except re.error:
                raise Recoverable("invalid regular expression")
            return lambda p: self.eval_pathset_regex(p, search, flags)
        else:
            return lambda p: self.eval_pathset(p, matcher)
    @debug_lexer
    func eval_pathset_regex(self, preselection, search, flags):
        "Resolve a path regex to the set of commits that refer to it."
        chosen = self.chosen()
        if "c" in flags:
            return self.eval_pathset_full(search,
                                          preselection,
                                          "a" in flags)
        all_or_any = all if "a" in flags else any
        if "a" in flags:
            flags.remove("a")
        hits = orderedIntSet()
        for (i, event) in chosen.iterevents(
                        preselection, types=(Commit, Blob)):
            if all_or_any(itertools.imap(search, itertools.imap(polybytes, event.paths(flags)))):
                hits.add(i)
        return hits
    @debug_lexer
    func eval_pathset(self, preselection, matcher):
        "Resolve a path name to the set of commits that refer to it."
        chosen = self.chosen()
        return orderedIntSet(
            i for (i, event) in chosen.iterevents(
                preselection, types=(Commit, Blob))
            if matcher in event.paths())
    func eval_pathset_full(self, match_condition,
                                preselection,
                                match_all):
        # Try to match a regex in the trees. For each commit we remember
        # only the part of the tree that matches the regex. In most cases
        # it is a lot less memory and CPU hungry than running regexes on
        # the full commit manifests. In the match_all case we instead
        # select commits that nowhere match the opposite condition.
        match = match_condition
        if match_all:
            match = lambda p: not match_condition(p)
        match_trees = {}
        result = orderedIntSet()
        last_event = max(preselection)
        for (i, event) in self.chosen().iterevents(types=Commit):
            if i > last_event: break
            try:
                parent = event.parents()[0]
            except IndexError:
                tree = PathMap()
            else:
                tree = match_trees[parent.mark].snapshot()
            for fileop in event.operations():
                if fileop.op == opM and match(polybytes(fileop.path)):
                    tree[fileop.path] = true
                else if fileop.op in (opC, opR) and match(polybytes(fileop.target)):
                    tree[fileop.target] = true
                else if fileop.op == opD and match(polybytes(fileop.path)):
                    del tree[fileop.path]
                else if fileop.op == opR and match(polybytes(fileop.source)):
                    del tree[fileop.source]
                else if fileop.op == 'deleteall':
                    tree = PathMap()
            match_trees[event.mark] = tree
            if (not tree) == match_all:
                result.add(i)
        return result
    @debug_lexer
    func chn_handler(self, subarg):
        "All children of commits in the selection set."
        return self._accumulate_commits(subarg,
                                        operator.methodcaller("children"),
                                        recurse=false)
    @debug_lexer
    func dsc_handler(self, subarg):
        "All descendants of a selection set, recursively."
        return self._accumulate_commits(subarg,
                                        operator.methodcaller("children"))
    @debug_lexer
    func par_handler(self, subarg):
        "All parents of a selection set."
        return self._accumulate_commits(subarg,
                                        operator.methodcaller("parents"),
                                        recurse=false)
    @debug_lexer
    func anc_handler(self, subarg):
        "All ancestors of a selection set, recursively."
        return self._accumulate_commits(subarg,
                                        operator.methodcaller("parents"))
    func _accumulate_commits(self, subarg, operation, recurse=true):
        repo = self.chosen()
        result = orderedIntSet()
        subiter = repo.iterevents(subarg, types=Commit)
        if not recurse:
            for _, commit in subiter:
                result.update(itertools.imap(repo.index, operation(commit)))
            return result
        result |= subarg
        # Populate the queue with selected commits
        queue = collections.deque(itertools.imap(
                            operator.itemgetter(1),
                            subiter))
        # Breadth-first traversal of the graph
        while queue:
            for commit in operation(queue.popleft()):
                ind = repo.index(commit)
                if ind not in result:
                    result.add(ind)
                    queue.append(commit)
        return result

    #
    # Helpers
    #
    func report_select(self, line, method, optargs=()):
        "Generate a repository report on all objects with a specified method."
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            if self.selection is None and parse.line.strip():
                parse.line = self.set_selection_set(parse.line)
            else if self.selection is None:
                self.selection = self.chosen().all()
            for i, event in self.selected():
                if hasattr(event, method):
                    summary = getattr(event, method)(*((parse, i,)+optargs))
                    if summary:
                        if summary.endswith("\n"):
                            parse.stdout.write(summary)
                        else:
                            parse.stdout.write(summary + "\n")
    @staticmethod
    func pop_token(line):
        "Grab a whitespace-delimited token from the front of the line."
        tok = ""
        line = line.lstrip()
        while true:
            if not line or line[0].isspace():
                break
            else:
                tok += line[0]
                line = line[1:]
        line = line.lstrip()
        return (tok, line)
    func edit(self, selection, line):
        # Mailboxize and edit the non-blobs in the selection
        # Assumes that self.chosen() and selection are not None
        with RepoSurgeon.LineParse(self, line, capabilities=["stdin", "stdout"]) as parse:
            editor = parse.line or os.getenv("EDITOR")
            if not editor:
                complain("you have not specified an editor and $EDITOR is not set")
                # Fallback on /usr/bin/editor on Debian and derivatives.
                # See https://www.debian.org/doc/debian-policy/#editors-and-pagers
                editor = "/usr/bin/editor"
                editor_real = os.path.realpath(editor)
                if os.path.islink(editor) and os.path.exists(editor_real):
                    complain("using %s -> %s instead" % (editor, editor_real))
                else:
                    return
            # Special case: user selected a single blob
            if len(selection) == 1:
                singleton = self.chosen()[selection[0]]
                if isinstance(singleton, Blob):
                    func find_successor(event, path):
                        here = []
                        for child in event.children():
                            for fileop in child.operations():
                                if fileop.op == opM and fileop.path == path:
                                    here.append(child.mark)
                            here += find_successor(child, path)
                        return here
                    for event in self.chosen().commits():
                        for fileop in event.operations():
                            if fileop.op == opM and fileop.ref == singleton.mark:
                                if len(find_successor(event, fileop.path)) > 0:
                                    complain("beware: not the last 'M %s' on its branch" % fileop.path)
                                break
                    os.system(editor + " " + singleton.materialize())
                    return
                # Fall through
            (tfdesc, tfname) = tempfile.mkstemp()
            assert tfdesc > -1    # pacify pylint
            try:
                with open(tfname, "wb") as tfp:
                    for i in selection:
                        event = self.chosen()[i]
                        if hasattr(event, "emailOut"):
                            tfp.write(polybytes(event.emailOut([], i)))
            except IOError:
                raise Recoverable("write of editor tempfile failed")
            fp = subprocess.Popen([editor, tfname], stdin=parse.stdin, stdout=parse.stdout)
            if fp.wait():
                raise Recoverable("%s returned a failure status" % editor)
            else:
                self.do_mailbox_in("<" + tfname)
        # No try/finally here - we want the tempfile to survive on fatal error
        # because it might have megabytes of metadata edits in it.
        os.remove(tfname)
        os.close(tfdesc)

    func data_traverse(self, prompt, hook, attributes, safety):
        "Filter commit metadata (and possibly blobs) through a specified hook."
        blobs = any(isinstance(self.chosen().events[i], Blob)
                    for i in self.selection)
        nonblobs = any(not isinstance(self.chosen().events[i], Blob)
                       for i in self.selection)
        # Try to prevent user from shooting self in foot
        if safety and blobs and nonblobs:
            raise Recoverable("cannot transform blobs and nonblobs in same command")
        # If user is transforming blobs, transform all inlines within the range.
        # This is an expensive step because of the sort; avoid doing it
        # when possible.
        if blobs and self.chosen().inlines > 0:
            for ei in range(self.selection[0], self.selection[-1]):
                event = self.chosen().events[ei]
                if isinstance(event, (Commit, Tag)):
                    for fileop in event.operations():
                        if fileop.inline is not None:
                            self.selection.append(ei)
            self.selection.sort()
        with Baton(prompt=prompt, enable=(verbose == 1)) as baton:
            altered = 0
            for _, event in self.selected():
                if isinstance(event, Tag):
                    if nonblobs:
                        oldcomment = event.comment
                        event.comment = hook(event.comment)
                        anychanged = (oldcomment != event.comment)
                        oldtagger = event.tagger.who()
                        newtagger = hook(oldtagger)
                        if oldtagger != newtagger:
                            newtagger += " " + str(event.tagger.date)
                            event.tagger = Attribution(newtagger)
                            anychanged = true
                        if anychanged:
                            altered += 1
                else if isinstance(event, Commit):
                    if nonblobs:
                        anychanged = false
                        if "c" in attributes:
                            oldcomment = event.comment
                            event.comment = hook(event.comment)
                            if oldcomment != event.comment:
                                anychanged = true
                        if "C" in attributes:
                            oldcommitter = event.committer.who()
                            newcommitter = hook(oldcommitter)
                            changed = (oldcommitter != newcommitter)
                            if changed:
                                newcommitter += " " + str(event.committer.date)
                                event.committer = Attribution(newcommitter)
                                anychanged = true
                        if "a" in attributes:
                            for i in range(len(event.authors)):
                                oldauthor = event.authors[i].who()
                                newauthor = hook(oldauthor)
                                if oldauthor != newauthor:
                                    newauthor += " "+str(event.authors[i].date)
                                    event.authors[i] = Attribution(newauthor)
                                    anychanged = true
                        if anychanged:
                            altered += 1
                    if blobs and isinstance(event, Commit):
                        for fileop in event.operations():
                            if fileop.inline is not None:
                                oldinline = fileop.inline
                                fileop.inline = hook(fileop.inline, event.path)
                                altered += int(fileop.inline != oldinline)
                else if isinstance(event, Blob):
                    content = event.getContent()
                    modified = hook(content, " ".join(event.paths()))
                    if content != modified:
                        event.setContent(modified)
                    altered += (content != modified)
                baton.twirl("")
        announce(debugSHOUT, "%d items modified by %s." % (altered, prompt.lower()))

    func help_selection():
        os.Stdout.write("""
A quick example-centered reference for selection-set syntax.

First, these ways of constructing singleton sets:

123        event numbered 123 (1-origin)
:345       event with mark 345
<456>      commit with legacy-ID 456 (probably a Subversion revsion)
<foo>      the tag named 'foo', or failing that the tip commit of branch foo

You can select commits and tags by date, or by date and committer:

<2011-05-25>                  all commits and tags with this date
<2011-05-25!esr>              all with this date and committer
<2011-05-25T07:30:37Z>        all commits and tags with this date and time
<2011-05-25T07:30:37Z!esr>    all with this date and time and committer
<2011-05-25T07:30:37Z!esr#2>  event #2 (1-origin) in the above set

More ways to construct event sets:

/foo/      all commits and tags containing the string 'foo' in text or metadata
           suffix letters: a=author, b=branch, c=comment in commit or tag,
                           C=committer, r=committish, p=text, t=tagger, n=name,
                           B=blob content in blobs.
           A 'b' search also finds blobs and tags attached to commits on
           matching branches.
[foo]      all commits and blobs touching the file named 'foo'.
[/bar/]    all commits and blobs touching a file matching the regexp 'bar'.
           Suffix flags: a=all fileops must match other selectors, not just
           any one; c=match against checkout paths, DMRCN=match only against
           given fileop types (no-op when used with 'c').
=C         all commits
=H         all head (branch tip) commits
=T         all tags
=B         all blobs
=R         all resets
=P         all passthroughs
=O         all orphan (parentless) commits
=U         all commits with callouts as parents
=Z         all commits with no fileops
=M         all merge commits
=F         all fork (multiple-child) commits
=L         all commits with unclean multi-line comments
=I         all commits not decodable to UTF-8
=D         all commits in which every fileop is a D or deleteall
=N         all commits and tags matching a cookie (legacy-ID) format.

@min()     create singleton set of the least element in the argument
@max()     create singleton set of the greatest element in the argument

Other special functions are available: do 'help functions' for more.

You can compose sets as follows:

:123,<foo>     the event marked 123 and the event referenced by 'foo'.
:123..<foo>    the range of events from mark 123 to the reference 'foo'

Selection sets are ordered: elements remain in the order they were added,
unless sorted by the ? suffix.

Sets can be composed with | (union) and & (intersection). | has lower
precedence than &, but set expressions can be grouped with (
). Postfixing a ? to a selection expression widens it to include all
immediate neighbors of the selection and sorts it; you can do this
repeatedly for effect. Do set negation with prefix ~; it has higher
precedence than & | but lower than ?.
""")

    func help_syntax():
        os.Stdout.write("""
Commands are distinguished by a command keyword.  Most take a selection set
immediately before it; see 'help selection' for details.  Some
commands take additional modifier arguments after the command keyword.

Most report-generation commands support output redirection. When
arguments for these are parsed, any argument beginning with '>' is
extracted and interpreted as the name of a file to which command
output should be redirected.  Any remaining arguments are available to
the command logic.

Some commands support input redirection. When arguments for these are
parsed, any argument beginning with '<' is extracted and interpreted
as the name of a file from which command output should be taken.  Any
remaining arguments are available to the command logic.
""")

    func help_functions():
        os.Stdout.write("The following special selection functions are available:\n")
        for attr in sorted(RepoSurgeon.__dict__):
            if attr.endswith("_handler"):
                os.Stdout.write("@%s()\t%s\n" % (attr[:-8], getattr(RepoSurgeon, attr).__doc__))
    ##
    ## Command implementation begins here
    ##
    #
    # On-line help and instrumentation
    #
    func help_help():
        os.Stdout.write("Show help for a command. Follow with space and the command name.\n")
    func help_verbose():
        os.Stdout.write("""
Without an argument, this command requests a report of the verbosity
level.  'verbose 1' enables progress messages, 'verbose 0' disables
them. Higher levels of verbosity are available but intended for
developers only.
""")
    func do_verbose(self, line):
        global verbose
        if line:
            try:
                verbose = int(line)
            except ValueError:
                complain("verbosity value must be an integer")
        if not line or verbose:
            announce(debugSHOUT, "verbose %d" % verbose)

    func help_quiet():
        os.Stdout.write("""
Without an argument, this command requests a report of the quiet
boolean; with the argument 'on' or 'off' it is changed.  When quiet is
on, time-varying report fields which would otherwise cause spurious
failures in regression testing are suppressed.
""")
    func do_quiet(self, line):
        global quiet
        if line:
            if line == "on":
                quiet = true
            else if line == "off":
                quiet = false
        if not line:
            announce(debugSHOUT, "quiet %s" % ("on" if quiet else "off"))

    func help_echo():
        os.Stdout.write("""
Set or clear echoing of commands before processing.
""")
    func do_echo(self, line):
        "Set or clear echoing commands before processing."
        try:
            self.echo = int(line)
        except ValueError:
            complain("echo value must be an integer")
        if verbose:
            announce(debugSHOUT, "echo %d" % self.echo)

    func help_print():
        os.Stdout.write("""
Print a literal string.
""")
    func do_print(self, line):
        "Print a literal string."
        os.Stdout.write(line + "\n")

    func help_resolve():
        os.Stdout.write("""
Does nothing but resolve a selection-set expression
and report the resulting event-number set to standard
output. The remainder of the line after the command is used
as a label for the output.

Implemented mainly for regression testing, but may be useful
for exploring the selection-set language.
""")
    func do_resolve(self, line):
        "Display the set of event numbers generated by a selection set."
        if self.selection is None:
            os.Stdout.write("No selection\n")
        else if isinstance(self.selection, list):
            if line:
                os.Stdout.write("%s: " % line)
            os.Stdout.write(str([x+1 for x in self.selection]) + "\n")
        else:
            complain("resolve didn't expect a selection of %s" % self.selection)

    func help_assign():
        os.Stdout.write("""

Compute a leading selection set and assign it to a symbolic name,
which must follow the assign keyword. It is an error to assign to a
name that is already assigned, or to any existing branch name.
Assignments may be cleared by some sequence mutations (though not by
ordinary deletion); you will see a warning when this occurs.

With no selection set and no argument, list all assignments.

If the option --singleton is given, the assignment will throw an error
if the selection set is not a singleton.

Use this to optimize out location and selection computations
that would otherwise be performed repeatedly, e.g. in macro calls.
""")
    func do_assign(self, line):
        repo = self.chosen()
        if not repo:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            if line:
                raise Recoverable("No selection")
            else:
                for n, v in repo.assignments.items():
                    announce(debugSHOUT, "%s = %s" % (n, v))
                return
        with RepoSurgeon.LineParse(repo, line) as parse:
            name = parse.line.strip()
            if name in repo.assignments:
                raise Recoverable("%s has already been set" % name)
            else if repo.named(name):
                raise Recoverable("%s conflicts with a branch, tag, legacy-ID, or date" % name)
            else if "--singleton" in parse.options and len(self.selection) != 1:
                raise Recoverable("a singleton selection was required here")
            else:
                repo.assignments[name] = self.selection

    func help_unassign():
        os.Stdout.write("""
Unassign a symbolic name.  Throws an error if the name is not assigned.
Tab-completes on the list of defined names.
""")
    func complete_unassign(self, text, _line, _begidx, _endidx):
        repo = self.chosen()
        return sorted([x for x in repo.assignments.keys() if x.startswith(text)])
    func do_unassign(self, line):
        repo = self.chosen()
        if not repo:
            complain("no repo has been chosen.")
            return
        if self.selection is not None:
            raise Recoverable("cannot take a selection")
        name = line.strip()
        if name in repo.assignments:
            del repo.assignments[name]
        else:
            raise Recoverable("%s has not been set" % name)

    func help_names():
        os.Stdout.write("""
List all known symbolic names of branches and tags. Supports > redirection.
""")
    func do_names(self, line):
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            branches = list(self.chosen().branchset())
            branches.sort()
            for branch in branches:
                parse.stdout.write("branch %s\n" % branch)
            for event in self.chosen():
                if isinstance(event, Tag):
                    parse.stdout.write("tag    %s\n" % event.name)

    func do_script(self, line):
        "Read and execute commands from a named file."
        if not line:
            complain("script requires a file argument")
            return
        try:
            self.callstack.append(line.split())
            with open(self.callstack[-1][0], "rb") as scriptfp:
                scriptfp = make_wrapper(scriptfp)
                while true:
                    scriptline = scriptfp.readline()
                    if not scriptline:
                        break
                    # Handle multiline commands
                    while scriptline.endswith("\\\n"):
                        scriptline = scriptline[:-2] + scriptfp.readline()
                    # Simulate shell here-document processing
                    if '<<' not in scriptline:
                        heredoc = None
                    else:
                        (scriptline, terminator) = scriptline.split("<<")
                        heredoc = tempfile.NamedTemporaryFile(mode="wb",
                                                              delete=false)
                        while true:
                            nextline = scriptfp.readline()
                            if nextline == '':
                                break
                            else if nextline == terminator:
                                break
                            else:
                                heredoc.write(polybytes(nextline))
                        heredoc.close()
                        # Note: the command must accept < redirection!
                        scriptline += "<" + heredoc.name
                    # End of heredoc simulation
                    for i in range(len(self.callstack[-1])):
                        scriptline = scriptline.replace('$' + str(i), self.callstack[-1][i])
                    scriptline =  scriptline.replace('$$', str(os.getpid()))
                    self.onecmd(self.precmd(scriptline))
                    if heredoc:
                        os.remove(heredoc.name)
            self.callstack.pop()
        except IOError as e:
            complain("script failure on '%s': %s" % (line, e))

    func do_history(self, _line):
        "Dump your command list from this session so far."
        for line in self.history:
            os.Stdout.write(line + "\n")

    func do_coverage(self, unused):
        "Display the coverage-case set (developer instrumentation)."
        assert unused is not None   # pacify pylint
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        for e in self.chosen().commits():
            e.fileopDump()
        os.Stdout.write("Case coverage: %s\n" % sorted(self.chosen().caseCoverage))

    func help_index():
        os.Stdout.write("""
Display four columns of info on selected objects: their number, their
type, the associate mark (or '-' if no mark) and a summary field
varying by type.  For a branch or tag it's the reference; for a commit
it's the commit branch; for a blob it's the repository path of the
file in the blob.  Supports > redirection.
""")
    func do_index(self, line):
        "Generate a summary listing of objects."
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        # We could do all this logic using report_select() and index() methods
        # in the objects, but that would have two disadvantages.  First, we'd
        # get a default-set computation we don't want.  Second, for this
        # function it's helpful to have the method strings close together so
        # we can maintain columnation.
        if self.selection is None:
            self.selection = [n for n, o1 in enumerate(self.chosen()) if not isinstance(o1, Blob)]
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            for i, event in self.selected():
                if isinstance(event, Blob):
                    parse.stdout.write("%6d blob   %6s    %s\n" % (i+1, event.mark," ".join(event.paths())))
                    continue
                if isinstance(event, Commit):
                    parse.stdout.write("%6d commit %6s    %s\n" % (i+1, event.mark or '-', event.branch))
                    continue
                if isinstance(event, Tag):
                    parse.stdout.write("%6d tag    %6s    %4s\n" % (i+1, event.committish, repr(event.name),))
                    continue
                if isinstance(event, Reset):
                    parse.stdout.write("%6d branch %6s    %s\n" % (i+1, event.committish or '-', event.ref))
                    continue
                else:
                    parse.stdout.write("?      -      %s\n" % (event,))
    func help_profile():
        os.Stdout.write("""
Enable profiling. Profile statistics are dumped to the path given as argument.
Must be one of the initial command-line arguments, and gathers statistics only
on code executed via '-'.
""")
    func do_profile(self, line):
        "Enable profiling."
        assert line is not None # Pacify pylint
        self.profile_log = line
        announce(debugSHOUT, "profiling enabled.")

    func help_timing():
        os.Stdout.write("""
Report phase-timing results and memory usage from repository analysis.
""")
    func do_timing(self, line):
        "Report repo-analysis times and memory usage."
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        if line:
            self.chosen().timings.append((line, time.now()))
        self.repo.dumptimes()
        if psutil is None:
            complain("The psutil module required for memory statistics is not installed.")
        else:
            mem = psutil.virtual_memory()
            announce(debugSHOUT, repr(mem))

    #
    # Information-gathering
    #
    func help_stats():
        os.Stdout.write("""
Report size statistics and import/export method information of the
currently chosen repository. Supports > redirection.
""")
    func do_stats(self, line):
        "Report information on repositories."
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            if not parse.line:
                if not self.chosen():
                    complain("no repo has been chosen.")
                    return
                parse.line = self.chosen().name
                if parse.line is None:
                    complain("no repo has been chosen.")
                    return
            for name in parse.tokens():
                repo = self.repo_by_name(name)
                if repo is None:
                    raise Recoverable("no such repo as %s" % name)
                else:
                    func count(otype):
                        return sum(1 for x in repo.events if isinstance(x,otype))
                    parse.stdout.write("%s: %.0fK, %d events, %d blobs, %d commits, %d tags, %d resets, %s.\n" % \
                          (repo.name, repo.size() / 1000.0, len(repo),
                           count(Blob), count(Commit), count(Tag), count(Reset),
                           rfc3339(repo.readtime)))
                    if repo.sourcedir:
                        parse.stdout.write("  Loaded from %s\n" % repo.sourcedir)
                    #if repo.vcs:
                    #    parse.stdout.write(polystr(repo.vcs) + "\n")

    func help_count():
        os.Stdout.write("""
Report a count of items in the selection set. Default set is everything
in the currently-selected repo. Supports > redirection.
""")
    func do_count(self, line):
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        else if self.selection is None:
            self.selection = self.chosen().all()
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            parse.stdout.write("%d\n" % len(self.selection))

    func help_list():
        os.Stdout.write("""
Display commits in a human-friendly format; the first column is raw
event numbers, the second a timestamp in local time. If the repository
has legacy IDs, they will be displayed in the third column. The
leading portion of the comment follows. Supports > redirection.
""")
    func do_list(self, line):
        "Generate a human-friendly listing of objects."
        self.report_select(line, "lister", (screenwidth(),))

    func help_tip():
        os.Stdout.write("""
Display the branch tip names associated with commits in the selection
set.  These will not necessarily be the same as their branch fields
(which will often be tag names if the repo contains either annotated
or lightweight tags).

If a commit is at a branch tip, its tip is its branch name.  If it has
only one child, its tip is the child's tip.  If it has multiple children,
then if there is a child with a matching branch name its tip is the
child's tip.  Otherwise this function throws a recoverable error.

Supports > redirection.
""")
    func do_tip(self, line):
        "Generate a human-friendly listing of objects."
        self.report_select(line, "tip", (screenwidth(),))

    func help_tags():
        os.Stdout.write("""
Display tags and resets: three fields, an event number and a type and a name.
Branch tip commits associated with tags are also displayed with the type
field 'commit'. Supports > redirection.
""")
    func do_tags(self, line):
        "Generate a human-friendly listing of tags and resets."
        self.report_select(line, "tags", (screenwidth(),))

    func help_stamp():
        os.Stdout.write("""
Display full action stamps correponding to commits in a select.
The stamp is followed by the first line of the commit message.
Supports > redirection.
""")
    func do_stamp(self,line):
        self.report_select(line, "stamp", (screenwidth(),))

    func help_sizes():
        os.Stdout.write("""
Print a report on data volume per branch; takes a selection set,
defaulting to all events. The numbers tally the size of uncompressed
blobs, commit and tag comments, and other metadata strings (a blob is
counted each time a commit points at it).  Not an exact measure of
storage size: intended mainly as a way to get information on how to
efficiently partition a repository that has become large enough to be
unwieldy. Supports > redirection.
""")
    func do_sizes(self, line):
        "Report branch relative sizes."
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        sizes = {}
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            for _, event in self.selected():
                if isinstance(event, Commit):
                    if event.branch not in sizes:
                        sizes[event.branch] = 0
                    sizes[event.branch] += len(str(event.committer))
                    for author in event.authors:
                        sizes[event.branch] += len(str(author))
                    sizes[event.branch] += len(event.comment)
                    for fileop in event.operations():
                        if fileop.op == opM:
                            sizes[event.branch] += self.repo.markToEvent(fileop.ref).size
                else if isinstance(event, Tag):
                    commit = event.target
                    if commit.branch not in sizes:
                        sizes[commit.branch] = 0
                    sizes[commit.branch] += len(str(event.tagger))
                    sizes[commit.branch] += len(event.comment)
            total = sum(sizes.values())
            func sz(n, s):
                parse.stdout.write("%9d\t%2.2f%%\t%s\n" \
                                   % (n, (n * 100.0) / total, s))
            for key in sorted(sizes):
                sz(sizes[key], key)
            sz(total, "")
    func help_lint():
        os.Stdout.write("""
Look for DAG and metadata configurations that may indicate a
problem. Presently checks for: (1) Mid-branch deletes, (2)
disconnected commits, (3) parentless commits, (4) the existance of
multiple roots, (5) committer and author IDs that don't look
well-formed as DVCS IDs, (6) multiple child links with identical
branch labels descending from the same commit, (7) time and
action-stamp collisions.

Supports > redirection.
""")
    func do_lint(self, line):
        "Look for lint in a repo."
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            unmapped = regexp.MustCompile(("[^@]*$|[^@]*@" + str(self.chosen().uuid) + "$").encode('ascii'))
            shortset = set()
            deletealls = set()
            disconnected = set()
            roots = set()
            emptyaddr = set()
            emptyname = set()
            badaddress = set()
            for _, event in self.selected(Commit):
                if event.operations() and event.operations()[0].op == 'deleteall' and event.hasChildren():
                    deletealls.add("on %s at %s" % (event.branch, event.idMe()))
                if not event.hasParents() and not event.hasChildren():
                    disconnected.add(event.idMe())
                else if not event.hasParents():
                    roots.add(event.idMe())
                if unmapped:
                    for person in [event.committer] + event.authors:
                        if unmapped.match(polybytes(person.email)):
                            shortset.add(person.email)
                if not event.committer.email:
                    emptyaddr.add(event.idMe())
                else if "@" not in event.committer.email:
                    badaddress.add(event.idMe())
                for author in event.authors:
                    if not author.email:
                        emptyaddr.add(event.idMe())
                    else if "@" not in author.email:
                        badaddress.add(event.idMe())
                if not event.committer.name:
                    emptyname.add(event.idMe())
                for author in event.authors:
                    if not author.name:
                        emptyname.add(event.idMe())

            if not parse.options or "--deletealls" in parse.options \
                   or "-d" in parse.options:
                for item in sorted(deletealls):
                    parse.stdout.write("mid-branch delete: %s\n" % item)
            if not parse.options or "--connected" in parse.options \
                   or "-c" in parse.options:
                for item in sorted(disconnected):
                    parse.stdout.write("disconnected commit: %s\n" % item)
            if not parse.options or "--roots" in parse.options \
                   or "-r" in parse.options:
                if len(roots) > 1:
                    parse.stdout.write("multiple root commits: %s\n" % sorted(roots))
            if not parse.options or "--names" in parse.options \
                   or "-n" in parse.options:
                for item in sorted(shortset):
                    parse.stdout.write("unknown shortname: %s\n" % item)
                for item in sorted(emptyaddr):
                    parse.stdout.write("empty committer address: %s\n" % item)
                for item in sorted(emptyname):
                    parse.stdout.write("empty committer name: %s\n" % item)
                for item in sorted(badaddress):
                    parse.stdout.write("email address missing @: %s\n" % item)
            if not parse.options or "--uniqueness" in parse.options \
                   or "-u" in parse.options:
                self.chosen().check_uniqueness(true, announcer=lambda s: parse.stdout.write("reposurgeon: " + s + "\n"))
            if "--options" in parse.options or "-?" in parse.options:
                os.Stdout.write("""\
--deletealls    -d     report mid-branch deletealls
--connected     -c     report disconnected commits
--roots         -r     report on multiple roots
--attributions  -a     report on anomalies in usernames and attributions
--uniqueness    -u     report on collisions among action stamps
--options       -?     list available options\
""")
    #
    # Housekeeping
    #
    func help_prefer():
        os.Stdout.write("""
Report or set (with argument) the preferred type of repository. With
no arguments, describe capabilities of all supported systems. With an
argument (which must be the name of a supported version-control
system, and tab-completes in that list) this has two effects:

First, if there are multiple repositories in a directory you do a read
on, reposurgeon will read the preferred one (otherwise it will
complain that it can't choose among them).

Secondly, this will change reposurgeon's preferred type for output.
This means that you do a write to a directory, it will build a repo of
the preferred type rather than its original type (if it had one).

If no preferred type has been explicitly selected, reading in a
repository (but not a fast-import stream) will implicitly set reposurgeon's
preference to the type of that repository.
""")
    func complete_prefer(self, text, _line, _begidx, _endidx):
        return sorted([x.name for x in vcstypes if x.importer and x.name.startswith(text)])
    func do_prefer(self, line):
        "Report or select the preferred repository type."
        if not line:
            for vcs in vcstypes:
                os.Stdout.write(str(vcs) + "\n")
            for option in file_filters:
                os.Stdout.write("read and write have a --format=%s option that supports %s files.\n"
                      % (option, option.capitalize()))
            if any(ext.visible and not ext.vcstype for ext in extractors):
                os.Stdout.write("Other systems supported for read only: %s\n\n" \
                      % " ".join(ext.name for ext in extractors if ext.visible))
        else:
            for repotype in vcstypes + extractors:
                if line.lower() == repotype.name:
                    self.preferred = repotype
                    break
            else:
                complain("known types are %s." % " ".join([x.name for x in vcstypes] + [x.name for x in extractors if x.visible]))
        if verbose:
            if not self.preferred:
                os.Stdout.write("No preferred type has been set.\n")
            else:
                os.Stdout.write("%s is the preferred type.\n" % self.preferred.name)

    func help_sourcetype():
        os.Stdout.write("""
Report (with no arguments) or select (with one argument) the current
repository's source type.  This type is normally set at
repository-read time, but may remain unset if the source was a stream
file. The argument tab-completes in the list of supported systems.

The source type affects the interpretation of legacy IDs (for
purposes of the =N visibility set and the 'references' command) by
controlling the regular expressions used to recognize them. If no
preferred output type has been set, it may also change the output
format of stream files made from the repository.

The repository source type is reliably set when reading a Subversion
stream.
""")
    func complete_sourcetype(self, text, _line, _begidx, _endidx):
        return sorted([x.name for x in vcstypes if x.exporter and x.name.startswith(text)])
    func do_sourcetype(self, line):
        "Report or select the current repository's source type."
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        if not line:
            if self.chosen().vcs:
                os.Stdout.write("%s: %s\n" % (repo.name, repo.vcs.name))
            else:
                os.Stdout.write("%s: no preferred type.\n" % repo.name)
        else:
            for repotype in vcstypes + extractors:
                if line.lower() == repotype.name:
                    self.chosen().vcs = repotype
                    break
            else:
                complain("known types are %s." % " ".join([x.name for x in vcstypes] + [x.name for x in extractors if x.visible]))

    func help_choose():
        os.Stdout.write("""
Choose a named repo on which to operate.  The name of a repo is
normally the basename of the directory or file it was loaded from, but
repos loaded from standard input are 'unnamed'. The program will add
a disambiguating suffix if there have been multiple reads from the
same source.

With no argument, lists the names of the currently stored repositories
and their load times.  The second column is '*' for the currently selected
repository, '-' for others.

With an argument, the command tab-completes on the above list.
""")
    func complete_choose(self, text, _line, _begidx, _endidx):
        if not self.repolist:
            return None
        return sorted([x.name for x in self.repolist if x.name.startswith(text)])
    func do_choose(self, line):
        "Choose a named repo on which to operate."
        if self.selection is not None:
            raise Recoverable("choose does not take a selection set")
        if not self.repolist:
            if verbose > 0:
                complain("no repositories are loaded.")
                return
        self.repolist.sort(key=operator.attrgetter("name"))
        if not line:
            for repo in self.repolist:
                status =  '-'
                if self.chosen() and repo == self.chosen():
                    status = '*'
                if not quiet:
                    os.Stdout.write(rfc3339(repo.readtime) + " ")
                os.Stdout.write("%s %s\n" % (status, repo.name))
        else:
            if line in self.reponames():
                self.choose(self.repo_by_name(line))
                if verbose:
                    self.do_stats(line)
            else:
                complain("no such repo as %s" % line)

    func help_drop():
        os.Stdout.write("""
Drop a repo named by the argument from reposurgeon's list, freeing the memory
used for its metadata and deleting on-disk blobs. With no argument, drops the
currently chosen repo. Tab-completes on the list of loaded repositories.
""")
    complete_drop = complete_choose
    func do_drop(self, line):
        "Drop a repo from reposurgeon's list."
        if not self.reponames():
            if verbose:
                complain("no repositories are loaded.")
                return
        if self.selection is not None:
            raise Recoverable("drop does not take a selection set")
        if not line:
            if not self.chosen():
                complain("no repo has been chosen.")
                return
            line = self.chosen().name
        if line in self.reponames():
            if self.chosen() and line == self.chosen().name:
                self.unchoose()
            holdrepo = self.repo_by_name(line)
            holdrepo.cleanup()
            self.remove_by_name(line)
            del holdrepo
        else:
            complain("no such repo as %s" % line)
        if verbose:
            # Emit listing of remaining repos
            self.do_choose('')

    func help_rename():
        os.Stdout.write("""
Rename the currently chosen repo; requires an argument.  Won't do it
if there is already one by the new name.
""")
    func do_rename(self, line):
        "Rename a repository."
        if self.selection is not None:
            raise Recoverable("rename does not take a selection set")
        if line in self.reponames():
            complain("there is already a repo named %s." % line)
        else if not self.chosen():
            complain("no repository is currently chosen.")
        else:
            self.chosen().rename(line)

    func help_preserve():
        os.Stdout.write("""
Add (presumably untracked) files or directories to the repo's list of
paths to be restored from the backup directory after a rebuild. Each
argument, if any, is interpreted as a pathname.  The current preserve
list is displayed afterwards.
""")
    func do_preserve(self, line):
        "Add files and subdirectories to the preserve set."
        if self.selection is not None:
            raise Recoverable("preserve does not take a selection set")
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        for filename in line.split():
            self.chosen().preserve(filename)
        announce(debugSHOUT, "preserving %s." % list(self.chosen().preservable()))

    func help_unpreserve():
        os.Stdout.write("""
Remove (presumably untracked) files or directories to the repo's list
of paths to be restored from the backup directory after a
rebuild. Each argument, if any, is interpreted as a pathname.  The
current preserve list is displayed afterwards.
""")
    func do_unpreserve(self, line):
        "Remove files and subdirectories from the preserve set."
        if self.selection is not None:
            raise Recoverable("unpreserve does not take a selection set")
        if not self.chosen():
            complain("no repo has been chosen.")
            return
        for filename in line.split():
            self.chosen().unpreserve(filename)
        announce(debugSHOUT, "preserving %s." % list(self.chosen().preservable()))

    #
    # Serialization and de-serialization.
    #
    func help_read():
        os.Stdout.write("""
A read command with no arguments is treated as 'read .', operating on the
current directory.

With a directory-name argument, this command attempts to read in the
contents of a repository in any supported version-control system under
that directory.

If input is redirected from a plain file, it will be read in as a
fast-import stream or Subversion dump, whichever it is.

With an argument of '-', this command reads a fast-import stream or
Subversion dump from standard input (this will be useful in filters
constructed with command-line arguments).

The --format option can be used to read in binary repository dump files.
For a list of supported types, invoke the 'prefer' command.
""")
    func do_read(self, line):
        "Read in a repository for surgery."
        if self.selection is not None:
            raise Recoverable("read does not take a selection set")
        with RepoSurgeon.LineParse(self, line, capabilities=["stdin"]) as parse:
            if parse.redirected:
                repo = Repository()
                for option in parse.options:
                    if option.startswith("--format="):
                        vcs = option.split("=")[1]
                        try:
                            infilter = file_filters[vcs][0]
                            srcname = parse.stdin.name
                            # parse is redirected so this must be something besides sys.stdin, so
                            # we can close it and substitute another redirect
                            parse.stdin.close()
                            parse.stdin = make_wrapper(popenOrDie(infilter % srcname, mode="r").open())
                        except KeyError:
                            raise Recoverable("unrecognized --format")
                        break
                repo.fastImport(parse.stdin, parse.options, progress=(verbose==1 and not quiet))
            # This is slightly asymmetrical with the write side, which
            # interprets an empty argument list as '-'
            else if not parse.line or parse.line == '.':
                repo = read_repo(os.getcwd(), parse.options, self.preferred)
            else if os.path.isdir(parse.line):
                repo = read_repo(parse.line, parse.options, self.preferred)
            else:
                raise Recoverable("read no longer takes a filename argument - use < redirection instead")
        self.repolist.append(repo)
        self.choose(repo)
        if self.chosen():
            if self.chosen().vcs:
                self.preferred = self.chosen().vcs
            name = self.uniquify(os.path.basename(self.chosen().sourcedir or parse.infile or "unnamed"))
            self.chosen().rename(name)
        if verbose:
            self.do_choose('')

    func help_write():
        os.Stdout.write("""
Dump a fast-import stream representing selected events to standard
output (if second argument is empty or '-') or via > redirect to a file.
Alternatively, if there ia no redirect and the argument names a
directory the repository is rebuilt into that directory, with any
selection set argument being ignored; if that target directory is
nonempty its contents are backed up to a save directory.

Property extensions will be omitted if the importer for the
preferred repository type cannot digest them.

The --fossil option can be used to write out binary repository dump files.
For a list of supported types, invoke the 'prefer' command.
""")
    func do_write(self, line):
        "Stream out the results of repo surgery."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        if line:
            line = os.path.expanduser(line)
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            # This is slightly asymmetrical with the read side, which
            # interprets an empty argument list as '.'
            if parse.redirected or not parse.line:
                for option in parse.options:
                    if option.startswith("--format="):
                        vcs = option.split("=")[1]
                        try:
                            outfilter = file_filters[vcs][1]
                            dstname = parse.stdout.name
                            # parse is redirected so this must be
                            # something besides os.Stdout, so we can
                            # close it and substitute another redirect
                            parse.stdout.close()
                            parse.stdout = make_wrapper(popenOrDie(outfilter % dstname, mode="w").open())
                        except KeyError:
                            raise Recoverable("unrecognized --format")
                        break
                self.chosen().fast_export(self.selection, parse.stdout, parse.options, progress=(verbose==1 and not quiet), target=self.preferred)
            else if os.path.isdir(parse.line):
                rebuild_repo(self.chosen(), parse.line, parse.options, self.preferred)
            else:
                raise Recoverable("write no longer takes a filename argument - use > redirection instead")

    func help_inspect():
        os.Stdout.write("""
Dump a fast-import stream representing selected events to standard
output or via > redirect to a file.  Just like a write, except (1) the
progress meter is disabled, and (2) there is an identifying header
before each event dump.
""")
    func do_inspect(self, line):
        "Dump raw events."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            if self.selection is None and parse.line.strip():
                parse.line = self.set_selection_set(parse.line)
            else if self.selection is None:
                self.selection = self.chosen().all()
            for ei, event in self.selected():
                header = "Event %s, " % repr(ei+1)
                header = header[:-2]
                header += " " + ((72 - len(header)) * "=") + "\n"
                parse.stdout.write(header)
                if isinstance(event, Commit):
                    parse.stdout.write(event.dump())
                else:
                    parse.stdout.write(str(event))

    func help_strip():
        os.Stdout.write("""
Replace the blobs in the selected repository with self-identifying stubs;
and/or strip out topologically uninteresting commits.  The modifiers for
this are 'blobs' and 'reduce' respectively; the default is 'blobs'.

A selection set is effective only with the 'blobs' option, defaulting to all
blobs. The 'reduce' mode always acts on the entire repository.

This is intended for producing reduced test cases from large repositories.
""")
    func complete_strip(self, _text, _line, _begidx, _endidx):
        return ["blobs", "reduce"]
    func do_strip(self, line):
        "Drop content to produce a reduced test case."
        repo = self.chosen()
        if repo is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        if not line:
            striptypes = ["blobs"]
        else:
            striptypes = line.split()
        if "blobs" in striptypes:
            for (_, event) in self.selected(Blob):
                event.setContent("Blob at %s\n" % event.mark)
        if "reduce" in striptypes:
            interesting = set([])
            for event in repo.events:
                if isinstance(event, Tag):
                    interesting.add(event.committish)
                else if isinstance(event, Reset):
                    interesting.add(event.ref)
                else if isinstance(event, Commit):
                    if len(event.children()) != 1 or len(event.parents()) != 1:
                        interesting.add(event.mark)
                    else:
                        for op in event.operations():
                            if op.op != opM or repo.ancestor_count(event.parents()[0], op.path) == 0:
                                interesting.add(event.mark)
                                break
            neighbors = set()
            for event in repo.events:
                if isinstance(event, Commit) and event.mark in interesting:
                    neighbors |= set(event.parentMarks())
                    neighbors |= set(event.childMarks())
            interesting |= neighbors
            oldlen = len(repo.events)
            repo.delete([i for i in range(len(repo.events)) \
                         if isinstance(event, Commit) and event.mark not in interesting])
            announce(debugSHOUT, "From %d to %d events." % (oldlen, len(repo.events)))
    func help_graph():
        os.Stdout.write("""
Dump a graph representing selected events to standard output in DOT markup
for graphviz. Supports > redirection.
""")
    func do_graph(self, line):
        "Dump a commit graph."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            parse.stdout.write("digraph {\n")
            for _, event in self.selected():
                if isinstance(event, Commit):
                    for parent in event.parentMarks():
                        if self.chosen().find(parent) in self.selection:
                            parse.stdout.write('\t%s -> %s;\n' \
                                               % (parent[1:], event.mark[1:]))
                if isinstance(event, Tag):
                    parse.stdout.write('\t"%s" -> "%s" [style=dotted];\n' \
                                       % (event.name, event.committish[1:], ))
                    parse.stdout.write('\t{rank=same; "%s"; "%s"}\n' \
                                       % (event.name, event.committish[1:], ))
            for _, event in self.selected():
                if isinstance(event, Commit):
                    summary = cgi.escape(event.comment.split('\n')[0][:42])
                    cid = event.mark
                    if event.legacyID:
                        cid = event.showlegacy() + " &rarr; " + cid
                    parse.stdout.write('\t%s [shape=box,width=5,label=<<table cellspacing="0" border="0" cellborder="0"><tr><td><font color="blue">%s</font></td><td>%s</td></tr></table>>];\n' \
                                       % (event.mark[1:], cid, summary))
                    if all(event.branch != child.branch for child in event.children()):
                        parse.stdout.write('\t"%s" [shape=oval,width=2];\n' % event.branch)
                        parse.stdout.write('\t"%s" -> "%s" [style=dotted];\n' % (event.mark[1:], event.branch))
                if isinstance(event, Tag):
                    summary = cgi.escape(event.comment.split('\n')[0][:32])
                    parse.stdout.write('\t"%s" [label=<<table cellspacing="0" border="0" cellborder="0"><tr><td><font color="blue">%s</font></td><td>%s</td></tr></table>>];\n' \
                                       % (event.name, event.name, summary))
            parse.stdout.write("}\n")

    func help_rebuild():
        os.Stdout.write("""
Rebuild a repository from the state held by reposurgeon.  The argument
specifies the target directory in which to do the rebuild;x0 if the
repository read was from a repo directory (and not a git-import stream), it
defaults to that directory.  If the target directory is nonempty
its contents are backed up to a save directory.
""")
    func do_rebuild(self, line):
        "Rebuild a repository from the edited state."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is not None:
            raise Recoverable("rebuild does not take a selection set")
        with RepoSurgeon.LineParse(self, line) as parse:
            rebuild_repo(self.chosen(), parse.line, parse.options, self.preferred)

    #
    # Editing commands
    #
    func help_mailbox_out():
        os.Stdout.write("""
Emit a mailbox file of messages in RFC822 format representing the
contents of repository metadata. Takes a selection set; members of the set
other than commits, annotated tags, and passthroughs are ignored (that
is, presently, blobs and resets). Supports > redirection.

May have an option --filter, followed by = and a /-enclosed regular expression.
If this is given, only headers with names matching it are emitted.  In this
context the name of the header includes its trailing colon.
""")
    func do_mailbox_out(self, line):
        "Generate a mailbox file representing object metadata."
        filterRegexp = None
        opts = shlex.split(line)
        for token in opts:
            if token.startswith("--filter="):
                token = token[9:]
                if len(token) < 2 or token[0] != '/' or token[-1] != '/':
                    raise Recoverable("malformed filter option in mailbox_out")
                try:
                    filterRegexp = regexp.MustCompile(token[1:-1].encode('ascii'))
                except sre_constants.error as e:
                    raise Recoverable("filter compilation error - %s" % e)
            else if token.startswith(">"):
                continue
            else:
                raise Recoverable("unknown option %s in mailbox_out" % token)
        self.report_select(line, "emailOut", (filterRegexp,))

    func help_mailbox_in():
        os.Stdout.write("""
Accept a mailbox file of messages in RFC822 format representing the
contents of the metadata in selected commits and annotated tags. Takes
no selection set. If there is an argument it will be taken as the name
of a mailbox file to read from; if no argument, or one of '-', reads
from standard input. Supports < redirection.

Users should be aware that modifying an Event-Number or Event-Mark field
will change which event the update from that message is applied to.  This
is unlikely to have good results.

The header CheckText, if present, is examined to see if the comment
text of the associated event begins with it. If not, the mailbox
modification is aborted. This helps ensure that you are landing
updates ob the events you intend.

If the --create modifier is present, new tags and commits will be
appended to the repository.  In this case it is an error for a tag
name to match any exting tag name. Commit objects are created with no
fileops.  If Committer-Date or Tagger-Date fields are not present they
are filled in with the time at which this command is executed. If
Committer or Tagger fields are not present, reposurgeon will attempt
to deduce the user's git-style identity and fill it in. If a singleton
commit set was specified for commit creations, the new commits are
made children of that commit.

Otherwise, if the Event-Number and Event-Mark fields are absent, the
mailbox_in logic will attempt to match the commit or tag first by Legacy-ID,
then by a unique committer ID and timestamp pair.

If output is redirected and the modifier '--changed' appears, a minimal
set of modifications actually made is written to the output file in a form
that can be fed back in. Supports > redirection.

If the option --empty-only is given, this command will throw a recoverable error
if it tries to alter a message body that is neither empty nor consists of the
CVS empty-comment marker.
""")
    func do_mailbox_in(self, line):
        "Accept a mailbox file representing object metadata and update from it."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        with RepoSurgeon.LineParse(self, line, capabilities=["stdin","stdout"]) as parse:
            update_list = []
            while true:
                var msg MessageBlock
                err = msg.readMessage(parse.stdin)
                if err != nil:
                    break
                update_list.append(email.message_from_string(msg))
        # First, a validation pass
        attribution_by_author = {}
        attribution_by_committer = {}
        name_map = {}
        author_counts = collections.Counter()
        committer_counts = collections.Counter()
        for commit in self.chosen().commits():
            stamp = commit.actionStamp()
            if stamp in attribution_by_author and attribution_by_author[stamp] != commit:
                author_counts[stamp] += 1
            attribution_by_author[stamp] = commit
            stamp = commit.committer.action_stamp()
            if stamp in attribution_by_committer and attribution_by_committer[stamp] != commit:
                committer_counts[stamp] += 1
            attribution_by_committer[stamp] = commit
        for event in self.chosen().events:
            if isinstance(event, Tag):
                if event.name:
                    name_map[event.name] = event
                if event.tagger:
                    stamp = event.tagger.action_stamp()
                    if stamp in attribution_by_author and attribution_by_author[stamp] != event:
                        author_counts[stamp] += 1
                    attribution_by_author[stamp] = event
        legacyMap = {}
        for commit in self.chosen().commits():
            if commit.legacyID:
                legacyMap[commit.legacyID] = commit
        events = []
        errors = 0
        # Special case - event creation
        if '--create' in parse.options:
            for (i, message) in enumerate(update_list):
                if "Tag-Name" in message:
                    blank = Tag()
                    blank.tagger = Attribution()
                    blank.emailIn(message, fill=true)
                    blank.committish = [c for c in self.chosen().commits()][-1].mark
                    #self.chosen().addEvent(blank)
                else:
                    blank = Commit()
                    blank.committer = Attribution()
                    blank.emailIn(message, fill=true)
                    blank.mark = self.chosen().newmark()
                    blank.repo = self.chosen()
                    if not blank.branch:
                        # Avoids crapping out on name lookup.
                        blank.branch = "generated-" + blank.mark[1:]
                    if not self.selection or len(self.selection) != 1:
                        self.chosen().addEvent(blank)
                    else:
                        event = self.chosen().events[self.selection[0]]
                        blank.setParents([event])
                        self.chosen().addEvent(blank, where=self.selection[0]+1)
            self.chosen().declare_sequence_mutation("event creation")
            return
        # Normal case - no --create
        for (i, message) in enumerate(update_list):
            event = None
            if "Event-Number" in message:
                try:
                    eventnum = int(message["Event-Number"]) - 1
                except ValueError:
                    complain("event number garbled in update %d" % (i+1,))
                    errors += 1
                else:
                    if eventnum < 0 or eventnum >= len(self.chosen()):
                        complain("event number %d out of range in update %d" \
                                        % (eventnum, i+1))
                        errors += 1
                    else:
                        event = self.chosen()[eventnum]
            else if "Legacy-ID" in message:
                try:
                    event = legacyMap[message["Legacy-ID"]]
                except KeyError:
                    complain("no commit matches legacy-ID %s" \
                                      % message["Legacy-ID"])
                    errors += 1
            else if "Event-Mark" in message:
                event = self.chosen().markToEvent(message["Event-Mark"])
                if not event:
                    complain("no commit matches mark %s" \
                             % message["Event-Mark"])
                    errors += 1
            else if "Author" in message and "Author-Date" in message:
                blank = Commit()
                blank.authors.append(Attribution())
                blank.emailIn(message)
                stamp = blank.action_stamp()
                try:
                    event = attribution_by_author[stamp]
                except KeyError:
                    complain("no commit matches stamp %s" % stamp)
                    errors += 1
                if author_counts[stamp] > 1:
                    complain("multiple events (%d) match %s" % (author_counts[stamp], stamp))
                    errors += 1
            else if "Committer" in message and "Committer-Date" in message:
                blank = Commit()
                blank.committer = Attribution()
                blank.emailIn(message)
                stamp = blank.committer.action_stamp()
                try:
                    event = attribution_by_committer[stamp]
                except KeyError:
                    complain("no commit matches stamp %s" % stamp)
                    errors += 1
                if committer_counts[stamp] > 1:
                    complain("multiple events (%d) match %s" % (committer_counts[stamp], stamp))
                    errors += 1
            else if "Tagger" in message and "Tagger-Date" in message:
                blank = Tag()
                blank.tagger = Attribution()
                blank.emailIn(message)
                stamp = blank.tagger.action_stamp()
                try:
                    event = attribution_by_author[stamp]
                except KeyError:
                    complain("no tag matches stamp %s" % stamp)
                    errors += 1
                if author_counts[stamp] > 1:
                    complain("multiple events match %s" % stamp)
                    errors += 1
            else if "Tag-Name" in message:
                blank = Tag()
                blank.tagger = Attribution()
                blank.emailIn(message)
                try:
                    event = name_map[blank.name]
                except KeyError:
                    complain("no tag matches name %s" % blank.name)
                    errors += 1
            else:
                complain("no commit matches update %d:\n%s" % (i+1, message.as_string()))
                errors += 1
            if event is not None and not hasattr(event, "emailIn"):
                try:
                    complain("event %d cannot be modified"%(event.index()+1))
                except AttributeError:
                    complain("event cannot be modified")
                errors += 1
            # Always append, even None, to stay in sync with update_list
            events.append(event)
        if errors > 0:
            raise Recoverable("%d errors in metadata updates" % errors)
        # Now apply the updates
        changers = []
        for (i, (event, update)) in enumerate(zip(events, update_list)):
            if "Check-Text" in update and not event.comment.strip().startswith(update["Check-Text"].strip()):
                raise Recoverable("check text mismatch at %s (input %s of %s), expected %s saw %s, bailing out" % (event.action_stamp(), i+1, len(update_list), repr(update["Check-Text"]), repr(event.comment[:64])))
            if '--empty-only' in parse.options:
                if event.comment != update.get_payload() and not emptyComment(event.comment):
                    raise Recoverable("nonempty comment at %s (input %s of %s), bailing out" % (event.action_stamp(), i+1, len(update_list)))
            if event.emailIn(update):
                changers.append(update)
        if verbose:
            if not changers:
                complain("no events modified by mailbox_in.")
            else:
                complain("%d events modified by mailbox_in." % len(changers))
        if parse.stdout != os.Stdout:
            if "--changed" in parse.options:
                for update in changers:
                    parse.stdout.write(MessageBlockDivider + "\n" + update.as_string(unixfrom=false))

    func help_edit():
        os.Stdout.write("""
Report the selection set of events to a tempfile as mailbox_out does,
call an editor on it, and update from the result as mailbox_in does.
If you do not specify an editor name as second argument, it will be
taken from the $EDITOR variable in your environment.
If $EDITOR is not set, /usr/bin/editor will be used as a fallback
if it exists as a symlink to your default editor, as is the case on
Debian, Ubuntu and their derivatives.

Normally this command ignores blobs because mailbox_out does.
However, if you specify a selection set consisting of a single
blob, your editor will be called on the blob file.

Supports < and > redirection.
""")
    func do_edit(self, line):
        "Edit metadata interactively."
        if not self.chosen():
            complain("no repo is loaded")
            return
        if self.selection is None:
            self.selection = [n for n, o2 in enumerate(self.chosen()) \
                              if hasattr(o2, "emailOut")]
        self.edit(self.selection, line)

    func help_filter():
        os.Stdout.write("""
Run blobs, commit comments and committer/author names, or tag comments
and tag committer names in the selection set through the filter
specified on the command line.

With any mode other than --dedos, attempting to specify a selection
set including both blobs and non-blobs (that is, commits or tags)
throws an error. Inline content in commits is filtered when the
selection set contains (only) blobs and the commit is within the range
bounded by the earliest and latest blob in the specification.

When filtering blobs, if the command line contains the magic cookie
'%PATHS%' it is replaced with a space-separated list of all paths
that reference the blob.

With --shell, the remainder of the line specifies a filter as a
shell command. Each blob or comment is presented to the filter on
standard input; the content is replaced with whatever the filter emits
to standard output.

With --regex, the remainder of the line is expected to be a Go
regular expression substitution written as /from/to/ with 'from' and
'to' being passed as arguments to the standard re.sub() function and
that applied to modify the content. Actually, any non-space character
will work as a delimiter in place of the /; this makes it easier to
use / in patterns. Ordinarily only the first such substitution is
performed; putting 'g' after the slash replaces globally, and a
numeric literal gives the maximum number of substitutions to
perform. Other flags available restrict substiution scope - 'c' for
comment text only, 'C' for committer name only, 'a' for author names
only.

With --replace, the behavior is like --regexp but the expressions are
not interpreted as regular expressions. (This is slighly faster).

With --dedos, DOS/Windows-style \\r\\n line terminators are replaced with \\n.
""")
    func do_filter(self, line):
        if not self.chosen():
            complain("no repo is loaded")
            return
        if not line:
            complain("no filter is specified")
            return
        if self.selection is None:
            complain("no selection")
            return
        class FilterCommand:
            func __init__(self, repo, filtercmd):
                "Initialize the filter from the command line."
                self.repo = repo
                self.filtercmd = None
                self.sub = None
                self.regex = None
                self.attributes = set([])
                # Must not use LineParse here as it would try to strip options
                # in shell commands.
                if filtercmd.startswith('--shell'):
                    self.filtercmd = filtercmd[7:].lstrip()
                    self.attributes = {"c", "a", "C"}
                else if filtercmd.startswith('--regex') or filtercmd.startswith('--replace'):
                    firstspace = filtercmd.find(' ')
                    if firstspace == -1:
                        raise Recoverable("missing filter specification")
                    stripped = filtercmd[firstspace:].lstrip()
                    parts = stripped.split(stripped[0])
                    subflags = parts[-1]
                    if len(parts) != 4:
                        raise Recoverable("malformed filter specification")
                    else if parts[0]:
                        raise Recoverable("bad prefix '%s' on filter specification" % parts[0])
                    else if subflags and not re.match(r"[0-9]*g?".encode('ascii'), polybytes(subflags)):
                        raise Recoverable("unrecognized filter flags")
                    else if "%PATHS%" in filtercmd:
                        raise Recoverable("%PATHS% is not yet supported in regex filters")
                    else:
                        subcount = 1
                        while subflags:
                            flag = subflags[0]
                            subflags = subflags[:-1]
                            if flag == "g":
                                subcount = 0
                            else if flag in {"c", "a", "C"}:
                                self.attributes.add(flag)
                            else if flag.isdigit():
                                subcount = int(subflags)
                            else:
                                raise Recoverable("unknown filter flag")
                        if not self.attributes:
                            self.attributes = {"c", "a", "C"}
                        # subcount 0 does not reliably work as it should
                        if filtercmd.startswith('--regex'):
                            try:
                                pattern = parts[1]
                                if str is not bytes:
                                    pattern = pattern.encode(master_encoding)
                                self.regex = regexp.MustCompile(pattern)
                            except sre_constants.error as e:
                                raise Recoverable("filter compilation error - %s" % e)
                            self.sub = lambda s: polystr(self.regex.sub(polybytes(parts[2]),
                                                                        polybytes(s),
                                                                        len(polybytes(s)) if subcount == 0 else subcount))
                        else if filtercmd.startswith('--replace'):
                            self.sub = lambda s: s.replace(parts[1],
                                                           parts[2],
                                                           len(s) if subcount == 0 else subcount)
                else if filtercmd.startswith('--dedos'):
                    if not self.attributes:
                        self.attributes = {"c", "a", "C"}
                    self.sub = lambda s: s.replace("\r\n", "\n")
                else:
                    raise Recoverable("--shell or --regex or --dedos required")
            func do(self, content, pathsubst=""):
                "Perform the filter on string content or a file."
                if self.filtercmd:
                    if pathsubst:
                        filtercmd = self.filtercmd.replace("%PATHS%", pathsubst)
                    else:
                        filtercmd = self.filtercmd
                    (indesc, intmp) = tempfile.mkstemp(prefix=self.repo.subdir())
                    (outdesc, outtmp) = tempfile.mkstemp(prefix=self.repo.subdir())
                    try:
                        assert indesc > -1 and outdesc > -1    # pacify pylint
                        with open(intmp, "wb") as wfp:
                            wfp.write(polybytes(content))
                        return polystr(captureFromProcess("%s <%s" % (filtercmd, intmp)))
                    finally:
                        os.remove(intmp)
                        os.close(indesc)
                        os.remove(outtmp)
                        os.close(outdesc)
                else if self.sub:
                    return self.sub(content)
                else:
                    raise Recoverable("unknown mode in filter command")
        # Mainline of do_filter() continues:
        filterhook = FilterCommand(self.chosen(), line)
        self.data_traverse(prompt="Filtering",
                           hook=filterhook.do,
                           attributes=filterhook.attributes,
                           safety=not line.startswith('--dedos'))

    func help_transcode():
        os.Stdout.write("""
Transcode blobs, commit comments and committer/author names, or tag
comments and tag committer names in the selection set to UTF-8 from
the character encoding specified on the command line.

Attempting to specify a selection set including both blobs and
non-blobs (that is, commits or tags) throws an error. Inline content
in commits is filtered when the selection set contains (only) blobs
and the commit is within the range bounded by the earliest and latest
blob in the specification.

The encoding argument must name one of the codecs known to the Python
standard codecs library. In particular, 'latin-1' is a valid codec name.

Errors in this command are fatal, because an error may leave
repository objects in a damaged state.
""")
    func do_transcode(self, line):
        if not self.chosen():
            complain("no repo is loaded")
            return
        else if self.selection is None:
            self.selection = self.chosen().all()
        (codec, line) = RepoSurgeon.pop_token(line)
        func transcode(txt, _paths=None):
            return polystr(codecs.encode(codecs.decode(polybytes(txt), codec), "utf-8"))
        try:
            self.data_traverse(prompt="Transcoding",
                               hook=transcode,
                               attributes={"c", "a", "C"},
                               safety=true)
        except UnicodeError:
            raise Fatal("UnicodeError during transcoding")

    func help_setfield():
        os.Stdout.write("""
In the selected objects (defaulting to none) set every instance of a
named field to a string value.  The string may be quoted to include
whitespace, and use backslash escapes interpreted by the Python
string-escape codec, such as \\s.

Attempts to set nonexistent attributes are ignored. Valid values for
the attribute are internal Python field names; in particular, for
commits, 'comment' and 'branch' are legal.  Consult the source code
for other interesting values.

The special fieldnames 'author', 'commitdate' and 'authdate' apply
only to commits in the range.  The latter two sets attribution
dates. The former sets the author's name and email address (assuming
the value can be parsed for both), copying the committer
timestamp. The author's timezone may be deduced from the email
address.
""")
    func do_setfield(self, line):
        "Set an object field from a string."
        if not self.chosen():
            complain("no repo is loaded")
            return
        repo = self.chosen()
        if self.selection is None:
            raise Recoverable("no selection")
        fields = shlex.split(line)
        if not fields or len(fields) != 2:
            raise Recoverable("missing or malformed setfield line")
        field = fields[0]
        value = string_escape(fields[1])
        for _, event in self.selected():
            if hasattr(event, field):
                setattr(event, field, value)
            else if field == "author" and isinstance(event, Commit):
                attr = value
                attr += " " + str(event.committer.date.timestamp)
                attr += " " + event.committer.date.orig_tz_string
                newattr = Attribution(attr)
                for (_, nemail, tz) in repo.authormap.values():
                    if newattr.email == nemail:
                        newattr.date.set_tz(tz)
                        break
                event.authors.append(newattr)
            else if field == "commitdate" and isinstance(event, Commit):
                event.committer.date = Date(value)
            else if field == "authdate" and isinstance(event, Commit):
                event.authors[0].date = Date(value)

    func help_setperm():
        os.Stdout.write("""
For the selected objects (defaulting to none) take the first argument as an
octal literal describing permissions.  All subsequent arguments are paths.
For each M fileop in the selection set and exactly matching one of the
paths, patch the permission field to the first argument value.
""")
    func do_setperm(self, line):
        "Set permissions on M fileops matching a path list."
        if not self.chosen():
            complain("no repo is loaded")
            return
        if self.selection is None:
            raise Recoverable("no selection")
        fields = shlex.split(line)
        if not fields or len(fields) < 2:
            raise Recoverable("missing or malformed setperm line")
        perm = fields.pop(0)
        if perm not in ('100644', '100755', '120000'):
            raise Recoverable("unexpected permission literal %s" % perm)
        with Baton(prompt="patching modes", enable=(verbose == 1)) as baton:
            for _, event in self.selected(Commit):
                for op in event.operations():
                    if op.op == opM and op.path in fields:
                        op.mode = perm
                baton.twirl("")

    func help_append():
        os.Stdout.write("""
Append text to the comments of commits and tags in the specified
selection set. The text is the first token of the command and may
be a quoted string. C-style escape sequences in the string are
interpreted using Python's string_decode codec.

If the option --rstrip is given, the comment is right-stripped before
the new text is appended.
""")
    func do_append(self, line):
        "Append a line to comments in the specified selection set."
        if not self.chosen():
            complain("no repo is loaded")
            return
        if self.selection is None:
            raise Recoverable("no selection")
        with RepoSurgeon.LineParse(self, line) as parse:
            fields = shlex.split(parse.line)
            if not fields:
                raise Recoverable("missing append line")
            line = string_escape(fields[0])
            for _, event in self.selected((Tag, Commit)):
                if '--rstrip' in parse.options:
                    event.comment = event.comment.rstrip()
                event.comment += line

    func help_squash():
        os.Stdout.write("""
Combine a selection set of events; this may mean deleting them or
pushing their content forward or back onto a target commit just
outside the selection range, depending on policy flags.

The default selection set for this command is empty.  Blobs cannot be
directly affected by this command; they move or are deleted only when
removal of fileops associated with commits requires this.
""")
    func do_squash(self, line):
        "Squash events in the specified selection set."
        if not self.chosen():
            complain("no repo is loaded")
            return
        if self.selection is None:
            self.selection = []
        with RepoSurgeon.LineParse(self, line) as parse:
            self.chosen().squash(self.selection, parse.options)
    func help_delete():
        os.Stdout.write("""
Delete a selection set of events.  The default selection set for this
command is empty.  Tags, resets, and passthroughs are deleted with no
side effects.  Blobs cannot be directly deleted with this command; they
are removed only when removal of fileops associated with commits requires this.

When a commit is deleted, what becomes of tags and fileops attached to
it is controlled by policy flags.  A delete is equivalent to a
squash with the --delete flag.
""")
    func do_delete(self, line):
        "Delete events in the specified selection set."
        if not self.chosen():
            complain("no repo is loaded")
            return
        if self.selection is None:
            self.selection = []
        with RepoSurgeon.LineParse(self, line) as parse:
            self.chosen().squash(self.selection, set(["--delete"]) | parse.options)

    func help_coalesce():
        os.Stdout.write("""
Scan the selection set (defaulting to all) for runs of commits with
identical comments close to each other in time (this is a common form
of scar tissues in repository up-conversions from older file-oriented
version-control systems).  Merge these cliques by pushing their
fileops and tags up to the last commit, in order.

The optional argument, if present, is a maximum time separation in
seconds; the default is 90 seconds.

With the --changelog option, any commit with a comment containing the
string 'empty log message' (such as is generated by CVS) and containing
exactly one file operation modifing a path ending in 'ChangeLog' is
treated specially.  Such ChangeLog commits are considered to match any
commit before them by content, and will coalesce with it if the committer
matches and the commit separation is small enough.  This option handles
a convention used by Free Software Foundation projects.

With  the --debug option, show messages about mismatches.
""")
    func do_coalesce(self, line):
        "Coalesce events in the specified selection set."
        repo = self.chosen()
        if not repo:
            complain("no repo is loaded")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        with RepoSurgeon.LineParse(self, line) as parse:
            timefuzz = 90
            changelog = "--changelog" in parse.options
            if parse.line:
                try:
                    timefuzz = int(parse.line)
                except ValueError:
                    raise Recoverable("time-fuzz value must be an integer")
            func is_clog(commit):
                return "empty log message" in commit.comment \
                           and len(commit.operations()) == 1 \
                           and commit.operations()[0].op == opM \
                           and commit.operations()[0].path.endswith("ChangeLog")
            func coalesce_match(cthis, cnext):
                if cthis.committer.email != cnext.committer.email:
                    if verbose >= debugDELETE or '--debug' in parse.options:
                        complain("committer email mismatch at %s" % cnext.idMe())
                    return false
                if cthis.committer.date.delta(cnext.committer.date) >= timefuzz:
                    if verbose >= debugDELETE or '--debug' in parse.options:
                        complain("time fuzz exceeded at %s" % cnext.idMe())
                    return false
                if changelog and not is_clog(cthis) and is_clog(cnext):
                    return true
                if cthis.comment != cnext.comment:
                    if verbose >= debugDELETE or '--debug' in parse.options:
                        complain("comment mismatch at %s" % cnext.idMe())
                    return false
                return true
            eligible = {}
            squashes = []
            for (_i, commit) in self.selected(Commit):
                if commit.branch not in eligible:
                    # No active commit span for this branch - start one
                    # with the mark of this commit
                    eligible[commit.branch] = [commit.mark]
                else if coalesce_match(
                    repo.markToEvent(eligible[commit.branch][-1]),
                    commit):
                    # This commit matches the one at the end of its branch span.
                    # Append its mark to the span.
                    eligible[commit.branch].append(commit.mark)
                else:
                    # This commit doesn't match the one at the end of its span.
                    # Coalesce the span and start a new one with this commit.
                    if len(eligible[commit.branch]) > 1:
                        squashes.append(eligible[commit.branch])
                    eligible[commit.branch] = [commit.mark]
            for endspan in eligible.values():
                if len(endspan) > 1:
                    squashes.append(endspan)
            for span in squashes:
                # Prevent lossage when last is a ChangeLog commit
                repo.markToEvent(span[-1]).comment = repo.markToEvent(span[0]).comment
                repo.squash([repo.find(mark) for mark in span[:-1]], ("--coalesce",))
            if verbose > 0:
                announce(debugSHOUT, "%d spans coalesced." % len(squashes))
    func help_add():
        os.Stdout.write("""
From a specified commit, add a specified fileop. The syntax is

     add {D path | M perm mark path | R source target | C source target}

For a D operation to be valid there must be an M operation for the path
in the commit's ancestry.  For an M operation to be valid, the 'perm'
part must be a token ending with 755 or 644 and the 'mark' must
refer to a blob that precedes the commit location.  For an R or C
operation to be valid, there must be an M operation for the source
in the commit's ancestry.

""")
    func do_add(self, line):
        "Add a fileop to a specified commit."
        if not self.chosen():
            complain("no repo is loaded")
            return
        if self.selection is None:
            self.selection = []
        repo = self.chosen()
        fields = shlex.split(line)
        if len(fields) < 2:
            raise Recoverable("add requires an operation type and arguments")
        optype = fields[0]
        if optype == "D":
            path = fields[1]
            for _, event in self.selected(Commit):
                if path in event.paths():
                    raise Recoverable("%s already has an op for %s" \
                                      % (event.mark, path))
                if repo.ancestor_count(event, path) == 0:
                    raise Recoverable("no previous M for %s" % path)
        else if optype == "M":
            if len(fields) != 4:
                raise Recoverable("wrong field count in add command")
            else if fields[1].endswith("644"):
                perms = 0o100644
            else if fields[1].endswith("755"):
                perms = 0o100755
            mark = fields[2]
            if not mark.startswith(":"):
                raise Recoverable("garbled mark %s in add command" % mark)
            try:
                markval = int(mark[1:])
            except ValueError:
                raise Recoverable("non-numeric mark %s in add command" % mark)
            if not isinstance(repo.markToEvent(mark), Blob):
                raise Recoverable("mark %s in add command does not refer to a blob" % mark)
            else if markval >= min(self.selection):
                raise Recoverable("mark %s in add command is after add location" % mark)
            path = fields[3]
            for _, event in self.selected(Commit):
                if path in event.paths():
                    raise Recoverable("%s already has an op for %s" \
                                      % (event.mark, path))
        else if optype in (opR, "C"):
            try:
                source = fields[1]
                target = fields[2]
            except IndexError:
                raise Recoverable("too few arguments in add %s" % optype)
            for _, event in self.selected(Commit):
                if source in event.paths() or target in event.paths():
                    raise Recoverable("%s already has an op for %s or %s" \
                                      % (event.mark, source, target))
                if repo.ancestor_count(event, source) == 0:
                    raise Recoverable("no previous M for %s" % source)
        else:
            raise Recoverable("unknown operation type %s in add command" % optype)
        for _, event in self.selected(Commit):
            event.invalidatePathsetCache()
            fileop = FileOp(self.chosen())
            if optype == "D":
                fileop.construct("D", path)
            else if optype == "M":
                fileop.construct(opM, perms, mark, path)
            else if optype in (opR, "C"):
                fileop.construct(optype, source, target)
            event.appendOperation(fileop)

    func help_blob():
        os.Stdout.write("""
Syntax:

     blob

Create a blob at mark :1 after renumbering other marks starting from
:2.  Data is taken from stdin, which may be a here-doc.  This can be
used with the add command to patch data into a repository.
""")
    func do_blob(self, line):
        "Add a fileop to a specified commit."
        if not self.chosen():
            complain("no repo is loaded")
            return
        repo = self.chosen()
        repo.renumber(2)
        blob = Blob(repo)
        blob.setMark(":1")
        repo.addEvent(blob, where=0)
        with RepoSurgeon.LineParse(self, line, capabilities=["stdin"]) as parse:
            blob.setContent(parse.stdin.read())
        repo.declare_sequence_mutation("adding blob")
        repo.invalidateNamecache()

    func help_remove():
        os.Stdout.write("""
From a specified commit, remove a specified fileop. The syntax is:

     remove [DMRCN] OP [to COMMIT]

The OP must be one of (a) the keyword 'deletes', (b) a file path, (c)
a file path preceded by an op type set (some subset of the letters
DMRCN), or (c) a 1-origin numeric index.  The 'deletes' keyword
selects all D fileops in the commit; the others select one each.

If the to clause is present, the removed op is appended to the
commit specified by the following singleton selection set.  This option
cannot be combined with 'deletes'.

Note that this command does not attempt to scavenge blobs even if the
deleted fileop might be the only reference to them. This behavior may
change in a future release.
""")
    func do_remove(self, line):
        "Delete a fileop from a specified commit."
        repo =  self.chosen()
        if not repo:
            complain("no repo is loaded")
            return
        if self.selection is None:
            self.selection = []
        orig = line
        (opindex, line) = RepoSurgeon.pop_token(line)
        # FIXME: This needs more general parsing
        optypes = "DMRCN"
        if re.match(r"[DMRCN]+$".encode('ascii'), polybytes(opindex)):
            optypes = opindex
            (opindex, line) = RepoSurgeon.pop_token(line)
        for ie, event in self.selected(Commit):
            event.invalidatePathsetCache()
            if opindex == "deletes":
                event.setOperations([e for e in event.operations() if e.op != opD])
                return
            for (ind, op) in enumerate(event.operations()):
                if hasattr(op, "op") and getattr(op, "op") not in optypes:
                    continue
                if hasattr(op, "path") and getattr(op, "path") == opindex:
                    break
                if hasattr(op, "source") and getattr(op, "source") == opindex:
                    break
                if hasattr(op, "target") and getattr(op, "target") == opindex:
                    break
            else:
                try:
                    ind = int(opindex) - 1
                except (ValueError, IndexError):
                    complain("invalid or missing fileop specification '%s' on %s" % (opindex, repr(orig)))
                    return
            target = None
            if line:
                (verb, line)  = RepoSurgeon.pop_token(line)
                if verb == 'to':
                    self.set_selection_set(line)
                    if len(self.selection) != 1:
                        raise Recoverable("remove to requires a singleton selection")
                    target = self.selection[0]
            try:
                removed = event.operations().pop(ind)
                if target:
                    repo.events[target].appendOperation(removed)
                    # Blob might have to move, too - we need to keep the
                    # relocated op from having an unresolvable forward
                    # mark reference.
                    if removed.ref is not None and target < ie:
                        blob = repo.events.pop(repo.find(removed.ref))
                        repo.addEvent(blob, target)
                        repo.declare_sequence_mutation("blob move")
                    # FIXME: Scavenge blobs left with no references
            except IndexError:
                complain("out-of-range fileop index %s" % ind)
                return

    func help_renumber():
        os.Stdout.write("""
Renumber the marks in a repository, from :1 up to <n> where <n> is the
count of the last mark. Just in case an importer ever cares about mark
ordering or gaps in the sequence.
""")
    func do_renumber(self, unused):
        "Renumber the marks in the selected repo."
        assert unused is not None    # pacify pylint
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        self.repo.renumber()

    func help_dedup():
        os.Stdout.write("""
Deduplicate blobs in the selection set.  If multiple blobs in the selection
set have the same SHA1, throw away all but the first, and change fileops
referencing them to instead reference the (kept) first blob.
""")
    func do_dedup(self, line):
        "Deduplicate identical (up to SHA1) blobs within the selection set"
        pacify_pylint(line)
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        blob_map = {} # hash -> mark
        dup_map = {} # duplicate mark -> canonical mark
        for _, event in self.selected():
            if isinstance(event, Blob):
                sha = event.sha()
                if sha in blob_map:
                    dup_map[event.mark] = blob_map[sha]
                else:
                    blob_map[sha] = event.mark
        self.chosen().dedup(dup_map)
        return

    func help_timeoffset():
        os.Stdout.write("""
Apply a time offset to all time/date stamps in the selected set.  An offset
argument is required; it may be in the form [+-]ss, [+-]mm:ss or [+-]hh:mm:ss.
The leading sign is required to distingush it from a selection expression.

Optionally you may also specify another argument in the form [+-]hhmm, a
timeone literal to apply.  To apply a timezone without an offset, use
an offset literal of +0 or -0.
""")
    func do_timeoffset(self, line):
        "Apply a time offset to all dates in selected events."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        if not line:
            complain("a signed time offset argument is required.")
            return
        else if line[0] not in ('-', '+'):
            complain("time offset argument must begin with + or -.")
            return
        line = str(line)   # pacify pylint by forcing string type
        args = line.split()
        h = m = "0"
        if args[0].count(":") == 0:
            s = args[0]
        else if args[0].count(":") == 1:
            (m, s) = args[0].split(":")
        else if args[0].count(":") == 2:
            (h, m, s) = args[0].split(":")
        else:
            complain("too many colons")
            return
        try:
            offset = int(h)*360 + int(m)*60 + int(s)
        except ValueError:
            complain("expected numeric literals in date format")
            return
        if len(args) > 1:
            if not re.match(r"[+-][0-9][0-9][0-9][0-9]".encode('ascii'), polybytes(args[1])):
                complain("expected timezone literal to be [+-]hhmm")
        for _, event in self.selected():
            if isinstance(event, Tag):
                if event.tagger:
                    event.tagger.date.timestamp += offset
                    if len(args) > 1:
                        event.tagger.date.orig_tz_string = args[1]
            else if isinstance(event, Commit):
                event.committer.date.timestamp += offset
                if len(args) > 1:
                    event.committer.date.orig_tz_string = args[1]
                for author in event.authors:
                    author.date.timestamp += offset
                    if len(args) > 1:
                        author.date.orig_tz_string = args[1]

    func help_when():
        os.Stdout.write("""
Interconvert between git timestamps (integer Unix time plus TZ) and
RFC3339 format.  Takes one argument, autodetects the format.  Useful
when eyeballing export streams.  Also accepts any other supported
date format and converts to RFC3339.
""")
    func do_when(self, line):
        "Interconvert between integer Unix time and RFC3339 format."
        if not line:
            complain("a timestamp in either integer or RFC3339 form is required.")
            return
        d = Date(line, Recoverable)
        if 'Z' in line:
            os.Stdout.write(polystr(d) + "\n")
        else:
            os.Stdout.write(d.rfc3339() + "\n")

    func help_divide():
        os.Stdout.write("""
Attempt to partition a repo by cutting the parent-child link
between two specified commits (they must be adjacent). Does not take a
general selection-set argument.  It is only necessary to specify the
parent commit, unless it has multiple children in which case the child
commit must follow (separate it with a comma).

If the repo was named 'foo', you will normally end up with two repos
named 'foo-early' and 'foo-late'.  But if the commit graph would
remain connected through another path after the cut, the behavior
changes.  In this case, if the parent and child were on the same
branch 'qux', the branch segments are renamed 'qux-early' and
'qux-late'.
""")
    func do_divide(self, _line):
        "Attempt to topologically partition the repo."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = []
        if len(self.selection) == 0:
            complain("one or possibly two arguments specifying a link are required")
            return
        early = self.chosen()[self.selection[0]]
        if not isinstance(early, Commit):
            complain("first element of selection is not a commit")
            return
        possibles = list(early.children())
        if len(self.selection) == 1:
            if len(possibles) > 1:
                complain("commit has multiple children, one must be specified")
                return
            else if len(possibles) == 1:
                late = possibles[0]
            else:
                complain("parent has no children")
                return
        else if len(self.selection) == 2:
            late = self.chosen()[self.selection[1]]
            if not isinstance(late, Commit):
                complain("last element of selection is not a commit")
                return
            if early.mark not in late.parentMarks():
                complain("not a parent-child pair")
                return
        else if len(self.selection) > 2:
            complain("too many arguments")
        assert(early and late)
        # Try the topological cut first
        if not self.cut(early, late):
            # If that failed, cut anyway and rename the branch segments
            late.removeParent(early)
            if early.branch != late.branch:
                announce(debugSHOUT, "no branch renames were required")
            else:
                basename = early.branch
                announce(debugSHOUT, "%s has been split into %s-early and %s-late" \
                         % (basename, basename, basename))
                for (i, event) in enumerate(self.chosen().events):
                    if hasattr(event, "branch") and event.branch == basename:
                        if i <= self.selection[0]:
                            event.branch += "-early"
                        else:
                            event.branch += "-late"
        if verbose:
            self.do_choose("")

    func help_expunge():
        os.Stdout.write("""
Expunge files from the selected portion of the repo history; the
default is the entire history.  The arguments to this command may be
paths or Python regular expressions matching paths (regexps must
be marked by being surrounded with //).

All filemodify (M) operations and delete (D) operations involving a
matched file in the selected set of events are disconnected from the
repo and put in a removal set.  Renames are followed as the tool walks
forward in the selection set; each triggers a warning message. If a
selected file is a copy (C) target, the copy will be deleted and a
warning message issued. If a selected file is a copy source, the copy
target will be added to the list of paths to be deleted and a warning
issued.

After file expunges have been performed, any commits with no
remaining file operations will be deleted, and any tags pointing to
them. By default each deleted commit is replaced with a tag of the form
emptycommit-<ident> on the preceding commit unless --notagify is
specified as an argument.  Commits with deleted fileops pointing both
in and outside the path set are not deleted, but are cloned into the
removal set.

The removal set is not discarded. It is assembled into a new
repository named after the old one with the suffix "-expunges" added.
Thus, this command can be used to carve a repository into sections by
file path matches.
""")
    func do_expunge(self, line):
        "Expunge files from the chosen repository."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        self.expunge(self.selection, line.split())

    func help_split():
        os.Stdout.write("""
Split a specified commit in two, the opposite of squash.

    split at M
    split by PREFIX

The selection set is required to be a commit location; the modifier is
a preposition which indicates which splitting method to use. If the
preposition is 'at', then the third argument must be an integer
1-origin index of a file operation within the commit. If it is 'by',
then the third argument must be a pathname to be matched.

The commit is copied and inserted into a new position in the
event sequence, immediately following itself; the duplicate becomes
the child of the original, and replaces it as parent of the original's
children. Commit metadata is duplicated; the mark of the new commit is
then changed.  If the new commit has a legacy ID, the suffix '.split' is
appended to it.

Finally, some file operations - starting at the one matched or indexed
by the split argument - are moved forward from the original commit
into the new one.  Legal indices are 2-n, where n is the number of
file operations in the original commit.
""")
    func do_split(self, line):
        "Split a commit."
        if self.chosen() is None:
            raise Recoverable("no repo has been chosen.")
        if self.selection is None:
            self.selection = []
        if len(self.selection) != 1:
            raise Recoverable("selection of a single commit required for this command")
        where = self.selection[0]
        event = self.chosen()[where]
        if not isinstance(event, Commit):
            raise Recoverable("fileop argument doesn't point at a commit")
        line = str(line)   # pacify pylint by forcing string type
        try:
            (prep, obj) = line.split()
        except ValueError:
            raise Recoverable("ill-formed split command")
        if prep == 'at':
            try:
                splitpoint = int(obj) - 1
                if splitpoint not in range(1, len(event.operations())):
                    raise Recoverable("fileop index %d out of range" % splitpoint)
                self.chosen().split_commit_by_index(where, splitpoint)
            except ValueError:
                raise Recoverable("expected integer fileop index (1-origin)")
        else if prep == 'by':
            split = self.chosen().split_commit_by_prefix(where, obj)
            if not split:
                raise Recoverable("couldn't find '%s' in a fileop path." \
                                  % obj)
        else:
            raise Recoverable("don't know what to do for preposition %s" % prep)
        if verbose:
            announce(debugSHOUT, "new commits are events %s and %s." % (where+1, where+2))

    func help_unite():
        os.Stdout.write("""
Unite repositories. Name any number of loaded repositories; they will
be united into one union repo and removed from the load list.  The
union repo will be selected.

The root of each repo (other than the oldest repo) will be grafted as
a child to the last commit in the dump with a preceding commit date.
This will produce a union repository with one branch for each part.
Running last to first, tag and branch duplicate names will be
disambiguated using the source repository name (thus, recent
duplicates will get priority over older ones). After all grafts, marks
will be renumbered.

The name of the new repo will be the names of all parts concatenated,
separated by '+'. It will have no source directory or preferred system
type.

With the option --prune, at each join generate D ops for every
file that doesn't have a modify operation in the root commit of the
branch being grafted on.
""")
    func do_unite(self, line):
        "Unite repos together."
        self.unchoose()
        factors = []
        with RepoSurgeon.LineParse(self, line) as parse:
            for name in parse.line.split():
                repo = self.repo_by_name(name)
                if repo is None:
                    raise Recoverable("no such repo as %s" % name)
                else:
                    factors.append(repo)
            if not factors or len(factors) < 2:
                raise Recoverable("unite requires repo name arguments")
            self.unite(factors, parse.options)
        if verbose:
            self.do_choose('')

    func help_graft():
        os.Stdout.write("""
For when unite doesn't give you enough control. This command may have
either of two forms, selected by the size of the selection set.  The
first argument is always required to be the name of a loaded repo.

If the selection set is of size 1, it must identify a single commit in
the currently chosen repo; in this case the name repo's root will
become a child of the specified commit. If the selection set is
empty, the named repo must contain one or more callouts matching a
commits in the currently chosen repo.

Labels and branches in the named repo are prefixed with its name; then
it is grafted to the selected one. Any other callouts in the named repo are also
resolved in the context of the currently chosen one. Finally, the
named repo is removed from the load list.

With the option --prune, prepend a deleteall operation into the root
of the grafted repository.
""")
    func do_graft(self, line):
        "Graft a named repo onto the selected one."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if not self.repolist:
            raise Recoverable("no repositories are loaded.")
        with RepoSurgeon.LineParse(self, line) as parse:
            if parse.line in self.reponames():
                graft_repo = self.repo_by_name(parse.line)
            else:
                raise Recoverable("no such repo as %s" % parse.line)
            require_graft_point = true
            if self.selection is not None and len(self.selection) == 1:
                graft_point = self.selection[0]
            else:
                for commit in graft_repo.commits():
                    for parent in commit.parents():
                        if Commit.isCallout(parent.mark):
                            require_graft_point = false
                if not require_graft_point:
                    graft_point = None
                else:
                    raise Recoverable("a singleton selection set is required.")
            # OK, we've got the two repos and the graft point.  Do it.
            self.chosen().graft(graft_repo, graft_point, parse.options)
            self.remove_by_name(graft_repo.name)

    func help_debranch():
        os.Stdout.write("""
Takes one or two arguments which must be the names of source and target
branches; if the second (target) argument is omitted it defaults to 'master'.
The history of the source branch is merged into the history of the target
branch, becoming the history of a subdirectory with the name of the source
branch. Any trailing segment of a branch name is accepted as a synonym for
it; thus 'master' is the same as 'refs/heads/master'.  Any resets of the
source branch are removed.
""")
    func do_debranch(self, line):
        "Turn a branch into a subdirectory."
        if self.chosen() is None:
            complain("no repo has been chosen.")
        args = line.split()
        if not args:
            complain("debranch command requires at least one argument")
        else:
            target = 'refs/heads/master'
            source = args[0]
            if len(args) == 2:
                target = args[1]
            repo = self.chosen()
            branches = repo.branchmap()
            if source not in branches.keys():
                for candidate in branches.keys():
                    if candidate.endswith(os.sep + source):
                        source = candidate
                        break
                else:
                    complain("no branch matches source %s" % source)
                    return
            if target not in branches.keys():
                for candidate in branches.keys():
                    if candidate.endswith(os.sep + target):
                        target = candidate
                        break
                else:
                    complain("no branch matches %s" % target)
                    return
            # Now that the arguments are in proper form, implement
            stip = repo.find(branches[source])
            scommits = repo.ancestors(stip) + [stip]
            scommits.sort()
            ttip = repo.find(branches[target])
            tcommits = repo.ancestors(ttip) + [ttip]
            tcommits.sort()
            # Don't touch commits up to the branch join.
            last_parent = []
            while scommits and tcommits and scommits[0] == tcommits[0]:
                last_parent = [repo.events[scommits[0]].mark]
                scommits.pop(0)
                tcommits.pop(0)
            pref = os.path.basename(source)
            for ci in scommits:
                found = false
                for fileop in repo.events[ci].operations():
                    if fileop.op in (opD, opM):
                        fileop.path = os.path.join(pref, fileop.path)
                        found = true
                    else if fileop.op in (opR, opC):
                        fileop.source = os.path.join(pref, fileop.source)
                        fileop.target = os.path.join(pref, fileop.target)
                        found = true
                if found:
                    repo.events[ci].invalidatePathsetCache()
            merged = sorted(set(scommits + tcommits))
            source_reset = None
            for i in merged:
                event = repo.events[i]
                if last_parent is not None:
                    event.setParentMarks(last_parent + event.parentMarks()[1:])
                event.setBranch(target)
                last_parent = [event.mark]
            for (i, event) in enumerate(self.repo.events):
                if isinstance(event, Reset) and event.ref == source:
                    source_reset = i
            if source_reset is not None:
                del repo.events[source_reset]
            repo.declare_sequence_mutation("debranch operation")

    func help_path():
        os.Stdout.write("""
Rename a path in every fileop of every selected commit.  The
default selection set is all commits. The first argument is interpreted as a
Python regular expression to match against paths; the second may contain
back-reference syntax.

Ordinarily, if the target path already exists in the fileops, or is visible
in the ancestry of the commit, this command throws an error.  With the
--force option, these checks are skipped.
""")
    func do_path(self, line):
        "Rename paths in the history."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        if self.selection is None:
            self.selection = repo.all()
        (source_re, line) = RepoSurgeon.pop_token(line)
        (verb, line) = RepoSurgeon.pop_token(line)
        with RepoSurgeon.LineParse(self, line) as parse:
            if verb == "rename":
                force = '--force' in parse.options
                (target_re, _) = RepoSurgeon.pop_token(parse.line)
                if not target_re:
                    raise Recoverable("no target specified in rename")
                actions = []
                for _,commit in self.selected(Commit):
                    touched = false
                    for fileop in commit.operations():
                        for attr in ("path", "source", "target"):
                            if hasattr(fileop, attr):
                                oldpath = getattr(fileop, attr)
                                if oldpath and re.search(polybytes(source_re), polybytes(oldpath)):
                                    newpath = polystr(re.sub(polybytes(source_re), polybytes(target_re), polybytes(oldpath)))
                                    if not force and commit.visible(newpath):
                                        raise Recoverable("rename at %s failed, %s visible in ancestry" % (commit.idMe(), newpath))
                                    else if not force and newpath in commit.paths():
                                        raise Recoverable("rename at %s failed, %s exists there" % (commit.idMe(), newpath))
                                    else:
                                        actions.append((fileop, attr, newpath))
                                        touched = true
                    if touched:
                        commit.invalidatePathsetCache()
                # All checks must pass before any renames
                for (fileop, attr, newpath) in actions:
                    setattr(fileop, attr, newpath)
            else:
                raise Recoverable("unknown verb '%s' in path command." % verb)

    func help_paths():
        os.Stdout.write("""
Without a modifier, list all paths touched by fileops in
the selection set (which defaults to the entire repo). This
variant does > redirection.

With the 'sub' modifier, take a second argument that is a directory
name and prepend it to every path. With the 'sup' modifier, strip
any directory argument from the start of the path if it appears there;
with no argument, strip the first directory component from every path.
""" )
    func do_paths(self, line):
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        if not line.startswith(("sub", "sup")):
            with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
                allpaths = set()
                for _, event in self.selected(Commit):
                    allpaths.update(event.paths())
                parse.stdout.write("\n".join(sorted(allpaths)) + "\n")
                return
        fields = line.split()
        if fields[0] == "sub":
            if len(fields) < 2:
                raise Fatal("Error paths sub needs a directory name argument")
            prefix = fields[1]
            modified = self.chosen().path_walk(self.selection,
                                               lambda f: os.path.join(prefix,f))
            os.Stdout.write("\n".join(modified) + "\n")
        else if fields[0] == "sup":
            if len(fields) == 1:
                try:
                    modified = self.chosen().path_walk(self.selection,
                                                   lambda f: f[f.find(os.sep)+1:])
                    os.Stdout.write("\n".join(modified) + "\n")
                except IndexError:
                    raise Recoverable("no / in sup path.")
            else:
                prefix = fields[1]
                if not prefix.endswith(os.sep):
                    prefix = prefix + os.sep
                modified = self.chosen().path_walk(self.selection,
                                               lambda f: f[len(prefix):] if f.startswith(prefix) else f)
                os.Stdout.write("\n".join(modified) + "\n")
        self.chosen().invalidateManifests()

    func help_manifest():
        os.Stdout.write("""
Print commit path lists. Takes an optional selection set argument
defaulting to all commits, and an optional Python regular expression.
For each commit in the selection set, print the mapping of all paths in
that commit tree to the corresponding blob marks, mirroring what files
would be created in a checkout of the commit. If a regular expression
is given, only print "path -> mark" lines for paths matching it.
This command supports > redirection.
""")
    func do_manifest(self, line):
        "Print all files (matching the regex) in the selected commits trees."
        if self.chosen() is None:
            raise Recoverable("no repo has been chosen")
        if self.selection is None:
            self.selection = self.chosen().all()
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            filter_func = None
            line = parse.line.strip()
            if line:
                try:
                    filter_func = regexp.MustCompile(line.encode('ascii')).search
                except re.error:
                    raise Recoverable("invalid regular expression")
            for ei, event in self.selected(Commit):
                header = "Event %s, " % repr(ei+1)
                header = header[:-2]
                header += " " + ((72 - len(header)) * "=") + "\n"
                parse.stdout.write(header)
                if event.legacyID:
                    parse.stdout.write("# Legacy-ID: %s\n" % event.legacyID)
                parse.stdout.write("commit %s\n" % event.branch)
                if event.mark:
                    parse.stdout.write("mark %s\n" % event.mark)
                parse.stdout.write("\n")
                if filter_func is None:
                    parse.stdout.write("\n".join("%s -> %s" % (path, mark)
                            for path, (mode, mark, _)
                            in event.manifest().items()))
                else:
                    parse.stdout.write("\n".join("%s -> %s" % (path, mark)
                            for path, (mode, mark, _)
                            in event.manifest().items()
                            if filter_func(polybytes(path))))
                parse.stdout.write("\n")

    func help_tagify():
        os.Stdout.write("""
Search for empty commits and turn them into tags. Takes an optional selection
set argument defaulting to all commits. For each commit in the selection set,
turn it into a tag with the same message and author information if it has no
fileops. By default merge commits are not considered, even if they have no
fileops (thus no tree differences with their first parent). To change that, see
the '--tagify-merges' option.

The name of the generated tag will be 'emptycommit-<ident>', where <ident>
is generated from the legacy ID of the deleted commit, or from its
mark, or from its index in the repository, with a disambiguation
suffix if needed.

tagify currently recognizes three options: first is '--canonicalize' which
makes tagify try harder to detect trivial commits by first ensuring that all
fileops of selected commits will have an actual effect when processed by
fast-import.

The second option is '--tipdeletes' which makes tagify also consider branch
tips with only deleteall fileops to be candidates for tagification. The
corresponding tags get names of the form 'tipdelete-<branchname>' rather than
the default 'emptycommit-<ident>'.

The third option is '--tagify-merges' that makes reposurgeon also
tagify merge commits that have no fileops.  When this is done the
merge link is moved to the tagified commit's parent.
""")
    func do_tagify(self, line):
        "Search for empty commits and turn them into tags."
        repo = self.chosen()
        if repo is None:
            raise Recoverable("no repo has been chosen")
        if self.selection is None:
            self.selection = repo.all()
        with RepoSurgeon.LineParse(self, line) as parse:
            if parse.line:
                raise Recoverable("too many arguments for tagify.")
            before = len([c for c in repo.commits()])
            repo.tagify_empty(
                    commits = self.selection,
                    canonicalize = "--canonicalize" in parse.options,
                    tipdeletes = "--tipdeletes" in parse.options,
                    tagify_merges = "--tagify-merges" in parse.options)
            after = len([c for c in repo.commits()])
            announce(debugSHOUT, "%d commits tagified." % (before - after))

    func help_merge():
        os.Stdout.write("""
Create a merge link. Takes a selection set argument, ignoring all but
the lowest (source) and highest (target) members.  Creates a merge link
from the highest member (child) to the lowest (parent).

""" )
    func do_merge(self, _line):
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        try:
            commits = sorted(self.selected(Commit))
            commits[1:-1] = [] # Drop all but first and last
            (_, earlier), (_, later) = commits
        except (TypeError, ValueError):
            raise Recoverable("merge requires a selection set "
                              "with at least two commits.")
        later.addParentCommit(earlier)
        #earlier_id = "%s (%s)" % (earlier.mark, earlier.branch)
        #later_id = "%s (%s)" % (later.mark, later.branch)
        #announce(debugSHOUT, "%s added as a parent of %s" % (earlier_id, later_id))

    func help_unmerge():
        os.Stdout.write("""
Linearizes a commit. Takes a selection set argument, which must resolve to a
single commit, and removes all its parents except for the first. It is
equivalent to reparent --rebase {first parent},{commit}, where {commit} is the
selection set given to unmerge and {first parent} is a set resolving to that
commit's first parent, but doesn't need you to find the first parent yourself.

""" )
    func do_unmerge(self, _line):
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        try:
            if len(self.selection) != 1: raise ValueError()
            (_, commit), = self.selected(Commit)
        except (TypeError, ValueError):
            raise Recoverable("unmerge requires a single commit.")
        commit.setParents(commit.parents()[:1])

    func help_reparent():
        os.Stdout.write("""
Changes the parent list of a commit.  Takes a selection set, zero or
more option arguments, and an optional policy argument.

Selection set:

    The selection set must resolve to one or more commits.  The
    selected commit with the highest event number (not necessarily the
    last one selected) is the commit to modify.  The remainder of the
    selected commits, if any, become its parents:  the selected commit
    with the lowest event number (which is not necessarily the first
    one selected) becomes the first parent, the selected commit with
    second lowest event number becomes the second parent, and so on.
    All original parent links are removed.  Examples:

        # this makes 17 the parent of 33
        17,33 reparent

        # this also makes 17 the parent of 33
        33,17 reparent

        # this makes 33 a root (parentless) commit
        33 reparent

        # this makes 33 an octopus merge commit.  its first parent
        # is commit 15, second parent is 17, and third parent is 22
        22,33,15,17 reparent

Options:

    --use-order

        Use the selection order to determine which selected commit is
        the commit to modify and which are the parents (and if there
        are multiple parents, their order).  The last selected commit
        (not necessarily the one with the highest event number) is the
        commit to modify, the first selected commit (not necessarily
        the one with the lowest event number) becomes the first
        parent, the second selected commit becomes the second parent,
        and so on.  Examples:

            # this makes 33 the parent of 17
            33|17 reparent --use-order

            # this makes 17 an octopus merge commit.  its first parent
            # is commit 22, second parent is 33, and third parent is 15
            22,33,15|17 reparent --use-order

        Because ancestor commit events must appear before their
        descendants, giving a commit with a low event number a parent
        with a high event number triggers a re-sort of the events.  A
        re-sort assigns different event numbers to some or all of the
        events.  Re-sorting only works if the reparenting does not
        introduce any cycles.  To swap the order of two commits that
        have an ancestor-descendant relationship without introducing a
        cycle during the process, you must reparent the descendant
        commit first.

Policy:

    By default, the manifest of the reparented commit is computed
    before modifying it; a 'deleteall' and some fileops are prepended
    so that the manifest stays unchanged even when the first parent
    has been changed.  This behavior can be changed by specifying a
    policy flag:

    --rebase

        Inhibits the default behavior -- no 'deleteall' is issued and
        the tree contents of all descendents can be modified as a
        result.
""")
    func do_reparent(self, line):
        repo = self.chosen()
        if repo is None:
            complain("no repo has been chosen.")
            return
        with RepoSurgeon.LineParse(self, line) as parse:
            use_order = '--use-order' in parse.options
            try:
                selected = list(self.selected(Commit))
                if not len(selected): raise ValueError()
                if len(self.selection) != len(selected): raise ValueError()
            except (TypeError, ValueError):
                raise Recoverable("reparent requires one or more selected commits")
            if not use_order:
                selected.sort()
            # determine whether an event resort might be needed.  it is
            # assumed that ancestor commits already have a lower event
            # index before this function is called, which should be true
            # as long as every function that modifies the DAG calls
            # Repository.resort() when needed.  thus, a call to resort()
            # should only be necessary if --use-order is passed and a
            # parent will have an index higher than the modified commit.
            do_resort = use_order and not all(selected[-1][0] > x[0]
                                              for x in selected[0:-1])
            parents = [x[1] for x in selected[0:-1]]
            child = selected[-1][1]
            if do_resort and any(p.descendedFrom(child) for p in parents):
                raise Recoverable('reparenting a commit to its own descendant' \
                                  + ' would introduce a cycle')
            if "--rebase" not in parse.options:
                # Recreate the state of the tree
                f = FileOp(repo)
                f.construct("deleteall")
                newops = [f]
                for (path, (mode, mark, inline)) in child.manifest().items():
                    f = FileOp(repo)
                    f.construct("M", mode, mark, path)
                    if mark == "inline":
                        f.inline = inline
                    newops.append(f)
                newops.extend(child.operations())
                child.setOperations(newops)
            child.setParents(parents)
            if do_resort:
                repo.resort()

    func help_reorder():
        os.Stdout.write("""
Re-order a contiguous range of commits.

Older revision control systems tracked change history on a per-file basis,
rather than as a series of atomic "changesets", which often made it difficult
to determine the relationships between changes. Some tools which convert a
history from one revision control system to another attempt to infer
changesets by comparing file commit comment and time-stamp against those of
other nearby commits, but such inference is a heuristic and can easily fail.
In the best case, when inference fails, a range of commits in the resulting
conversion which should have been coalesced into a single changeset instead
end up as a contiguous range of separate commits. This situation typically can
be repaired easily enough with the 'coalesce' or 'squash' commands. However,
in the worst case, numerous commits from several different "topics", each of
which should have been one or more distinct changesets, may end up interleaved
in an apparently chaotic fashion. To deal with such cases, the commits need to
be re-ordered, so that those pertaining to each particular topic are clumped
together, and then possibly squashed into one or more changesets pertaining to
each topic. This command, 'reorder', can help with the first task; the
'squash' command with the second.

Selected commits are re-arranged in the order specified; for instance:
":7,:5,:9,:3 reorder". The specified commit range must be contiguous; each
commit must be accounted for after re-ordering. Thus, for example, ':5' can
not be omitted from ":7,:5,:9,:3 reorder". (To drop a commit, use the 'delete'
or 'squash' command.) The selected commits must represent a linear history,
however, the lowest numbered commit being re-ordered may have multiple
parents, and the highest numbered may have multiple children.

Re-ordered commits and their immediate descendants are inspected for
rudimentary fileops inconsistencies. Warns if re-ordering results in a commit
trying to delete, rename, or copy a file before it was ever created. Likewise,
warns if all of a commit's fileops become no-ops after re-ordering. Other
fileops inconsistencies may arise from re-ordering, both within the range of
affected commits and beyond; for instance, moving a commit which renames a
file ahead of a commit which references the original name. Such anomalies can
be discovered via manual inspection and repaired with the 'add' and 'remove'
(and possibly 'path') commands. Warnings can be suppressed with '--quiet'.

In addition to adjusting their parent/child relationships, re-ordering commits
also re-orders the underlying events since ancestors must appear before
descendants, and blobs must appear before commits which reference them. This
means that events within the specified range will have different event numbers
after the operation.
""")
    func do_reorder(self, line):
        "Re-order a contiguous range of commits."
        repo = self.chosen()
        if repo is None:
            raise Recoverable("no repo has been chosen")
        if self.selection is None:
            raise Recoverable("no selection")
        sel = [i for i in self.selection if isinstance(repo[i], Commit)]
        if len(sel) == 0:
            raise Recoverable("no commits in selection")
        if len(sel) == 1:
            complain("only 1 commit selected; nothing to re-order")
            return
        with RepoSurgeon.LineParse(self, line) as parse:
            if parse.line:
                raise Recoverable("'reorder' takes no arguments")
            repo.reorder_commits(sel, '--quiet' in parse.options)

    func help_branch():
        os.Stdout.write("""
Rename or delete a branch (and any associated resets).  First argument
must be an existing branch name; second argument must one of the verbs
'rename' or 'delete'. The branchname may use backslash escapes
interpreted by the Python string-escape codec, such as \\s.

For a 'rename', the third argument may be any token that is a syntactically
valid branch name (but not the name of an existing branch). For a 'delete',
no third argument is required.

For either name, if it does not contain a '/' the prefix 'heads/'
is prepended. If it does not begin with 'refs/', 'refs/' is prepended.
""")
    func do_branch(self, line):
        "Rename a branch or delete it."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        (branchname, line) = RepoSurgeon.pop_token(line)
        branchname = string_escape(branchname)
        if "/" not in branchname:
            branchname = 'refs/heads/' + branchname
        if branchname not in repo.branchset():
            raise Recoverable("no such branch as %s" % branchname)
        (verb, line) = RepoSurgeon.pop_token(line)
        if verb == "rename":
            (newname, line) = RepoSurgeon.pop_token(line)
            if not newname:
                raise Recoverable("new branch name must be nonempty.")
            if "/" not in newname:
                newname = 'refs/heads/' + newname
            if newname in repo.branchset():
                raise Recoverable("there is already a branch named '%s'." \
                                  % newname)
            for event in repo:
                if isinstance(event, Commit):
                    if event.branch == branchname:
                        event.setBranch(newname)
                else if isinstance(event, Reset):
                    if event.ref == branchname:
                        event.ref = newname
        else if verb == "delete":
            repo.delete([i for i in range(len(repo.events)) if
                         (isinstance(repo.events[i], Reset) and repo.events[i].ref == branchname) \
                         or \
                         (isinstance(repo.events[i], Commit) and repo.events[i].branch == branchname)])
        else:
            raise Recoverable("unknown verb '%s' in branch command." % verb)

    func help_tag():
        os.Stdout.write("""
Create, move, rename, or delete a tag.

Creation is a special case.  First argument is a name, which must not
be an existing tag. Takes a singleton event second argument which must
point to a commit.  A tag object pointing to the commit is created and
inserted just after the last tag in the repo (or just after the last
commit if there are no tags).  The tagger, committish, and comment
fields are copied from the commit's committer, mark, and comment
fields.

Otherwise, the first argument must be an existing name referring to a
tag object, lightweight tag, or reset; second argument must be one of
the verbs 'move', 'rename', or 'delete'.

For a 'move', a third argument must be a singleton selection set. For
a 'rename', the third argument may be any token that is a
syntactically valid tag name (but not the name of an existing
tag).

For a 'delete', no third argument is required.  The name portion of a
delete may be a regexp wrapped in //; if so, all objects of the
specified type with names matching the regexp are deleted.  This is
useful for mass deletion of junk tags such as CVS branch-root tags.

Tag names may use backslash escapes interpreted by the Python
string-escape codec, such as \\s.

The behavior of this command is complex because features which present
as tags may be any of three things: (1) true tag objects, (2)
lightweight tags, actually sequences of commits with a common
branchname beginning with 'refs/tags' - in this case the tag is
considered to point to the last commit in the sequence, (3) Reset
objects.  These may occur in combination; in fact, stream exporters
from systems with annotation tags commonly express each of these as a
true tag object (1) pointing at the tip commit of a sequence (2) in
which the basename of the common branch field is identical to the tag
name.  An exporter that generates lightweight-tagged commit sequences (2)
may or may not generate resets pointing at their tip commits.

This command tries to handle all combinations in a natural way by
doing up to three operations on any true tag, commit sequence, and
reset matching the source name. In a rename, all are renamed together.
In a delete, any matching tag or reset is deleted; then matching
branch fields are changed to match the branch of the unique descendent
of the tagged commit, if there is one.  When a tag is moved, no branch
fields are changed and a warning is issued.
""")
    func do_tag(self, line):
        "Move a tag to point to a specified commit, or rename it, or delete it."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        # A tag name can refer to one of the following things:
        # (1) A tag object, by name
        # (2) A reset object having a name in the tags/ namespace
        # (3) The tip commit of a branch with branch fields
        # These things often occur in combination. Notably, git-fast-export
        # generates for each tag object corresponding branch labels on
        # some ancestor commits - the rule for where this stops is unclear.
        (tagname, line) = RepoSurgeon.pop_token(line)
        tagname = string_escape(tagname)
        (verb, line) = RepoSurgeon.pop_token(line)
        if verb == 'create':
            if repo.named(tagname):
                raise Recoverable("something is already named %s" % tagname)
            self.set_selection_set(line)
            if self.selection is None:
                raise Recoverable("usage: tag <name> create <singleton-selection>")
            try:
                if len(self.selection) != 1: raise ValueError()
                (_, target), = self.selected(Commit)
            except (TypeError, ValueError):
                raise Recoverable("tag create requires a singleton commit set.")
            tag = Tag(name=tagname,
                      committish=target.mark,
                      target=target,
                      tagger=target.committer.clone(),
                      comment=target.comment)
            tag.tagger.date.timestamp += 1	# So it's unique
            lasttag = None
            lastcommit = None
            for (i, event) in enumerate(repo.events):
                if isinstance(event, Tag):
                    lasttag = i
                else if isinstance(event, Commit):
                    lastcommit = i
            if lasttag is None:
                lasttag = lastcommit
            repo.addEvent(tag, lasttag+1, "tag creation")
            return
        else:
            tags = []
            resets = []
            commits = []
            if tagname[0] == '/' and tagname[-1] == '/':
                # Regexp - can refer to a list of tags matched
                tagre = regexp.MustCompile(tagname[1:-1])
                for event in repo.events:
                    if isinstance(event, Tag) and tagre.search(event.name):
                        tags.append(event)
                    # len("refs/heads/") = 11
                    else if isinstance(event, Reset) and tagre.search(event.ref[11:]):
                        resets.append(event)
                    # len("refs/tags/") = 10
                    else if isinstance(event, Commit) and tagre.search(event.branch[10:]):
                        commits.append(event)
            else:
                # Non-regexp - can only refer to a single tag
                fulltagname = Tag.branchname(tagname)
                for event in repo.events:
                    if isinstance(event, Tag) and event.name == tagname:
                        tags.append(event)
                    else if isinstance(event, Reset) and event.ref == fulltagname:
                        resets.append(event)
                    else if isinstance(event, Commit) and event.branch == fulltagname:
                        commits.append(event)
            if not tags and not resets and not commits:
                raise Recoverable("no tags matching %s" % tagname)
        if verb == "move":
            self.set_selection_set(line)
            try:
                if len(self.selection) != 1: raise ValueError()
                (_, target), = self.selected(Commit)
            except (TypeError, ValueError):
                raise Recoverable("tag move requires a singleton commit set.")
            if tags:
                for tag in tags:
                    tag.forget()
                    tag.remember(repo, target=target)
            if resets:
                if len(resets) == 1:
                    resets[0].committish = target.mark
                else:
                    complain("cannot move multiple tags.")
            if commits:
                complain("warning - tag move does not modify branch fields")
        else if verb == "rename":
            if len(tags) > 1:
                raise Recoverable("exactly one tag is required for rename")
            (newname, line) = RepoSurgeon.pop_token(line)
            if not newname:
                raise Recoverable("new tag name must be nonempty.")
            if len(tags) == 1:
                for event in repo.events:
                    if isinstance(event, Tag) and event != tags[0] and event.name == tags[0].name:
                        raise Recoverable("tag name collision, not renaming.")
                tags[0].name = newname
            fullnewname = Tag.branchname(newname)
            for reset in resets:
                reset.ref = fullnewname
            for event in commits:
                event.branch = fullnewname
        else if verb == "delete":
            for tag in tags:
                tag.forget()
                repo.events.remove(tag)
            if len(tags) > 0:
                repo.declare_sequence_mutation("tag deletion")
            for reset in resets:
                reset.forget()
                repo.events.remove(reset)
            if len(resets) > 0:
                repo.declare_sequence_mutation("reset deletion")
            if commits:
                successors = {child.branch for child in commits[-1].children() if child.parents()[0] == commits[-1]}
                if len(successors) == 1:
                    successor = successors.pop()
                    for event in commits:
                        event.branch = successor
                else:
                    complain("couldn't determine a unique successor for %s at %s" % (tagname, commits[-1].idMe()))
        else:
            raise Recoverable("unknown verb '%s' in tag command." % verb)

    func help_reset():
        os.Stdout.write("""
Create, move, rename, or delete a reset. Create is a special case; it
requires a singleton selection which is the associate commit for the
reset, takes as a first argument the name of the reset (which must not
exist), and ends with the keyword create.

In the other modes, the first argument must match an existing reset
name with the selection; second argument must be one of the verbs
'move', 'rename', or 'delete'. The default selection is all events.

For a 'move', a third argument must be a singleton selection set. For
a 'rename', the third argument may be any token that can be interpreted
as a valid reset name (but not the name of an existing
reset). For a 'delete', no third argument is required.

Reset names may use backslash escapes interpreted by the Python
string-escape codec, such as \\s.

An argument matches a reset's name if it is either the entire
reference (refs/heads/FOO or refs/tags/FOO for some some value of FOO)
or the basename (e.g. FOO), or a suffix of the form heads/FOO or tags/FOO.
An unqualified basename is assumed to refer to a head.

When a reset is renamed, commit branch fields matching the tag are
renamed with it to match.  When a reset is deleted, matching branch
fields are changed to match the branch of the unique descendent of the
tip commit of the associated branch, if there is one.  When a reset is
moved, no branch fields are changed.
""")
    func do_reset(self, line):
        "Move a reset to point to a specified commit, or rename it, or delete it."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        if self.selection is None:
            self.selection = repo.all()
        (resetname, line) = RepoSurgeon.pop_token(line)
        resetname = string_escape(resetname)
        if "/" not in resetname:
            resetname = "heads/" + resetname
        if not resetname.startswith("refs/"):
            resetname = "refs/" + resetname
        resets = [e for _,e in repo.iterevents(indices=self.selection, types=Reset)
                      if e.ref == resetname]
        (verb, line) = RepoSurgeon.pop_token(line)
        if verb == "create":
            if resets:
                raise Recoverable("one or more resets match %s" % resetname)
            try:
                if len(self.selection) != 1: raise ValueError()
                target, = self.selected(Commit)
            except (TypeError, ValueError):
                raise Recoverable("reset create requires a singleton commit set.")
            reset = Reset(repo, ref=resetname)
            repo.addEvent(reset)
            reset.remember(repo, target=target[1])
            repo.declare_sequence_mutation("reset create")
        else if verb == "move":
            if not resets:
                raise Recoverable("no such reset as %s" % resetname)
            if len(resets) == 1:
                reset = resets[0]
            else:
                raise Recoverable("can't move multiple resets")
            self.set_selection_set(line)
            reset.forget()
            try:
                if len(self.selection) != 1: raise ValueError()
                (_, target), = self.selected(Commit)
            except (TypeError, ValueError):
                raise Recoverable("reset move requires a singleton commit set.")
            reset.forget()
            reset.remember(repo, target=target)
            repo.declare_sequence_mutation("reset move")
        else if verb == "rename":
            if not resets:
                raise Recoverable("no such reset as %s" % resetname)
            (newname, line) = RepoSurgeon.pop_token(line)
            if not newname:
                raise Recoverable("new reset name must be nonempty.")
            if newname.count("/") == 0:
                newname = "heads/" + newname
            if not newname.startswith("refs/"):
                newname = "refs/" + newname
            if any(r.ref == newname for _,r in repo.iterevents(types=Reset)) \
                    or any(c.branch == newname
                           for _,c in repo.iterevents(types=Commit)):
                raise Recoverable("reset reference collision, not renaming.")
            for reset in resets:
                reset.ref = newname
            for (_, event) in repo.iterevents(types=Commit):
                if event.branch == resetname:
                    event.branch = newname
        else if verb == "delete":
            if not resets:
                raise Recoverable("no such reset as %s" % resetname)
            tip = next((c for _,c in repo.iterevents(types=Commit)
                          if c.branch == resetname),
                       None)
            if tip and len(tip.children()) == 1:
                successor = tip.children()[0].branch
                for (_, event) in repo.iterevents(types=Commit):
                    if event.branch == resetname:
                        event.branch = successor
            for reset in resets:
                reset.forget()
                repo.events.remove(reset)
            repo.declare_sequence_mutation("reset delete")
        else:
            raise Recoverable("unknown verb '%s' in reset command." % verb)

    func help_ignores():
        os.Stdout.write("""Intelligent handling of ignore-pattern files.
This command fails if no repository has been selected or no preferred write
type has been set for the repository.  It does not take a selection set.

If the rename modifier is present, this command attempts to rename all
ignore-pattern files to whatever is appropriate for the preferred type
- e.g. .gitignore for git, .hgignore for hg, etc.  This option does not
cause any translation of the ignore files it renames.

If the translate modifier is present, syntax translation of each ignore
file is attempted. At present, the only transformation the code knows
is to prepend a 'syntax: glob' header if the preferred type is hg.

If the defaults modifier is present, the command attempts to prepend
these default patterns to all ignore files. If no ignore file is
created by the first commit, it will be modified to create one
containing the defaults.  This command will error out on prefer types
that have no default ignore patterns (git and hg, in particular).  It
will also error out when it knows the import tool has already set
default patterns.
""")
    func do_ignores(self, line):
        "Manipulate ignore patterns in the repo."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        if self.preferred and not self.ignorename:
            self.ignorename = self.preferred.ignorename
        if not self.preferred:
            raise Recoverable("preferred repository type has not been set")
        if not self.ignorename:
            raise Recoverable("preferred repository type has no declared ignorename")
        func isignore(blob):
            return len(blob.pathlist) \
                       and all(x.endswith(self.ignorename) for x in blob.pathlist)
        for verb in line.split():
            if verb == 'defaults':
                if "import-defaults" in self.preferred.styleflags:
                    raise Recoverable("importer already set default ignores")
                else if not self.preferred.dfltignores:
                    raise Recoverable("no default ignores in %s" % self.preferred.name)
                else:
                    changecount = 0
                    # Modify existing ignore files
                    for (_, blob) in repo.iterevents(indices=None, types=(Blob,)):
                        if isignore(blob):
                            blob.setContent(self.preferred.dfltignores \
                                         + blob.getContent())
                            changecount += 1
                    # Create an early ignore file if required.
                    # Don't move this before the modification pass!
                    earliest = repo.earliest_commit()
                    if not [fileop for fileop in earliest.operations() if fileop.op == opM and fileop.path.endswith(self.ignorename)]:
                        blob = Blob(repo)
                        blob.addalias(self.ignorename)
                        blob.setContent(self.preferred.dfltignores)
                        blob.mark = ":insert"
                        repo.events.insert(repo.index(earliest), blob)
                        repo.declare_sequence_mutation("ignore creation")
                        newop = FileOp(self.chosen())
                        newop.construct("M", 0o100644, ":insert", self.ignorename)
                        earliest.appendOperation(newop)
                        repo.renumber()
                        announce(debugSHOUT, "initial %s created." % self.ignorename)
                announce(debugSHOUT, "%d %s blobs modified." % (changecount, self.ignorename))
            else if verb == 'rename':
                changecount = 0
                for (_, event) in repo.iterevents(indices=None, types=(Commit,)):
                    for fileop in event.operations():
                        for attr in ("path", "source", "target"):
                            if hasattr(fileop, attr):
                                oldpath = getattr(fileop, "path")
                                if oldpath and oldpath.endswith(self.ignorename):
                                    newpath = os.path.join(os.path.dirname(oldpath),
                                                       self.preferred.ignorename)
                                    setattr(fileop, attr, newpath)
                                    changecount += 1
                                    if fileop.op == opM:
                                        blob = repo.markToEvent(fileop.ref)
                                        if blob.pathlist[0] == oldpath:
                                            blob.pathlist[0] = newpath
                announce(debugSHOUT, "%d ignore files renamed (%s -> %s)."
                         % (changecount,
                            self.ignorename,
                            self.preferred.ignorename))
                self.ignorename = self.preferred.ignorename
            else if verb == 'translate':
                changecount = 0
                for (_, blob) in repo.iterevents(indices=None, types=(Blob,)):
                    if isignore(blob):
                        if self.preferred.name == "hg":
                            if not blob.getContent().startswith("syntax: glob\n"):
                                blob.setContent("syntax: glob\n" + blob.getContent())
                                changecount += 1
                announce(debugSHOUT, "%d %s blobs modified." % (changecount, self.ignorename))
            else:
                raise Recoverable("unknown verb %s in ignores line" % verb)

    func help_attribution():
        os.Stdout.write("""
Inspect, modify, add, and remove commit and tag attributions.

Attributions upon which to operate are selected in much the same way as events
are selected. The <selection> argument of each action is an expression
composed of 1-origin attribution-sequence numbers, '$' for last attribution,
'..' ranges, comma-separated items, '(...)' grouping, set operations '|'
union, '&' intersection, and '~' negation, and function calls @min(), @max(),
@amp(), @pre(), @suc(), @srt().

Attributions can also be selected by visibility set '=C' for committers, '=A'
for authors, and '=T' for taggers.

Finally, /regex/ will attempt to match the Python regular expression regex
against an attribution name and email address; '/n' limits the match to only
the name, and '/e' to only the email address.

With the exception of 'show', all actions require an explicit event selection
upon which to operate.

Available actions are:

[<selection>] [show] [>file]
    Inspect the selected attributions of the specified events (commits and
    tags). The 'show' keyword is optional. If no attribution selection
    expression is given, defaults to all attributions. If no event selection
    is specified, defaults to all events. Supports > redirection.

<selection> set <name> [<email>] [<date>]
<selection> set [<name>] <email> [<date>]
<selection> set [<name>] [<email>] <date>
    Assign <name>, <email>, <date> to the selected attributions. As a
    convenience, if only some fields need to be changed, the others can be
    omitted. Arguments <name>, <email>, and <date> can be given in any order.

[<selection>] delete
    Delete the selected attributions. As a convenience, deletes all authors if
    <selection> is not given. It is an error to delete the mandatory committer
    and tagger attributions of commit and tag events, respectively.

[<selection>] prepend <name> [<email>] [<date>]
[<selection>] prepend [<name>] <email> [<date>]
    Insert a new attribution before the first attribution named by <selection>.
    The new attribution has the same type ('committer', 'author', or 'tagger')
    as the one before which it is being inserted. Arguments <name>, <email>,
    and <date> can be given in any order.

    If <name> is omitted, an attempt is made to infer it from <email> by
    trying to match <email> against an existing attribution of the event, with
    preference given to the attribution before which the new attribution is
    being inserted. Similarly, <email> is inferred from an existing matching
    <name>. Likewise, for <date>.

    As a convenience, if <selection> is empty or not specified a new author is
    prepended to the author list.

    It is presently an error to insert a new committer or tagger attribution.
    To change a committer or tagger, use 'set' instead.

[<selection>] append <name> [<email>] [<date>]
[<selection>] append [<name>] <email> [<date>]
    Insert a new attribution after the last attribution named by <selection>.
    The new attribution has the same type ('committer', 'author', or 'tagger')
    as the one after which it is being inserted. Arguments <name>, <email>,
    and <date> can be given in any order.

    If <name> is omitted, an attempt is made to infer it from <email> by
    trying to match <email> against an existing attribution of the event, with
    preference given to the attribution after which the new attribution is
    being inserted. Similarly, <email> is inferred from an existing matching
    <name>. Likewise, for <date>.

    As a convenience, if <selection> is empty or not specified a new author is
    appended to the author list.

    It is presently an error to insert a new committer or tagger attribution.
    To change a committer or tagger, use 'set' instead.

<selection> resolve [>file] [label-text...]
    Does nothing but resolve an attribution selection-set expression for the
    selected events and echo the resulting attribution-number set to standard
    output. The remainder of the line after the command is used as a label for
    the output.

    Implemented mainly for regression testing, but may be useful for exploring
    the selection-set language.
""")
    func do_attribution(self, line):
        "Inspect, modify, add, and remove commit and tag attributions."
        repo = self.chosen()
        if repo is None:
            raise Recoverable("no repo has been chosen")
        selparser = AttributionEditor.SelParser()
        machine, rest = selparser.compile(line)
        with RepoSurgeon.LineParse(self, rest, capabilities=["stdout"]) as parse:
            try:
                fields = shlex.split(parse.line)
            except ValueError as e:
                raise Recoverable("attribution parse failed: %s" % e)
            action = fields[0] if fields else 'show'
            args = fields[1:]
            if self.selection is None:
                if action == 'show':
                    self.selection = repo.all()
                else:
                    raise Recoverable("no selection")
            sel = list(self.selected((Commit, Tag)))
            if not sel:
                raise Recoverable("no commits or tags in selection")
            ed = AttributionEditor(sel, lambda a: selparser.evaluate(machine, a))
            if action == 'show':
                if len(args) > 0:
                    raise Recoverable("'show' takes no arguments")
                ed.inspect(parse.stdout)
            else if action == 'delete':
                if len(args) > 0:
                    raise Recoverable("'delete' takes no arguments")
                ed.delete()
            else if action == 'set':
                if len(args) < 1 or len(args) > 3:
                    raise Recoverable("'set' requires at least one of: name, email, date")
                ed.assign(args)
            else if action in ('prepend', 'append'):
                if len(args) < 1 or len(args) > 3:
                    raise Recoverable("'%s' requires at least one of: name, email; date is optional" % action)
                if action == 'prepend':
                    ed.insert(args, false)
                else if action == 'append':
                    ed.insert(args, true)
            else if action == 'resolve':
                ed.resolve(parse.stdout, ' '.join(args) if args else None)
            else:
                raise Recoverable("unrecognized action: %s" % action)

    #
    # Artifact removal
    #
    func help_authors():
        os.Stdout.write("""
Apply or dump author-map information for the specified selection
set, defaulting to all events.

Lifts from CVS and Subversion may have only usernames local to
the repository host in committer and author IDs. DVCSes want email
addresses (net-wide identifiers) and complete names. To supply the map
from one to the other, an authors file is expected to consist of
lines each beginning with a local user ID, followed by a '=' (possibly
surrounded by whitespace) followed by a full name and email address.

When an authors file is applied, email addresses in committer and author
metdata for which the local ID matches between &lt; and @ are replaced
according to the mapping (this handles git-svn lifts). Alternatively,
if the local ID is the entire address, this is also considered a match
(this handles what git-cvsimport and cvs2git do). If a timezone was
specified in the map entry, that person's author and committer dates
are mapped to it.

With the 'read' modifier, or no modifier, apply author mapping data
(from standard input or a <-redirected input file).  May be useful if
you are editing a repo or dump created by cvs2git or by
cvs-fast-export or git-svn invoked without -A.

With the 'write' modifier, write a mapping file that could be
interpreted by 'authors read', with entries for each unique committer,
author, and tagger (to standard output or a >-redirected file). This
may be helpful as a start on building an authors file, though each
part to the right of an equals sign will need editing.
""")
    func do_authors(self, line):
        "Apply or dump author-mapping file."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        if line.startswith("write"):
            line = line[5:].strip()
            with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
                if parse.tokens():
                    raise Recoverable("authors write no longer takes a filename argument - use > redirection instead")
                self.chosen().writeAuthorMap(self.selection, parse.stdout)
        else:
            if line.startswith("read"):
                line = line[4:].strip()
            with RepoSurgeon.LineParse(self, line, capabilities=["stdin"]) as parse:
                if parse.tokens():
                    raise Recoverable("authors read no longer takes a filename argument - use < redirection instead")
                self.chosen().readAuthorMap(self.selection, parse.stdin)

    #
    # Reference lifting
    #
    func help_legacy():
        os.Stdout.write("""
Apply or list legacy-reference information. Does not take a
selection set. The 'read' variant reads from standard input or a
<-redirected filename; the 'write' variant writes to standard
output or a >-redirected filename.
""")
    func do_legacy(self, line):
        "Apply a reference-mapping file."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if line.startswith("write"):
            line = line[5:].strip()
            with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
                if parse.tokens():
                    raise Recoverable("legacy write does not take a filename argument - use > redirection instead")
                self.chosen().write_legacymap(parse.stdout)
        else:
            if line.startswith("read"):
                line = line[4:].strip()
            with RepoSurgeon.LineParse(self, line, capabilities=["stdin"]) as parse:
                if parse.tokens():
                    raise Recoverable("legacy read does not take a filename argument - use < redirection instead")
                self.chosen().read_legacymap(parse.stdin)

    func help_references():
        os.Stdout.write("""
With the 'list' modifier, produces a listing of events that may have
Subversion or CVS commit references in them.  This version
of the command supports >-redirection.  Equivalent to '=N list'.

With the modifier 'edit', edit this set.  This version of the command
supports < and > redirection.  Equivalent to '=N edit'.

With the modifier 'lift', transform commit-reference cookies from CVS
and Subversion into action stamps.  This command expects cookies
consisting of the leading string '[[', followed by a VCS identifier
(currently SVN or CVS) followed by VCS-dependent information, followed
by ']]'. An action stamp pointing at the corresponding commit is
substituted when possible.  Enables writing of the legacy-reference
map when the repo is written or rebuilt.
""")
    func do_references(self, line):
        "Look for things that might be CVS or Subversion revision references."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        if self.selection is None:
            self.selection = self.chosen().all()
        if "lift" in line:
            self.chosen().parse_dollar_cookies()
            hits = 0
            func substitute(getter, matchobj):
                payload = polystr(matchobj.group(0)[2:-2])
                commit = getter(payload)
                if commit is None:
                    complain("no commit matches " + repr(payload))
                    return matchobj.group(0) # no replacement
                else if commit:
                    text = commit.action_stamp()
                    return polybytes(text)
                else:
                    complain("cannot resolve %s" % payload)
                    return matchobj.group(0) # no replacement
            for (regexp, getter) in \
                    ((r"CVS:[^:\]]+:[0-9.]+",
                      lambda p: repo.legacyMap.get(p) or repo.dollarMap.get(p)),
                     ("SVN:[0-9]+",
                      lambda p: repo.legacyMap.get(p) or repo.dollarMap.get(p)),
                     ("HG:[0-9a-f]+",
                      lambda p: repo.legacyMap.get(p)),
                     (":[0-9]+",
                      lambda p: repo.markToEvent(p)),
                     ):
                match_re = regexp.MustCompile((re.escape("[[")+regexp+re.escape("]]")).encode('ascii'))
                for _, event in self.selected():
                    if isinstance(event, (Commit, Tag)):
                        event.comment, new_hits = match_re.subn(
                            lambda m: substitute(getter, m),
                            polybytes(event.comment))
                        event.comment = polystr(event.comment)
                        hits += new_hits
            announce(debugSHOUT, "%d references resolved." % hits)
            repo.write_legacy = true
        else:
            self.selection = [e for e in range(len(repo.events)) if self.has_reference(repo.events[e])]
            if self.selection:
                if line.startswith("edit"):
                    self.edit(self.selection, line[4:].strip())
                else:
                    with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
                        for ei in self.selection:
                            event = repo.events[ei]
                            if hasattr(event, "lister"):
                                summary = event.lister(None, ei, screenwidth())
                                if summary:
                                    parse.stdout.write(summary + "\n")

    func help_gitify():
        os.Stdout.write("""
Attempt to massage comments into a git-friendly form with a blank
separator line after a summary line.  This code assumes it can insert
a blank line if the first line of the comment ends with '.', ',', ':',
';', '?', or '!'.  If the separator line is already present, the comment
won't be touched.

Takes a selection set, defaulting to all commits and tags.
""")
    func do_gitify(self, _line):
        "Gitify comments."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            self.selection = self.chosen().all()
        line_enders = ('.', ',', ';', ':', '?', '!')
        with Baton(prompt="gitifying comments", enable=(verbose == 1)) as baton:
            for ei in range(self.selection[0], self.selection[-1]):
                event = self.chosen().events[ei]
                if isinstance(event, (Commit, Tag)):
                    event.comment = event.comment.strip() + "\n"
                    if event.comment.count('\n') < 2:
                        continue
                    firsteol = event.comment.index('\n')
                    if event.comment[firsteol+1] == '\n':
                        continue
                    if event.comment[firsteol-1] in line_enders:
                        event.comment = event.comment[:firsteol] + \
                                        '\n' + \
                                        event.comment[firsteol:]
                baton.twirl("")
    #
    # Examining tree states
    #
    func help_checkout():
        os.Stdout.write("""
Check out files for a specified commit into a directory.  The selection
set must resolve to a singleton commit.
""")
    func do_checkout(self, line):
        "Check out files for a specified commit into a directory."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        if self.selection is None:
            self.selection = self.chosen().all()
        if not line:
            raise Recoverable("no target directory specified.")
        if len(self.selection) == 1:
            commit = repo.events[self.selection[0]]
            if not isinstance(commit, Commit):
                raise Recoverable("not a commit.")
        else:
            raise Recoverable("a singleton selection set is required.")
        commit.checkout(line)

    func help_diff():
        os.Stdout.write("""
Display the difference between commits. Takes a selection-set argument which
must resolve to exactly two commits. Supports > redirection.
""")
    func do_diff(self,line):
        "Display a diff between versions."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        if self.selection is None:
            self.selection = self.chosen().all()
        bounds = tuple(repo.events[i] for i in self.selection)
        if len(self.selection) != 2 or \
               not isinstance(bounds[0], Commit) or \
               not isinstance(bounds[1], Commit):
            raise Recoverable("a pair of commits is required.")
        dir1 = set(bounds[0].manifest())
        dir2 = set(bounds[1].manifest())
        allpaths = list(dir1 | dir2)
        allpaths.sort()
        with RepoSurgeon.LineParse(self, line, capabilities=["stdout"]) as parse:
            for path in allpaths:
                if path in dir1 and path in dir2:
                    # FIXME: Can we detect binary files and do something
                    # more useful here?
                    fromtext = bounds[0].blobByName(path)
                    totext = bounds[1].blobByName(path)
                    # Don't list identical files
                    if fromtext != totext:
                        lines0 = fromtext.split('\n')
                        lines1 = totext.split('\n')
                        file0 = path + " (" + bounds[0].mark + ")"
                        file1 = path + " (" + bounds[1].mark + ")"
                        for diffline in difflib.unified_diff(lines0, lines1,
                                                         fromfile=file0,
                                                         tofile=file1,
                                                         lineterm=""):
                            parse.stdout.write(diffline + "\n")
                else if path in dir1:
                    parse.stdout.write("%s: removed\n" % path)
                else if path in dir2:
                    parse.stdout.write("%s: added\n" % path)
                else:
                    raise Recoverable("internal error - missing path in diff")

    #
    # Setting paths to branchify
    #
    func help_branchify():
        os.Stdout.write("""
Specify the list of directories to be treated as potential branches (to
become tags if there are no modifications after the creation copies)
when analyzing a Subversion repo. This list is ignored when reading
with the --nobranch option.  It defaults to the 'standard layout'
set of directories, plus any unrecognized directories in the
repository root.

With no arguments, displays the current branchification set.

An asterisk at the end of a path in the set means 'all immediate
subdirectories of this path, unless they are part of another (longer)
path in the branchify set'.

Note that the branchify set is a property of the reposurgeon interpreter, not
of any individual repository, and will persist across Subversion
dumpfile reads. This may lead to unexpected results if you forget
to re-set it.
""")
    func do_branchify(self, line):
        if self.selection is not None:
            raise Recoverable("branchify does not take a selection set")
        if line.strip():
            globalOptions['svn_branchify'] = line.strip().split()
        announce(debugSHOUT, "branchify " + " ".join(globalOptions['svn_branchify']))
    #
    # Setting branch name rewriting
    #
    func help_branchify_map():
        os.Stdout.write("""
Specify the list of regular expressions used for mapping the svn branches that
are detected by branchify. If none of the expressions match, the default behavior
applies. This maps a branch to the name of the last directory, except for trunk
and '*' which are mapped to master and root.

With no arguments the current regex replacement pairs are shown. Passing 'reset'
will clear the reset mapping.

Syntax: branchify_map /regex1/branch1/ /regex2/branch2/ ...

Will match each branch name against regex1 and if it matches rewrite its branch
name to branch1. If not it will try regex2 and so forth until it either found a
matching regex or there are no regexs left. The regular expressions should be in
python's format (see http://docs.python.org/2/library/re.html). The branch name
can use backreferences (see the sub function in the python documentation).

Note that the regular expressions are appended to 'refs/' without either the
needed 'heads/' or 'tags/'. This allows for choosing the right kind of branch
type.

While the syntax template above uses slashes, any first character will
be used as a delimeter (and you will need to use a different one in the
common case that the paths contain slashes).

You must give this command *before* the Subversion repository read it
is supposed to affect!

Note that the branchify_map set is a property of the reposurgeon interpreter,
not of any individual repository, and will persist across Subversion
dumpfile reads. This may lead to unexpected results if you forget
to re-set it.
""")
    func do_branchify_map(self, line):
        if self.selection is not None:
            raise Recoverable("branchify_map does not take a selection set")
        line = line.strip()
        if line == "reset":
            globalOptions['svn_branchify_mapping'] = []
        else if line:
            func split_regex(regex):
                separator = regex[0]
                if separator != regex[-1]:
                    raise Recoverable("Regex '%s' did not end with separator character" % regex)
                match, _, replace = regex[1:-1].partition(separator)
                if not replace or not match:
                    raise Recoverable("Regex '%s' has an empty search or replace part" % regex)
                return match ,replace
            globalOptions['svn_branchify_mapping'] = \
                    list(map(split_regex, line.split()))
        if globalOptions['svn_branchify_mapping']:
            announce(debugSHOUT, "branchify_map, regex -> branch name:")
            for match, replace in globalOptions['svn_branchify_mapping']:
                announce(debugSHOUT,  "\t" + match + " -> " + replace)
        else:
            complain("branchify_map is empty.")

    #
    # Setting options
    #
    func help_set():
        os.Stdout.write("""
Set a (tab-completed) boolean option to control reposurgeon's
behavior.  With no arguments, displays the state of all flags and
options. The following flags and options are defined:
""")
        for (opt, expl) in RepoSurgeon.OptionFlags:
            os.Stdout.write(opt + ":\n" + expl + "\n")
    func complete_set(self, text, _line, _begidx, _endidx):
        return sorted([x for (x, _) in RepoSurgeon.OptionFlags if x.startswith(text)])
    func do_set(self, line):
        if not line.strip():
            for (opt, _expl) in RepoSurgeon.OptionFlags:
                os.Stdout.write("\t%s = %s\n" % (opt, globalOptions.get(opt, false)))
        else:
            for option in line.split():
                if option not in dict(RepoSurgeon.OptionFlags):
                    complain("no such option flag as '%s'" % option)
                else:
                    globalOptions[option] = true
    func help_clear():
        os.Stdout.write("""
Clear a (tab-completed) boolean option to control reposurgeon's
behavior.  With no arguments, displays the state of all flags. The
following flags and options are defined:
""")
        for (opt, expl) in RepoSurgeon.OptionFlags:
            os.Stdout.write(opt + ":\n" + expl + "\n")
    complete_clear = complete_set
    func do_clear(self, line):
        if not line.strip():
            for opt in dict(RepoSurgeon.OptionFlags):
                os.Stdout.write("\t%s = %s\n" % (opt, globalOptions.get(opt, false)))
        else:
            for option in line.split():
                if option not in dict(RepoSurgeon.OptionFlags):
                    complain("no such option flag as '%s'" % option)
                else:
                    globalOptions[option] = false

    #
    # Macros and custom extensions
    #
    func help_define():
        os.Stdout.write("""
Define a macro.  The first whitespace-separated token is the name; the
remainder of the line is the body, unless it is '{', which begins a
multi-line macro terminated by a line beginning with '}'.

A later 'do' call can invoke this macro.

'define' by itself without a name or body produces a macro list.
""")
    func do_define(self, line):
        "Define a macro"
        try:
            name = line.split()[0]
        except IndexError:
            name = line.strip()
        body = line[len(name):].strip()
        if not body:
            for (name, body) in self.definitions.items():
                if len(body) == 1:
                    os.Stdout.write("define %s %s\n" % (name, body[0]))
                else:
                    os.Stdout.write("define %s {\n" % name)
                    for bodyline in body:
                        os.Stdout.write(bodyline)
                    os.Stdout.write("}\n")
        else if body[0] != '{':
            self.definitions[name] = [body]
        else:
            self.capture = self.definitions[name] = []

    func help_do():
        os.Stdout.write("""
Expand and perform a macro.  The first whitespace-separated token is
the name of the macro to be called; remaining tokens replace {0},
{1}... in the macro definition (the conventions used are those of the
Python format method). Tokens may contain whitespace if they are
string-quoted; string quotes are stripped. Macros can call macros.
If the macro expansion does not itself begin with a selection set,
whatever set was specified before the 'do' keyword is available to
the command generated by the expansion.
""")
    func do_do(self, line):
        "Do a macro."
        try:
            name = line.split()[0]
        except IndexError:
            complain("no macro name was givenn.")
            return
        if name not in self.definitions:
            raise Recoverable("'%s' is not a defined macro" % name)
        try:
            args = shlex.split(line[len(name):])
        except ValueError as e:
            raise Recoverable("macro parse failed, %s" % e)
        do_selection = self.selection
        for defline in self.definitions[name]:
            try:
                defline = defline.format(*args)
            except IndexError:
                raise Recoverable("macro argument error")
            # If a leading portion of the expansion body is a selection
            # expression, use it.  Otherwise we'll restore whatever
            # selection set came before the do keyword.
            expansion = self.precmd(defline)
            if self.selection is None:
                self.selection = do_selection
            # Call the base method so RecoverableExceptions
            # won't be caught; we want them to abort macros.
            self.onecmd(expansion)
    func help_undefine():
        os.Stdout.write("""
Undefine the macro named in this command's first argument.
""")
    func complete_undefine(self, text, _line, _begidx, _endidx):
        return sorted([x for x in self.definitions if x.startswith(text)])
    func do_undefine(self, line):
        try:
            name = line.split()[0]
        except IndexError:
            complain("no macro name was givenn.")
            return
        if name not in self.definitions:
            raise Recoverable("'%s' is not a defined macro" % name)
        else:
            del self.definitions[name]

    func help_exec():
        os.Stdout.write("""
Execute custom code from standard input (normally a file via < redirection).

Use this to set up custom extension functions for later calls. The
code has full access to all internal data structures. Functions
defined are accessible to later 'eval' calls.
""")
    func do_exec(self, line):
        "Execute custom python code."
        with RepoSurgeon.LineParse(self, line, capabilities=["stdin"]) as parse:
            try:
                # The additional args are required to make the function
                # visible to a later eval.
                with open(parse.stdin.name, 'rb') as fp:
                    exec(compile(polystr(fp.read()), parse.stdin.name, 'exec'), locals(), globals())
            except SyntaxError as e:
                raise Recoverable("extension function - %s\n%s" % (e, e.text))
            except IOError:
                raise Recoverable("I/O error, can't find or open input source")

    func help_eval():
        os.Stdout.write("""
Evaluate a line of code in the current interpreter context.
Typically this will be a call to a function defined by a previous exec.
The variables '_repository' and '_selection' will have the obvious values.
Note that '_selection' will be a list of integers, not objects.
""")
    func do_eval(self, line):
        "Call a function from custom python code."
        if self.selection is None:
            os.Stdout.write("no selection\n")
        else:
            _selection = self.selection
            _repository = self.chosen()
            try:
                eval(line)
            except (NameError, SyntaxError) as e:
                raise Recoverable(str(e))

    #
    # Timequakes and bumping
    #
    func help_timequake():
        os.Stdout.write("""
Attempt to hack committer and author time stamps to make all action
stamps in the selection set (defaulting to all commits in the
repository) to be unique.  Works by identifying collisions between parent
and child, than incrementing child timestamps so they no longer
coincide. Won't touch commits with multiple parents.

Because commits are checked in ascending order, this logic will
normally do the right thing on chains of three or more commits with
identical timestamps.

Any collisions left after this operation are probably cross-branch and have
to be individually dealt with using 'timebump' commands.

The normal use case for this command is early in converting CVS or Subversion
repositories, to ensure that the surgical language can count on having a unique
action-stamp ID for each commit.
""")
    func do_timequake(self, _line):
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        if self.selection is None:
            self.selection = self.chosen().all()
        with Baton(prompt="reposurgeon: disambiguating", enable=(verbose == 1)) as baton:
            modified = 0
            for (_, event) in self.selected(Commit):
                parents = event.parents()
                if len(parents) == 1:
                    if event.committer.date.timestamp == parents[0].committer.date.timestamp:
                        event.bump()
                        modified += 1
                baton.twirl("")
            announce(debugSHOUT, "%d events modified" % modified)
        repo.invalidateNamecache()
    func help_timebump():
        os.Stdout.write("""
Bump the committer and author timestamps of commits in the selection
set (defaulting to empty) by one second.  With following integer agument,
that many seconds.  Argument may be negative.

The normal use case for this command is early in converting CVS or Subversion
repositories, cleaning up after 'timequake', to ensure that the surgical
language can count on having a unique action-stamp ID for each commit.
""")
    func do_timebump(self, line):
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        if self.selection is None:
            raise Recoverable("reposurgeon: no default select set for bump.")
        offset = int(line) if line else 1
        for (_, event) in self.selected(Commit):
            event.bump(offset)

    #
    # Changelog processing
    #
    func help_changelogs():
        os.Stdout.write("""
Mine the ChangeLog files for authorship data.

Assume such files have basenam 'ChangeLog', and that they are in the
format used by FSF projects: entry header lines begin with YYYY-MM-DD
and are followed by a fullname/address.

When a ChangeLog file modification is found in a clique, the entry
header at or before the section changed since its last revision is
parsed and the address is inserted as the commit author.  This is
useful in converting CVS and Subversion repositories that don't have
any notion of author separate from committer but which use the FSF
ChangeLog convention.

If the entry header contains an email address but no name, a name
will be filled in if possible by looking for the address in author
map entries.

In accordance with FSF policy for ChangeLogs, any date in an
attribution header is discarded and the committer date is used.
However, if the nam is an author-map alias with an associated timezone,
that zone is used.
""")
    func do_changelogs(self, line):
        "Mine repository changelogs for authorship data."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        cc = cl = cm = cd = 0
        differ = difflib.Differ()
        func parse_attribution_line(line):
            if len(line) <= 10 or line[0].isspace():
                return None
            # Massage old-style addresses into newstyle
            line = line.replace("(", "<").replace(")", ">")
            # Deal with some address masking
            line = line.replace(" <at> ", "@")
            # Malformation in a GCC Changelog that might be replicated elsewhere.
            if line.endswith(">>"):
                line = line[:-1]
            # Line must contain an email address
            if not (line.count('<') == 1 and line.endswith(">")):
                return None
            if line[0].isdigit() and line[1].isdigit():
                space = line.find(" ")
                if space < 0:
                    return None
                date = line[:space]
                try:
                    calendar.timegm(time.strptime(date, "%Y-%m-%d"))
                except ValueError:
                    return None
                addr = line[space+1:].strip()
                return addr
            # Scan for old-style date like "Tue Dec  9 01:16:06 1997"
            try:
                possible_date = " ".join(line.split()[:5])
                # Doesn't matter that TZ is wrong here, we're only going
                # to use the day part at most.
                calendar.timegm(time.strptime(possible_date, "%a %b %d %H:%M:%S %Y"))
                skipre = regexp.MustCompile("\s+".join(line.split()[:5]))
                m = skipre.match(line)
                addr = line[len(m.group(0)):].strip()
                return addr
            except ValueError:
                pass
            return None
        with Baton("reposurgeon: parsing changelogs", enable=(verbose == 1)) as baton:
            for commit in repo.commits():
                cc += 1
                # If a changeset is *all* ChangeLog mods, it's probably either
                # a log rotation or a maintainer fixing a typo. In either case,
                # best not to re-attribute this.
                if not [op.path for op in commit.operations() \
                        if op.op==opM and not os.path.basename(op.path).startswith("ChangeLog")]:
                    continue
                for op in commit.operations():
                    baton.twirl("")
                    if op.op == opM and os.path.basename(op.path) == "ChangeLog":
                        cl += 1
                        blobfile = repo.markToEvent(op.ref).materialize()
                        # Figure out where we should look for changes in
                        # this blob by comparing it to its nearest ancestor.
                        ob = repo.blob_ancestor(commit, op.path)
                        if ob:
                            with open(ob.materialize()) as oldblob:
                                then = oldblob.read().splitlines()
                        else:
                            then = ""
                        with open(blobfile) as newblob:
                            now = newblob.read().splitlines()
                        before = true
                        inherited = new = None
                        #print("Analyzing Changelog at %s." % commit.mark)
                        for diffline in differ.compare(then, now):
                            if diffline[0] != ' ':
                                #print("Change encountered")
                                before = false
                            #print("I see: %s" % repr(diffline))
                            line = diffline[2:]
                            attribution = parse_attribution_line(line)
                            if attribution is not None:
                                addr = attribution
                                #print("I notice: %s %s %s" % (diffline[0], attribution, before))
                                # This is the tricky part.  We want the
                                # last attribution from before the change
                                # band to stick unless there's one *in*
                                # the change band. If there's more than one,
                                # assume the most recent is the latest and
                                # correct.
                                if attribution:
                                    if before:
                                        inherited = attribution
                                        #print("Inherited: %s" % repr(inherited))
                                    if diffline[0] in ('+', '?'):
                                        if attribution and not new:
                                            new = attribution
                                            #print("New: %s" % repr(new))
                                            break
                            #print("Attributions: %s %s" % (inherited, new))
                            attribution = new if new else inherited
                        if attribution is not None:
                            addr = attribution
                            cm += 1
                            newattr = commit.committer.clone()
                            (newattr.name, newattr.email) = addr.split("<")
                            newattr.email = newattr.email.strip()[:-1]
                            newattr.name = newattr.name.strip()
                            if not newattr.name:
                                for mapentry in repo.authormap.values():
                                    if len(mapentry) != 3:
                                        complain("malformed author map entry %s" % (mapentry,))
                                        continue
                                    (name, nemail, _tz) = mapentry
                                    if newattr.email == nemail:
                                        newattr.name = name
                                        break
                            if newattr.email in repo.tzmap:
                                newattr.date.set_tz(repo.tzmap[newattr.email])
                            else:
                                newattr.date.set_tz(zoneFromEmail(newattr.email))
                            if (newattr.name, newattr.email) in repo.aliases:
                                (newattr.name, newattr.email) = repo.aliases[(newattr.name, newattr.email)]
                            if not commit.authors:
                                commit.authors = [newattr]
                            else:
                                # Required because git sometimed fills in the
                                # author field from the committer.
                                if commit.authors[-1].address() == commit.committer.address():
                                    commit.authors.pop()
                                # Someday, detect whether target VCS allows
                                # multiple authors and append unconditonally
                                # if so.
                                if not commit.authors and newattr.address() not in [x.address for x in commit.authors]:
                                    commit.authors.append(newattr)
                                    cd += 1
        repo.invalidateNamecache()
        announce(debugSHOUT, "fills %d of %d authorships, changing %s, from %d ChangeLogs." \
                 % (cm, cc, cd, cl))

    #
    # Tarball incorporation
    #
    func help_incorporate():
        os.Stdout.write("""
Insert the contents of a specified tarball as a commit.  The tarball name is
given as an argument.  It may be a gzipped or bzipped tarball.  The initial
segment of each path is assumed to be a version directory and stripped off.
The number of segments stripped off can be set with the option --strip=<n>,
n defaulting to 1.

Takes a singleton selection set.  Normally inserts before that commit; with
the option --after, insert after it.  The default selection set is the very
first commit of the repository.

The option --date can be used to set the commit date. It takes an argument,
which is expected to be an RFC3339 timestamp.

The generated commit has a committer field (the invoking user) and
gets as its commit date the modification time of the newest file in
the tarball (not the mod time of the tarball itself). No author field
is generated.  A comment recording the tarball name is generated.

Note that the import stream generated by this command is - while correct -
not optimal, and may in particular contain duplicate blobs.
""")
    func do_incorporate(self, line):
        "Create a new commit from a tarball."
        if self.chosen() is None:
            complain("no repo has been chosen.")
            return
        repo = self.chosen()
        if self.selection is None:
            self.selection = [repo.find(repo.earliest_commit().mark)]
        if len(self.selection) == 1:
            commit = repo.events[self.selection[0]]
            if not isinstance(commit, Commit):
                raise Recoverable("not a commit.")
        else:
            raise Recoverable("a singleton selection set is required.")
        with RepoSurgeon.LineParse(self, line) as parse:
            if not parse.line:
                raise Recoverable("no tarball specified.")
            # Create new commit to carry the new content
            blank = Commit()
            blank.committer = Attribution()
            blank.mark = repo.newmark()
            blank.repo = repo
            (blank.committer.name, blank.committer.email) = whoami()
            blank.branch = commit.branch
            blank.comment = "Content from %s\n" % parse.line
            blank.committer.date = Date("1970-01-01T00:00:00Z")
            strip = int(parse.optval("strip") or 1)
            if "--after" in parse.options:
                loc = repo.find(commit.mark)+1
            else:
                loc = repo.find(commit.mark)
                while loc > 0:
                    if isinstance(repo.events[loc-1], Blob):
                        loc -= 1
                    else:
                        break
            # Incorporate the tarball content
            try:
                newest = 0
                here = os.getcwd()
                with tarfile.open(parse.line) as tarball:
                    os.Chdir(repo.subdir())
                    tarball.extractall()
                    os.Chdir(here)
                IXANY = stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH
                with tarfile.open(parse.line) as tarball:
                    # Pre-sorting avoids an indeterminacy bug in tarfile
                    # order traversal.
                    info = []
                    for tarinfo in tarball:
                        info.append(tarinfo)
                    info.sort(key=lambda x: x.name)
                    for tarinfo in info:
                        if tarinfo.type == tarfile.REGTYPE:
                            if newest < tarinfo.mtime:
                                newest = tarinfo.mtime
                            b = Blob(repo)
                            repo.addEvent(b, where=loc)
                            loc += 1
                            repo.declare_sequence_mutation()
                            repo.invalidateObjectMap()
                            b.setMark(repo.newmark())
                            #b.size = tarinfo.size
                            b.setBlobfile(os.path.join(self.repo.subdir(), tarinfo.name))
                            op = FileOp(repo)
                            fn = os.path.join(*os.path.split(tarinfo.name)[strip:])
                            mode = 0o100644
                            if tarinfo.mode & IXANY:
                                mode = 0o100755
                            op.construct("M", mode, b.mark, fn)
                            blank.appendOperation(op)
                repo.declare_sequence_mutation()
                repo.invalidateObjectMap()
                if not globalOptions["testmode"]:
                    blank.committer.date = Date(rfc3339(newest))
            except IOError:
                raise Recoverable("open or read failed on %s" % parse.line)
            # Link it into the repository
            if "--after" not in parse.options:
                repo.addEvent(blank, where=loc)
                blank.setParents(commit.parents())
                commit.setParents([blank])
            else:
                blank.setParents([commit])
                for offspring in commit.children():
                    offspring.replaceParent(commit, blank)
                repo.addEvent(blank, where=loc)
            # We get here if incorporation worked OK.
            for opt in parse.options:
                if opt.startswith("--date"):
                    blank.committer.date = Date(opt.split("=")[1])
            # Generate deletes into the next commit(s) so files won't
            # leak forward. Also prevent files leaking forward from any
            # previous commit.  We gave to force determinstic path list
            # order here, otherwise regressio tests will fail in flaky
            # ways.
            blank_path_list = list(blank.paths())
            blank_path_list.sort()
            for path in blank_path_list:
                for child in blank.children():
                    if path not in child.paths():
                        op = FileOp(repo)
                        op.construct("D", path)
                        child.appendOperation(op)
            for parent in blank.parents():
                for leaker in parent.paths():
                    if leaker not in blank_path_list:
                        op = FileOp(repo)
                        op.construct("D", leaker)
                        blank.appendOperation(op)

    #
    # Version binding
    #
    func help_version():
        os.Stdout.write("""
With no argument, display the reposurgeon version and supported VCSes.
With argument, declare the major version (single digit) or full
version (major.minor) under which the enclosing script was developed.
The program will error out if the major version has changed (which
means the surgical language is not backwards compatible).
""")
    func do_version(self, line):
        if not line:
            announce(debugSHOUT, "reposurgeon " + version + " supporting " + " ".join(x.name for x in (vcstypes+extractors)))
        else:
            (vmajor, _) = version.split(".")
            if '.' in line:
                try:
                    (major, _) = line.strip().split(".")
                except ValueError:
                    complain("invalid version.")
                    return
            else:
                major = line.strip()
            if major != vmajor:
                raise Fatal("major version mismatch, aborting.")
            else if verbose > 0:
                announce(debugSHOUT, "version check passed.")

    #
    # Exiting (in case EOT has been rebound)
    #
    func help_elapsed():
        os.Stdout.write("""
Desplay elapsed time since start.
""")
    func do_elapsed(self, _line):
        announce(debugSHOUT, "elapsed time %s." % humanize(time.time() - self.start_time))

    func help_exit():
        os.Stdout.write("""
Exit the program cleanly, emitting a goodbye message.

Typing EOT (usually Ctrl-D) will exit quietly.
""")
    func do_exit(self, _line):
        announce(debugSHOUT, "exiting, elapsed time %s." % humanize(time.time() - self.start_time))
        sys.exit(0)

    #
    # Prompt customization
    #
    func help_prompt():
        os.Stdout.write("""
Set the command prompt format to the value of the command line; with
an empty command line, display it. The prompt format is evaluated in Python
after each command with the following dictionary substitutions:

chosen: The name of the selected repository, or None if none currently selected.

Thus, one useful format might be 'rs[%(chosen)s]%% '

More format items may be added in the future.  The default prompt corresponds
to the format 'reposurgeon%% '. The format line is evaluated with shell quotng
of tokens, so that spaces can be included.
""")
    func do_prompt(self, line):
        if line:
            self.prompt_format = " ".join(shlex.split(line))
        else:
            os.Stdout.write("prompt = %s\n" % self.prompt_format)

func main():
    try:
        func interactive():
            global verbose
            interpreter.use_rawinput = true
            if verbose == 0:
                verbose = 1
            interpreter.cmdloop()
            interpreter.use_rawinput = false
        interpreter = RepoSurgeon()
        interpreter.use_rawinput = false
        if not sys.argv[1:]:
            sys.argv.append("-")
        try:
            for arg in sys.argv[1:]:
                for acmd in arg.split(";"):
                    if acmd == '-':
                        if interpreter.profile_log is None:
                            interactive()
                        else if interpreter.profile_log:
                            cProfile.run('interactive()', \
                                         interpreter.profile_log)
                        else:
                            cProfile.run('interactive()')
                    else:
                        # A minor concession to people used to GNU conventions.
                        # Makes "reposurgeon --help" and "reposurgeon --version"
                        # work as expected.
                        if acmd.startswith("--"):
                            acmd = acmd[2:]
                        # Call the base method so RecoverableExceptions
                        # won't be caught; we want them to abort scripting.
                        cmd.Cmd.onecmd(interpreter, interpreter.precmd(acmd))
        finally:
            interpreter.cleanup()
    except (Recoverable, Fatal) as xe:
        complain(xe.msg)
        sys.exit(1)
    except KeyboardInterrupt:
        os.Stdout.write("\n")

*/

func main() {
	if false {
		fmt.Print(vcstypes[1])
	}
}

/*
	FIXME: This is the rest of svnProcess()

        # Build filemaps.
        announce(debugEXTRACT, "Pass 2")
        filemaps = {}
        filemap = PathMap()
        for (revision, record) in sp.revisions.items():
            for node in record.nodes:
                # Mutate the filemap according to copies
                if node.fromRev:
                    assert parseInt(node.fromRev) < parseInt(revision)
                    filemap.copyFrom(node.path, filemaps[node.fromRev],
                                      node.fromPath)
                    announce(debugFILEMAP, "r%d~%s copied to %s" \
                                 % (node.fromRev, node.fromPath, node.path))
                # Mutate the filemap according to adds/deletes/changes
                if node.action == sdADD && node.kind == sdFILE:
                    filemap[node.path] = node
                    announce(debugFILEMAP, "r%d~%s added" % (node.revision, node.path))
                else if node.action == sdDELETE or (node.action == sdREPLACE && node.kind == sdDIR):
                    if node.kind == sdNONE:
                        node.kind = sdFILE if node.path in filemap else sdDIR
                    # Snapshot the deleted paths before removing them.
                    node.fromSet = PathMap()
                    node.fromSet.copyFrom(node.path, filemap, node.path)
                    del filemap[node.path]
                    announce(debugFILEMAP, "r%d~%s deleted" \
                                 % (node.revision, node.path))
                else if node.action in (sdCHANGE, sdREPLACE) && node.kind == sdFILE:
                    filemap[node.path] = node
                    announce(debugFILEMAP, "r%d~%s changed" % (node.revision, node.path))
            filemaps[revision] = filemap.snapshot()
            baton.twirl("")
        del filemap
        timeit("filemaps")
        # Blows up huge on large repos...
        #if debugEnable(debugFILEMAP):
        #    announce(debugSHOUT, "filemaps %s" % filemaps)

        # Build from sets in each directory copy record.
        announce(debugEXTRACT, "Pass 3")
        for copynode in copynodes:
            if debugEnable(debugFILEMAP):
                # Conditional retained because computing this filemap
                # slice can be expensive enough to look like a hang forever
                # on a sufficiently large repository - GCC was the type case.
                announce(debugFILEMAP, "r%s copynode filemap is %s" \
                         % (copynode.fromRev, filemaps[copynode.fromRev]))
            copynode.fromSet = PathMap()
            copynode.fromSet.copyFrom(copynode.fromPath,
                                        filemaps[copynode.fromRev],
                                        copynode.fromPath)
            baton.twirl("")
        timeit("copysets")
*/

/*
	# Build commits
        # This code can eat your processor, so we make it give up
        # its timeslice at reasonable intervals. Needed because
        # it doesn't hit the disk.
        announce(debugEXTRACT, "Pass 4")
        split_commits = {}
        func (sp *StreamParser)  last_relevant_commit(max_rev, path,
                                 getbranch = operator.attrgetter("branch")):
            # Make path look like a branch
            if path[0] == "/": path = path[1:]
            if path[-1] != svnSep: path = path + svnSep
            # If the revision is split, try from the last split commit
            try:
                max_rev = split_commits[max_rev]
            except KeyError:
                pass
            # Find the commit object...
            try:
                obj = sp.repo.legacyMap["SVN:%s" % max_rev]
            except KeyError:
                return None
            for ind in range(sp.repo.index(obj), -1, -1):
                event = sp.repo.events[ind]
                if isinstance(event, Commit):
`                    b = getbranch(event)
                    if b && path.startswith(b):
                        return event
            return None
        previous = None
        # If the repo is large, we'll give up on some diagnostic info in order
        # to reduce the working set size.
        if len(sp.revisions.keys()) > 50000:
            sp.large = true
        for (revision, record) in sp.revisions.items():
            announce(debugEXTRACT, "Revision %s:" % revision)
            for node in record.nodes:
                # In Subversion, we can assume .cvsignores are
                # legacies from a bygone era that have been long since
                # replaced by svn:ignore properties.  Therefore we can
                # just drop them.
                if node.path.endswith(".cvsignore"):
                    continue
                # if node.props is None, no property section.
                # if node.blob is None, no text section.
                try:
                    assert node.action in (sdCHANGE, sdADD, sdDELETE, sdREPLACE)
                    assert node.blob is not None or \
                           node.props is not None or \
                           node.fromRev or \
                           node.action in (sdADD, sdDELETE)
                    assert (node.fromRev is None) == (node.fromPath is None)
                    assert node.kind in (sdFILE, sdDIR)
                    assert node.kind != sdNONE or node.action == sdDELETE
                    assert node.action in (sdADD, sdREPLACE) or not node.fromRev
                except AssertionError:
                    raise Fatal("forbidden operation in dump stream at r%s: %s" \
                                % (revision, node))
            #memcheck(sp.repo)
            commit = Commit(sp.repo)
            ad = record.date
            if ad is None:
                sp.error("missing required date field")
            if record.author:
                au = record.author
            else:
                au = "no-author"
            if record.log:
                commit.comment = record.log
                if not commit.comment.endswith("\n"):
                    commit.comment += "\n"
            if '@' in au:
                # This is a thing that happens occasionally.  A DVCS-style
                # attribution (name + email) gets stuffed in a Subversion
                # author field
                # First, check to see if it's a fully-formed address
                if au.count("<") == 1 and au.count(">") == 1 and au.count(" ") > 0:
                    attribution = au + " " + ad
                else:
                    # Punt...
                    (au, ah) = au.split("@")
                    attribution = au + " <" + au  + "@" + ah  + "> " + ad
            else if '--use-uuid' in options:
                attribution = "%s <%s@%s> %s" % (au, au, sp.repo.uuid, ad)
            else:
                attribution = "%s <%s> %s" % (au, au, ad)
            commit.committer = Attribution(attribution)
            # Use this with just-generated input streams
            # that have wall times in them.
            if haveGlobalOptions("testmode"):
                commit.committer.name = "Fred J. Foonly"
                commit.committer.email = "foonly@foo.com"
                commit.committer.date.timestamp = parseInt(revision) * 360
                commit.committer.date.set_tz("GMT")
            commit.properties = record.props
            # Zero revision is never interesting - no operations, no
            # comment, no author, it's just a start marker for a
            # non-incremental dump.
            if revision == "0":
                continue
            expanded_nodes = []
            has_properties = set()
            for (n, node) in enumerate(record.nodes):
                if debugEnable(debugEXTRACT):
                    announce(debugEXTRACT, "r%s:%d: %s" % (revision, n+1, node))
                else if node.kind == sdDIR \
                         && node.action != sdCHANGE \
                         && debugEnable(debugTOPOLOGY):
                    announce(debugSHOUT, str(node))
                # Handle per-path properties.
                if node.props is not None:
                    if "cvs2svn:cvs-rev" in node.props:
                        cvskey = "CVS:%s:%s" % (node.path,
                                                node.props["cvs2svn:cvs-rev"])
                        sp.repo.legacyMap[cvskey] = commit
                        del node.props["cvs2svn:cvs-rev"]
                    # Remove blank lines from svn:ignore property values.
                    if "svn:ignore" in node.props:
                        old_ignore = node.props["svn:ignore"]
                        ignore_lines = [line for line in old_ignore.splitlines(true) if line != "\n"]
                        new_ignore = "".join(ignore_lines)
                        if new_ignore == "":
                            del node.props["svn:ignore"]
                        else:
                            node.props["svn:ignore"] = new_ignore
                    if "--ignore-properties" not in options:
                        prop_items = ((prop, val) \
                                        for (prop,val) in node.props.items() \
                                        if ((prop not in StreamParser.IgnoreProperties) && not (prop == "svn:mergeinfo" && node.kind == sdDIR)))
                        try:
                            first = next(prop_items)
                        except StopIteration:
                            if node.path in has_properties:
                                sp.gripe("r%d~%s: properties cleared." \
                                             % (node.revision, node.path))
                                has_properties.discard(node.path)
                        else:
                            sp.gripe("r%d~%s properties set:" \
                                                   % (node.revision, node.path))
                            for prop, val in itertools.chain((first,), prop_items):
                                sp.gripe("\t%s = '%s'" % (prop, val))
                            has_properties.add(node.path)
                if node.kind == sdFILE:
                    expanded_nodes.append(node)
                else if node.kind == sdDIR:
                    # svnSep is appended to avoid collisions with path
                    # prefixes.
                    node.path += svnSep
                    if node.fromPath:
                        node.fromPath += svnSep
                    if node.action in (sdADD, sdCHANGE):
                        if node.path in sp.branches:
                            if not node.props: node.props = {}
                            startwith = next(vcs.dfltignores for vcs in vcstypes if vcs.name == "svn")
                            try:
                                ignore = startwith + \
                                         "# The contents of the svn:ignore " \
                                         "property on the branch root.\n" + \
                                         node.props["svn:ignore"]
                            except KeyError:
                                ignore = startwith
                            node.props["svn:ignore"] = ignore
                    else if node.action in (sdDELETE, sdREPLACE):
                        if node.path in sp.branches:
                            sp.branchdeletes.add(node.path)
                            expanded_nodes.append(node)
                            # The deleteall will also delete .gitignore files
                            for ignorepath in list(gi
                                        for gi in sp.activeGitignores
                                        if gi.startswith(node.path)):
                                del sp.activeGitignores[ignorepath]
                        else:
                            # A delete or replace with no from set
                            # can occur if the directory is empty.
                            # We can just ignore this case.
                            if node.fromSet is not None:
                                for child in node.fromSet:
                                    announce(debugEXTRACT, "r%s: deleting %s" \
                                                 % (revision, child))
                                    newnode = StreamParser.NodeAction()
                                    newnode.path = child
                                    newnode.revision = revision
                                    newnode.action = sdDELETE
                                    newnode.kind = sdFILE
                                    newnode.generated = true
                                    expanded_nodes.append(newnode)
                            # Emit delete actions for the .gitignore files we
                            # have generated. Note that even with a directory
                            # with no files from SVN, we might have added
                            # .gitignore files we now must delete.
                            for ignorepath in list(gi
                                        for gi in sp.activeGitignores
                                        if gi.startswith(node.path)):
                                newnode = StreamParser.NodeAction()
                                newnode.path = ignorepath
                                newnode.revision = revision
                                newnode.action = sdDELETE
                                newnode.kind = sdFILE
                                newnode.generated = true
                                expanded_nodes.append(newnode)
                                del sp.activeGitignores[ignorepath]
                    # Handle directory copies.  If this is a copy
                    # between branches, no fileop should be issued
                    # until there is an actual file modification on
                    # the new branch. Instead, remember that the
                    # branch root inherits the tree of the source
                    # branch and should not start with a deleteall.
                    # Exception: If the target branch has been
                    # deleted, perform a normal copy and interpret
                    # this as an ad-hoc branch merge.
                    if node.fromPath:
                        branchcopy = node.fromPath in sp.branches \
                                         && node.path in sp.branches \
                                         && node.path not in sp.branchdeletes
                        announce(debugTOPOLOGY, "r%s: directory copy to %s from " \
                                     "r%d~%s (branchcopy %s)" \
                                     % (revision,
                                        node.path,
                                        node.fromRev,
                                        node.fromPath,
                                        branchcopy))
                        # Update our .gitignore list so that it includes those
                        # in the newly created copy, to ensure they correctly
                        # get deleted during a future directory deletion.
                        l = len(node.fromPath)
                        for sourcegi, value in list((gi,v) for (gi,v) in
                                    sp.activeGitignores.items()
                                    if gi.startswith(node.fromPath)):
                            destgi = node.path + sourcegi[l:]
                            sp.activeGitignores[destgi] = value
                        if branchcopy:
                            sp.branchcopies.add(node.path)
                            # Store the minimum information needed to propagate
                            # executable bits across branch copies. If we needed
                            # to preserve any other properties, sp.propagate
                            # would need to have property maps as values.
                            for source in node.fromSet:
                                lookback = filemaps[node.fromRev][source]
                                if lookback.props && "svn:executable" in lookback.props:
                                    stem = source[len(node.fromPath):]
                                    targetpath = node.path + stem
                                    sp.propagate[targetpath] = true
                                    announce(debugTOPOLOGY, "r%s: exec-mark %s" \
                                             % (revision, targetpath))
                        else:
                            sp.branchdeletes.discard(node.path)
                            # Generate copy ops for generated .gitignore files
                            # to match the copy of svn:ignore props on the
                            # Subversion side. We use the just updated
                            # activeGitignores dict for that purpose.
                            if '--user-ignores' not in options:
                                for gipath, ignore in list(
                                            (gi,v) for (gi,v) in
                                            sp.activeGitignores.items()
                                            if gi.startswith(node.path)):
                                    blob = Blob(sp.repo)
                                    blob.setContent(ignore)
                                    subnode = StreamParser.NodeAction()
                                    subnode.path = gipath
                                    subnode.revision = revision
                                    subnode.action = sdADD
                                    subnode.kind = sdFILE
                                    subnode.blob = blob
                                    subnode.contentHash = \
                                            hashlib.md5(polybytes(ignore)).hexdigest()
                                    subnode.generated = true
                                    expanded_nodes.append(subnode)
                            # Now generate copies for all files in the source
                            for source in node.fromSet:
                                lookback = filemaps[node.fromRev][source]
                                if lookback is None:
                                    raise Fatal("r%s: can't find ancestor %s" \
                                             % (revision, source))
                                subnode = StreamParser.NodeAction()
                                subnode.path = node.path + \
                                        source[len(node.fromPath):]
                                subnode.revision = revision
                                subnode.fromPath = lookback.path
                                subnode.fromRev = lookback.revision
                                subnode.fromHash = lookback.contentHash
                                subnode.props = lookback.props
                                subnode.action = sdADD
                                subnode.kind = sdFILE
                                announce(debugTOPOLOGY, "r%s: generated copy r%d~%s -> %s" \
                                             % (revision,
                                                subnode.fromRev,
                                                subnode.fromPath,
                                                subnode.path))
                                subnode.generated = true
                                expanded_nodes.append(subnode)
                    # Property settings can be present on either
                    # sdADD or sdCHANGE actions.
                    if node.propchange && node.props is not None:
                        announce(debugEXTRACT, "r%s: setting properties %s on %s" \
                                     % (revision, node.props, node.path))
                        # svn:ignore gets handled here,
                        if '--user-ignores' not in options:
                            if node.path == svnSep:
                                gitignore_path = ".gitignore"
                            else:
                                gitignore_path = os.path.join(node.path,
                                                              ".gitignore")
                            # There are no other directory properties that can
                            # turn into fileops.
                            ignore = node.props.get("svn:ignore")
                            if ignore is not None:
                                # svn:ignore properties are nonrecursive
                                # to lower directories, but .gitignore
                                # patterns are recursive.  Thus we need to
                                # anchor the translated pattern with
                                # leading / in order to render the
                                # Subversion behavior accurately.  However,
                                # if done naively this clobbers the branch-root
                                # defaults, so we need to have protected these
                                # with a leading slash and reverse the transform.
                                ignore = polystr(re.sub("\n(?!#)".encode('ascii'), "\n/".encode('ascii'), polybytes("\n" + ignore)))
                                ignore = ignore.replace("\n//", "\n")
                                ignore = ignore[1:]
                                if ignore.endswith("/"):
                                    ignore = ignore[:-1]
                                blob = Blob(sp.repo)
                                blob.setContent(ignore)
                                newnode = StreamParser.NodeAction()
                                newnode.path = gitignore_path
                                newnode.revision = revision
                                newnode.action = sdADD
                                newnode.kind = sdFILE
                                newnode.blob = blob
                                newnode.contentHash = \
                                        hashlib.md5(polybytes(ignore)).hexdigest()
                                announce(debugIGNORES, "r%s: queuing up %s generation with:\n%s." % (revision, newnode.path, node.props["svn:ignore"]))
                                # Must append rather than simply performing.
                                # Otherwise when the property is unset we
                                # won't have the right thing happen.
                                newnode.generated = true
                                expanded_nodes.append(newnode)
                                sp.activeGitignores[gitignore_path] = ignore
                            else if gitignore_path in sp.activeGitignores:
                                newnode = StreamParser.NodeAction()
                                newnode.path = gitignore_path
                                newnode.revision = revision
                                newnode.action = sdDELETE
                                newnode.kind = sdFILE
                                announce(debugIGNORES, "r%s: queuing up %s deletion." % (revision, newnode.path))
                                newnode.generated = true
                                expanded_nodes.append(newnode)
                                del sp.activeGitignores[gitignore_path]
            # Ugh.  Because cvs2svn is brain-dead and issues D/M pairs
            # for identical paths in generated commits, we have to remove those
            # D ops here.  Otherwise later on when we're generating ops, if
            # the M node happens to be missing its hash it will be seen as
            # unmodified and only the D will be issued.
            seen = set()
            for node in reversed(expanded_nodes):
                if node.action == sdDELETE and node.path in seen:
                    node.action = None
                seen.add(node.path)
            # Create actions corresponding to both
            # parsed and generated nodes.
            actions = []
            ancestor_nodes = {}
            for node in expanded_nodes:
                if node.action is None: continue
                if node.kind == sdFILE:
                    if node.action == sdDELETE:
                        assert node.blob is None
                        fileop = FileOp(sp.repo)
                        fileop.construct("D", node.path)
                        actions.append((node, fileop))
                        ancestor_nodes[node.path] = None
                    else if node.action in (sdADD, sdCHANGE, sdREPLACE):
                        # Try to figure out who the ancestor of
                        # this node is.
                        if node.fromPath or node.fromHash:
                            # Try first via fromPath
                            ancestor = filemaps[node.fromRev][node.fromPath]
                            if debugEnable(debugTOPOLOGY):
                                if ancestor:
                                    announce(debugSHOUT, "r%d~%s -> %s (via filemap)" % \
                                             (node.revision, node.path, ancestor))
                                else:
                                    announce(debugSHOUT, "r%d~%s has no ancestor (via filemap)" % \
                                             (node.revision, node.path))
                            # Fallback on the first blob that had this hash
                            if node.fromHash && not ancestor:
                                ancestor = sp.hashmap[node.fromHash]
                                announce(debugTOPOLOGY, "r%d~%s -> %s (via hashmap)" % \
                                         (node.revision, node.path, ancestor))
                            if not ancestor && not node.path.endswith(".gitignore"):
                                sp.gripe("r%d~%s: missing filemap node." \
                                          % (node.revision, node.path))
                        else if node.action != sdADD:
                            # Ordinary inheritance, no node copy.  For
                            # robustness, we don't assume revisions are
                            # consecutive numbers.
                            try:
                                ancestor = ancestor_nodes[node.path]
                            except KeyError:
                                ancestor = filemaps[previous][node.path]
                        else:
                            ancestor = None
                        # Time for fileop generation
                        if node.blob is not None:
                            if node.contentHash in sp.hashmap:
                                # Blob matches an existing one -
                                # node was created by a
                                # non-Subversion copy followed by
                                # add.  Get the ancestry right,
                                # otherwise parent pointers won't
                                # be computed properly.
                                ancestor = sp.hashmap[node.contentHash]
                                node.fromPath = ancestor.fromPath
                                node.fromRev = ancestor.fromRev
                                node.blobmark = ancestor.blobmark
                            else:
                                # An entirely new blob
                                node.blobmark = node.blob.setMark(sp.repo.newmark())
                                sp.repo.addEvent(node.blob)
                                # Blobs generated by reposurgeon
                                # (e.g .gitignore content) have no
                                # content hash.  Don't record
                                # them, otherwise they'll all
                                # collide :-)
                                if node.contentHash:
                                    sp.hashmap[node.contentHash] = node
                        else if ancestor:
                            node.blobmark = ancestor.blobmark
                        else:
                            # No ancestor, no blob. Has to be a
                            # pure property change.  There's no
                            # way to figure out what mark to use
                            # in a fileop.
                            if not node.path.endswith(".gitignore"):
                                sp.gripe("r%d~%s: permission information may be lost." \
                                           % (node.revision, node.path))
                            continue
                        ancestor_nodes[node.path] = node
                        assert node.blobmark
                        # Time for fileop generation.
                        perms = sp.nodePermissions(node)
                        if node.path in sp.propagate:
                            perms = 0o100755
                            del sp.propagate[node.path]
                        new_content = (node.blob is not None)
                        # Ignore and complain about explicit .gitignores
                        # created, e.g, by git-svn.  In an ideal world we
                        # would merge these with svn:ignore properties. but
                        # this would be hairy and bug-prone. So we give
                        # the user a heads-up and expect these to be
                        # merged by hand.
                        if new_content \
                           && not node.generated \
                           && '--user-ignores' not in options \
                           && node.path.endswith(".gitignore"):
                            sp.gripe("r%d~%s: user-created .gitignore ignored." \
                                       % (node.revision, node.path))
                            continue
                        # This ugly nasty guard is critically important.
                        # We need to generate a modify if:
                        # 1. There is new content.
                        # 2. This node was generated as an
                        # expansion of a directory copy.
                        # 3. The node was produced by an explicit
                        # Subversion file copy (not a directory copy)
                        # in which case it has an MD5 hash that points
                        # back to a source.
                        # 4. The permissions for this path have changed;
                        # we need to generate a modify with an old mark
                        # but new permissions.
                        generated_file_copy = node.generated
                        subversion_file_copy = (node.fromHash is not None)
                        if (new_content or
                            generated_file_copy or
                            subversion_file_copy or
                            node.propchange):
                            assert perms
                            fileop = FileOp(sp.repo)
                            fileop.construct(opM,
                                             perms,
                                             node.blobmark,
                                             node.path)
                            actions.append((node, fileop))
                            sp.repo.markToEvent(fileop.ref).addalias(node.path)
                        else if debugEnable(debugEXTRACT):
                            announce(debugEXTRACT, "r%d~%s: unmodified" % (node.revision, node.path))
                # These are directory actions.
                else if node.action in (sdDELETE, sdREPLACE):
                    announce(debugEXTRACT, "r%s: deleteall %s" % (revision,node.path))
                    fileop = FileOp(sp.repo)
                    fileop.construct("deleteall", node.path[:-1])
                    actions.append((node, fileop))
            # Time to generate commits from actions and fileops.
            announce(debugEXTRACT, "r%s: %d actions" % (revision, len(actions)))
            # First, break the file operations into branch cliques
            cliques = newOrderedMap()
            lastbranch = None
            for (node, fileop) in actions:
                # Try last seen branch first
                if lastbranch && node.path.startswith(lastbranch):
                    cliques.setdefault(lastbranch, []).append(fileop)
                    continue
                # Preferentially match longest branches
                for branch in sp.branchlist():
                    if node.path.startswith(branch):
                        cliques.setdefault(branch, []).append(fileop)
                        lastbranch = branch
                        break
                else:
                    cliques.setdefault("", []).append(fileop)
            # Make two operation lists from the cliques, sorting cliques
            # containing only branch deletes from other cliques.
            deleteall_ops = []
            other_ops = []
            for (branch, ops) in cliques.items():
                if len(ops) == 1 && ops[0].op == FileOp.deleteall:
                    deleteall_ops.append((branch, ops))
                else:
                    other_ops.append((branch, ops))
            oplist = itertools.chain(other_ops, deleteall_ops)
            # Create all commits corresponding to the revision
            newcommits = []
            commit.legacyID = revision
            if len(other_ops) <= 1:
                # In the ordinary case, we can assign all non-deleteall fileops
                # to the base commit.
                sp.repo.legacyMap["SVN:%s" % commit.legacyID] = commit
                try:
                    commit.common, stage = next(oplist)
                    commit.setOperations(stage)
                    commit.invalidatePathsetCache()
                except StopIteration:
                    commit.common = os.path.commonprefix([node.path for node in record.nodes])
                commit.setMark(sp.repo.newmark())
                announce(debugEXTRACT, "r%s gets mark %s" % (revision, commit.mark))
                newcommits.append(commit)
            # If the commit is mixed, or there are deletealls left over,
            # handle that.
            oplist = sorted(oplist, key=operator.itemgetter(0))
            for (i, (branch, fileops)) in enumerate(oplist):
                split = commit.clone()
                split.common = branch
                # Sequence numbers for split commits are 1-origin
                split.legacyID += StreamParser.SplitSep + str(i + 1)
                sp.repo.legacyMap["SVN:%s" % split.legacyID] = split
                if split.comment is None:
                    split.comment = ""
                split.comment += "\n[[Split portion of a mixed commit.]]\n"
                split.setMark(sp.repo.newmark())
                split.setOperations(fileops)
                split.invalidatePathsetCache()
                newcommits.append(split)
            # The revision is truly mixed if there is more than one clique
            # not consisting entirely of deleteall operations.
            if len(other_ops) > 1:
                # Store the last used split id
                split_commits[revision] = split.legacyID
            # Sort fileops according to git rules
            for newcommit in newcommits:
                newcommit.sortOperations()
            # Deduce links between branches on the basis of copies. This
            # is tricky because a revision can be the target of multiple
            # copies.  Humans don't abuse this because tracking multiple
            # copies is too hard to do in a slow organic brain, but tools
            # like cvs2svn can generate large sets of them. cvs2svn seems
            # to try to copy each file && directory from the commit
            # corresponding to the CVS revision where the file was last
            # changed before the copy, which may be substantially earlier
            # than the CVS revision corresponding to the
            # copy. Fortunately, we can resolve such sets by the simple
            # expedient of picking the *latest* revision in them!
            # No code uses the result if branch analysis is turned off.
            if not nobranch:
                for newcommit in newcommits:
                    if commit.mark in sp.branchlink: continue
                    copies = [node for node in record.nodes \
                              if node.fromRev is not None \
                              && node.path.startswith(newcommit.common)]
                    if copies && debugEnable(debugTOPOLOGY):
                        announce(debugSHOUT, "r%s: copy operations %s" %
                                     (newcommit.legacyID, copies))
                    # If the copies include one for the directory, use that as
                    # the first parent: most of the files in the new branch
                    # will come from that copy, and that might well be a full
                    # branch copy where doing that way is needed because the
                    # fileop for the copy didn't get generated and the commit
                    # tree would be wrong if we didn't.
                    latest = next((node for node in copies
                                    if node.kind == sdDIR &&
                                       node.fromPath &&
                                       node.path == newcommit.common),
                                  None)
                    if latest is not None:
                        sp.directoryBranchlinks.add(newcommit.common)
                        announce(debugTOPOLOGY, "r%s: directory copy with %s" \
                                     % (newcommit.legacyID, copies))
                    # Use may have botched a branch creation by doing a
                    # non-Subversion directory copy followed by a bunch of
                    # Subversion adds. Blob hashes will match existing files,
                    # but fromRev and fromPath won't be set at parse time.
                    # Our code detects this case and makes file
                    # backlinks, but can't deduce the directory copy.
                    # Thus, we have to treat multiple file copies as
                    # an instruction to create a gitspace branch.
                    #
                    # This guard filters out copy op sets that are
                    # *single* file copies. We're making an assumption
                    # here that multiple file copies should always
                    # trigger a branch link creation.  This assumption
                    # could be wrong, which is why we emit a warning
                    # message later on for branch links detected this
                    # way
                    #
                    # Even with this filter you'll tend to end up with lots
                    # of little merge bubbles with no commits on one side;
                    # these have to be removed by a debubbling pass later.
                    # I don't know what generates these things - cvs2svn, maybe.
                    #
                    # The second conjunct of this guard filters out the case
                    # where the user actually did do a previous Subversion file
                    # copy to start the branch, in which case we want to link
                    # through that.
                    else if len(copies) > 1 \
                             && newcommit.common not in sp.directoryBranchlinks:
                        # Use max() on the reversed iterator since max returns
                        # the first item with the max key and we want the last
                        latest = max(reversed(copies),
                                     key=lambda node: parseInt(node.fromRev))
                    if latest is not None:
                        prev = last_relevant_commit(
                                latest.fromRev, latest.fromPath,
                                operator.attrgetter("common"))
                        if prev is None:
                            if debugEnable(debugTOPOLOGY):
                                complain("lookback for %s failed, not making branch link" % latest)
                        else:
                            sp.fileopBranchlinks.add(newcommit.common)
                            announce(debugTOPOLOGY, "r%s: making branch link %s" %
                                         (newcommit.legacyID, newcommit.common))
                            sp.branchlink[newcommit.mark] = (newcommit, prev)
                            announce(debugTOPOLOGY, "r%s: link %s (%s) back to %s (%s, %s)" % \
                                         (newcommit.legacyID,
                                          newcommit.mark,
                                          newcommit.common,
                                          latest.fromRev,
                                          prev.mark,
                                          prev.common
                                          ))
            # We're done, add all the new commits
            sp.repo.events += newcommits
            sp.repo.declare_sequence_mutation()
            # Report progress, and give up our scheduler slot
            # so as not to eat the processor.
            baton.twirl("")
            time.sleep(0)
            previous = revision
            # End of processing for this Subversion revision.  If the
            # repo is large, we throw out file records for this node in
            # order to reduce the maximum working set from proportional
            # to two times the number of Subversion commits to one time.
            # What we give up is some detail in the diagnostic messages
            # on zero-fileop commits.
            if sp.large:
                record.nodes = [n for n in record.nodes if n.kind == sdDIR]
                sp.revisions[revision] = record
        # Filemaps are no longer needed
        del filemaps
        # Bail out if we have read no commits
        try:
            sp.repo.earliest_commit()
        except StopIteration:
            raise Recoverable("empty stream or repository.")
        # Warn about dubious branch links
        sp.fileopBranchlinks.discard("trunk" + svnSep)
        if sp.fileopBranchlinks - sp.directoryBranchlinks:
            sp.gripe("branch links detected by file ops only: %s" % " ".join(sorted(sp.fileopBranchlinks - sp.directoryBranchlinks)))
        timeit("commits")
        if debugEnable(debugEXTRACT):
            announce(debugEXTRACT, "at post-parsing time:")
            for commit in sp.repo.commits():
                msg = commit.comment
                if msg is None:
                    msg = ""
                announce(debugSHOUT, "r%-4s %4s %2d %2d '%s'" % \
                         (commit.legacyID, commit.mark,
                          len(commit.operations()),
                          len(commit.properties or ""),
                          msg.strip()[:20]))
        # First, turn the root commit into a tag
        if sp.repo.events && not sp.repo.earliest_commit().operations():
            try:
                initial, second = itertools.islice(sp.repo.commits(), 2)
                sp.repo.tagify(initial,
                                 "root",
                                 second,
                                 "[[Tag from root commit at Subversion r%s]]\n" % initial.legacyID)
            except ValueError: # sp.repo has less than two commits
                sp.gripe("could not tagify root commit.")
        timeit("rootcommit")
        # Now, branch analysis.
        branchroots = []
        if not sp.branches or nobranch:
            last = None
            for commit in sp.repo.commits():
                commit.setBranch(os.path.join("refs", "heads", "master") + svnSep)
                if last is not None: commit.setParents([last])
                last = commit
        else:
            # Instead, determine a branch for each commit...
            announce(debugEXTRACT, "Branches: %s" % (sp.branches,))
            lastbranch = None
            for commit in sp.repo.commits():
                if lastbranch is not None \
                        && commit.common.startswith(lastbranch):
                    branch = lastbranch
                else:
                    # Prefer the longest possible branch
                    branch = next((b for b in sp.branchlist()
                                  if commit.common.startswith(b)),
                                  None)
                if branch is not None:
                    commit.setBranch(branch)
                    for fileop in commit.operations():
                        if fileop.op in (opM, opD):
                            fileop.path = fileop.path[len(branch):]
                        else if fileop.op in (opR, opC):
                            fileop.source = fileop.source[len(branch):]
                            fileop.target = fileop.target[len(branch):]
                    commit.invalidatePathsetCache()
                else:
                    commit.setBranch("root")
                    sp.branches["root"] = None
                lastbranch = branch
                baton.twirl("")
            timeit("branches")
            # ...then rebuild parent links so they follow the branches
            for commit in sp.repo.commits():
                if sp.branches[commit.branch] is None:
                    branchroots.append(commit)
                    commit.setParents([])
                else:
                    commit.setParents([sp.branches[commit.branch]])
                sp.branches[commit.branch] = commit
                # Per-commit spinner disabled because this pass is fast
                #baton.twirl("")
            sp.timeMark("parents")
            baton.twirl("")
            # The root branch is special. It wasn't made by a copy, so
            # we didn't get the information to connect it to trunk in the
            # last phase.
            try:
                commit = next(c for c in sp.repo.commits()
                              if c.branch == "root")
            except StopIteration:
                pass
            else:
                earliest = sp.repo.earliest_commit()
                if commit != earliest:
                    sp.branchlink[commit.mark] = (commit, earliest)
            timeit("root")
            # Add links due to Subversion copy operations
            announce(debugEXTRACT, "branch roots: [{roots}], links {{{links}}}".format(
                    roots = ", ".join(c.mark for c in branchroots),
                    links = ", ".join("{l[0].mark}: {l[1].mark}".format(l=l)
                                      for l in sp.branchlink.values())))
            for (child, parent) in sp.branchlink.values():
                if parent.repo is not sp.repo:
                    # The parent has been deleted since, don't add the link;
                    # it can only happen if parent was the now tagified root.
                    continue
                if not child.hasParents() \
                        && child.branch not in sp.branchcopies:
                    # The branch wasn't created by copying another branch and
                    # is instead populated by fileops. Prepend a deleteall to
                    # ensure that it starts with a clean tree instead of
                    # inheriting that of its soon to be added first parent.
                    # The deleteall is put on the first commit of the branch
                    # which has fileops or more than one child.
                    commit = child
                    while len(commit.children()) == 1 && not commit.operations():
                        commit = commit.firstChild()
                    if commit.operations() or commit.hasChildren():
                        fileop = FileOp(sp.repo)
                        fileop.construct("deleteall")
                        commit.prependOperation(fileop)
                        sp.generatedDeletes.append(commit)
                if parent not in child.parents():
                    child.addParentCommit(parent)
            for root in branchroots:
                if getattr(commit.branch, "fileops", None) \
                        && root.branch != ("trunk" + svnSep):
                    sp.gripe("r%s: can't connect nonempty branch %s to origin" \
                                % (root.legacyID, root.branch))
            timeit("branchlinks")
            # Add links due to svn:mergeinfo properties
            mergeinfo = PathMap()
            mergeinfos = {}
            for (revision, record) in sp.revisions.items():
                for node in record.nodes:
                    if node.kind != sdDIR: continue
                    # Mutate the mergeinfo according to copies
                    if node.fromRev:
                        assert parseInt(node.fromRev) < parseInt(revision)
                        mergeinfo.copyFrom(
                                node.path,
                                mergeinfos.get(node.fromRev) or PathMap(),
                                node.fromPath)
                        announce(debugEXTRACT, "r%d~%s mergeinfo copied to %s" \
                                % (node.fromRev, node.fromPath, node.path))
                    # Mutate the filemap according to current mergeinfo.
                    # The general case is multiline: each line may describe
                    # multiple spans merging to this revision; we only consider
                    # the end revision of each span.
                    # Because svn:mergeinfo will persist like other properties,
                    # we need to compare with the already present mergeinfo and
                    # only take new entries into account when creating merge
                    # links. Also, since merging will also inherit the
                    # mergeinfo entries of the source path, we also need to
                    # gather and ignore those.
                    existing_merges = set(mergeinfo[(node.path,)] or [])
                    own_merges = set()
                    try:
                        info = node.props['svn:mergeinfo']
                    except (AttributeError, TypeError, KeyError):
                        pass
                    else:
                        for line in info.split('\n'):
                            try:
                                fromPath, ranges = line.split(":", 1)
                            except ValueError:
                                continue
                            for span in ranges.split(","):
                                # Ignore single-rev fields, they are cherry-picks.
                                # TODO: maybe we should even test if min_rev
                                # corresponds to some fromRev + 1 to ensure no
                                # commit has been skipped.
                                try:
                                    min_rev, fromRev = span.split("-", 1)
                                except ValueError:
                                    min_rev = fromRev = None
                                if (not min_rev) or (not fromRev): continue
                                # Import mergeinfo from merged branches
                                try:
                                    past_merges = mergeinfos[fromRev][(fromPath,)]
                                except KeyError:
                                    pass
                                else:
                                    if past_merges:
                                        existing_merges.update(past_merges)
                                # Svn doesn't fit the merge range to commits on
                                # the source branch; we need to find the latest
                                # commit between min_rev and fromRev made on
                                # that branch.
                                from_commit = last_relevant_commit(
                                                    fromRev, fromPath)
                                if from_commit is not None && \
                                        parseInt(from_commit.legacyID.split(".",1)[0]) \
                                            >= parseInt(min_rev):
                                    own_merges.add(from_commit.mark)
                                else:
                                    sp.gripe("cannot resolve mergeinfo "
                                               "source from revision %s for "
                                               "path %s." % (fromRev,
                                                             node.path))
                    mergeinfo[(node.path,)] = own_merges
                    new_merges = own_merges - existing_merges
                    if not new_merges: continue
                    # Find the correct commit in the split case
                    commit = last_relevant_commit(revision, node.path)
                    if commit is None or \
                            not commit.legacyID.startswith(revision):
                        # The reverse lookup went past the target revision
                        sp.gripe("cannot resolve mergeinfo destination "
                                   "to revision %s for path %s."
                                   % (revision, node.path))
                        continue
                    # Alter the DAG to express merges.
                    for mark in new_merges:
                        parent = sp.repo.markToEvent(mark)
                        if parent not in commit.parents():
                            commit.addParentCommit(parent)
                        announce(debugTOPOLOGY, "processed new mergeinfo from r%s "
                                     "to r%s." % (parent.legacyID,
                                                  commit.legacyID))
                mergeinfos[revision] = mergeinfo.snapshot()
                baton.twirl("")
            del mergeinfo, mergeinfos
            timeit("mergeinfo")
            if debugEnable(debugEXTRACT):
                announce(debugEXTRACT, "after branch analysis")
                for commit in sp.repo.commits():
                    try:
                        ancestor = commit.parents()[0]
                    except IndexError:
                        ancestor = '-'
                    announce(debugSHOUT, "r%-4s %4s %4s %2d %2d '%s'" % \
                             (commit.legacyID,
                              commit.mark, ancestor,
                              len(commit.operations()),
                              len(commit.properties or ""),
                              commit.branch))
        baton.twirl("")
        # Code controlled by --nobranch option ends.
        # Canonicalize all commits to ensure all ops actually do something.
        for commit in sp.repo.commits():
            commit.canonicalize()
            baton.twirl("")
        timeit("canonicalize")
        announce(debugEXTRACT, "after canonicalization")
        # Now clean up junk commits generated by cvs2svn.
        deleteables = []
        newtags = []
        for (i, event) in enumerate(sp.repo):
            if isinstance(event, Commit):
                # It is possible for commit.comment to be None if
                # the repository has been dumpfiltered and has
                # empty commits.  If that's the case it can't very
                # well have CVS artifacts in it.
                if event.comment is None:
                    sp.gripe("r%s has no comment" % event.legacyID)
                    continue
                # Things that cvs2svn created as tag surrogates
                # get turned into actual tags.
                m = StreamParser.cvs2svnTagRE.search(polybytes(event.comment))
                if m && not event.hasChildren():
                    fulltag = os.path.join("refs", "tags", polystr(m.group(1)))
                    newtags.append(Reset(sp.repo, ref=fulltag,
                                                  target=event.parents()[0]))
                    deleteables.append(i)
                # Childless generated branch commits carry no informationn,
                # and just get removed.
                m = StreamParser.cvs2svnBranchRE.search(polybytes(event.comment))
                if m && not event.hasChildren():
                    deleteables.append(i)
                baton.twirl("")
        sp.repo.delete(deleteables, ["--tagback"])
        sp.repo.events += newtags
        baton.twirl("")
        timeit("junk")
        announce(debugEXTRACT, "after cvs2svn artifact removal")
        # Now we need to tagify all other commits without fileops, because git
        # is going to just discard them when we build a live repo and they
        # might possibly contain interesting metadata.
        # * Commits from tag creation often have no fileops since they come
        #   from a directory copy in Subversion. The annotated tag name is the
        #   basename of the SVN tag directory.
        # * Same for branch-root commits. The tag name is the basename of the
        #   branch directory in SVN, with "-root" appended to distinguish them
        #   from SVN tags.
        # * Commits at a branch tip that consist only of deleteall are also
        #   tagified: their fileops aren't worth saving; the comment metadata
        #   just might be.
        # * All other commits without fileops get turned into an annotated tag
        #   with name "emptycommit-<revision>".
        rootmarks = {root.mark for root in branchroots} # empty if nobranch
        rootskip = {"trunk"+svnSep, "root"}
        func (sp *StreamParser)  tagname(commit):
            # Give branch and tag roots a special name, except for "trunk" and
            # "root" which do not come from a regular branch copy.
            if commit.mark in rootmarks:
                name = branchbase (commit.branch)
                if name not in rootskip:
                    if commit.branch.startswith("refs/tags/"):
                        return name
                    return name + "-root"
            # Fallback on standard rules.
            return None
        func (sp *StreamParser)  taglegend(commit):
            # Tipdelete commits and branch roots don't get any legend.
            if commit.operations() or (commit.mark in rootmarks \
                    && branchbase(commit.branch) not in rootskip):
                return ""
            # Otherwise, generate one for inspection.
            legend = ["[[Tag from zero-fileop commit at Subversion r%s" \
                             % commit.legacyID]
            # This guard can fail on a split commit
            if commit.legacyID in sp.revisions:
                if sp.revisions[commit.legacyID].nodes:
                    legend.append(":\n")
                    legend.extend(str(node)+"\n"
                            for node in sp.revisions[commit.legacyID].nodes)
            legend.append("]]\n")
            return "".join(legend)
        #Pre compile the regex mappings for the next step
        func (sp *StreamParser)  compile_regex (mapping):
            regex, replace = mapping
            return regexp.MustCompile(regex.encode('ascii')), polybytes(replace)
        compiled_mapping = list(map(compile_regex, globalOption("svn_branchify_mapping")))
        # Now pretty up the branch names
        deletia = []
        for (index, commit) in enumerate(sp.repo.events):
            if not isinstance(commit, Commit):
                continue
            matched = false
            for regex, replace in compiled_mapping:
                result, substitutions = regex.subn(replace,polybytes(commit.branch))
                if substitutions == 1:
                    matched = true
                    commit.setBranch(os.path.join("refs",polystr(result)))
                    break
            if matched:
                continue
            if commit.branch == "root":
                commit.setBranch(os.path.join("refs", "heads", "root"))
            else if commit.branch.startswith("tags" + svnSep):
                branch = commit.branch
                if branch.endswith(svnSep):
                    branch = branch[:-1]
                commit.setBranch(os.path.join("refs", "tags",
                                              os.path.basename(branch)))
            else if commit.branch == "trunk" + svnSep:
                commit.setBranch(os.path.join("refs", "heads", "master"))
            else:
                basename = os.path.basename(commit.branch[:-1])
                commit.setBranch(os.path.join("refs", "heads", basename))
                # Some of these should turn into resets.  Is this a branchroot
                # commit with no fileops?
                if '--preserve' not in options && len(commit.parents()) == 1:
                    parent = commit.parents()[0]
                    if parent.branch != commit.branch && not commit.operations():
                        announce(debugEXTRACT, "branch root of %s with comment %s discarded"
                                 % (commit.branch, repr(commit.comment)))
                        # FIXME: Adding a reset for the new branch at the end
                        # of the event sequence was erroneous - caused later
                        # commits to be ignored. Possibly we should add a reset
                        # where the branch commit was?
                        #sp.repo.addEvent(Reset(sp.repo, ref=commit.branch,
                        #                          target=parent))
                        deletia.append(index)
            baton.twirl("")
        sp.repo.delete(deletia)
        timeit("polishing")
        announce(debugEXTRACT, "after branch name mapping")
        sp.repo.tagify_empty(tipdeletes = true,
                               canonicalize = false,
                               name_func = tagname,
                               legend_func = taglegend,
                               gripe = sp.gripe)
        sp.timeMark("tagifying")
        baton.twirl("")
        announce(debugEXTRACT, "after tagification")
        # cvs2svn likes to crap out sequences of deletes followed by
        # filecopies on the same node when it's generating tag commits.
        # These are lots of examples of this in the nut.svn test load.
        # These show up as redundant (D, M) fileop pairs.
        for commit in sp.repo.commits():
            if any(fileop is None for fileop in commit.operations()):
                raise Fatal("Null fileop at r%s" % commit.legacyID)
            for i in range(len(commit.operations())-1):
                if commit.operations()[i].op == opD && commit.operations()[i+1].op == opM:
                    if commit.operations()[i].path == commit.operations()[i+1].path:
                        commit.operations()[i].op = None
            commit.setOperations([fileop for fileop in commit.operations() if fileop.op is not None])
            baton.twirl("")
        timeit("tagcleaning")
        announce(debugEXTRACT, "after delete/copy canonicalization")
        # Remove spurious parent links caused by random cvs2svn file copies.
        #baton.twirl("debubbling")
        for commit in sp.repo.commits():
            try:
                a, b = commit.parents()
            except ValueError:
                pass
            else:
                if a is b:
                    sp.gripe("r%s: duplicate parent marks" % commit.legacyID)
                else if a.branch == b.branch == commit.branch:
                    if b.committer.date < a.committer.date:
                        (a, b) = (b, a)
                    if b.descendedFrom(a):
                        commit.removeParent(a)
            # Per-commit spinner disabled because this pass is fast
            #baton.twirl("")
        timeit("debubbling")
        sp.repo.renumber(baton=baton)
        timeit("renumbering")
        # Look for tag and branch merges that mean we may want to undo a
        # tag or branch creation
        ignore_deleteall = set(commit.mark
                               for commit in sp.generatedDeletes)
        for commit in sp.repo.commits():
            if commit.operations() && commit.operations()[0].op == 'deleteall' \
                    && commit.hasChildren() \
                    && commit.mark not in ignore_deleteall:
                sp.gripe("mid-branch deleteall on %s at <%s>." % \
                        (commit.branch, commit.legacyID))
        timeit("linting")
        # Treat this in-core state as though it was read from an SVN repo
        sp.repo.hint("svn", strong=true)

class SubversionDumper:
    "Repository to Subversion stream dump."
    func __init__(self, repo, nobranch=false):
        self.repo = repo
        self.nobranch = nobranch
        self.pathmap = {}
        self.mark_to_revision = {}
        self.branches_created = []
    class FlowState:
        func __init__(self, rev, props=None):
            self.rev = rev
            self.props = props or {}
            self.is_directory = false
            self.subfiles = 0
    dfltignores = next(vcs.dfltignores for vcs in vcstypes if vcs.name == "svn").replace("\n/", "\n")
    @staticmethod
    func svnprops(pdict):
        return "".join("K %d\n%s\nV %d\n%s\n" % (len(key), key, len(val), val)
                        for key, val in sorted(pdict.items()) if val)
    @staticmethod
    func dump_revprops(fp, revision, date, author=None, log=None, parents=None):
        "Emit a Revision-number record describing unversioned properties."
        fp.write("Revision-number: %d\n" % revision)
        parts = []
        parts.append(SubversionDumper.svnprops({"svn:log": log}))
        parts.append(SubversionDumper.svnprops({"svn:author": author}))
        # Ugh.  Subversion apparently insists on those decimal places
        parts.append(SubversionDumper.svnprops({"svn:date": date.rfc3339()[:-1]+".000000Z"}))
        # Hack merge links into mergeinfo properties.  This is a kluge
        # - the Subversion model is really like cherrypicking rather
        # than branch merging - but it's better than nothing, and
        # should at least round-trip with the logic in the Subversion
        # dump parser.
        if len(parents or []) > 1:
            parents = iter(parents)
            next(parents) # ignore main parent
            ancestral = ".".join(itertools.imap(str, sorted(parents)))
            parts.append(SubversionDumper.svnprops({"svn:mergeinfo": ancestral}))
        parts.append("PROPS-END\n")
        parts.append("\n")
        revprops = "".join(parts)
        fp.write("Prop-content-length: %d\n" % (len(revprops)-1))
        fp.write("Content-length: %d\n\n" % (len(revprops)-1))
        fp.write(revprops)
    @staticmethod
    func dump_node(fp, path, kind, action, content="",
                  fromRev=None, fromPath=None,
                  props=None):
        "Emit a Node record describing versioned properties and content."
        fp.write("Node-path: %s\n" % path)
        fp.write("Node-kind: %s\n" % kind)
        fp.write("Node-action: %s\n" % action)
        if fromRev:
            fp.write("Node-copyfrom-rev: %s\n" % fromRev)
        if fromPath:
            fp.write("Node-copyfrom-path: %s\n" % fromPath)
        nodeprops = SubversionDumper.svnprops(props or {}) + "PROPS-END\n"
        fp.write("Prop-content-length: %d\n" % len(nodeprops))
        if content:
            fp.write("Text-content-length: %d\n" % len(content))
            # Checksum validation in svnload works if we do sha1 but
            # not if we try md5.  It's unknown why - possibly svn load
            # is simply ignoring sha1.
            #fp.write("Text-content-md5: %s\n" % hashlib.md5(polybytes(content)).hexdigest())
            fp.write("Text-content-sha1: %s\n" % hashlib.sha1(polybytes(content)).hexdigest())
        fp.write("Content-length: %d\n\n" % (len(nodeprops) + len(content)))
        fp.write(nodeprops)
        if content:
            fp.write(content)
        fp.write("\n\n")
    @staticmethod
    func commitbranch(commit):
        "The branch that a commit belongs to prefering master and branches rather than tags"
        #FIXME: This logic should be improved to match the logic in branchColor more closely
        if commit.branch.startswith("refs/heads/") or not commit.hasChildren():
            return commit.branch
        candidatebranch = None
        for child in commit.children():
            childbranch = SubversionDumper.commitbranch(child)
            if childbranch == "refs/heads/master":
                return "refs/heads/master"
            else if childbranch.startswith("refs/heads/") && not candidatebranch:
                candidatebranch = childbranch
        if candidatebranch and not commit.branch.startswith("refs/heads/"):
            return candidatebranch
        else:
            return commit.branch
    @staticmethod
    func svnbranch(branch):
        "The branch directory corresponding to a specified git branch."
        segments = branch.split(svnSep)
        if segments[0] == "HEAD":
            return "trunk"
        assert segments[0] == "refs"
        if tuple(segments) == ("refs", "heads", "master"):
            return "trunk"
        if segments[1] not in ("tags", "heads") or len(segments) != 3:
            raise Recoverable("%s can't be mapped to Subversion." % branch)
        svnbase = segments[2]
        if svnbase.endswith("trunk"):
            svnbase += "-git"
        if segments[1] == "tags":
            return os.path.join("tags", svnbase)
        else:
            return os.path.join("branches", svnbase)
    func svnize(self, branch, path=""):
        "Return SVN path corresponding to a specified gitspace branch and path."
        if self.nobranch:
            return path
        return os.path.join(SubversionDumper.svnbranch(branch), path)
    func filedelete(self, fp, revision, branch, path, parents):
        "Emit the dump-stream records required to delete a file."
        announce(debugSVNDUMP, "filedelete%s" % repr((branch, path)))
        # Branch and directory creation may be required.
        # This has to be called early so copy can update the filemap.
        self.directory_create(fp, revision, branch, path, parents)
        svnpath = self.svnize(branch, path)
        fp.write("Node-path: %s\n" % svnpath)
        fp.write("Node-action: delete\n\n\n")
        del self.pathmap[revision][svnpath]
        while true:
            svnpath = os.path.dirname(svnpath)
            # The second disjunct in this guard is a
            # spasmodic twitch in the direction of
            # respecting Subversion's notion of a "flow".
            # We refrain from deleting branch directories
            # so they'll have just one flow throughout the
            # life of the repository.
            if not svnpath or svnpath in self.branches_created:
                break
            self.pathmap[revision][svnpath].subfiles -= 1
            if self.pathmap[revision][svnpath].subfiles == 0:
                fp.write("Node-path: %s\n" % svnpath)
                fp.write("Node-action: delete\n\n\n")
                del self.pathmap[revision][svnpath]
            else:
                break # Don't consider parents of directories we keep
    func filedeleteall(self, fp, revision, branch):
        # Create branch if required, no need to copy from a parent!
        self.directory_create(fp, revision, branch, path="", parents=None)
        branchdir = self.svnbranch(branch)
        # Here again the object is mutated, so a copy list must be used.
        for path in self.pathmap[revision].keys():
            if path.startswith(branchdir + svnSep):
                del self.pathmap[revision][path]
        self.branches_created.remove(branchdir)
        fp.write("Node-path: %s\n" % branchdir)
        fp.write("Node-action: delete\n\n\n")
    func directory_create(self, fp, revision, branch, path, parents=None):
        announce(debugSVNDUMP, "directory_create%s" % repr((revision, branch, path)))
        creations = []
        # Branch creation may be required
        svnout = SubversionDumper.svnbranch(branch)
        if svnout not in self.branches_created:
            if svnout.startswith("branches") && "branches" not in self.branches_created:
                self.branches_created.append("branches")
                creations.append(("branches", None, None))
            else if svnout.startswith("tags") && "tags" not in self.branches_created:
                self.branches_created.append("tags")
                creations.append(("tags", None, None))
            self.branches_created.append(svnout)
            if parents and parents[0].mark in self.mark_to_revision && branch != parents[0].color: # Handle empty initial commit(s)
                fromRev = self.mark_to_revision[parents[0].mark]
                from_branch = SubversionDumper.svnbranch(parents[0].color)
                creations.append((svnout, fromRev, from_branch))
                # Careful about the following - the path map gets mutated in
                # this loop, you need to get a list of the keys up front or
                # Python will barf.  Thing is, in Python 3 keys() returns an
                # iterator...
                for key in list(self.pathmap[fromRev].keys()):
                    if key.startswith(from_branch + svnSep) && key != from_branch:
                        counterpart = svnout + key[len(from_branch):]
                        self.pathmap[revision][counterpart] = SubversionDumper.FlowState(revision)
                        self.pathmap[revision][counterpart].subfiles = self.pathmap[fromRev][key].subfiles
                        self.pathmap[revision][counterpart].is_directory = self.pathmap[fromRev][key].is_directory
            else:
                creations.append((svnout, None, None))
        # Create all directory segments required
        # to get down to the level where we can
        # create the file.
        parts = os.path.dirname(path).split(svnSep)
        if parts[0]:
            parents = [svnSep.join(parts[:i+1])
                                   for i in range(len(parts))]
            for parentdir in parents:
                fullpath = os.path.join(svnout, parentdir)
                if fullpath not in self.pathmap[revision]:
                    creations.append((fullpath, None, None))
        for (dpath, fromRev, fromPath) in creations:
            SubversionDumper.dump_node(fp,
                                       path=dpath,
                                       kind="dir",
                                       action="add",
                                       fromRev=fromRev,
                                       fromPath=fromPath)
            self.pathmap[revision][dpath] = SubversionDumper.FlowState(revision)
            self.pathmap[revision][dpath].is_directory = true
            parentdir = os.path.dirname(dpath)
            if parentdir in self.pathmap[revision]:
                self.pathmap[revision][parentdir].subfiles += 1
    func filemodify(self, fp, revision, branch, mode, ref, path, inline, parents):
        "Emit the dump-stream records required to add or modify a file."
        announce(debugSVNDUMP, "filemodify%s" % repr((revision, branch, mode, ref, path,
                                            [event.mark for event in parents])))
        # Branch and directory creation may be required.
        # This has to be called early so copy can update the filemap.
        self.directory_create(fp, revision, branch, path, parents)
        svnpath = self.svnize(branch, path)
        if svnpath in self.pathmap[revision]:
            svnop = "change"
            self.pathmap[revision][svnpath].rev = revision
        else:
            svnop = "add"
            self.pathmap[revision][os.path.dirname(svnpath)].subfiles += 1
            self.pathmap[revision][svnpath] = SubversionDumper.FlowState(revision)
        announce(debugSVNDUMP, "Generating %s %s" % (svnpath, svnop))
        if ref == "inline":
            content = inline
        else:
            content = self.repo.markToEvent(ref).getContent()
        changeprops = None
        if svnpath in self.pathmap[revision]:
            if mode == '100755':
                if "svn:executable" not in self.pathmap[revision][svnpath].props:
                    self.pathmap[revision][svnpath].props["svn:executable"] = "true"
                    changeprops = self.pathmap[revision][svnpath].props
            else if mode == '100644':
                if "svn:executable" in self.pathmap[revision][svnpath].props:
                    self.pathmap[revision][svnpath].props["svn:executable"] = "false"
                    changeprops = self.pathmap[revision][svnpath].props
        #if mode == "120000":
        #    changeprops = {"svn:special":"*"}
        #    content = "link " + content
        # The actual content
        SubversionDumper.dump_node(fp,
                  path=svnpath,
                  kind="file",
                  action=svnop,
                  props=changeprops,
                  content=content)
    func filecopy(self, fp, revision, branch, source, target, parents):
        announce(debugSVNDUMP, "filecopy%s" % repr((revision, branch, source, target)))
        # Branch and directory creation may be required.
        # This has to be called early so copy can update the filemap.
        self.directory_create(fp, revision, branch, target, parents)
        svnsource = self.svnize(branch, source)
        try:
            flow = self.pathmap[revision][svnsource]
        except:
            raise Fatal("couldn't retrieve flow information for %s" % source)
        svntarget = self.svnize(branch, target)
        self.pathmap[revision][os.path.dirname(svntarget)].subfiles += 1
        self.pathmap[revision][svntarget] = self.pathmap[revision][svnsource]
        SubversionDumper.dump_node(fp,
                                   path=svntarget,
                                   kind="file",
                                   action="add",
                                   fromPath=svnsource,
                                   fromRev=flow.rev)
    func make_tag(self, fp, revision, name, log, author, parents):
        announce(debugSVNDUMP, "make_tag%s" % repr((revision, name, log, str(author))))
        tagrefpath = os.path.join("refs/tags", name)
        SubversionDumper.dump_revprops(fp, revision,
                                       log=log,
                                       author=author.email.split("@")[0],
                                       date=author.date)
        self.directory_create(fp, revision, tagrefpath, "", parents)
    func dump(self, selection, fp, progress=false):
        "Export the repository as a Subversion dumpfile."
        tags = [event for event in self.repo.events if isinstance(event, Tag)]
        # Fast-export prefers tags to branches as commit parents but SVN prefers branches
        for i in selection:
            event = self.repo.events[i]
            if isinstance(event, Commit):
                event.color = SubversionDumper.commitbranch(event)
        with Baton("reposurgeon: dumping", enable=progress) as baton:
            try:
                fp.write("SVN-fs-dump-format-version: 2\n\n")
                fp.write("UUID: %s\n\n" % (self.repo.uuid or uuid.uuid4()))
                SubversionDumper.dump_revprops(fp,
                                               revision=0,
                                               date=Date(rfc3339(time.time())))
                baton.twirl("")
                revision = 0
                self.pathmap[revision] = {}
                for i in selection:
                    event = self.repo.events[i]
                    # Passthroughs are lost; there are no equivalents
                    # in Subversion's ontology.
                    if not isinstance(event, Commit):
                        continue
                    if event.branch.startswith("refs/notes"):
                        complain("skipping note as unsupported")
                        continue
                    if event.branch == "refs/stash":
                        complain("skipping stash as unsupported")
                        continue
                    if event.color.startswith("refs/remotes"):
                        complain("skipping remote as unsupported %s" % event.color)
                        continue
                    revision += 1
                    parents = event.parents()
                    # Need a deep copy iff the parent commit is a branching point
                    if len(parents) == 1 && len(parents[0].children()) == 1 && parents[0].color == event.color:
                        self.pathmap[revision] = self.pathmap[revision-1]
                    else:
                        self.pathmap[revision] = copy.deepcopy(self.pathmap[revision-1])
                    self.mark_to_revision[event.mark] = revision
                    # We must treat the gitspace committer attribute
                    # as the author: gitspace author information is
                    # lost.  So is everything but the local part of
                    # the committer name.
                    backlinks = [self.mark_to_revision[mark]
                                 for mark in event.parentMarks() if mark in self.mark_to_revision]
                    SubversionDumper.dump_revprops(fp, revision,
                                                   log=event.comment.replace("\r\n", "\n"),
                                                   author=event.committer.email.split("@")[0],
                                                   date=event.committer.date,
                                                   parents=backlinks)
                    for fileop in event.operations():
                        if fileop.op == opD:
                            if fileop.path.endswith(".gitignore"):
                                self.directory_create(fp, revision,
                                                      branch=event.color,
                                                      path=fileop.path,
                                                      parents=parents)
                                svnpath = self.svnize(event.color, os.path.dirname(fileop.path))
                                self.pathmap[revision][svnpath].props["svn:ignore"] = ""
                                SubversionDumper.dump_node(fp,
                                          path=os.path.dirname(svnpath),
                                          kind="dir",
                                          action="change",
                                          props = self.pathmap[revision][svnpath].props)
                            else:
                                self.filedelete(fp, revision, event.color, fileop.path, parents)
                        else if fileop.op == opM:
                            if fileop.path.endswith(".gitignore"):
                                svnpath = self.svnize(event.color,
                                                      os.path.dirname(fileop.path))
=                                self.directory_create(fp, revision,
                                                      branch=event.color,
                                                      path=fileop.path,
                                                      parents=parents)
                                if fileop.ref == "inline":
                                    content = fileop.inline
                                else:
                                    content = self.repo.markToEvent(fileop.ref).getContent()
                                content = content.replace(SubversionDumper.dfltignores,"") # Strip out default SVN ignores
                                if svnpath not in self.pathmap[revision]:
                                    self.pathmap[revision][svnpath] = SubversionDumper.FlowState(revision)
                                if len(content) > 0 or "svn:ignore" in self.pathmap[revision][svnpath].props:
                                    self.pathmap[revision][svnpath].props["svn:ignore"] = content
                                    SubversionDumper.dump_node(fp,
                                              path=os.path.dirname(svnpath),
                                              kind="dir",
                                              action="change",
                                              props = self.pathmap[revision][svnpath].props)
                            else if fileop.mode == "160000":
                                complain("skipping submodule link reference %s" % fileop.ref)
                            else:
                                self.filemodify(fp,
                                                revision,
                                                event.color,
                                                fileop.mode,
                                                fileop.ref,
                                                fileop.path,
                                                fileop.inline,
                                                parents)
                        else if fileop.op == opR:
                            self.filecopy(fp,
                                          revision,
                                          event.color,
                                          fileop.source,
                                          fileop.target,
                                          parents)
                            self.filedelete(fp, revision, event.branch, fileop.source, event.parents())
                        else if fileop.op == opC:
                            self.filecopy(fp,
                                          revision,
                                          event.color,
                                          fileop.source,
                                          fileop.target,
                                          parents)
                        else if fileop.op == FileOp.deleteall:
                            self.filedeleteall(fp,
                                               revision,
                                               event.color)
                        else:
                            raise Fatal("unsupported fileop type %s." \
                                        % fileop.op)
                    # Turn any annotated tag pointing at this commit into
                    # a directory copy.
                    for tag in tags:
                        if tag.target is event:
                            if event.operations():
                                revision += 1
                                self.pathmap[revision] = self.pathmap[revision-1]
                                tagparents = [event]
                            else:
                                tagparents = parents
                            self.make_tag(fp,
                                          revision,
                                          name=tag.name,
                                          log=tag.comment.replace("\r\n", "\n"),
                                          author=tag.tagger,
                                          parents=tagparents)
                            break

                    # Preserve lightweight tags, too.  Ugh, O(n**2).
                    if event.branch.startswith("refs/tags"):
                        svntarget = os.path.join("tags", branchbase(event.branch))
                        createtag = svntarget not in self.branches_created
                        if createtag && event.hasChildren():
                            for child in event.children():
                                if child.branch == event.branch:
                                    createtag = false
                                    break
                        if createtag:
                            if event.operations():
                                revision += 1
                                self.pathmap[revision] = self.pathmap[revision-1]
                                tagparents = [event]
                            else:
                                tagparents = parents
                            self.make_tag(fp,
                                          revision,
                                          name=branchbase(event.branch),
                                          log="",
                                          author=event.committer,
                                          parents=tagparents)
                    fp.Flush()
            except IOError as e:
                raise Fatal("export error: %s" % e)

*/

// end
