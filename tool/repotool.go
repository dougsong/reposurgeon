// repotool queries and manipulate multiple repository types in a uniform way.
package main

// Copyright by Eric S. Raymond
// SPDX-License-Identifier: BSD-2-Clause

import (
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"text/template"
	"time"

	readline "github.com/chzyer/readline"
)

// TMPDIR is the temporary directory under which to perform checkouts
var TMPDIR string

// FIXME: Partial copy of the set type from reposurgeon. Should be factored

type stringSet struct {
	store map[string]bool
}

func newStringSet(elements ...string) stringSet {
	var ns stringSet
	ns.store = make(map[string]bool, 0)
	for _, el := range elements {
		ns.store[el] = true
	}
	return ns
}

// Iterare bares the underlying map so we can iterate over its keys
func (s stringSet) Iterate() map[string]bool {
	return s.store
}

func (s stringSet) Contains(item string) bool {
	return s.store[item]
}

func (s *stringSet) Remove(item string) {
	delete(s.store, item)
}

func (s *stringSet) Add(item string) {
	s.store[item] = true
}

func (s stringSet) Subtract(other stringSet) stringSet {
	diff := newStringSet()
	for item := range s.store {
		if !other.store[item] {
			diff.store[item] = true
		}
	}
	return diff
}

func (s stringSet) Intersection(other stringSet) stringSet {
	intersection := newStringSet()
	for item := range s.store {
		if other.store[item] {
			intersection.store[item] = true
		}
	}
	return intersection
}

func (s stringSet) Union(other stringSet) stringSet {
	// Naive O(n**2) method - don't use on large sets if you care about speed
	union := newStringSet()
	for item := range s.store {
		union.store[item] = true
	}
	for item := range other.store {
		union.store[item] = true
	}
	return union
}

func (s stringSet) Equal(other stringSet) bool {
	if len(s.store) != len(other.store) {
		return false
	}
	for item := range s.store {
		if !other.store[item] {
			return false
		}
	}
	for item := range other.store {
		if !s.store[item] {
			return false
		}
	}
	return true
}

func (s stringSet) Listify() []string {
	ordered := make([]string, len(s.store))
	i := 0
	for el := range s.store {
		ordered[i] = el
		i++
	}
	sort.Strings(ordered)
	return ordered
}

func (s stringSet) Empty() bool {
	return len(s.store) == 0
}

func (s stringSet) Len() int {
	return len(s.store)
}

type squishyParts struct{
	Project string
	SourceVCS string
	TargetVCS string
}

var makefileTemplate = `# Makefile for {{.Project}} conversion using reposurgeon
#
# Steps to using this:
# 1. Make sure reposurgeon and repotool are on your $PATH.
# 2. (Skip this step if you're starting from a stream file.) For svn, set
#    REMOTE_URL to point at the remote repository you want to convert.
#    If the repository is already in a DVCS such as hg or git,
#    set REMOTE_URL to either the normal cloning URL (starting with hg://,
#    git://, etc.) or to the path of a local clone.
# 3. For cvs, set CVS_HOST to the repo hostname and CVS_MODULE to the module,
#    then uncomment the line that builds REMOTE_URL 
#    Note: for CVS hosts other than Sourceforge or Savannah you will need to 
#    include the path to the CVS modules directory after the hostname.
# 4. Set any required read options, such as --user-ignores or --nobranch,
#    by setting READ_OPTIONS.
# 5. Optionally, replace the default value of DUMPFILTER with a
#    command or pipeline that actually filters the dump rather than
#    just copying it through.  The most usual reason to do this is
#    that your Subversion repository is multiproject and you want to
#    strip out one subtree for conversion with repocutter sift and pop
#    commands.  Note that if you ever did copies across project
#    subtrees this simple stripout will not work - you are in deep
#    trouble and should find an expert to advise you
# 6. Run 'make stubmap' to create a stub author map.
# 7. Run 'make' to build a converted repository.
#
# The reason both first- and second-stage stream files are generated is that,
# especially with Subversion, making the first-stage stream file is often
# painfully slow. By splitting the process, we lower the overhead of
# experiments with the lift script.
#
# For a production-quality conversion you will need to edit the map
# file and the lift script.  During the process you can set EXTRAS to
# name extra metadata such as a comments message-box.
#
# Afterwards, you can use the headcompare and tagscompare productions
# to check your work.
#

EXTRAS = 
REMOTE_URL = svn://svn.debian.org/{{.Project}}
#REMOTE_URL = https://{{.Project}}.googlecode.com/svn/
CVS_HOST = {{.Project}}.cvs.sourceforge.net
#CVS_HOST = cvs.savannah.gnu.org
CVS_MODULE = {{.Project}}
#REMOTE_URL = cvs://$(CVS_HOST)/{{.Project}}\#$(CVS_MODULE)
READ_OPTIONS =
DUMPFILTER = cat
VERBOSITY = "set progress"
REPOSURGEON = reposurgeon
LOGFILE = conversion.log

# Configuration ends here

.PHONY: local-clobber remote-clobber gitk gc compare clean dist stubmap
# Tell make not to auto-remove tag directories, because it only tries rm 
# and hence fails
.PRECIOUS: {{.Project}}-%-checkout {{.Project}}-%-{{.TargetVCS}}

default: {{.Project}}-{{.TargetVCS}}

# Build the converted repo from the second-stage fast-import stream
{{.Project}}-{{.TargetVCS}}: {{.Project}}.fi
	rm -fr {{.Project}}-{{.TargetVCS}}; $(REPOSURGEON) $(VERBOSITY) 'read <{{.Project}}.fi' 'prefer {{.TargetVCS}}' 'rebuild {{.Project}}-{{.TargetVCS}}'

# Build the second-stage fast-import stream from the first-stage stream dump
{{.Project}}.fi: {{.Project}}.{{.SourceVCS}} {{.Project}}.opts {{.Project}}.lift {{.Project}}.map $(EXTRAS)
	$(REPOSURGEON) $(VERBOSITY) 'logfile $(LOGFILE)' 'script {{.Project}}.opts' "read $(READ_OPTIONS) <{{.Project}}.{{.SourceVCS}}" 'authors read <{{.Project}}.map' 'sourcetype {{.SourceVCS}}' 'prefer git' 'script {{.Project}}.lift' 'legacy write >{{.Project}}.fo' 'write >{{.Project}}.fi'

# Build the first-stage stream dump from the local mirror
{{.Project}}.{{.SourceVCS}}: {{.Project}}-mirror
	(cd {{.Project}}-mirror/ >/dev/null; repotool export) | $(DUMPFILTER) >{{.Project}}.{{.SourceVCS}}

# Build a local mirror of the remote repository
{{.Project}}-mirror:
	repotool mirror $(REMOTE_URL) {{.Project}}-mirror

# Make a local checkout of the source mirror for inspection
{{.Project}}-checkout: {{.Project}}-mirror
	cd {{.Project}}-mirror >/dev/null; repotool checkout $(PWD)/{{.Project}}-checkout

# Make a local checkout of the source mirror for inspection at a specific tag
{{.Project}}-%-checkout: {{.Project}}-mirror
	cd {{.Project}}-mirror >/dev/null; repotool checkout $(PWD)/{{.Project}}-$*-checkout $*

# Force rebuild of first-stage stream from the local mirror on the next make
local-clobber: clean
	rm -fr {{.Project}}.fi {{.Project}}-{{.TargetVCS}} *~ .rs* {{.Project}}-conversion.tar.gz {{.Project}}-*-{{.TargetVCS}}

# Force full rebuild from the remote repo on the next make.
remote-clobber: local-clobber
	rm -fr {{.Project}}.{{.SourceVCS}} {{.Project}}-mirror {{.Project}}-checkout {{.Project}}-*-checkout

# Get the (empty) state of the author mapping from the first-stage stream
stubmap: {{.Project}}.{{.SourceVCS}}
	$(REPOSURGEON) $(VERBOSITY) "read $(READ_OPTIONS) <{{.Project}}.{{.SourceVCS}}" 'authors write >{{.Project}}.map'

# Compare the histories of the unconverted and converted repositories at head
# and all tags.
EXCLUDE = -x CVS -x .{{.SourceVCS}} -x .{{.TargetVCS}}
EXCLUDE += -x .{{.SourceVCS}}ignore -x .{{.TargetVCS}}ignore
headcompare: {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
	repotool compare $(EXCLUDE) {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
tagscompare: {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
	repotool compare-tags $(EXCLUDE) {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
branchescompare: {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
	repotool compare-branches $(EXCLUDE) {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
allcompare: {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
	repotool compare-all $(EXCLUDE) {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}

# General cleanup and utility
clean:
	rm -fr *~ .rs* {{.Project}}-conversion.tar.gz *.{{.SourceVCS}} *.fi *.fo

# Bundle up the conversion metadata for shipping
SOURCES = Makefile {{.Project}}.lift {{.Project}}.map $(EXTRAS)
{{.Project}}-conversion.tar.gz: $(SOURCES)
	tar --dereference --transform 's:^:{{.Project}}-conversion/:' -czvf {{.Project}}-conversion.tar.gz $(SOURCES)

dist: {{.Project}}-conversion.tar.gz
`

var gitTemplateAdditions = `
#
# The following productions are git-specific
#

# Browse the generated git repository
gitk: {{.Project}}-git
	cd {{.Project}}-git; gitk --all

# Run a garbage-collect on the generated git repository.  Import doesn't.
# This repack call is the active part of gc --aggressive.  This call is
# tuned for very large repositories.
gc: {{.Project}}-git
	cd {{.Project}}-git; time git -c pack.threads=1 repack -AdF --window=1250 --depth=250
`

var verbose = false
var quiet = true

func croak(msg string, args ...interface{}) {
	content := fmt.Sprintf(msg, args...)
	os.Stderr.WriteString("repotool: " + content + "\n")
	os.Exit(1)
}

func announce(msg string, args ...interface{}) {
	if !quiet {
		content := fmt.Sprintf(msg, args...)
		os.Stdout.WriteString("repotool: " + content + "\n")
	}
}

func complain(msg string, args ...interface{}) {
	if !quiet {
		content := fmt.Sprintf(msg, args...)
		os.Stderr.WriteString("repotool: " + content + "\n")
	}
}

// Either execute a command or die noisily
func runShellProcessOrDie(dcmd string, legend string) {
	if legend != "" {
		legend = " " + legend
	}
	if verbose {
		announce("executing '%s'%s", dcmd, legend)
	}
	cmd := exec.Command("sh", "-c", "(" + dcmd + ")")
	cmd.Stdin = os.Stdin
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	err := cmd.Run()
	if err != nil {
		croak("executing %q: %v", dcmd, err)
	}
}

// captureFromProcess runs a specified command, capturing the output.
func captureFromProcess(command string, legend string) string {
	if verbose {
		announce("%s: capturing %s%s", time.Now(), command, legend)
	}
	cmd := exec.Command("sh", "-c", command)
	content, err := cmd.CombinedOutput()
	if err != nil {
		croak("executing %q: %v", cmd, err)
	}
	if verbose {
		announce(string(content))
	}
	return string(content)
}


func exists(pathname string) bool {
	_, err := os.Stat(pathname)
	return !os.IsNotExist(err)
}

func isdir(pathname string) bool {
	st, err := os.Stat(pathname)
	return err == nil && st.Mode().IsDir()
}

func islink(pathname string) bool {
	st, err := os.Stat(pathname)
	return err == nil && (st.Mode()&os.ModeSymlink) != 0
}

func under(target string, hook func()) {
        if verbose {
		fmt.Printf("repotool: in %s...\n", target)
	}
	source, err := os.Getwd()
	if err != nil {
		log.Fatal(err)
	}
	if isdir(target) {
		os.Chdir(target)
	} else {
		os.Chdir(filepath.Dir(target))
	}
	hook()
	os.Chdir(source)
}

// What repository type in this directory?
func vcstype(d string) string {
	if isdir(filepath.Join(d, "CVSROOT")) {
		return "cvs"
	}
	files, err := ioutil.ReadDir(d)
	if err != nil {
		log.Fatal(err)
	}
	for _, p := range files {
		if strings.HasSuffix(p.Name(), ",v") {
			return "cvs"
		}
	}
        if isdir(filepath.Join(d, "CVS")) {
		return "cvs-checkout"
	}
        if isdir(filepath.Join(d, "locks")) {
		return "svn"
	}
        if isdir(filepath.Join(d, ".svn")) {
		return "svn-checkout"
	}
        if isdir(filepath.Join(d, ".git")) {
		return "git"
	}
        if isdir(filepath.Join(d, ".bzr")) {
		return "bzr"
	}
        if isdir(filepath.Join(d, ".hg")) {
		return "hg"
	}
        if isdir(filepath.Join(d, "_darcs")) {
		return "darcs"
	}
        if isdir(filepath.Join(d, ".bk")) {
		return "bk"
	}
	croak("%s does not look like a repository of known type.", d)
	return ""
}

func isDvcsOrCheckout() bool {
	// Is this a DVCS or checkout where we can compare files?
	t := vcstype(".")
	return t != "cvs" && t != "svn"
}

func vcsignores() [] string {
    // Return ignorable directories.
    return []string{".svn",
            "CVS", ".cvsignore",
            ".git", ".gitignore",
            ".hg", ".hgignore",
            ".bzr", ".bzrignore",
            ".bk", ".bkignore",
            "_darcs"}
}

func input(prompt string) string {
	rl, err := readline.New(prompt)
	if err != nil {
		log.Fatal(err)
	}
	defer rl.Close()
	line, _ := rl.Readline()
	return line
}

func makeStub (name string, contents string) {
	fp, err := os.OpenFile(name, os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		log.Fatal(err)
	}
	defer fp.Close()
	fp.WriteString(contents)
}

func initialize(args []string) {
	if verbose {
		fmt.Printf("initialize args: %v\n", args)
	}
	var squishy squishyParts
	if len(args) < 1 {
		croak("initialize requires a project name.")
	}
	project, args := args[0], args[1:]
	squishy.Project = project
	if len(args) == 0 {
		squishy.SourceVCS = input("repotool: what VCS do you want to convert from? ")
	} else {
		squishy.SourceVCS, args = args[0], args[1:]
	}
	if !newStringSet("cvs", "svn", "git", "bzr", "hg", "darcs", "bk").Contains(squishy.SourceVCS) {
		croak("unknown source VCS type %s", squishy.SourceVCS)
	}
	if len(args) == 0 {
		squishy.TargetVCS = input("repotool: what VCS do you want to convert to? ")
	} else {
		squishy.TargetVCS = args[0]
		args = args[1:]
	}
	if !newStringSet("git", "bzr", "hg", "darcs").Contains(squishy.TargetVCS) {
		croak("unknown target VCS type %s", squishy.TargetVCS)
	}
	if exists("Makefile") {
		complain("a Makefile already exists here.")
	} else {
		fmt.Printf("repotool: generating Makefile, some variables in it need to be set.\n")
		instructions := makefileTemplate
		if squishy.TargetVCS == "git" {
			instructions += gitTemplateAdditions
		}
		// Create a new template and parse the letter into it.
		t := template.Must(template.New("Makefile").Parse(instructions))
		fp, err := os.OpenFile("Makefile", os.O_CREATE|os.O_WRONLY, 0644)
		if err != nil {
			log.Fatal(err)
		}
		defer fp.Close()
		err2 := t.Execute(fp, squishy)
		if err2 != nil {
			log.Println("executing template:", err2)
		}
	}
	if exists(project + ".opts") {
		complain("a project options file already exists here.")
	} else {
		fmt.Printf("repotool: generating a stub options file.\n")
		makeStub(project + ".opts", "# Pre-read options for reposurgeon go here.\n")
	}
	if exists(project + ".lift") {
		complain("a project lift file already exists here.")
	} else {
		fmt.Printf("repotool: generating a stub lift file.\n")
		makeStub(project + ".lift", fmt.Sprintf("# Lift commands for %s\n", project))
	}
}

func export(args []string) {
	// Export from the current working directory to standard output.
	m := map[string]string{
		"cvs": `find . -name \*,v | cvs-fast-export -q --reposurgeon`,
		"svn": "svnadmin -q dump .",
		"git": "git fast-export --all --use-done-feature",
		"bzr": "bzr fast-export --no-plain .",
		"hg": "reposurgeon 'read .' 'prefer git' 'write -'",
		"darcs": "darcs fastconvert export",
		"bk": "bk fast-export -q",
	}
	vcs := vcstype(".")
	if e := m[vcs]; e == "" {
		croak("can't export from directory of type %s.", vcs)
	} else {
		runShellProcessOrDie(e, " export command")
	}
}

// Unimplemented stubs begin

func mirror(args []string) {
	if verbose {
		fmt.Printf("initialize args: %v\n", args)
	}
	operand := args[0]
	mirrordir := ""
	if len(args) >= 1 {
		mirrordir = args[1]
	}
	pwd, err := os.Getwd()
	if err != nil {
		log.Fatal(err)
	}
	var locald string
	tillHash := regexp.MustCompile("^.*#")
	isFullURL, badre := regexp.Match("svn://|svn\\+ssh://|https://|http://", []byte(operand))
	if (badre == nil && isFullURL) || (strings.HasPrefix(operand, "file://") && isdir(filepath.Join(operand[6:], "locks"))) {
		if mirrordir == "" {
			locald = filepath.Base(operand) + "-mirror"
		} else if strings.HasPrefix(mirrordir, "/") {
			locald = mirrordir
		} else {
			locald = pwd + "/" + mirrordir
		}
		runShellProcessOrDie("svnadmin create " + locald, "mirror creation")
		makeStub(locald + "/hooks/pre-revprop-change", "#!/bin/sh\nexit 0;\n")
		os.Remove(locald + "/hooks/post-revprop-change")
		// Note: The --allow-non-empty and --steal-lock options permit
		// this to operate on a Subversion repository you have pulled
		// in with rsync (which is very much faster than mirroring via
		// SVN protocol), but they disable some safety checking.  Be
		// very sure you have not made any local changes to the repo
		// since rsyncing, or havoc will ensue.
		runShellProcessOrDie(fmt.Sprintf("chmod a+x %s/hooks/pre-revprop-change", locald), "mirroring")
		runShellProcessOrDie(fmt.Sprintf("svnsync init --allow-non-empty file://%s %s", locald, operand), "mirroring")
		runShellProcessOrDie(fmt.Sprintf("svnsync synchronize --steal-lock file://%s", locald), "mirroring")
	} else if isdir(operand + "/locks") {
		runShellProcessOrDie(fmt.Sprintf("svnsync --steal-lock synchronize file://%s/%s", pwd, operand), "mirroring")
	} else if strings.HasPrefix(operand, "cvs://") {
		if mirrordir != "" {
			locald = mirrordir
		} else {
			locald = tillHash.ReplaceAllString(filepath.Base(operand), pwd)
		}
		os.MkdirAll(locald, 0755)	// Needs to be searchable all the way down.
		runShellProcessOrDie(fmt.Sprintf("cvssync -c -o %s %s", locald, operand), "mirroring")
		makeStub(locald + "/.cvssync", operand)
	} else if exists(operand + "/.cvssync") {
		contents, err := ioutil.ReadFile(operand + "/.cvssync")
		if err != nil {
			croak(operand + "/.cvssync is missing or unreadable")
		}
		runShellProcessOrDie("cvssync -c -o " + operand + " " + string(contents), "mirroring")
	} else if strings.HasPrefix(operand, "git://") || (strings.HasPrefix(operand, "file://") && isdir(filepath.Join(operand[6:], ".git"))) {
		if strings.HasPrefix(operand, "file://") {
			operand = operand[6:]
		}
		if mirrordir != ""{
			locald = mirrordir
		} else {
			locald = tillHash.ReplaceAllString(filepath.Base(operand), pwd)
		}
		runShellProcessOrDie(fmt.Sprintf("git clone -q %s %s", operand, locald), "mirroring")
	} else if isdir(operand + "/.git") {
		under(operand, func() {runShellProcessOrDie("git pull", "mirroring")})
		runShellProcessOrDie(fmt.Sprintf("git clone %s %s", operand, mirrordir), "mirroring")
	} else if strings.HasPrefix(operand, "hg://") || (strings.HasPrefix(operand, "file://") && isdir(filepath.Join(operand[6:], ".hg"))) {
		if strings.HasPrefix(operand, "file://") {
			operand = operand[6:]
		}
		if mirrordir != ""{
			locald = mirrordir
		} else {
			locald = tillHash.ReplaceAllString(filepath.Base(operand), pwd)
		}
		runShellProcessOrDie(fmt.Sprintf("hg clone %s %s", operand, locald), "mirroring")
	} else if isdir(operand + "/.hg") {
		under(operand, func() {runShellProcessOrDie("hg update", "mirroring")})
		runShellProcessOrDie(fmt.Sprintf("hg clone %s %s", operand, mirrordir), "mirroring")
	} else {
		croak(fmt.Sprintf("%s does not look like a repository mirror.", operand))
	}
}

func tags(args []string) {
	croak("tags is not yet supported")
}

func branches(args []string) {
	croak("initialize is not yet supported")
}

func checkout(args []string) {
	croak("initialize is not yet supported")
}

func compareRevision(args []string) {
	croak("compare is not yet supported")
}

func compareTags(args []string) {
	croak("compare-tags is not yet supported")
}

func compareBranches(args []string) {
	croak("initialize is not yet supported")
}

func compareAll(args []string) {
	croak("compare-all is not yet supported")
}

func main() {
	TMPDIR = os.Getenv("TMPDIR")
	if TMPDIR == "" {
		TMPDIR = "/tmp"
	}

	flag.BoolVar(&verbose, "v", false, "show subcommands and diagnostics")
	flag.BoolVar(&quiet, "q", false, "run as quietly as possible")
	flag.Parse()

	if flag.NArg() == 0 {
		fmt.Fprintf(os.Stderr,
			"repotool requires an operation argument.\n")
		os.Exit(1)
	}

	operation, args := flag.Args()[0], flag.Args()[1:]

	if operation == "initialize" {
		initialize(args)
	} else if operation == "export" {
		export(args)
	} else if operation == "mirror" {
		mirror(args)
	} else if operation == "tags" {
		tags(args)
	} else if operation == "branches" {
		branches(args)
	} else if operation == "checkout" {
		checkout(args)
	} else if operation == "compare" {
		compareRevision(args)
	} else if operation == "compare-tags" {
		compareTags(args)
	} else if operation == "compare-branches" {
		compareBranches(args)
	} else if operation == "compare-all" {
		compareAll(args)
	} else {
		print(`
repotool commands:

initialize  - create Makefile and stub files for standard conversion workflow.
export - export a stream dump of the source repository
mirror [URL] localdir - create or update a mirror of the source repository
branches - list repository branch names
checkout [-r rev] [-t tag] [-b branch] - check out a working copy of the repo
compare [-r rev] [-t tag] [-b branch] - compare head content of two repositories
compare-tags - compare source and target repo content at all tags
compare-branches - compare source and target repo content at all branches
compare-all - compare repositories at head, all tags, and all branches
`)
		os.Exit(1)
	}
}

// end
