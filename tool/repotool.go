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

// Define a couplee of partial capability tables for querying
// checkout directories.

var cvsCheckout = VCS{
	name:         "cvs-checkout",
	subdirectory: "CVS",
	taglister:    "",
	branchlister: "",
}

var svnCheckout = VCS{
	name:         "svn-checkout",
	subdirectory: ".svn",
	taglister:    "ls tags 2>/dev/null || exit 0",
	branchlister: "ls branches 2>/dev/null || exit 0",
}

func init() {
	setInit()
	vcsInit()
	vcstypes = append(vcstypes, cvsCheckout)
	vcstypes = append(vcstypes, svnCheckout)
	vcsignores = append(vcsignores, []string{"CVS", ".svn"}...)
}

type squishyParts struct {
	Project   string
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
headcompare: {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
	repotool compare {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
tagscompare: {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
	repotool compare-tags {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
branchescompare: {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
	repotool compare-branches {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
allcompare: {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}
	repotool compare-all {{.Project}}-mirror {{.Project}}-{{.TargetVCS}}

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

var acceptMissing = false
var nobranch = false
var seeignores = false
var quiet = false
var unified = true
var verbose = false

var branch string
var comparemode string
var refexclude string
var revision string
var basedir string
var tag string

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
	cmd := exec.Command("sh", "-c", "("+dcmd+")")
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
		err = os.Chdir(filepath.Dir(target))
		if err != nil {
			log.Fatal(err)
		}
	}
	hook()
	os.Chdir(source)
}

func isDvcsOrCheckout() bool {
	// Is this a DVCS or checkout where we can compare files?
	t := identifyRepo(".")
	return t != nil && t.name != "cvs" && t.name != "svn"
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

func makeStub(name string, contents string) {
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
		makeStub(project+".opts", "# Pre-read options for reposurgeon go here.\n")
	}
	if exists(project + ".lift") {
		complain("a project lift file already exists here.")
	} else {
		fmt.Printf("repotool: generating a stub lift file.\n")
		makeStub(project+".lift", fmt.Sprintf("# Lift commands for %s\n", project))
	}
}

func export() {
	pwd, err := os.Getwd()
	if err != nil {
		log.Fatal(err)
	}
	rt := identifyRepo(".")
	if rt == nil {
		croak("unknown repository type")
	}
	cmd := rt.exporter
	if rt.name == "hg" {
		// Grotty repotool-only special case that takes the long way around
		// through reposurgeon's extractor classes.  Remove if and when there
		// is a real exporter for hg
		cmd = "reposurgeon 'read .' 'prefer git' 'write -'"
	}
	if cmd == "" {
		croak("can't export from repository of type %s.", rt.name)
	} else {
		if rt.quieter != "" {
			cmd += " " + rt.quieter
		}
		runShellProcessOrDie(cmd, " export command in "+pwd)
	}
}

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
	if (badre == nil && isFullURL) || (strings.HasPrefix(operand, "file:///") && isdir(filepath.Join(operand[7:], "locks"))) {
		if mirrordir == "" {
			locald = filepath.Base(operand) + "-mirror"
		}
		if mirrordir[0] == os.PathSeparator {
			locald = mirrordir
		} else {
			locald = filepath.Join(pwd, mirrordir)
		}
		runShellProcessOrDie("svnadmin create "+locald, "mirror creation")
		makeStub(locald+"/hooks/pre-revprop-change", "#!/bin/sh\nexit 0;\n")
		os.Remove(locald + "/hooks/post-revprop-change")
		// Note: The --allow-non-empty and --steal-lock options permit
		// this to operate on a Subversion repository you have pulled
		// in with rsync (which is very much faster than mirroring via
		// SVN protocol), but they disable some safety checking.  Be
		// very sure you have not made any local changes to the repo
		// since rsyncing, or havoc will ensue.
		runShellProcessOrDie(fmt.Sprintf("chmod a+x %s/hooks/pre-revprop-change", locald), "mirroring")
		runShellProcessOrDie(fmt.Sprintf("svnsync init -q --allow-non-empty file://%s %s", locald, operand), "mirroring")
		runShellProcessOrDie(fmt.Sprintf("svnsync synchronize -q --steal-lock file://%s", locald), "mirroring")
	} else if isdir(filepath.Join(operand, "locks")) {
		if operand[0] == os.PathSeparator {
			locald = operand
		} else {
			locald = filepath.Join(pwd, operand)
		}
		runShellProcessOrDie(fmt.Sprintf("svnsync synchronize -q --steal-lock file://%s", locald), "mirroring")
	} else if strings.HasPrefix(operand, "cvs://") {
		if mirrordir != "" {
			locald = mirrordir
		} else {
			locald = tillHash.ReplaceAllString(filepath.Base(operand), pwd)
		}
		os.MkdirAll(locald, 0755) // Needs to be searchable all the way down.
		runShellProcessOrDie(fmt.Sprintf("cvssync -c -o %s %s", locald, operand), "mirroring")
		makeStub(locald+"/.cvssync", operand)
	} else if exists(operand + "/.cvssync") {
		contents, err := ioutil.ReadFile(operand + "/.cvssync")
		if err != nil {
			croak(operand + "/.cvssync is missing or unreadable")
		}
		runShellProcessOrDie("cvssync -c -o "+operand+" "+string(contents), "mirroring")
	} else if strings.HasPrefix(operand, "git://") || (strings.HasPrefix(operand, "file://") && isdir(filepath.Join(operand[6:], ".git"))) {
		if strings.HasPrefix(operand, "file://") {
			operand = operand[6:]
		}
		if mirrordir != "" {
			locald = mirrordir
		} else {
			locald = tillHash.ReplaceAllString(filepath.Base(operand), pwd)
		}
		runShellProcessOrDie(fmt.Sprintf("git clone -q %s %s", operand, locald), "mirroring")
	} else if isdir(operand + "/.git") {
		under(operand, func() { runShellProcessOrDie("git pull", "mirroring") })
		runShellProcessOrDie(fmt.Sprintf("git clone %s %s", operand, mirrordir), "mirroring")
	} else if strings.HasPrefix(operand, "hg://") || (strings.HasPrefix(operand, "file://") && isdir(filepath.Join(operand[6:], ".hg"))) {
		if strings.HasPrefix(operand, "file://") {
			operand = operand[6:]
		}
		if mirrordir != "" {
			locald = mirrordir
		} else {
			locald = tillHash.ReplaceAllString(filepath.Base(operand), pwd)
		}
		runShellProcessOrDie(fmt.Sprintf("hg clone -q %s %s", operand, locald), "mirroring")
	} else if isdir(operand + "/.hg") {
		under(operand, func() { runShellProcessOrDie("hg update", "mirroring") })
		runShellProcessOrDie(fmt.Sprintf("hg clone %s %s", operand, mirrordir), "mirroring")
	} else {
		croak("%s does not look like a repository mirror.", operand)
	}
}

func tags() string {
	pwd, err := os.Getwd()
	if err != nil {
		log.Fatal(err)
	}
	rt := identifyRepo(".")
	if rt == nil {
		croak("unknown repository type")
	}
	if rt.taglister == "" {
		croak("can't list tags from repository or directory of type %s.", rt.name)
	} else {
		cmd := strings.ReplaceAll(rt.taglister, "${pwd}", pwd)
		return captureFromProcess(cmd, " tag-list command in "+pwd)
	}
	return ""
}

func branches() string {
	pwd, err := os.Getwd()
	if err != nil {
		log.Fatal(err)
	}
	rt := identifyRepo(".")
	if rt == nil {
		croak("unknown repository type")
	}
	if rt.branchlister == "" {
		croak("can't list branches from repository or directory of type %s.", rt.name)
	} else {
		cmd := strings.ReplaceAll(rt.branchlister, "${pwd}", pwd)
		return captureFromProcess(cmd, " branch-list command in "+pwd)
	}
	return ""
}

func checkout(outdir string, rev string) string {
	if verbose {
		fmt.Printf("checkout: %s\n", outdir)
	}
	if nobranch {
		branch = "" // nobranch will also prevent the automatic switch to "trunk"
	}
	if outdir[0] != os.PathSeparator {
		croak("checkout requires absolute target path")
	}
	if basedir != "" {
		os.Chdir(basedir)
	}
	var err error
	if exists(outdir) {
		outdir, err = filepath.EvalSymlinks(outdir)
		if err != nil {
			log.Fatal(fmt.Sprintf("chasing symlink: %v", err))
		}
	}
	pwd, err2 := os.Getwd()
	if err != nil {
		log.Fatal(err2)
	}
	vcs := identifyRepo(".")
	if vcs.name == "cvs" {
		module := captureFromProcess("ls -1 | grep -v CVSROOT", " listing modules")
		if rev != "" {
			rev = "-r " + rev
		}
		// By choosing -kb we get binary files right, but won't
		// suppress any expanded keywords that might be lurking
		// in masters.
		runShellProcessOrDie(fmt.Sprintf("cvs -Q -d:local:%s co -P %s %s %s -d %s -kb %s", pwd, branch, tag, rev, outdir, module), "checkout")
		return outdir
	} else if vcs.name == "cvs-checkout" {
		runShellProcessOrDie(fmt.Sprintf("cvs -Q -d:local:%s co -P %s %s %s -kb", pwd, branch, tag, rev), "checkout")
		return outdir
	} else if vcs.name == "svn" {
		if rev != "" {
			rev = "-r " + rev
		}
		runShellProcessOrDie(fmt.Sprintf("svn co -q %s file://%s %s", rev, pwd, outdir), "checkout")
		if nobranch {
			// flat repository
		} else if tag != "" {
			outdir = filepath.Join(outdir, "tags", tag)
		} else if branch == "" || branch == "master" || branch == "trunk" {
			outdir = filepath.Join(outdir, "trunk")
		} else if branch != "" {
			outdir = filepath.Join(outdir, "branches", branch)
		}
		return outdir
	} else if vcs.name == "svn-checkout" {
		if rev != "" {
			rev = "-r " + rev
			// Potentially dangerous assumption: User made a full checkout
			// of HEAD and the update operation (which is hideously slow on
			// large repositories) only needs to be done if an explicit rev
			// was supplied.
			runShellProcessOrDie("svn up -q "+rev, "checkout")
		}
		relpath := ""
		if nobranch {
			// flat repository
		} else if tag != "" && (acceptMissing || isdir("tags")) {
			relpath = filepath.Join("tags", tag)
		} else if (branch == "" || branch == "master" || branch == "trunk") && isdir("trunk") {
			relpath = "trunk"
		} else if branch != "" && isdir(filepath.Join("branches", branch)) {
			relpath = filepath.Join("branches", branch)
		} else if branch != "" && isdir(branch) {
			complain("branch '%s' found at the root which is non-standard", branch)
			relpath = branch
		} else if (branch == "master" || branch == "trunk") && acceptMissing {
			relpath = "trunk"
		} else if branch != "" && acceptMissing {
			relpath = filepath.Join("branches", branch)
		} else {
			croak("invalid branch or tag")
		}
		if exists(outdir) {
			if islink(outdir) {
				os.Remove(outdir)
			} else {
				croak("can't checkout SVN repo to existing %s", outdir)
			}
		}
		part := filepath.Join(pwd, relpath)
		err := os.Symlink(part, outdir)
		if err != nil {
			log.Fatal(err)
		}
		if verbose {
			fmt.Printf("Subversion inward link %s -> %s\n", outdir, part)
		}
		return outdir
	} else if vcs.name == "git" {
		// Only one rev should be given to git checkout
		// Use the passed-in arguments, in some order of specificity.
		handleMissing := false
		if rev == "" {
			if tag != "" {
				rev = tag
			} else if branch != "" {
				rev = branch
			} else {
				rev = "master"
			}
			handleMissing = acceptMissing &&
				(captureFromProcess(fmt.Sprintf("git rev-parse --verify -q %s >/dev/null || echo no", rev), "checkout") != "")
		}
		var path string
		if handleMissing {
			path = pwd + ".git/this/path/does/not/exist"
		} else {
			runShellProcessOrDie(fmt.Sprintf("git checkout --quiet %s", rev), "checkout")
			path = pwd
		}
		if exists(outdir) {
			if islink(outdir) {
				os.Remove(outdir)
			}
		}
		err := os.Symlink(path, outdir) // to, from
		if err != nil {
			log.Fatal(err)
		}
		if verbose {
			fmt.Printf("Git inward link %s -> %s\n", outdir, path)
		}
		return outdir
	} else if vcs.name == "bzr" {
		croak("checkout is not yet supported in bzr.")
	} else if vcs.name == "hg" {
		spec := ""
		if rev != "" {
			spec = "-r " + rev
		} else if tag != "" {
			spec = "-r " + tag
		} else if branch != "" {
			spec = "-r " + branch
		}
		runShellProcessOrDie(fmt.Sprintf("hg update -q %s", spec), "checkout")
		if outdir == "." {
			return pwd
		} else if exists(outdir) {
			if islink(outdir) {
				os.Remove(outdir)
			}
		}
		err = os.Symlink(pwd, outdir)
		if err != nil {
			log.Fatal(err)
		}
		if verbose {
			fmt.Printf("Hg inward link %s -> %s\n", outdir, pwd)
		}
		return outdir
	} else if vcs.name == "darcs" {
		croak("checkout is not yet supported for darcs.")
	} else {
		croak("checkout not supported for this repository type.")
	}
	// Empty return indicates error
	return ""
}

func dirlist(top string, excl stringSet) stringSet {
	outset := newStringSet()
	filepath.Walk(top, func(path string, info os.FileInfo, err error) error {
		clean := filepath.Clean(path) // Remove leading ./ if any
		if !excl.Contains(clean) {
			outset.Add(clean)
		}
		return nil
	})
	return outset
}

// Compare two repositories at a specified revision, defaulting to mainline tip.
func compareRevision(args []string, rev string) string {
	if verbose {
		fmt.Printf("compare: %s\n", args)
	}
	var sourceRev, targetRev string

	if revision != "" {
		vals := strings.Split(revision, ":")
		if len(vals) == 1 {
			sourceRev = vals[0]
			targetRev = vals[0]
		} else if len(vals) == 2 {
			sourceRev = vals[0]
			targetRev = vals[1]
		} else {
			croak("incorrect value for compare -r option.")
		}
	}
	if verbose {
		fmt.Printf("Checkout 1 revision: %s\n", sourceRev)
		fmt.Printf("Checkout 2 revision: %s\n", targetRev)
	}
	if len(args) != 2 {
		croak("compare requires exactly two repository-name args, but there are %v.", args)
	}
	source := args[0]
	target := args[1]
	if !isdir(source) || !isdir(target) {
		croak("both repository directories must exist.")
	}
	rsource := filepath.Join(TMPDIR, "source")
	os.RemoveAll(rsource)
	rtarget := filepath.Join(TMPDIR, "target")
	os.RemoveAll(rtarget)
	diffopts := make([]string, 0)
	sourceignores := make([]string, 0)
	var sourcedir, targetdir string
	under(source, func() {
		if isDvcsOrCheckout() && !seeignores {
			sourceignores = vcsignores
			for _, f := range sourceignores {
				diffopts = append(diffopts, []string{"-x", f}...)
			}
		}
		sourcedir = checkout(rsource, sourceRev)
		if sourcedir == "" {
			panic("sourcedir unexpectedly nil")
		}
	})
	targetignores := make([]string, 0)
	under(target, func() {
		if isDvcsOrCheckout() && !seeignores {
			targetignores = vcsignores
			for _, f := range targetignores {
				diffopts = append(diffopts, []string{"-x", f}...)
			}
		}
		targetdir = checkout(rtarget, targetRev)
		if targetdir == "" {
			panic("sourcedir unexpectedly nil")
		}
	})
	diffArgs := make([]string, 0)
	// The following options are passed from the repotool command line to diff
	if quiet {
		diffArgs = append(diffArgs, "-q")
	}
	if unified {
		diffArgs = append(diffArgs, "-u")
	}
	diffoptStr := strings.Join(append(diffArgs, diffopts...), " ")
	if acceptMissing {
		if !exists(sourcedir) {
			// replace by empty directory
			os.MkdirAll(sourcedir, 0755)
		}
		if !exists(targetdir) {
			// replace by empty directory
			os.MkdirAll(targetdir, 0755)
		}
	}
	// add missing empty directories in checkouts of VCSs that do not support them
	dirsToNuke := make([]string, 0)
	sourcetype := identifyRepo(source)
	targettype := identifyRepo(target)
	if (sourcetype.name != "git" && targettype.name != "hg") && (targettype.name == "git" || targettype.name == "hg") {
		under(sourcedir, func() {
			filepath.Walk(".", func(path string, info os.FileInfo, err error) error {
				if err != nil {
					fmt.Printf("error while tree-walking %s: %v\n", sourcedir, err)
					return err
				}
				if isdir(path) {
					matching := filepath.Join(targetdir, path)
					if !exists(matching) {
						dirsToNuke = append(dirsToNuke, matching)
						os.MkdirAll(matching, 0755)
					}
				}
				return nil
			})
		})
		under(targetdir, func() {
			filepath.Walk(".", func(path string, info os.FileInfo, err error) error {
				if err != nil {
					fmt.Printf("error while tree-walking %s: %v\n", targetdir, err)
					return err
				}
				if isdir(path) {
					matching := filepath.Join(sourcedir, path)
					if !exists(matching) {
						dirsToNuke = append(dirsToNuke, matching)
						os.MkdirAll(matching, 0755)
					}
				}
				return nil
			})
		})
	}
	var diff string
	under(TMPDIR, func() {
		// FIXME: use difflib here?
		silenceDiffErrors := "2>/dev/null" // for dangling symlinks or similar
		if verbose {
			fmt.Printf("Comparing %s to %s\n", sourcedir, targetdir)
			silenceDiffErrors = ""
		}
		diff = captureFromProcess(fmt.Sprintf("diff -r %s --ignore-matching-lines=' @(#) ' --ignore-matching-lines='$Id.*$' --ignore-matching-lines='$Header.*$' --ignore-matching-lines='$Log.*$' %s %s %s || exit 0", diffoptStr, sourcedir, targetdir, silenceDiffErrors), "diffing")

		// Check for permission match
		common := dirlist(sourcedir, newStringSet(sourceignores...)).Intersection(dirlist(targetdir, newStringSet(targetignores...)))
		commonList := common.Ordered()
		for _, path := range commonList {
			sstat, err1 := os.Stat(filepath.Join(sourcedir, path))
			tstat, err2 := os.Stat(filepath.Join(targetdir, path))
			if err1 != nil {
				log.Fatal(err1)
			}
			if err2 != nil {
				log.Fatal(err2)
			}
			if sstat.Mode() != tstat.Mode() {
				diff += fmt.Sprintf("%s: %0o -> %0o\n", path, sstat.Mode(), tstat.Mode())
			}
		}
	})
	// cleanup in case the checkouts were a symlink to an existing worktree
	sort.Slice(dirsToNuke, func(i, j int) bool {
		return len(dirsToNuke[i]) > len(dirsToNuke[j])
	})
	for _, d := range dirsToNuke {
		os.Remove(d)
	}
	os.RemoveAll(rsource)
	os.RemoveAll(rtarget)
	return diff
}

func compareEngine(_singular string, plural string, lister func() string, args []string) string {
	// Compare two repositories at all revisions implied by a specified command.
	if len(args) != 2 {
		croak("compareEngine requires exactly two repository-name arguments, but there are %d %v.", len(args), args)
	}
	source := args[0]
	target := args[1]
	if !isdir(source) || !isdir(target) {
		croak("both repository directories must exist.")
	}
	var sourcerefs, targetrefs []string
	under(source, func() {
		sourcerefs = strings.Fields(strings.TrimSpace(lister()))
	})
	under(target, func() {
		targetrefs = strings.Fields(strings.TrimSpace(lister()))
	})
	common := newStringSet(sourcerefs...).Intersection(newStringSet(targetrefs...))
	sourceonly := newStringSet(sourcerefs...).Subtract(common)
	targetonly := newStringSet(targetrefs...).Subtract(common)
	if refexclude != "" {
		re := regexp.MustCompile(refexclude)
		for k := range sourceonly.store {
			if re.MatchString(k) {
				sourceonly.Remove(k)
			}
		}
		for k := range targetonly.store {
			if re.MatchString(k) {
				targetonly.Remove(k)
			}
		}
	}

	compareResult := ""
	if sourceonly.Len() > 0 {
		compareResult += "----------------------------------------------------------------\n"
		compareResult += fmt.Sprintf("%s only in source:\n", plural)
		for _, item := range sourceonly.Ordered() {
			compareResult += item + "\n"
		}
	}
	if targetonly.Len() > 0 {
		compareResult += "----------------------------------------------------------------\n"
		compareResult += fmt.Sprintf("%s only in target:\n", plural)
		for _, item := range targetonly.Ordered() {
			compareResult += item + "\n"
		}
	}
	if compareResult != "" {
		croak(compareResult)
	}
	report := ""
	if !common.Empty() {
		for _, ref := range common.Ordered() {
			report += compareRevision([]string{source, target}, ref)
		}
	}
	return report
}

func compareTags(args []string) {
	diff := compareEngine("Tag", "Tags", tags, args)
	if diff != "" {
		fmt.Print(diff)
		os.Exit(1)
	} else {
		os.Exit(0)
	}
}

func compareBranches(args []string) {
	diff := compareEngine("Branch", "Branches", branches, args)
	if diff != "" {
		fmt.Print(diff)
		os.Exit(1)
	} else {
		os.Exit(0)
	}
}

func compareAll(args []string) {
	if nobranch {
		if verbose {
			fmt.Print("Comparing the complete repository...")
		}
		compareRevision(args, "")
		return
	}
	if verbose {
		fmt.Print("Comparing master...")
	}
	// -a will compare against an empty
	// directory if trunk does not exist, which will thus fail the
	// comparison if it exists on one side but not the other, but
	// will succeed if both repositories have no trunk
	acceptMissing = true
	branch = "master"
	diff := compareRevision(args, "")
	if verbose {
		fmt.Print("Comparing tags...")
	}
	diff += compareEngine("Branch", "Branches", branches, args)
	if verbose {
		fmt.Print("Comparing branches...")
	}
	compareBranches(args)
	diff += compareEngine("Branch", "Branches", branches, args)
	if diff != "" {
		fmt.Print(diff)
		os.Exit(1)
	} else {
		os.Exit(0)
	}
}

func main() {
	TMPDIR = os.Getenv("TMPDIR")
	if TMPDIR == "" {
		TMPDIR = "/tmp"
	}

	flags := flag.NewFlagSet("repotool", flag.ExitOnError)

	flags.BoolVar(&acceptMissing, "a", false, "accept missing trunk directory")
	flags.BoolVar(&seeignores, "i", false, "do not suppress comparison of normally ignored directories")
	flags.BoolVar(&nobranch, "n", false, "compare raw structure, ignore SVN branching")
	flags.BoolVar(&quiet, "q", false, "run as quietly as possible")
	flags.BoolVar(&unified, "u", false, "emit unified diff")
	flags.BoolVar(&verbose, "v", false, "show subcommands and diagnostics")

	flags.StringVar(&branch, "b", "", "select branch for checkout or comparison")
	flags.StringVar(&basedir, "c", "", "chdir to the argument repository path before doing checkout")
	flags.StringVar(&refexclude, "e", "", "exclude pattern for tag and branch names.")
	flags.StringVar(&revision, "r", "", "select revision for checkout or comparison")
	flags.StringVar(&tag, "t", "", "select tag for checkout or comparison")

	explain := func() {
		print(`
repotool commands:

initialize  - create Makefile and stub files for standard conversion workflow
export - export a stream dump of the source repository
mirror [URL] localdir - create or update a mirror of the source repository
branches - list repository branch names
checkout [-r rev] [-t tag] [-b branch] - check out a working copy of the repo
compare [-r rev] [-t tag] [-b branch] - compare head content of two repositories
compare-tags - compare source and target repo content at all tags
compare-branches - compare source and target repo content at all branches
compare-all - compare repositories at head, all tags, and all branches
version - report software version

repotool options:
`)
		flags.PrintDefaults()
		os.Exit(1)
	}

	if len(os.Args) < 2 {
		fmt.Fprintf(os.Stderr,
			"repotool: requires an operation argument.\n")
		explain()
	}
	operation := os.Args[1]

	flags.Parse(os.Args[2:])

	args := flags.Args()
	if operation == "help" {
		explain()
	} else if operation == "initialize" {
		initialize(args)
	} else if operation == "export" {
		export()
	} else if operation == "mirror" {
		mirror(args)
	} else if operation == "tags" {
		os.Stdout.WriteString(tags())
	} else if operation == "branches" {
		os.Stdout.WriteString(branches())
	} else if operation == "checkout" {
		checkout(args[0], revision)
	} else if operation == "compare" {
		if diff := compareRevision(args, revision); diff != "" {
			fmt.Print(diff)
		}
	} else if operation == "compare-tags" {
		compareTags(args)
	} else if operation == "compare-branches" {
		compareBranches(args)
	} else if operation == "compare-all" {
		compareAll(args)
	} else if operation == "version" {
		fmt.Println(version)
	} else {
		fmt.Fprintf(os.Stderr, "repotool: unknown operation %q\n", operation)
		explain()
	}
}

// end
