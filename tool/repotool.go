// repotool queries and manipulate multiple repository types in a uniform way.
package main

// Copyright by Eric S. Raymond
// SPDX-License-Identifier: BSD-2-Clause

import (
	"bytes"
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"regexp"
	//"sort"
	"strings"
	"text/template"
	"time"

	readline "github.com/chzyer/readline"
	difflib "github.com/ianbruene/go-difflib/difflib"
)

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

# Build the repository from the stream dump
{{.Project}}-{{.TargetVCS}}: {{.Project}}.{{.SourceVCS}} {{.Project}}.opts {{.Project}}.lift {{.Project}}.map $(EXTRAS)
	$(REPOSURGEON) $(VERBOSITY) 'logfile $(LOGFILE)' 'script {{.Project}}.opts' "read $(READ_OPTIONS) <{{.Project}}.{{.SourceVCS}}" 'authors read <{{.Project}}.map' 'sourcetype {{.SourceVCS}}' 'prefer git' 'script {{.Project}}.lift' 'legacy write >{{.Project}}.fo' 'rebuild {{.Project}}-{{.TargetVCS}}'

# Build a stream dump from the local mirror
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

var acceptMissing bool
var context bool
var nobranch bool
var seeignores bool
var quiet bool
var same bool
var unified bool
var verbose bool

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
	WriteSupport := newStringSet()
	for _, vcs := range vcstypes {
		if vcs.importer != "" {
			WriteSupport.Add(vcs.name)
		}
	}
	ReadSupport := newStringSet()
	for _, vcs := range vcstypes {
		if vcs.exporter != "" {
			ReadSupport.Add(vcs.name)
		}
	}
	// Hacky special case implemented through extractor class
	ReadSupport.Add("hg")
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
	if !ReadSupport.Contains(squishy.SourceVCS) {
		croak("unknown source VCS type %s", squishy.SourceVCS)
	}
	if len(args) == 0 {
		squishy.TargetVCS = input("repotool: what VCS do you want to convert to? ")
	} else {
		squishy.TargetVCS = args[0]
		args = args[1:]
	}
	if !WriteSupport.Contains(squishy.TargetVCS) {
		croak("unknown target VCS type %s", squishy.TargetVCS)
	}
	if exists("Makefile") {
		complain("a Makefile already exists here.")
	} else {
		if !quiet {
			fmt.Printf("repotool: generating Makefile, some variables in it need to be set.\n")
		}
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
		if !quiet {
			fmt.Printf("repotool: generating a stub options file.\n")
		}
		makeStub(project+".opts", "# Pre-read options for reposurgeon go here.\n")
	}
	if exists(project + ".lift") {
		complain("a project lift file already exists here.")
	} else {
		if !quiet {
			fmt.Printf("repotool: generating a stub lift file.\n")
		}
		makeStub(project+".lift", fmt.Sprintf("# Lift commands for %s\n", project))
	}
	if exists(project + ".map") {
		complain("a project map file already exists here.")
	} else {
		if !quiet {
			fmt.Printf("repotool: generating a stub map file.\n")
		}
		makeStub(project+".map", fmt.Sprintf("# Author map for %s\n", project))
	}
}

func export() {
	pwd, err := os.Getwd()
	if err != nil {
		log.Fatal(err)
	}
	rt := identifyRepo(".")
	if rt == nil {
		croak("unknown repository type at %s", pwd)
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
	// Identifies local repositories of a specified type
	localrepo := func(operand string, prefix string, vcs string) bool {
		if !strings.HasPrefix(operand, prefix) {
			return false
		}
		vtype := identifyRepo(operand[len(prefix)-1:])
		return vtype != nil && vtype.name == vcs
	}
	var locald string
	tillHash := regexp.MustCompile("^.*#")
	isFullURL, badre := regexp.Match("svn://|svn\\+ssh://|https://|http://", []byte(operand))
	if (badre == nil && isFullURL) || localrepo(operand, "file:///", "svn") {
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
	} else if strings.HasPrefix(operand, "cvs://") || localrepo(operand, "file://", "cvs") {
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
	} else if strings.HasPrefix(operand, "git://") || localrepo(operand, "file://", "git") {
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
	} else if strings.HasPrefix(operand, "hg://") || localrepo(operand, "file://", "hg") {
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
	var err error
	pwd, err := os.Getwd()
	if err != nil {
		log.Fatal(err)
	}
	if nobranch {
		branch = "" // nobranch will also prevent the automatic switch to "trunk"
	}
	if outdir[0] != os.PathSeparator {
		croak("checkout requires absolute target path")
	}
	if exists(outdir) {
		outdir, err = filepath.EvalSymlinks(outdir)
		if err != nil {
			log.Fatal(fmt.Sprintf("chasing symlink: %v", err))
		}
	}
	if verbose {
		fmt.Printf("checkout: from %s to %s\n", pwd, outdir)
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
		// The reason for checkout's odd calling signature -
		// pass it a checkout directory, get back a symlink
		// toi what you actually wanted - is here. The problem
		// is that Subversion checkoutd on large repositories
		// are horribly slow.  In case we're doing a
		// comparison on all tags and branches, we want to
		// checlk out the full repo *once* and pass back
		// symlinks to parts in the checkout directory,
		// updating it only as needed. This is is much faster
		// than doing a fresh checkout every time.
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

// dirlist lists all files and directories under a sprcfief directory.
func dirlist(top string) stringSet {
	outset := newStringSet()
	here, _ := os.Getwd()
	os.Chdir(top)
	filepath.Walk(".", func(path string, info os.FileInfo, err error) error {
		outset.Add(filepath.Clean(path)) // Remove leading ./ if any
		return nil
	})
	os.Chdir(here)
	return outset
}

// ignorable says whether the specified path
func ignorable(filepath string, vcs *VCS) bool {
	// ignorable dotfile
	if path.Base(filepath) == vcs.ignorename {
		return true
	}
	// ignorable checkout subdirectory
	if vcs.checkignore != "" && strings.HasPrefix(filepath, vcs.checkignore+"/") {
		return true
	}
	// ignorable metadata directory
	if strings.HasPrefix(filepath, vcs.subdirectory+"/") {
		return true
	}
	return false
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
	TMPDIR := os.Getenv("TMPDIR")
	rsource, err := ioutil.TempDir(TMPDIR, "sourcecheckout")
	if err != nil {
		log.Fatal(err)
	}
	os.RemoveAll(rsource)
	rtarget, err := ioutil.TempDir(TMPDIR, "targetcheckout")
	if err != nil {
		log.Fatal(err)
	}
	os.RemoveAll(rtarget)
	var sourcedir, targetdir string
	under(source, func() {
		sourcedir = checkout(rsource, sourceRev)
		if sourcedir == "" {
			panic("sourcedir unexpectedly nil")
		}
	})
	under(target, func() {
		targetdir = checkout(rtarget, targetRev)
		if targetdir == "" {
			panic("sourcedir unexpectedly nil")
		}
	})
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
	// Ugh.  These are the types of the original repository
	// directories, which in particulat do not imply the ignorables
	// of any corresponding checkout directories.  The obvious way
	// to fix this - run identifyRepo() on the checkout
	// directories sourcedir and targetdir - works for the CVS
	// case but not for the Subversion case.  The problem is that
	// the checkout diectory is a *subdirectory* of the top-level
	// directory where we can expect to find a .svn file.
	sourcetype := identifyRepo(source)
	targettype := identifyRepo(target)
	var diff string
	dollarJunk := regexp.MustCompile(` @\(#\) |\$Id.*\$|\$Header.*\$|$Log.*\$`)
	isDollarLine := func(line string) bool {
		return dollarJunk.MatchString(line)
	}
	sourcefiles := dirlist(sourcedir)
	targetfiles := dirlist(targetdir)
	for _, path := range sourcefiles.Union(targetfiles).Ordered() {
		sourcepath := filepath.Join(sourcedir, path)
		targetpath := filepath.Join(targetdir, path)
		if isdir(sourcepath) || isdir(targetpath) || ignorable(path, sourcetype) || ignorable(path, targettype) {
			continue
		}
		if !targetfiles.Contains(path) {
			diff += fmt.Sprintf("%s: source only\n", path)
			continue
		}
		if !sourcefiles.Contains(path) {
			diff += fmt.Sprintf("%s: target only\n", path)
			continue
		}
		sourceText, err := ioutil.ReadFile(sourcepath)
		if err != nil {
			complain("%s %s is unreadable", sourcetype.name, path)
		}
		targetText, err := ioutil.ReadFile(targetpath)
		if err != nil {
			complain("%s %s is unreadable", targettype.name, path)
		}
		// When this shelled out to diff it had these filters:
		// --ignore-matching-lines=' @(#) '
		// --ignore-matching-lines='$Id.*$'
		// --ignore-matching-lines='$Header.*$'
		// --ignore-matching-lines='$Log.*$'

		if !bytes.Equal(sourceText, targetText) {
			lines0 := difflib.SplitLines(string(sourceText))
			lines1 := difflib.SplitLines(string(targetText))
			file0 := path + " (" + sourcetype.name + ")"
			file1 := path + " (" + targettype.name + ")"
			var text string
			diffObj := difflib.LineDiffParams{
				A:          lines0,
				B:          lines1,
				FromFile:   file0,
				ToFile:     file1,
				Context:    3,
				IsJunkLine: isDollarLine,
			}
			if unified {
				text, _ = difflib.GetUnifiedDiffString(diffObj)
			}
			if context {
				text, _ = difflib.GetContextDiffString(diffObj)
			}
			diff += text
		} else if same {
			diff += fmt.Sprintf("Same: %s\n", path)
		}

		// Check for permission mismatch,  We have to skip directories beccause
		// of Go MkdirAll's behavior that requiring seek permission; this makes for
		// spurious mismatches in the x permission bit. The error cases here
		// can be reached by symlink entries in Subversion files.
		sstat, err1 := os.Stat(sourcepath)
		if err1 != nil {
			complain("source path stat: %s", err1)
			continue
		}
		tstat, err2 := os.Stat(targetpath)
		if err2 != nil {
			complain("target path stat: %s", err2)
			continue
		}
		if sstat.Mode() != tstat.Mode() {
			diff += fmt.Sprintf("%s: %0o -> %0o\n", path, sstat.Mode(), tstat.Mode())
		}
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
		fmt.Print("Comparing master...\n")
	}
	// -a will compare against an empty
	// directory if trunk does not exist, which will thus fail the
	// comparison if it exists on one side but not the other, but
	// will succeed if both repositories have no trunk
	acceptMissing = true
	branch = ""
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
	flags := flag.NewFlagSet("repotool", flag.ExitOnError)

	flags.BoolVar(&acceptMissing, "a", false, "accept missing trunk directory")
	flags.BoolVar(&context, "c", false, "emit context diff")
	flags.BoolVar(&seeignores, "i", false, "do not suppress comparison of normally ignored directories")
	flags.BoolVar(&nobranch, "n", false, "compare raw structure, ignore SVN branching")
	flags.BoolVar(&quiet, "q", false, "run as quietly as possible")
	flags.BoolVar(&same, "s", false, "show same files")
	flags.BoolVar(&unified, "u", true, "emit unified diff")
	flags.BoolVar(&verbose, "v", false, "show subcommands and diagnostics")

	flags.StringVar(&branch, "b", "", "select branch for checkout or comparison")
	flags.StringVar(&basedir, "d", "", "chdir to the argument repository path before doing checkout")
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

	if !strings.HasPrefix(operation, "compare") && (acceptMissing || context || seeignores || same) {
		croak("compare option with non-compare operation, bailing out.")
	}
	if operation != "tag" && operation != "branches" && operation != "checkout" && !strings.HasPrefix(operation, "compare") && refexclude != "" {
		croak("exclusion option with an operation %s that does not accept it", operation)
	}
	if (operation != "checkout" && !strings.HasPrefix(operation, "compare")) && (revision != "" || branch != "" || tag != "") {
		croak("selection option with an operation that is not checkout or compare")
	}

	if basedir != "" {
		if err := os.Chdir(basedir); err != nil {
			croak("changing directory: %v", err)
		}
	}

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
