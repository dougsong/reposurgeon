// repotool queries and manipulate multiple repository types in a uniform way.
package main

// SPDX-License-Identifier: BSD-2-Clause

import (
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	//"regexp"
	//"sort"
	"strings"
	//"text/template"
	"time"

	readline "github.com/chzyer/readline"
)

// TMPDIR is the temporary directory under which to perform checkouts
var TMPDIR string

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
	croak("initialize is not yet supported")
}

func mirror(args []string) {
	croak("mirror is not yet supported")
}

func export(args []string) {
	croak("export is not yet supported")
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
