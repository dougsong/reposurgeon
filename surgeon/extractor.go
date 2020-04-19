// How to write extractor classes:
//
// Clone one of the existing ones and mutate.
//
// Significant fact: None of the get* methods for extracting information about
// a revision is called until after manifest has been called on that revision.
// (Thus if you implement manifest with a checkout, you can extract information
// from the working tree / checked out revision.)
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
//
//
// Everything in this module is implementation for RepoStreamer.
// Extractor is also used outside of here, but only trivially.
//
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"bufio"
	"crypto/sha1"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	_ "net/http/pprof"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"

	shellquote "github.com/kballard/go-shellquote"
)

// signature is a file signature - path, hash value of content and permissions."
type signature struct {
	//pathname string
	hashval [sha1.Size]byte
	perms   string
}

func newSignature(hashval [sha1.Size]byte, perms int) *signature {
	ps := new(signature)
	ps.hashval = hashval
	// Map to the restricted set of modes that are allowed in
	// the stream format.
	if (perms & 0000700) == 0000700 {
		perms = 0100755
	} else if (perms & 0000600) == 0000600 {
		perms = 0100644
	}
	ps.perms = fmt.Sprintf("%06o", perms)
	return ps
}

func (s signature) String() string {
	return fmt.Sprintf("<%s:%02x%02x%02x%02x%02x%02x>",
		s.perms, s.hashval[0], s.hashval[1], s.hashval[2], s.hashval[3], s.hashval[4], s.hashval[5])
}

func (s signature) Equal(other signature) bool {
	return s.hashval == other.hashval && s.perms == other.perms
}

type manifestEntry struct {
	pathname string
	sig      *signature
}

// Extractor specifies common features of all VCS-specific extractor classes.
type Extractor interface {
	// Hook for any setup actions required before streaming
	preExtract()
	// Hook called periodically (every 1000 commits) for
	// any housekeeping actions required.  Optional.
	keepHouse() error
	// Gather the topologically-ordered lists of revisions and the
	// parent map (revlist and parent members)
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
	// Return all files in the specified revision
	manifest(string) []manifestEntry
	// Check out a specified path from a revision, write to a
	// new file at dest
	catFile(rev string, path string, dest string) error
	// Return a commit's change comment as a string.
	getComment(string) string
}

// CommitMeta is the extractor's idea of per-commit metadata
type CommitMeta struct {
	ci     string
	ai     string
	branch string
}

// How these are structured: RepoStreamer is the common code that
// sequences extractions. It expects to be able to call a VCS-specific
// extractor class. Each of these extractors has the option of using
// ColorMixin, which can simulate Git's algorithm for branch-coloring
// commits.

// MixerCapable declares an extractor can use the Git coloring simulation
type MixerCapable interface {
	gatherCommitTimestamps() error
	gatherChildTimestamps(*RepoStreamer) map[string]time.Time
}

// ColorMixer is a mixin class for simulating the git branch-coloring algorithm
type ColorMixer struct {
	base         *RepoStreamer
	commitStamps map[string]time.Time // icommit -> timestamp
	childStamps  map[string]time.Time // commit -> timestamp of latest child
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
	if err != nil || cm.commitStamps == nil {
		panic(throw("extractor", "Could not retrieve commit timestamps: %v", err))
	}
	// This will be used in _branchColor below
	cm.childStamps = mc.gatherChildTimestamps(base)
	if logEnable(logTOPOLOGY) {
		for _, rev := range cm.base.revlist {
			if logEnable(logSHOUT) {logit("Revision %s has branch '%s'\n", rev, cm.base.meta[rev].branch)}
		}
	}
	// Depends on the order of the revlist to be correct.
	// The Python code did a sort by timestamp here -
	// not necessary id your VCS dumps branches in
	// revlist-tip order.
	for _, refname := range base.refs.keys {
		if logEnable(logTOPOLOGY) {logit("outside branch coloring %s %s", base.refs.get(refname), refname)}
		cm._branchColor(base.refs.get(refname), refname)
	}
}

// Exact value of this constant is unimportant, it just needs to be
// absurdly far in the future so no commit can have a committer date
// that's greater.  In fact it is 109626219-06-19 07:45:03 +0000 UTC
// We can't use the obvious 1<<63-1, because conversion to Go's epoch
// (year 1 rather than 1970) overflows an int64.
var farFuture = time.Unix(1<<62-1, 0)

func (cm *ColorMixer) _branchColor(rev, color string) {
	if cm.base.branchesAreColored && strings.HasPrefix(color, "refs/heads/") {
		return
	}
	if logEnable(logTOPOLOGY) {logit("inside branch coloring %s %s", rev, color)}
	// This ensures that a branch tip rev never gets colored over
	if _, ok := cm.childStamps[rev]; !ok {
		cm.childStamps[rev] = farFuture
	}
	// This is used below to ensure that a branch color is never colored
	// back to a tag
	isBranchColor := strings.HasPrefix(color, "refs/heads/")
	if logEnable(logTOPOLOGY) {logit("%s is-a-branch is %v", color, isBranchColor)}
	unassigned := func(rev string) bool {
		u := (cm.base.meta[rev].branch == "")
		if logEnable(logTOPOLOGY) {logit("%s unassigned is %v", rev, u)}
		return u
	}
	onTagBranch := func(rev string) bool {
		return strings.HasPrefix(cm.base.meta[rev].branch, "refs/tags/")
	}
	// No need for a condition here because we will only be starting
	// this while loop from an initial call with a branch tip or from
	// a recursive call with a parent we know we want to color; the
	// loop exit is controlled by filtering out the parents that are
	// already colored properly
	for {
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
		if logEnable(logTOPOLOGY) {logit("parents of %s (%s) before filtering %v", rev, timestamp.UTC(), cm.base.getParents(rev))}
		for _, p := range cm.base.getParents(rev) {
			if unassigned(p) || ((!(isBranchColor && onTagBranch(p))) && (cm.childStamps[p].Before(timestamp))) {
				parents = append(parents, p)
			}
		}
		if logEnable(logTOPOLOGY) {logit("parents of %s are %v", rev, parents)}

		if len(parents) == 0 {
			break
		} else if len(parents) == 1 {
			// This case avoids munching excessive stack space by recursing
			// too deep on large repos.
			rev = parents[0]
			// Mark the parent with the timestamp of the child it is
			// being colored from
			cm.childStamps[rev] = timestamp
			continue
		} else {
			for _, parent := range parents {
				// Mark each parent with the timestamp of the child it is
				// being colored from
				cm.childStamps[parent] = timestamp
				cm._branchColor(parent, color)
			}
			break
		}
	}
}

func findVCS(name string) *VCS {
	for _, vcs := range vcstypes {
		if vcs.name == name {
			return &vcs
		}
	}
	panic("reposurgeon: failed to find '" + name + "' in VCS types")
}

func lineByLine(rs *RepoStreamer, command string, errfmt string,
	hook func(string, *RepoStreamer) error) error {
	stdout, cmd, err1 := readFromProcess(command)
	if err1 != nil {
		return err1
	}
	defer stdout.Close()
	r := bufio.NewReader(stdout)
	for {
		line, err2 := r.ReadString(byte('\n'))
		if err2 == io.EOF {
			if cmd != nil {
				cmd.Wait()
			}
			break
		} else if err2 != nil {
			return fmt.Errorf(errfmt, err2)
		}
		hook(line, rs)
	}
	return nil
}

// GitExtractor is a repository extractor for the git version-control system
type GitExtractor struct {
}

func newGitExtractor() *GitExtractor {
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
	return ge
}

func (ge *GitExtractor) preExtract() {
}

func (ge *GitExtractor) keepHouse() error {
	return nil
}

func (ge *GitExtractor) gatherRevisionIDs(rs *RepoStreamer) error {
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

func (ge *GitExtractor) gatherCommitData(rs *RepoStreamer) error {
	hook := func(line string, rs *RepoStreamer) error {
		line = strings.Trim(line, "\n")
		fields := strings.Split(line, "|")
		rs.meta[fields[0]] = new(CommitMeta)
		rs.meta[fields[0]].ci = fields[1]
		rs.meta[fields[0]].ai = fields[2]
		return nil
	}
	return lineByLine(rs,
		"git log --all --reverse --date=raw --format='%H|%cn <%ce> %cd|%an <%ae> %ad'",
		"git's gatherCommitData: %v",
		hook)
}

func (ge *GitExtractor) gatherAllReferences(rs *RepoStreamer) error {
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
	rs.baton.twirl()

	rf, cmd, err1 := readFromProcess("git tag -l")
	tl := bufio.NewReader(rf)
	if err1 != nil {
		return fmt.Errorf("while listing tags: %v", err)
	}
	defer rf.Close()
	for {
		fline, err2 := tl.ReadString(byte('\n'))
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
		cfout, cmd, err3 := readFromProcess("git cat-file -p " + tag)
		if err3 != nil {
			return fmt.Errorf("while auditing tag %q: %v", tag, err)
		}
		defer cfout.Close()
		cf := bufio.NewReader(cfout)
		tagger := ""
		comment := ""
		inBody := false
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
		rs.refs.set("refs/tags/"+tag, objecthash)
		if objecthash != taghash {
			attrib, err := newAttribution(tagger)
			if err != nil {
				return fmt.Errorf("warning: atttribution in tag %s garbled: %v", tag, err)
			}
			// committish isn't a mark; we'll fix that later
			tagobj := *newTag(nil, tag, objecthash, attrib, comment)
			rs.tags = append(rs.tags, tagobj)
		}
		rs.baton.twirl()
	}
	return nil
}

// colorBranches colors all commits with their branch name.
func (ge *GitExtractor) colorBranches(rs *RepoStreamer) error {
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
	defer markfile.Close()
	data, err3 := captureFromProcess("git fast-export --all --export-marks=" + file.Name())
	if err3 != nil {
		panic(throw("extractor", "Couldn't spawn git-fast-export: %v", err3))
	}
	rf := bufio.NewReader(markfile)
	rs.baton.twirl()
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

func (ge *GitExtractor) _metadata(rev string, format string) string {
	line, err := captureFromProcess(fmt.Sprintf("git log -1 --format='%s' %s", format, rev))
	if err != nil {
		panic(throw("extractor", "Couldn't spawn git log: %v", err))
	}
	if line[len(line)-1] == '\n' {
		line = line[:len(line)-1]
	}
	return line
}

func (ge *GitExtractor) postExtract(_repo *Repository) {
	cmd := exec.Command("git", "checkout", "--quiet", "master")
	cmd.Stdin = os.Stdin
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	cmd.Run()
}

// isClean is a predicate;  return true if repo has no unsaved changes.
func (ge *GitExtractor) isClean() bool {
	data, err := captureFromProcess("git ls-files --modified")
	if err != nil {
		panic(throw("extractor", "Couldn't spawn git ls-files --modified: %v", err))
	}
	return data == ""
}

// manifest lists all files present as of a specified revision.
func (ge *GitExtractor) manifest(rev string) []manifestEntry {
	data, err := captureFromProcess("git ls-tree -rz --full-tree " + rev)
	if err != nil {
		panic(throw("extractor", "Couldn't spawn git ls-tree in manifest: %v", err))
	}
	lines := strings.Split(data, "\000")
	if lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	var manifest = make([]manifestEntry, 0, len(lines))
	for _, line := range lines {
		// format of git ls-tree output:
		// 100644 blob a8d26cb7dd7c02bcf5b332b1d306ad5641e93ab9	.dockerignore
		// (that last whitespace, before the path, is a TAB)
		fields := strings.SplitN(line, " ", 3)
		var perms int
		fmt.Sscanf(fields[0], "%o", &perms)
		typ := fields[1]
		if typ != "blob" {
			// type "commit" is for submodules, which we don't
			// currently support (we'll silently drop them)
			continue
		}
		tabs := strings.SplitN(fields[2], "\t", 2)
		hash, err := hex.DecodeString(tabs[0])
		if err != nil {
			panic(throw("extractor", "Malformed blob hash: %v", err))
		}
		var fixedhash [sha1.Size]byte
		copy(fixedhash[:], hash)
		sig := newSignature(fixedhash, perms)
		var me manifestEntry
		me.pathname = tabs[1]
		me.sig = sig
		manifest = append(manifest, me)
	}
	return manifest
}

// catFile extracts file content into a specified destination path
func (ge *GitExtractor) catFile(rev string, path string, dest string) error {
	cmd := exec.Command("git", "show", rev+":"+path)
	out, err := os.Create(dest)
	if err != nil {
		return err
	}
	cmd.Stdout = out
	return cmd.Run()
}

// getComment returns a commit's change comment as a string.
func (ge *GitExtractor) getComment(rev string) string {
	return ge._metadata(rev, "%B")
}

// HgExtractor is a repository extractor for the hg version-control system
type HgExtractor struct {
	ColorMixer
	tagsFound      bool
	bookmarksFound bool
	hgcl           *HgClient
	hashTranslate  map[[sha1.Size]byte][sha1.Size]byte
}

func newHgExtractor() *HgExtractor {
	he := new(HgExtractor)
	he.hashTranslate = make(map[[sha1.Size]byte][sha1.Size]byte)
	return he
}

func (he *HgExtractor) preExtract() {
	// We have to do this at preExtract time, rather than newHgExtractor(),
	// because the HgClient captures the cwd at the time of its creation
	he.hgcl = NewHgClient()
}

func (he *HgExtractor) keepHouse() error {
	// If we're using an hgclient, kill the hg server and start a new
	// one, to limit the memory leaks
	if he.hgcl != nil {
		// If this fails, we ignore the error because we're going
		// to drop our reference anyway when we start a new one.
		he.hgcl.Close()
	}
	// We should still have the correct cwd, as nothing in here chdirs
	he.hgcl = NewHgClient()
	return nil
}

// mimics captureFromProcess (and calls it if no HgClient)
func (he *HgExtractor) capture(cmd ...string) (string, error) {
	command := shellquote.Join(cmd...)
	if he == nil || he.hgcl == nil {
		return captureFromProcess(command)
	}
	if logEnable(logCOMMANDS) {logit("%s: capturing %s", rfc3339(time.Now()), command)}
	stdout, stderr, err := he.hgcl.runcommand(cmd)
	content := string(stdout) + string(stderr)
	if logEnable(logCOMMANDS) {
		control.baton.printLog([]byte(content))
	}
	return content, err
}

func (he *HgExtractor) mustCapture(cmd []string, errorclass string) string {
	data, err := he.capture(cmd...)
	if err != nil {
		if logEnable(logSHOUT) {logit("%s", strings.TrimSpace(data))}
		panic(throw(errorclass,
			"In %s, command %s failed: %v",
			errorclass, shellquote.Join(cmd...), err))
	}
	return data
}

// mimics lineByLine (and calls it if no HgClient)
func (he *HgExtractor) byLine(rs *RepoStreamer, cmd []string, errfmt string,
	hook func(string, *RepoStreamer) error) error {
	command := shellquote.Join(cmd...)
	if he == nil || he.hgcl == nil {
		return lineByLine(rs, command, errfmt, hook)
	}
	if logEnable(logCOMMANDS) {
		croak("%s: reading from '%s'\n",
			rfc3339(time.Now()), command)
	}
	stdout, stderr, err := he.hgcl.runcommand(cmd)
	if err != nil {
		if logEnable(logSHOUT) {logit("%s", strings.TrimSpace(string(stderr)))}
		return err
	}
	last := false
	for _, line := range strings.SplitAfter(string(stdout), "\n") {
		if line == "" {
			last = true
			continue
		}
		if last { // can't happen
			return errors.New("Line-splitting error")
		}
		hook(line, rs)
	}
	return nil
}

//gatherRevisionIDs gets the topologically-ordered list of revisions and parents.
func (he *HgExtractor) gatherRevisionIDs(rs *RepoStreamer) error {
	// Belated initialization
	he.base = rs
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
	err := he.byLine(rs,
		[]string{"hg", "log", "--template", `{node|short} {p1node|short} {p2node|short}\n`},
		"hg's gatherRevisionIDs: %v",
		hook)
	// No way to reverse the log order, so it has to be done here
	for i := len(rs.revlist)/2 - 1; i >= 0; i-- {
		opp := len(rs.revlist) - 1 - i
		rs.revlist[i], rs.revlist[opp] = rs.revlist[opp], rs.revlist[i]
	}

	return err
}

// gatherCommitData gets all other per-commit data except branch IDs
func (he *HgExtractor) gatherCommitData(rs *RepoStreamer) error {
	hook := func(line string, rs *RepoStreamer) error {
		fields := strings.Split(line, "|")
		hash := fields[0]
		ci := fields[1]
		// Because hg doesn't store separate author and committer info,
		// we just use the committer for both.  Alternate possibility,
		// just set the committer - I (ESR) believe git does that
		// defaulting itself.  But let's not count on it, since we
		// might be handing the history stream to somebody's importer
		// that handles that edge case differently.
		rs.meta[hash] = new(CommitMeta)
		rs.meta[hash].ci = ci
		rs.meta[hash].ai = ci
		return nil
	}
	return he.byLine(rs,
		[]string{"hg", "log", "--template", `{node|short}|{sub(r"<([^>]*)>", "", author|person)} <{author|email}> {date|rfc822date}\n`},
		"hg's gatherCommitData: %v",
		hook)
}

// gatherCommitTimestamps updates the ColorMixer mapping of hash -> timestamp
func (he *HgExtractor) gatherCommitTimestamps() error {
	he.commitStamps = make(map[string]time.Time)
	hook := func(line string, rs *RepoStreamer) error {
		fields := strings.Fields(line)
		d, err := newDate(fields[1])
		if err != nil {
			panic(throw("unrecognized date format in %q: %v", line, err))
		}
		he.commitStamps[fields[0]] = d.timestamp
		return nil
	}

	return he.byLine(nil,
		[]string{"hg", "log", "--template", `{node|short} {date|rfc3339date}\n`},
		"hg's gatherCommitTimestamps",
		hook)
}

// gatherAllReferences finds all branch heads and tags
func (he *HgExtractor) gatherAllReferences(rs *RepoStreamer) error {
	// Some versions of mercurial can return an error for showconfig
	// when the config is not present. This isn't an error.
	bookmarkRef, errcode := he.capture("hg", "showconfig", "reposurgeon.bookmarks")
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
		rs.refs.set("refs/heads/"+n, h)
		return nil
	}
	err := he.byLine(rs,
		[]string{"hg", "branches", "--closed"},
		"fetching hg branches",
		hook1)

	if err != nil {
		panic(throw("extractor", "while fetching hg branches: %v", err))
	}
	if bookmarkRef != "" {
		refRE := regexp.MustCompile(`\s*(?:\*\s+)?(\S+)\s+\d+:([0-9a-fA-F]+)(?: \(inactive|closed\))?`)
		hook2 := func(line string, rs *RepoStreamer) error {
			matches := refRE.FindStringSubmatch(line)
			if len(matches) != 3 {
				panic(throw("extractor",
					"Empty or garbled 'hg bookmarks' line: %q", line))
			}
			n := matches[1]
			h := matches[2]
			rs.refs.set("refs/"+bookmarkRef+n, h)
			he.bookmarksFound = true
			return nil
		}
		err = he.byLine(rs,
			[]string{"hg", "bookmarks"},
			"fetching hg bookmarks",
			hook2)
		if err != nil {
			panic(throw("extractor", "while fetching hg bookmarks: %v", err))
		}
	}
	he.tagsFound = false
	hook3 := func(line string, rs *RepoStreamer) error {
		// In Python this was:
		/* n, h = tuple(map(polystr, line.strip().rsplit(b'\t', 1))) */
		line = strings.TrimSpace(line)
		fields := strings.Split(line, "\t")
		h := fields[len(fields)-1]
		n := strings.Join(fields[:len(fields)-1], "\t")
		if n == "tip" { // pseudo-tag for most recent commit
			return nil // We don't want it
		}
		he.tagsFound = true
		rs.refs.set("refs/tags/"+n, h[:12])
		return nil
	}
	err = he.byLine(rs,
		[]string{"hg", "log", "--rev=tag()", `--template={tags}\t{node}\n`},
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

func (he *HgExtractor) _hgBranchItems() OrderedMap {
	out := newOrderedMap()
	err := he.byLine(nil,
		[]string{"hg", "log", "--template", `{node|short} {branch}\n`},
		"in _hgBranchItems: %v",
		func(line string, rs *RepoStreamer) error {
			fields := strings.Fields(line)
			out.set(fields[0], "refs/heads/"+fields[1])
			return nil
		})
	if err != nil {
		panic(throw("extractor", "in _hgBranchItems: %v", err))
	}
	return out
}

// Return initial mapping of commit hash -> timestamp of child it is colored from
func (he *HgExtractor) gatherChildTimestamps(rs *RepoStreamer) map[string]time.Time {
	results := make(map[string]time.Time)
	items := he._hgBranchItems()
	for _, h := range items.keys {
		branch := items.get(h)
		// Fill in the branch as a default; this will ensure
		// that any commit that is not in the ancestor tree of
		// a tag will get the correct hg branch name, even if
		// the hg branch coloring is not compatible with the
		// git coloring algorithm
		if logEnable(logTOPOLOGY) {logit("setting default branch of %s to %s", h, branch)}
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

func (he *HgExtractor) _branchColorItems() *OrderedMap {
	if !he.tagsFound && !he.bookmarksFound {
		if logEnable(logEXTRACT) {logit("no tags or bookmarks.")}
		// If we didn't find any tags or bookmarks, we can
		// safely color all commits using hg branch names,
		// since hg stores them with commit metadata; note,
		// however, that the coloring this will produce might
		// not be reproducible if the repo is written to a
		// fast-import stream and used to construct a git
		// repo, because hg branches can store colorings that
		// do not match the git coloring algorithm
		items := he._hgBranchItems()
		return &items
	}
	// Otherwise we have to use the emulated git algorithm to color
	// any commits that are tags or the ancestors of tags, since git
	// prioritizes tags over branches when coloring; we will color
	// commits that are not in the ancestor tree of any tag in
	// gatherChildTimestamps below, using the hg branch names
	return nil
}

// colorBanches assigns branches to commits in an extracted repository
func (he *HgExtractor) colorBranches(rs *RepoStreamer) error {
	colorItems := he._branchColorItems()
	if colorItems != nil {
		// If the repo will give us a complete list of (commit
		// hash, branch name) pairs, use that to do the coloring
		for _, h := range colorItems.keys {
			color := colorItems.get(h)
			if rs.meta[h] == nil {
				rs.meta[h] = new(CommitMeta)
			}
			if logEnable(logTOPOLOGY) {logit("setting branch from color items, %s to %s", h, color)}
			rs.meta[h].branch = color
		}
	} else {
		// Otherwise we have to emulate the git coloring algorithm
		he.simulateGitColoring(he, rs)
	}
	return nil
}

func (he *HgExtractor) postExtract(repo *Repository) {
	// Shut down the Hg command server, we're done with it
	if he.hgcl != nil {
		he.hgcl.Close()
		// whether Close succeeded or not, we drop our reference
		he.hgcl = nil
	}
	if !repo.branchset().Contains("refs/heads/master") {
		walkEvents(repo.events, func(_ int, event Event) {
			switch event.(type) {
			case *Commit:
				if event.(*Commit).Branch == "refs/heads/default" {
					event.(*Commit).Branch = "refs/heads/master"
				}
			case *Reset:
				if event.(*Reset).ref == "refs/heads/default" {
					event.(*Reset).ref = "refs/heads/master"
				}
			}
		})
	}
}

// isClean returns true if repo has no unsaved changes
func (he *HgExtractor) isClean() bool {
	data, err := he.capture("hg", "status", "--modified")
	if err != nil {
		if logEnable(logSHOUT) {logit("%s", strings.TrimSpace(data))}
		panic(throw("extractor", "Couldn't spawn hg status --modified: %v", err))
	}
	return data == ""
}

// manifest lists all files present as of a specified revision.
func (he HgExtractor) manifest(rev string) []manifestEntry {
	data := he.mustCapture([]string{"hg", "manifest", "-v", "--debug",
		"-r", rev}, "extractor")
	lines := strings.Split(data, "\n")
	if lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	var manifest = make([]manifestEntry, 0, len(lines))
	for _, line := range lines {
		// format of hg manifest output:
		// b80de5d138758541c5f05265ad144ab9fa86d1db 644 % .hgtags
		// % is either ' ' (normal file), '*' (executable) or '@'
		// (symlink).
		var perms int
		fmt.Sscanf(line[41:44], "%o", &perms)
		switch line[45] {
		case ' ': // regular file
			break
		case '*': // executable file
			if perms != 0755 {
				panic(throw("extractor", "perms do not match type for blob: %v", line))
			}
			break
		case '@': // symlink
			perms = 0120000
			break
		default:
			panic(throw("extractor", "unrecognised type flag in manifest: %v", line))
		}
		var me manifestEntry
		me.pathname = line[47:]
		// Sadly we can't just use hg's blob hash, because it includes
		// metadata like filenames, so if the file gets moved we'd
		// create a duplicate blob.  Thus, if the blob hash has
		// changed we have to cat the file and SHA it ourselves.
		// (We'll cat it again later when we create the Blob; we could
		// probably combine both cats, always creating a blobfile and
		// then deleting it if not needed, but that would mean
		// restructuring the calling code.)
		var fixedhghash [sha1.Size]byte
		hghash, err := hex.DecodeString(line[:40])
		if err != nil {
			panic(throw("extractor", "Malformed blob hash: %v", err))
		}
		copy(fixedhghash[:], hghash)
		fixedhash, ok := he.hashTranslate[fixedhghash]
		if !ok {
			func() {
				tempFile, err := ioutil.TempFile("", "rsc")
				if err != nil {
					panic(throw("extractor", "Couldn't create tempfile for hashing: %v", err))
				}
				defer os.Remove(tempFile.Name())
				defer tempFile.Close()
				// See HgExtractor.catFile() below for explanation
				dest := strings.ReplaceAll(tempFile.Name(), "%", "%%")
				data, err = he.capture("hg", "cat", "-r", rev, me.pathname, "-o", dest)
				if err != nil {
					if logEnable(logSHOUT) {logit("%s", strings.TrimSpace(data))}
					panic(throw("extractor", "Couldn't cat blob to hash it: %v", err))
				}
				hash := sha1.New()
				if _, err := io.Copy(hash, tempFile); err != nil {
					panic(throw("extractor", "Couldn't hash blob: %v", err))
				}
				copy(fixedhash[:], hash.Sum(nil))
				he.hashTranslate[fixedhghash] = fixedhash
			}()
		}
		sig := newSignature(fixedhash, perms)
		me.sig = sig
		manifest = append(manifest, me)
	}
	return manifest
}

// catFile extracts file content into a specified destination path
func (he *HgExtractor) catFile(rev string, path string, dest string) error {
	// -o interprets various special formatting codes, like %H for
	// the changeset hash, so we need to escape all % as %%.
	// (The blobfile stem and suffix won't have any, but the path
	// to the repodir might.)
	dest = strings.ReplaceAll(dest, "%", "%%")
	data, err := he.capture("hg", "cat", "-r", rev, path, "-o", dest)
	if err != nil {
		if logEnable(logSHOUT) {logit("%s", strings.TrimSpace(data))}
	}
	return err
}

// getComment returns a commit's change comment as a string.
func (he HgExtractor) getComment(rev string) string {
	data, err := he.capture("hg", "log", "-r", rev, "--template", `{desc}\n`)
	if err != nil {
		if logEnable(logSHOUT) {logit("%s", strings.TrimSpace(data))}
		panic(throw("extractor", "Couldn't spawn hg log: %v", err))
	}
	return data
}

// RepoStreamer is the repository factory driver class for all repo analyzers.
type RepoStreamer struct {
	revlist            []string               // commit identifiers, oldest first
	parents            map[string][]string    // commit -> [parent-commit, ...]
	meta               map[string]*CommitMeta // commit -> committer/author/branch
	refs               OrderedMap             // 'refs/class/name' -> commit
	tags               []Tag                  // Tag objects (annotated tags only)
	tagseq             int
	commitMap          map[string]*Commit
	visibleFiles       map[string]map[string]signature
	hashToMark         map[[sha1.Size]byte]markidx
	branchesAreColored bool
	baton              *Baton
	extractor          Extractor
}

func newRepoStreamer(extractor Extractor, progress bool) *RepoStreamer {
	rs := new(RepoStreamer)
	rs.revlist = make([]string, 0)
	rs.parents = make(map[string][]string)
	rs.meta = make(map[string]*CommitMeta)
	rs.refs = newOrderedMap()
	rs.tags = make([]Tag, 0)
	rs.tagseq = 0
	rs.commitMap = make(map[string]*Commit)
	rs.visibleFiles = make(map[string]map[string]signature)
	rs.hashToMark = make(map[[sha1.Size]byte]markidx)
	rs.extractor = extractor
	rs.baton = control.baton
	return rs
}

// getParents returns the list of commit IDs of a commit's parents.
func (rs *RepoStreamer) getParents(rev string) []string {
	return rs.parents[rev]
}

// getCommitter returns the committer's ID/date as a string.
func (rs *RepoStreamer) getCommitter(rev string) string {
	return rs.meta[rev].ci
}

// getAuthors returns a string list of the authors' names and email addresses.
func (rs *RepoStreamer) getAuthors(rev string) []string {
	return []string{rs.meta[rev].ai}
}

// fileSetAt returns the set of all files visible at a revision
func (rs *RepoStreamer) fileSetAt(revision string) orderedStringSet {
	var fs orderedStringSet
	for key := range rs.visibleFiles[revision] {
		fs.Add(key)
	}
	// Warning: order is nondeterministic
	return fs
}

func (rs *RepoStreamer) extract(repo *Repository, vcs *VCS) (_repo *Repository, err error) {
	if !rs.extractor.isClean() {
		return nil, fmt.Errorf("repository directory has unsaved changes")
	}

	//control.baton.startProcess("Extracting", "")
	//defer rs.baton.endProcess()

	defer func(r **Repository, e *error) {
		if thrown := catch("extractor", recover()); thrown != nil {
			if strings.HasPrefix(thrown.class, "extractor") {
				*e = errors.New(thrown.message)
				*r = nil
			}
		}
	}(&repo, &err)

	rs.extractor.preExtract()
	repo.makedir("extract")
	front := fmt.Sprintf("#reposurgeon sourcetype %s\n", vcs.name)
	repo.addEvent(newPassthrough(repo, front))

	err = rs.extractor.gatherRevisionIDs(rs)
	if err != nil {
		return nil, fmt.Errorf("while gathering revisions: %v", err)
	}
	rs.baton.twirl()
	err = rs.extractor.gatherCommitData(rs)
	if err != nil {
		return nil, fmt.Errorf("while gathering commit data: %v", err)
	}
	rs.baton.twirl()
	err = rs.extractor.gatherAllReferences(rs)
	if err != nil {
		return nil, fmt.Errorf("while gathering tag/branch refs: %v", err)
	}
	rs.baton.twirl()
	// Sort branch/tag references by target revision ID, earliest first
	// Needs to be done before branch coloring because the simulation
	// of the Git branch-coloring algorithm needs it.  Also controls the
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
	sort.Stable(rs.refs)
	rs.baton.twirl()
	rs.extractor.colorBranches(rs)

	var uncolored []string
	for _, revision := range rs.revlist {
		if rs.meta[revision] == nil {
			rs.meta[revision] = new(CommitMeta)
		}
		if rs.meta[revision].branch == "" {
			uncolored = append(uncolored, revision)
		}
	}

	if len(uncolored) > 0 {
		if control.isInteractive() {
			return nil, fmt.Errorf("missing branch attribute for %v", uncolored)
		}
		return nil, fmt.Errorf("some branches do not have local ref names")
	}
	rs.baton.twirl()

	// these two functions should change only in sync
	//shortdump := func(hash [sha1.Size]byte) string {
	//	return fmt.Sprintf("%02x%02x%02x%02x%02x%02x",
	//		hash[0], hash[1], hash[2], hash[3], hash[4], hash[5])
	//}
	trunc := func(instr string) string {
		return instr[:12]
	}

	rs.baton.startProgress("extracting commits", uint64(len(rs.revlist)))
	consume := make([]string, len(rs.revlist))
	copy(consume, rs.revlist)
	for revcount, revision := range consume {
		// Perform housekeeping every 1000 commits
		if (revcount%1000) == 0 && revcount != 0 {
			err = rs.extractor.keepHouse()
			if err != nil {
				panic(throw("extract", "Extractor housekeeping failed: %v", err))
			}
		}
		commit := newCommit(repo)
		rs.baton.twirl()
		present := rs.extractor.manifest(revision)
		//if logEnable(logEXTRACT) {logit("%s: present %v", trunc(revision), present)}
		parents := rs.getParents(revision)
		attrib, err := newAttribution(rs.getCommitter(revision))
		if err != nil {
			panic(throw("extract", "garbled commit attribution: %v", err))
		}
		commit.committer = *attrib
		for _, a := range rs.getAuthors(revision) {
			attrib, err = newAttribution(a)
			if err != nil {
				panic(throw("extract", "garbled author attribution: %v", err))
			}
			commit.authors = append(commit.authors, *attrib)
		}
		for _, rev := range parents {
			commit.addParentCommit(rs.commitMap[rev])
		}
		commit.setBranch(rs.meta[revision].branch)
		commit.Comment = rs.extractor.getComment(revision)
		//if debugEnable(logEXTRACT) {
		//	msg := strconv.Quote(commit.Comment)
		//	logit("%s: comment '%s'", trunc(revision), msg)
		//}
		// Git fast-import constructs the tree from the first parent only
		// for a merge commit; fileops from all other parents have to be
		// added explicitly.
		rs.visibleFiles[revision] = make(map[string]signature)
		if len(parents) > 0 {
			parent := parents[0]
			for k, v := range rs.visibleFiles[parent] {
				rs.visibleFiles[revision][k] = v
			}
		}

		//if logEnable(logEXTRACT) {logit("%s: visible files '%s'", trunc(revision), rs.visibleFiles[revision])}

		if len(present) > 0 {
			fileList := newOrderedStringSet()
			for _, me := range present {
				fileList.Add(me.pathname)
				if isdir(me.pathname) {
					continue
				}
				if mark, ok := rs.hashToMark[me.sig.hashval]; ok {
					//if debugEnable(logEXTRACT) {
					//	logit("%s: %s has old hash %v", trunc(revision), me.pathname, shortdump(me.sig.hashval))
					//}
					// The file's hash corresponds
					// to an existing blob;
					// generate modify, copy, or
					// rename as appropriate.
					if _, ok := rs.visibleFiles[revision][me.pathname]; !ok || rs.visibleFiles[revision][me.pathname] != *me.sig {
						//if logEnable(logEXTRACT) {logit("%s: update for %s", trunc(revision), me.pathname)}
						found := false
						var deletia []string
						for _, item := range deletia {
							delete(rs.visibleFiles[revision], item)
						}
						if !found {
							op := newFileOp(repo)
							op.construct(opM, me.sig.perms, mark.String(), me.pathname)
							commit.appendOperation(op)
						}
					}
				} else {
					// Content hash doesn't match
					// any existing blobs
					//if logEnable(logEXTRACT) {
					//	logit("%s: %s has new hash %v", trunc(revision), me.pathname, shortdump(me.sig.hashval))
					//}
					blobmark := markNumber(repo.newmark())
					rs.hashToMark[me.sig.hashval] = blobmark
					// Actual content enters the representation
					blob := newBlob(repo)
					blob.setMark(blobmark.String())
					//if logEnable(logEXTRACT) {logit("%s: blob gets mark %s", trunc(revision), blob.mark)}
					blobfile := blob.getBlobfile(true)
					err = rs.extractor.catFile(revision, me.pathname, blobfile)
					if err != nil {
						panic(throw("extract", "%s: failed to extract file contents for %s: %v", trunc(revision), me.pathname, err))
					}
					stat, err := os.Stat(blobfile)
					if err != nil {
						panic(throw("extract", "%s: failed to stat blobfile for %s: %v", trunc(revision), me.pathname, err))
					}
					blob.size = stat.Size()
					repo.addEvent(blob)
					// Its new fileop is added to the commit
					op := newFileOp(repo)
					op.construct(opM, me.sig.perms, blobmark.String(), me.pathname)
					commit.appendOperation(op)
				}
				rs.visibleFiles[revision][me.pathname] = *me.sig
			}
			removed := rs.fileSetAt(revision).Subtract(fileList)
			for _, tbd := range removed {
				op := newFileOp(repo)
				op.construct(opD, tbd)
				commit.appendOperation(op)
				delete(rs.visibleFiles[revision], tbd)
			}
		}
		if len(parents) == 0 { // && commit.Branch != "refs/heads/master"
			reset := newReset(repo, commit.Branch, commit.mark, "")
			repo.addEvent(reset)
		}
		commit.simplify()
		commit.legacyID = revision
		newprops := newOrderedMap()
		commit.properties = &newprops
		rs.commitMap[revision] = commit
		commit.setMark(repo.newmark())
		//if logEnable(logEXTRACT) {logit("%s: commit gets mark %s (%d ops)", trunc(revision), commit.mark, len(commit.operations()))}
		repo.addEvent(commit)
		rs.baton.percentProgress(uint64(revcount))
	}
	rs.baton.endProgress()
	// Now append branch reset objects
	// Note: we time-sort these to ensure that the ordering is
	// (a) deterministic, and (b) easily understood.
	sort.SliceStable(rs.refs.keys, func(i, j int) bool {
		refToCommit := func(refname string) *Commit {
			return rs.commitMap[rs.refs.dict[refname]]
		}
		a := refToCommit(rs.refs.keys[i])
		b := refToCommit(rs.refs.keys[j])
		m, _ := strconv.Atoi(a.mark[1:])
		n, _ := strconv.Atoi(b.mark[1:])
		if m < n {
			return true
		}
		if m == n && !a.committer.date.timestamp.After(b.committer.date.timestamp) {
			return true
		}
		return false
	})
	for _, resetname := range rs.refs.keys {
		if !strings.Contains(resetname, "/tags/") {
			committish := rs.commitMap[rs.refs.get(resetname)].mark
			if committish == "" {
				panic(throw("extractor", "could not get a mark for the target of %s", resetname))
			}

			reset := newReset(repo, resetname, committish, "")
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
		if ok {
			tag.remember(repo, c.mark)
			repo.addEvent(&tag)
		} else {
			return nil, fmt.Errorf("no commit corresponds to %s", tag.committish)
		}
	}
	rs.extractor.postExtract(repo)
	repo.vcs = vcs
	return repo, err
}

/**************************************************************************

Experimental ClearCase extractor code begins here

See https://stackoverflow.com/questions/60362158/in-clearcase-need-cli-invocation-to-list-all-revisions/60363075#60363075

Commands used:

cleartool lsbl -fmt "%n:%m:%[permissions]p:%[owner]Fp:%Nd":%l
   %n is the full name of the element.
   %m is the element type - typically file or directory.
   %[permissions]p is file or directory permissions in rwx format.
   %[owner]Fp is the user ID of the change owner.
   %Nd will be yyyymmdd.time date; time is local in 24-hour format.
   %l will be a comma-separated list of labels for this revision.
   This command requires UCM.

* Need one to get the parent of revision 0 on a branch.

* Need one to get content from revision

* Need one to get comment from revision

* Need one to get filename

We won't need a branch-coloring algorithm, as all revision
names contain a branch. There are no annotated tags.

How do we extract merge information?

Rescue per-revision attributes?


**************************************************************************/

// end
