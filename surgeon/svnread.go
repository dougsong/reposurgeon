// The rendezvous between parsing and object building for git import
// streams is pretty trivial and best done inline in the parser
// because reposurgeon's internal structures are designed to match
// those entities. For Subversion dumpfiles, on the other hand,
// there's a fair bit of impedance-matching required.  That happens
// in this module.
//
// The single entry point is parseSubversion(), which extends
// RepoStreamer.  The result of calling it is to fill in the repo
// member of the calling instance with a repository state.
//
// The Subversion dumpfile format that this reads is documented at
//
// https://svn.apache.org/repos/asf/subversion/trunk/notes/dump-load-format.txt
//
// While great effort has been expended attempting to make it
// comprehensible, the poor semantic locality of the dumpfile format
// makes interpreting it a complex and messy task. Another source
// of confusion is the cvs2svn conversion debris frequently found
// in sufficiently old repositories; the hacks required to clean it out
// are pretty ugly.
//
// Accordingly, this code will probably make your head hurt.  That is,
// alas, a normal reaction.

// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"bytes"
	"context"
	"fmt"
	_ "net/http/pprof"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"runtime/trace"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
	"unsafe" // Actually safe - only uses Sizeof
)

var defaultIgnoreHash string

func init() {
	defaultIgnoreHash = fmt.Sprintf("%s", subversionDefaultIgnores)
}

type svnReader struct {
	revisions    []RevisionRecord
	streamview   []*NodeAction // All nodes in stream order
	hashmap      map[string]*NodeAction
	history      *History
	branchlinks  map[revidx]revidx
	splitCommits map[revidx]int
	// Filled in ProcessBranches
	markToSVNBranch map[string]string
	// a map from SVN branch names to a revision-indexed list of "last commits"
	// (not to be used directly but through lastRelevantCommit)
	// Filled in LinkFixups
	lastCommitOnBranchAt map[string][]*Commit
	// a map from SVN branch names to root commits (there can be several in case
	// of branch deletions since the commit recreating the branch is also root)
	// Filled in LinkFixups
	branchRoots map[string][]*Commit
}

// Helpers for branch analysis

// containingDir is a cut-down version of filepath.Dir
func containingDir(s string) string {
	i := strings.LastIndexByte(s, os.PathSeparator)
	if i <= 0 {
		return ""
	}
	return s[:i]
}

// trimSep is an ad-hoc version of strings.Trim(xxx, svnSep)
func trimSep(s string) string {
	if len(s) > 0 && s[0] == svnSep[0] {
		s = s[1:]
	}
	l := len(s)
	if l > 0 && s[l-1] == svnSep[0] {
		s = s[:l-1]
	}
	return s
}

// isDeclaredBranch returns true iff the user requested that this path be treated as a branch or tag.
func isDeclaredBranch(path string) bool {
	if path == "" {
		return false
	}
	np := trimSep(path)
	maybeBranch := false
	isNamespace := false
	for _, trial := range control.listOptions["svn_branchify"] {
		if trial == "*" {
			// Replace it by rvnSepWithStar so that the next test will
			// trim it to "", which is what containingDir() returns for
			// paths without any separator.
			trial = svnSepWithStar
		}
		l := len(trial)
		if l >= 2 && trial[l-1] == '*' && trial[l-2] == os.PathSeparator {
			trialBase := trial[:len(trial)-2]
			if trialBase == np {
				isNamespace = true
			} else if trialBase == containingDir(np) {
				maybeBranch = true
			}
		} else if (trial[l-1] == os.PathSeparator && trial[:l-1] == np) || trial == np {
			// Exact match
			return true
		}
	}
	return maybeBranch && !isNamespace
}

// splitSVNBranchPath splits a node path into the part that identifies the branch and the rest, as determined by the current branch map
func splitSVNBranchPath(path string) (string, string) {
	candidate := path
	for {
		split := strings.LastIndex(candidate, svnSep)
		if split == -1 {
			return "", path
		}
		candidate = path[:split]
		if isDeclaredBranch(candidate) {
			return candidate, path[split+1:]
		}
	}
}

// History is a type to manage a collection of PathMaps used as a history of file visibility.
type History struct {
	visible     map[revidx]*PathMap
	visibleHere *PathMap
	revision    revidx
}

func newHistory() *History {
	h := new(History)
	h.visible = make(map[revidx]*PathMap) // Visibility maps by revision ID
	h.visibleHere = newPathMap()          // Snapshot of visibility after current revision ops
	return h
}

func (h *History) apply(revision revidx, nodes []*NodeAction) {
	// Digest the supplied nodes into the history.
	// Build the visibility map for this revision.
	// Fill in the node from-sets.
	for _, node := range nodes {
		// Mutate the filemap according to copies
		if node.isCopy() {
			//assert node.fromRev < revision
			h.visibleHere.copyFrom(node.path, h.visible[node.fromRev],
				node.fromPath)
			logit(logFILEMAP, "r%d-%d: r%d~%s copied to %s",
				node.revision, node.index, node.fromRev, node.fromPath, node.path)
		}
		// Mutate the filemap according to adds/deletes/changes
		if node.action == sdADD && node.kind == sdFILE {
			h.visibleHere.set(node.path, node)
			logit(logFILEMAP, "r%d-%d: %s added", node.revision, node.index, node.path)
		} else if node.action == sdDELETE || (node.action == sdREPLACE && node.kind == sdDIR) {
			// This test can't be moved back further, because both
			// directory and file deletion ops are sometimes issued
			// without a Node-kind field.
			if node.kind == sdNONE {
				if _, ok := h.visibleHere.get(node.path); ok {
					node.kind = sdFILE
				} else {
					node.kind = sdDIR
				}
			}
			//logit(logFILEMAP, "r%d-%d: deduced type for %s", node.revision, node.index, node)
			// Snapshot the deleted paths before
			// removing them.
			node.fromSet = newPathMap()
			node.fromSet.copyFrom(node.path, h.visibleHere, node.path)
			h.visibleHere.remove(node.path)
			logit(logFILEMAP, "r%d-%d: %s deleted",
				node.revision, node.index, node.path)
		} else if (node.action == sdCHANGE || node.action == sdREPLACE) && node.kind == sdFILE {
			h.visibleHere.set(node.path, node)
			logit(logFILEMAP, "r%d-%d: %s changed", node.revision, node.index, node.path)
		}
		control.baton.twirl()
	}
	h.visible[revision] = h.visibleHere.snapshot()

	for _, node := range nodes {
		if node.isCopy() {
			node.fromSet = newPathMap()
			node.fromSet.copyFrom(node.fromPath, h.visible[node.fromRev], node.fromPath)
		}
		control.baton.twirl()
	}

	h.revision = revision
	logit(logFILEMAP, "Filemap at %d: %v", revision, h.visible[revision])
}

func (h *History) getActionNode(revision revidx, source string) *NodeAction {
	p, _ := h.visible[revision].get(source)
	if p != nil {
		return p.(*NodeAction)
	}
	return nil
}

// Stream parsing
//

// Use numeric codes rather than (un-interned) strings
// to reduce working-set size.
const sdNONE = 0 // Must be integer zero
const sdFILE = 1
const sdDIR = 2
const sdADD = 1
const sdDELETE = 2
const sdCHANGE = 3
const sdREPLACE = 4
const sdNUKE = 5 // Not part of the Subversion data model

// If these don't match the constants above, havoc will ensue
var actionValues = [][]byte{[]byte("none"), []byte("add"), []byte("delete"), []byte("change"), []byte("replace")}
var pathTypeValues = [][]byte{[]byte("none"), []byte("file"), []byte("dir"), []byte("ILLEGAL-TYPE")}

// The reason for these suppressions is to avoid a huge volume of
// junk file properties - cvs2svn in particular generates them like
// mad.  We want to let through other properties that might carry
// useful information.
var ignoreProperties = map[string]bool{
	"svn:mime-type":  true,
	"svn:keywords":   true,
	"svn:needs-lock": true,
	"svn:eol-style":  true, // Don't want to suppress, but cvs2svn floods these.
}

// These properties, on the other hand, shouldn't be tossed out even
// if --ignore-properties is set.  svn:mergeinfo and svnmerge-integrated
// are not in this list because they need to be preserved conditionally
// on directories only.
var preserveProperties = map[string]bool{
	"cvs2svn:cvs-rev": true,
	"svn:executable":  true,
	"svn:externals":   true,
	"svn:ignore":      true,
	"svn:special":     true,
}

// Helpers for Subversion dumpfiles

func sdBody(line []byte) []byte {
	// Parse the body from a Subversion header line
	return bytes.TrimSpace(bytes.SplitN(line, []byte(":"), 2)[1])
}

func (sp *StreamParser) sdRequireHeader(hdr string) []byte {
	// Consume a required header line
	line := sp.readline()
	if !bytes.HasPrefix(line, []byte(hdr)) {
		sp.error("required header missing: " + hdr)
	}
	return sdBody(line)
}

func (sp *StreamParser) sdRequireSpacer() {
	line := sp.readline()
	if len(bytes.TrimSpace(line)) > 0 {
		sp.error("found " + strconv.Quote(string(line)) + " expecting blank line")
	}
}

func (sp *StreamParser) sdReadBlob(length int) []byte {
	// Read a Subversion file-content blob.
	buf := sp.read(length + 1)
	if buf[length] != '\n' {
		sp.error("EOL not seen where expected, Content-Length incorrect")
	}
	return buf[:length]
}

func (sp *StreamParser) sdReadProps(target string, checklength int) *OrderedMap {
	// Parse a Subversion properties section, return as an OrderedMap.
	props := newOrderedMap()
	start := sp.ccount
	for sp.ccount-start < int64(checklength) {
		line := sp.readline()
		logit(logSVNPARSE, "readprops, line %d: %q",
			sp.importLine, line)
		if bytes.HasPrefix(line, []byte("PROPS-END")) {
			// This test should be !=, but I get random
			// off-by-ones from real dumpfiles - I don't
			// know why.
			if sp.ccount-start < int64(checklength) {
				sp.error(fmt.Sprintf("expected %d property chars, got %d",
					checklength, sp.ccount-start))

			}
			break
		} else if len(bytes.TrimSpace(line)) == 0 {
			continue
		} else if line[0] == 'K' {
			payloadLength := func(s []byte) int {
				n, _ := strconv.Atoi(string(bytes.Fields(s)[1]))
				return n
			}
			key := string(sp.sdReadBlob(payloadLength(line)))
			line := sp.readline()
			if line[0] != 'V' {
				sp.error("property value garbled")
			}
			value := string(sp.sdReadBlob(payloadLength(line)))
			props.set(key, value)
			logit(logSVNPARSE,
				"readprops: on %s, setting %s = %q",
				target, key, value)
		}
	}
	return &props
}

func (sp *StreamParser) timeMark(label string) {
	sp.repo.timings = append(sp.repo.timings, TimeMark{label, time.Now()})
}

// Fast append avoids doing a full copy of the slice on every allocation
// Code trivially modified from AppendByte on "Go Slices: usage and internals".
func appendRevisionRecords(slice []RevisionRecord, data ...RevisionRecord) []RevisionRecord {
	m := len(slice)
	n := m + len(data)
	if n > cap(slice) { // if necessary, reallocate
		// allocate double what's needed, for future growth.
		newSlice := make([]RevisionRecord, max((n+1)*2, maxAlloc))
		copy(newSlice, slice)
		slice = newSlice
	}
	slice = slice[0:n]
	copy(slice[m:n], data)
	return slice
}

func (sp *StreamParser) parseSubversion(ctx context.Context, options *stringSet, baton *Baton, filesize int64) {
	defer trace.StartRegion(ctx, "SVN phase 1: read dump file").End()
	sp.revisions = make([]RevisionRecord, 0)
	sp.hashmap = make(map[string]*NodeAction)
	sp.splitCommits = make(map[revidx]int)
	sp.branchlinks = make(map[revidx]revidx)

	trackSymlinks := newOrderedStringSet()
	propertyStash := make(map[string]*OrderedMap)

	baton.startProgress("SVN phase 1: read dump file", uint64(filesize))
	for {
		line := sp.readline()
		if len(line) == 0 {
			break
		} else if len(bytes.TrimSpace(line)) == 0 {
			continue
		} else if bytes.HasPrefix(line, []byte(" # reposurgeon-read-options:")) {
			payload := bytes.Split(line, []byte(":"))[1]
			*options = (*options).Union(newStringSet(strings.Fields(string(payload))...))
		} else if bytes.HasPrefix(line, []byte("UUID:")) {
			sp.repo.uuid = string(sdBody(line))
		} else if bytes.HasPrefix(line, []byte("Revision-number: ")) {
			// Begin Revision processing
			logit(logSVNPARSE, "revision parsing, line %d: begins", sp.importLine)
			revint, rerr := strconv.Atoi(string(sdBody(line)))
			if rerr != nil {
				panic(throw("parse", "ill-formed revision number: "+string(line)))
			}
			revision := intToRevidx(revint)
			plen := parseInt(string(sp.sdRequireHeader("Prop-content-length")))
			sp.sdRequireHeader("Content-length")
			sp.sdRequireSpacer()
			props := *sp.sdReadProps("commit", plen)
			// Parsing of the revision header is done
			var node *NodeAction
			nodes := make([]*NodeAction, 0)
			plen = -1
			tlen := -1
			// Node list parsing begins
			for {
				line = sp.readline()
				logit(logSVNPARSE, "node list parsing, line %d: %q",
					sp.importLine, line)
				if len(line) == 0 {
					break
				} else if len(bytes.TrimSpace(line)) == 0 {
					if node == nil {
						continue
					} else {
						if plen > -1 {
							node.props = sp.sdReadProps(node.path, plen)
							if plen > 1 {
								node.propchange = true
							}
						}
						if tlen > -1 {
							start := sp.tell()
							text := sp.sdReadBlob(tlen)
							node.blob = newBlob(sp.repo)
							node.blob.setContent(text, start)
							// Ugh - cope with strange undocumented Subversion
							// format for storing links.  Apparently the dumper
							// puts "link " in front of the path and the loader
							// (or at least git-svn) removes it.  But the link
							// op is only marked with property svn:special on
							// creation, on modification.  So we have to track
							// which paths are currently symlinks, && take off
							// that mark when a path is deleted in case it
							// later gets recreated as a non-sym link.
							if bytes.HasPrefix(text, []byte("link ")) {
								if node.hasProperties() && node.props.has("svn:special") {
									trackSymlinks.Add(node.path)
								}
								if trackSymlinks.Contains(node.path) {
									node.blob.setContent(
										text[5:], start+5)
								}
							}
						}
						node.revision = revision
						// If there are property changes on this node, stash
						// them so they will be propagated forward on later
						// nodes matching this path but with no property fields
						// of their own.
						if node.propchange {
							propertyStash[node.path] = copyOrderedMap(node.props)
						} else if node.action == sdADD && node.fromPath != "" {
							//Contiguity assumption here
							for _, oldnode := range sp.revisions[node.fromRev].nodes {
								if oldnode.path == node.fromPath && oldnode.propchange {
									propertyStash[node.path] = oldnode.props
								}
							}
							//fmt.Fprintf(os.Stderr, "Copy node %d:%s stashes %s\n", node.revision, node.path, sp.propertyStash[node.path])
						}
						if node.action == sdDELETE {
							if _, ok := propertyStash[node.path]; ok {
								delete(propertyStash, node.path)
							}
						} else if !node.propchange {
							// The forward propagation.  Importanntly, this
							// also forwards empty property sets, which are
							// different from having no properties.
							node.props = propertyStash[node.path]
						}
						if !node.isBogon() {
							logit(logSVNPARSE, "node parsing, line %d: node %s appended", sp.importLine, node)
							node.index = intToNodeidx(len(nodes) + 1)
							nodes = append(nodes, node)
							sp.streamview = append(sp.streamview, node)
							if logEnable(logEXTRACT) {
								logit(logEXTRACT, fmt.Sprintf("r%d-%d: %s", node.revision, node.index, node))
							} else if node.kind == sdDIR &&
								node.action != sdCHANGE && logEnable(logTOPOLOGY) {
								logit(logSHOUT, node.String())
							}
						}
						node = nil
					}
				} else if bytes.HasPrefix(line, []byte("Revision-number: ")) {
					sp.pushback(line)
					break
				} else if bytes.HasPrefix(line, []byte("Node-path: ")) {
					// Node processing begins
					// Normal case
					if node == nil {
						node = new(NodeAction)
					}
					node.path = string(sdBody(line))
					plen = -1
					tlen = -1
				} else if bytes.HasPrefix(line, []byte("Node-kind: ")) {
					// svndumpfilter sometimes emits output
					// with the node kind first
					if node == nil {
						node = new(NodeAction)
					}
					kind := sdBody(line)
					for i, v := range pathTypeValues {
						if bytes.Equal(v, kind) {
							node.kind = uint8(i & 0xff)
						}
					}
					if node.kind == sdNONE {
						sp.error(fmt.Sprintf("unknown kind %s", kind))
					}
				} else if bytes.HasPrefix(line, []byte("Node-action: ")) {
					if node == nil {
						node = new(NodeAction)
					}
					action := sdBody(line)
					for i, v := range actionValues {
						if bytes.Equal(v, action) {
							node.action = uint8(i & 0xff)
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
				} else if bytes.HasPrefix(line, []byte("Node-copyfrom-rev: ")) {
					if node == nil {
						node = new(NodeAction)
					}
					uintrev, _ := strconv.ParseUint(string(sdBody(line)), 10, int((unsafe.Sizeof(revidx(0))*8)) & ^int(0))
					node.fromRev = revidx(uintrev & uint64(^revidx(0)))
				} else if bytes.HasPrefix(line, []byte("Node-copyfrom-path: ")) {
					if node == nil {
						node = new(NodeAction)
					}
					node.fromPath = string(sdBody(line))
				} else if bytes.HasPrefix(line, []byte("Text-copy-source-md5: ")) {
					if node == nil {
						node = new(NodeAction)
					}
					//node.fromHash = string(sdBody(line))
				} else if bytes.HasPrefix(line, []byte("Text-content-md5: ")) {
					node.contentHash = string(sdBody(line))
				} else if bytes.HasPrefix(line, []byte("Text-content-sha1: ")) {
					continue
				} else if bytes.HasPrefix(line, []byte("Text-content-length: ")) {
					tlen = parseInt(string(sdBody(line)))
				} else if bytes.HasPrefix(line, []byte("Prop-content-length: ")) {
					plen = parseInt(string(sdBody(line)))
				} else if bytes.HasPrefix(line, []byte("Content-length: ")) {
					continue
				} else {
					logit(logSVNPARSE, "node list parsing, line %d: uninterpreted line %q", sp.importLine, line)
					continue
				}
				// Node processing ends
				baton.twirl()
			}
			// Node list parsing ends
			newRecord := newRevisionRecord(nodes, props, revision)
			logit(logSVNPARSE, "revision parsing, line %d: r%d ends with %d nodes", sp.importLine, newRecord.revision, len(newRecord.nodes))
			sp.revisions = appendRevisionRecords(sp.revisions, *newRecord)
			sp.repo.legacyCount++
			if sp.repo.legacyCount == maxRevidx-1 {
				panic("revision counter overflow, recompile with a larger size")
			}
			// End Revision processing
			baton.percentProgress(uint64(sp.ccount))
			if control.readLimit > 0 && uint64(sp.repo.legacyCount) > control.readLimit {
				logit(logSHOUT, "read limit %d reached.", control.readLimit)
				break
			}
		}
	}
	control.baton.endProgress()
	if control.readLimit > 0 && uint64(sp.repo.legacyCount) <= control.readLimit {
		logit(logSHOUT, "EOF before readlimit.")
	}
	logit(logSVNPARSE, "revision parsing, line %d: ends with %d records", sp.importLine, sp.repo.legacyCount)
	sp.timeMark("parsing")
	sp.svnProcess(ctx, *options, baton)
}

const maxRevidx = int(^revidx(0)) // Use for bounds-checking in range loops.

func intToRevidx(revint int) revidx {
	return revidx(revint & int(^revidx(0)))
}

func intToNodeidx(nodeint int) nodeidx {
	return nodeidx(nodeint & int(^nodeidx(0)))
}

// NodeAction represents a file-modification action in a Subversion dump stream.
type NodeAction struct {
	path        string
	fromPath    string
	contentHash string
	//fromHash    string
	blob       *Blob
	props      *OrderedMap
	fromSet    *PathMap
	blobmark   markidx
	revision   revidx
	fromRev    revidx
	index      nodeidx
	fromIdx    nodeidx
	kind       uint8
	action     uint8 // initially sdNONE
	propchange bool
}

func (action NodeAction) String() string {
	out := "<NodeAction: "
	out += fmt.Sprintf("r%d-%d", action.revision, action.index)
	out += " " + string(actionValues[action.action])
	out += " " + string(pathTypeValues[action.kind])
	out += " '" + action.path + "'"
	if action.fromRev != 0 {
		out += fmt.Sprintf(" from=%d", action.fromRev) + "~" + action.fromPath
	}
	//if action.fromSet != nil && !action.fromSet.isEmpty() {
	//	out += " sources=" + action.fromSet.String()
	//}
	if action.hasProperties() && action.props.Len() > 0 {
		out += " props=" + action.props.vcString()
	}
	return out + ">"
}

func (action NodeAction) hasProperties() bool {
	return action.props != nil
}

func (action NodeAction) isCopy() bool {
	return action.fromPath != ""
}

func (action NodeAction) isBogon() bool {
	// if node.props is None, no property section.
	// if node.blob is None, no text section.
	// Delete actions may be issued without a dir or file kind
	if !((action.action == sdCHANGE || action.action == sdADD || action.action == sdDELETE || action.action == sdREPLACE) &&
		(action.kind == sdFILE || action.kind == sdDIR || action.action == sdDELETE) &&
		((action.fromRev == 0) == (action.fromPath == ""))) {
		logit(logSHOUT, "forbidden operation in dump stream (versoin 7?) at r%d: %s", action.revision, action)
		return true
	}

	// This guard filters out the empty nodes produced by format 7
	// dumps.  Not necessarily a bogon, actually/
	if action.action == sdCHANGE && !action.hasProperties() && action.blob == nil && !action.isCopy() {
		logit(logEXTRACT, "empty node rejected at r%d: %v", action.revision, action)
		return true
	}

	if !(action.blob != nil || action.hasProperties() ||
		action.fromRev != 0 || action.action == sdADD || action.action == sdDELETE) {
		logit(logSHOUT, "malformed node in dump stream at r%d: %s", action.revision, action)
		return true
	}
	if action.kind == sdNONE && action.action != sdDELETE {
		logit(logSHOUT, "missing type on a non-delete node r%d: %s", action.revision, action)
		return true
	}

	if (action.action != sdADD && action.action != sdREPLACE) && action.isCopy() {
		logit(logSHOUT, "invalid type in node with from revision r%d: %s", action.revision, action)
		return true
	}

	return false
}

func (action NodeAction) deleteTag() string {
	return action.path[:len(action.path)] + fmt.Sprintf("-deleted-r%d-%d", action.revision, action.index)
}

func (action NodeAction) hasDeleteTag() bool {
	return strings.Contains(action.path, "-deleted-")
}

// RevisionRecord is a list of NodeActions at a rev in a Subversion dump
// Note that the revision field differs from the index in the revisions
// array only if the stream is complete (missing leading revisions or
// has gaps). Processing of such streams is not well-tested and will
// probably fail.
type RevisionRecord struct {
	log      string
	date     string
	author   string
	nodes    []*NodeAction
	props    OrderedMap
	revision revidx
}

func newRevisionRecord(nodes []*NodeAction, props OrderedMap, revision revidx) *RevisionRecord {
	rr := new(RevisionRecord)
	rr.revision = revision
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

func walkRevisions(revs []RevisionRecord, hook func(int, *RevisionRecord)) {
	if control.flagOptions["serial"] {
		for i := range revs {
			hook(i, &revs[i])
		}
		return
	}

	var (
		maxWorkers = runtime.GOMAXPROCS(0)
		channel    = make(chan int, maxWorkers)
		done       = make(chan bool, maxWorkers)
	)

	// Create the workers that will loop though events
	for n := 0; n < maxWorkers; n++ {
		go func() {
			// The for loop will stop when channel is closed
			for i := range channel {
				hook(i, &revs[i])
			}
			done <- true
		}()
	}

	// Populate the channel with the events
	for i := range revs {
		channel <- i
	}
	close(channel)

	// Wait for all workers to finish
	for n := 0; n < maxWorkers; n++ {
		<-done
	}
}

// Cruft recognizers
var cvs2svnTagBranchRE = regexp.MustCompile("This commit was manufactured by cvs2svn to create ")

var blankline = regexp.MustCompile(`(?m:^\s*\n)`)

// Separator used for split part in a processed Subversion ID.
const splitSep = "."

// Path separator as found in Subversion dump files. Isolated because
// it might be "\" on OSes not to be mentioned in polite company.
var svnSep = string([]byte{os.PathSeparator})
var svnSepWithStar = svnSep + "*"

func nodePermissions(node NodeAction) string {
	// Fileop permissions from node properties
	if node.hasProperties() {
		if node.props.has("svn:executable") {
			return "100755"
		} else if node.props.has("svn:special") {
			// Map to git symlink, which behaves the same way.
			// Blob contents is the path the link should resolve to.
			return "120000"
		}
	}
	return "100644"
}

// Try to figure out who the ancestor of this node is.
func (sp *StreamParser) seekAncestor(node *NodeAction, hash map[string]*NodeAction) *NodeAction {
	/*
		// FIXME: This should replace the last bit of ancestry creatiion done in a later phase.
		if node.contentHash != "" {
			if hashlook, ok := sp.hashmap[node.contentHash]; ok {
				logit(logEXTRACT, "r%d: blob of %s matches existing hash %s, assigning '%s' from %s",
					node.revision, node, node.contentHash, hashlook.blobmark.String(), hashlook)
				return hashlook
			}
		}
	*/

	var lookback *NodeAction
	if node.fromPath != "" {
		// Try first via fromRev/fromPath.  The reason
		// we have to use the filemap at the copy
		// source rather than simply walking through
		// the old nodes to look for the path match is
		// because the source revision might have been
		// the target of a directory copy that created
		// the ancestor we are looking for
		lookback = sp.history.getActionNode(node.fromRev, node.fromPath)
		if lookback != nil {
			logit(logTOPOLOGY, "r%d~%s -> %v (via filemap of %d)",
				node.revision, node.path, lookback, node.fromRev)
		}
	} else if node.action != sdADD {
		// The ancestor could be a file copy node expanded
		// from an earlier expanded directory copy.
		if trial, ok := hash[node.path]; ok {
			return trial
		}
		// Ordinary inheritance, no node copy.
		// Contiguity assumption here
		lookback = sp.history.getActionNode(node.revision-1, node.path)
	}

	// We reach here with lookback still nil if the node is a non-copy add.
	if lookback == nil && node.isCopy() && !strings.HasSuffix(node.path, ".gitignore") {
		logit(logSHOUT, "r%d~%s: missing ancestor node for non-.gitignore",
			node.revision, node.path)
	}

	// If there is a content hash, it should match.
	//if lookback != nil && lookback.contentHash != "" && node.fromHash != "" && lookback.contentHash != node.fromHash {
	//	logit(logSHOUT, "r%d~%s: content hash does not match for copy",
	//		node.revision, node.path)
	//}

	return lookback
}

func (sp *StreamParser) svnProcess(ctx context.Context, options stringSet, baton *Baton) {
	// Subversion actions to import-stream commits.

	// This function starts with a deserialization of a Subversion
	// import stream that carres all the information in it. It
	// proceeds through a sequence of phases to massage the data
	// into a form from which a sequence of Gitspace objects
	// isomorphic to a GFIS (Git fast-import stream) can be
	// generated.
	//
	// At a high level, a Subversion stream dump is not unlike a GFIS -
	// a sequence of addition/modification operations with parent-child
	// relationships corresponding to time order. But there are two central
	// problems this code has to solve.
	//
	// One is a basic ontological mismatch between Subversions's
	// model of revision history and Git's.  A Subversion history
	// is a sequence of surgical operations on a file tree in
	// which some namespaces have onventional roles (tags/*,
	// branches/*, trunk).  In Subversion-land it's perfectly
	// legitimate to start a branch, delete it, and then recreate
	// it in a later revision.  The content on the deleted branch
	// has to be kept in the revision store because content on
	// it might have been grafted forward while it was live.
	//
	// Git has a more timeless view. Tree structure isn't central
	// at all. The model is a DAG (directed acyclic graph) of
	// revisions, ordered by parent-child relationships. When a
	// branch is deleted the content is just gone - you may
	// recreate a branch with thec same name later, but you never
	// have to be cognizamt of the content on the old branch.
	//
	// The other major issue is that Subversion dump streams have
	// poor semantic locality.  One of the basic tree-surgery
	// operations expressed in them is a wildcarded directory copy
	// - copy everything in the source directory at a specified
	// revision to the target directory in present time.  To
	// resolve this wildcard, one may have to look arbitrarily far
	// back in the history.
	//
	// A minor issue is that branch creations and tags are both
	// biormally expressed in stream dumps as commit-like objwcts
	// with no attached file delete/add/modify operations.  There
	// is no ntural place for these in gitspace, but the comments
	// in them could be interesting.  They're saved as synthetic
	// tags, most of which should typically be junked after conversion
	//
	// Search forward for the word "Phase" to find phase descriptions.
	//
	// An important invariant of ths code is that once a NodeAction is
	// created, it is never copied.  Though there may be multiple pointers
	// to the record for node N of revision M, they all point to the
	// same structure originally created to deserialize it.
	//
	timeit := func(tag string) {
		runtime.GC()
		sp.timeMark(tag)
		if control.flagOptions["bigprofile"] {
			e := len(sp.repo.timings) - 1
			fmt.Fprintf(baton, "%s:%v...", tag, sp.repo.timings[e].stamp.Sub(sp.repo.timings[e-1].stamp))
		} else {
			baton.twirl()
		}
	}

	sp.repo.addEvent(newPassthrough(sp.repo, "#reposurgeon sourcetype svn\n"))

	svnFilterProperties(ctx, sp, options, baton)
	timeit("filterprops")
	svnBuildFilemaps(ctx, sp, options, baton)
	timeit("filemaps")
	svnExpandCopies(ctx, sp, options, baton)
	timeit("expand")
	svnGenerateCommits(ctx, sp, options, baton)
	timeit("commits")
	svnSplitResolve(ctx, sp, options, baton)
	timeit("splits")
	svnProcessBranches(ctx, sp, options, baton)
	timeit("branches")
	svnDisambiguateRefs(ctx, sp, options, baton)
	timeit("disambiguate")
	svnLinkFixups(ctx, sp, options, baton)
	timeit("links")
	svnProcessMergeinfos(ctx, sp, options, baton)
	timeit("mergeinfo")
	svnProcessIgnores(ctx, sp, options, baton)
	timeit("ignores")
	svnProcessJunk(ctx, sp, options, baton)
	timeit("dejunk")
	svnProcessDebubble(ctx, sp, options, baton)
	timeit("debubbling")
	svnProcessRenumber(ctx, sp, options, baton)
	timeit("renumbering")

	// Treat this in-core state as though it was read from an SVN repo
	sp.repo.hint("svn", "", true)
}

func svnFilterProperties(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase 2:
	// Filter properties, throwing out everything that is not going to be of interest
	// to later analysis. Log warnings where we might be throwing away information.
	// Canonicalize svn:ignore propeerties (no more convenient place to do it).
	//
	// We could in theory parallwelize this, but it's cheap even on very large repositories
	// so we chhose to to not incur additional code comp;exity here.
	//
	defer trace.StartRegion(ctx, "SVN Phase 2: filter properties").End()
	logit(logEXTRACT, "SVN Phase 2: filter properties")
	baton.startProgress("SVN phase 2: filter properties", uint64(len(sp.streamview)))
	for si, node := range sp.streamview {
		// Handle per-path properties.
		if node.hasProperties() {
			// Some properties should be quietly ignored
			for k := range ignoreProperties {
				node.props.delete(k)
			}
			// Remove blank lines from svn:ignore property values.
			if node.props.has("svn:ignore") {
				oldIgnore := node.props.get("svn:ignore")
				newIgnore := blankline.ReplaceAllLiteralString(oldIgnore, "")
				node.props.set("svn:ignore", newIgnore)
			}
			tossThese := make([][2]string, 0)
			for prop, val := range node.props.dict {
				// Pass through the properties that can't be processed until we're ready to
				// generate commits. Delete the rest.
				if !preserveProperties[prop] && !((prop == "svn:mergeinfo" || prop == "svnmerge-integrated") && node.kind == sdDIR) {
					tossThese = append(tossThese, [2]string{prop, val})
					node.props.delete(prop)
				}
			}
			if !options.Contains("--ignore-properties") {
				// It would be good to emit messages
				// when a nonempty property set on a
				// path is entirely cleared.
				// Unfortunately, the Subversion dumper
				// spams empty property sets, emitting
				// them lots of places they're not
				// necessary.
				if len(tossThese) > 0 {
					logit(logSHOUT, "r%d#%d~%s properties set:", node.revision, node.index, node.path)
					for _, pair := range tossThese {
						logit(logSHOUT, "\t%s = %q", pair[0], pair[1])
					}
				}
			}
		}
		baton.percentProgress(uint64(si))
	}
	baton.endProgress()
	sp.streamview = nil // Allow GC
}

func svnBuildFilemaps(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase 3:
	// This is where we build file visibility maps. The visibility
	// map for each revision maps file paths to the Subversion
	// node for the version you see at that revision, which might
	// not have been modified for any number of revisions back,
	// If the path ever existed at any revision, the only way it
	// can fail to be visible is if the last thing done to it was
	// a delete.
	//
	// This phase is moderately expensive, but once the maps are
	// built they render unnecessary compuations that would have
	// been prohibitively expensive in later passes. Notably the
	// maps are everything necessary to compute node ancestry.
	//
	// This phase has revision-order dependency in spades and
	// cannot be parallelized. After the filemaps are built they
	// should not be modified by later phases.  Part of their
	// purpose is to express the web of relationships between
	// entities in the stream in a timeless way so that later
	// operations *don't* need to have revision-order dependencies
	// and can be safely parallelized.
	//
	defer trace.StartRegion(ctx, "SVN Phase 3: build filemaps").End()
	logit(logEXTRACT, "SVN Phase 3: build filemaps")
	baton.startProgress("SVN phase 3: build filemaps", uint64(len(sp.revisions)))
	sp.history = newHistory()
	for ri, record := range sp.revisions {
		sp.history.apply(intToRevidx(ri), record.nodes)
		baton.percentProgress(uint64(ri))
	}
	baton.endProgress()
}

func svnExpandCopies(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase 4:
	// Subversion dump files have one serious nonlocality. One of
	// the stream operations is a wildcarded directory copy.  This
	// phase expands these so that all of the implied file add
	// operations become explicit.  This is the main thing for
	// which we needed the file visibility map.
	//
	// Note that the directory copy nodes are not removed, as they
	// may carry properties we're going to need later - notably
	// mergeinfo properties.  svn:ignore is handled here.
	//
	// This phase looks like it should have revision-order
	// dependencies, but it doesn't.  Having file visibility
	// information pre-computed for all revisions forestalls that.
	// Thus, it can be parallelized.
	//
	// This pass is almost entirely indifferent to Subversion
	// branch structure.  One exceptions in what it does to
	// directory delete operations.  On a branch directory a
	// Subversion delete becomes a Git deleteall; on a non-branch
	// directory it is expanded to a set of file deletes for the
	// contents of the directory.
	//
	// The reason for turning branch deletes into deletealls
	// is so that when an importer interprets them, it will
	// clobber the branch so that it's not visible from
	// any revision after the deletion. This is the intended behavor
	// of a Subversion D operation and is simpler that expanding
	// the D into a recursive delete of the directory contents
	//
	// This pass also notices branch structure when it checks
	// where it should create copies of the default .gitignore
	// file.  We want this to happen at branch roots before
	// the first fileop, and only at branch roots.
	//
	// The exit contract of this phase is that all file content
	// modifications are expressed as file ops, every one of
	// which has a computable ancestor node.  If an ancestor
	// couldn't be found, that is logged as an error condition
	// and the node is skipped. Such a log message implies
	// a metadata malformation.  Generated nodes are marked
	// for later redundancy checking.
	//
	// Its is also here that ignore properties on directory nodes
	// are mapped to nodes for .gitignore files, then removed.
	//
	defer trace.StartRegion(ctx, "SVN Phase 4: directory copy expansion").End()
	logit(logEXTRACT, "SVN Phase 4: directory copy expansion")

	baton.startProgress("SVN phase 4a: directory copy expansion", uint64(len(sp.revisions)))
	nobranch := options.Contains("--nobranch")
	count := 0
	walkRevisions(sp.revisions, func(ri int, record *RevisionRecord) {
		expandedNodes := make([]*NodeAction, 0)
		for _, node := range record.nodes {
			appendExpanded := func(newnode *NodeAction) {
				newnode.index = intToNodeidx(len(expandedNodes) + 1)
				newnode.revision = intToRevidx(ri)
				expandedNodes = append(expandedNodes, newnode)
			}
			// Starting with the nodes in the Subversion
			// dump, expand them into a set that unpacks
			// all directory operations into equivalent
			// sets of file operations.
			// We always preserve the unexpanded directory
			// node. Many of these won't have an explicit
			// gitspace representation, but they may carry
			// properties that we will require in later
			// phases.
			appendExpanded(node)
			if node.kind == sdDIR {
				// svnSep is appended to avoid collisions with path
				// prefixes.
				node.path += svnSep
				if node.fromPath != "" {
					node.fromPath += svnSep
				}
				// No special actions need to be taken when directories are added or changed, but see below for actions
				// that are taken in all cases.  The reason we suppress expansion on a declared branch is that
				// we are later going to turn this directory delete into a git deleteall for the branch.
				if node.action == sdDELETE || node.action == sdREPLACE {
					if !nobranch && isDeclaredBranch(node.path) {
						logit(logEXTRACT, "r%d-%d~%s: declaring as sdNUKE", node.revision, node.index, node.path)
						node.action = sdNUKE
					} else {
						// A delete or replace with no from set
						// can occur if the directory is empty.
						// We can just ignore that case. Otherwise...
						if node.fromSet != nil {
							node.fromSet.iter(func(child string, _ interface{}) {
								logit(logEXTRACT, "r%d-%d~%s: deleting %s", node.revision, node.index, node.path, child)
								newnode := new(NodeAction)
								newnode.path = child
								newnode.revision = node.revision
								newnode.action = sdDELETE
								newnode.kind = sdFILE
								appendExpanded(newnode)
							})
						}
					}
				}
				// Handle directory copies.
				if node.isCopy() {
					copyType := "directory"
					if isDeclaredBranch(node.path) && isDeclaredBranch(node.fromPath) {
						copyType = "branch"
					}
					logit(logEXTRACT, "r%d-%d: %s copy to %s from r%d~%s",
						node.revision, node.index, copyType, node.path, node.fromRev, node.fromPath)
					// Now generate copies for all files in the
					// copy source directory.
					node.fromSet.iter(func(source string, _ interface{}) {
						found := sp.history.getActionNode(node.fromRev, source)
						if found == nil {
							logit(logSHOUT, "r%d-%d: can't find ancestor of %s at r%d",
								node.revision, node.index, source, node.fromRev)
							return
						}
						subnode := new(NodeAction)
						subnode.path = node.path + source[len(node.fromPath):]
						subnode.revision = node.revision
						subnode.fromPath = found.path
						subnode.fromRev = found.revision
						//subnode.fromHash = found.contentHash
						subnode.props = found.props
						subnode.action = sdADD
						subnode.kind = sdFILE
						if logEnable(logTOPOLOGY) {
							logit(logTOPOLOGY, "r%d-%d: %s %s copy r%d~%s -> %s %s",
								node.revision, node.index, node.path, copyType,
								subnode.fromRev, subnode.fromPath, subnode.path, subnode)
						}
						appendExpanded(subnode)
					})
				}
				// Allow GC to reclaim fromSet storage, we no longer need it
				node.fromSet = nil
			}
		}
		sp.revisions[ri].nodes = expandedNodes
		count++
		baton.percentProgress(uint64(count))
	})
	baton.endProgress()

	baton.startProgress("SVN phase 4b: ancestry computations", uint64(len(sp.revisions)))
	for ri := range sp.revisions {
		// Compute ancestry links for all file nodes
		revisionPathHash := make(map[string]*NodeAction)
		var lastnode *NodeAction
		for j := range sp.revisions[ri].nodes {
			node := sp.revisions[ri].nodes[j]
			if lastnode != nil {
				revisionPathHash[lastnode.path] = lastnode
			}
			lastnode = node
			node.fromIdx = 0
			if node.kind == sdFILE {
				ancestor := sp.seekAncestor(node, revisionPathHash)
				// It is possible for ancestor to still be nil here,
				// if the node was a pure property change
				if ancestor != nil {
					node.fromRev = ancestor.revision
					node.fromIdx = ancestor.index
				}
			}
		}

		baton.percentProgress(uint64(ri))
	}

	baton.endProgress()

	// We don't need the revision maps after ancestry links are in place
	sp.history = nil
	// sp.hashmap
}

func svnGenerateCommits(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase 5:
	// Transform the revisions into a sequence of gitspace commits.
	// This is a deliberately literal translation that is near
	// useless in itself; no branch analysis, no tagification of
	// redundant commits, etc.  The goal is to get everything into
	// gitspace where we have good surgical tools.  Then we can
	// mutate it to a proper git DAG in small steps.
	//
	// The only Subversion metadata this does not copy into
	// commits is per-directory properties. We processed and
	// removed svn:ignore properties in the last phase, but
	// svn:mergeinfo properties remain, to be handled in a later
	// phase.
	//
	// Interpretation of svn:executable is done in this phase.
	// The commit branch is set here in case we want to dump a
	// --nobranch analysis, but the from and merge fields are not.
	// That will happen in a later phase.
	//
	// Revisions with no nodes are skipped here. This guarantees
	// being able to assign them to a branch later.
	//
	defer trace.StartRegion(ctx, "SVN Phase 5: build commits").End()
	logit(logEXTRACT, "SVN Phase 5: build commits")
	baton.startProgress("SVN phase 5: build commits", uint64(len(sp.revisions)))

	var lastcommit *Commit
	for ri, record := range sp.revisions {
		// Zero revision is never interesting - no operations, no
		// comment, no author, it's just a start marker for a
		// non-incremental dump.
		if record.revision == 0 {
			continue
		}

		logit(logEXTRACT, "Revision %d:", record.revision)

		commit := newCommit(sp.repo)
		ad := record.date
		if ad == "" {
			sp.error("missing required date field")
		}
		var au string
		if record.author != "" {
			au = record.author
		} else {
			au = "no-author"
		}
		if record.log != "" {
			commit.Comment = record.log
			if !strings.HasSuffix(commit.Comment, "\n") {
				commit.Comment += "\n"
			}
		}
		attribution := ""
		if strings.Count(au, "@") == 1 {
			// This is a thing that happens occasionally.  A DVCS-style
			// attribution (name + email) gets stuffed in a Subversion
			// author field
			// First, check to see if it's a fully-formed address
			if strings.Count(au, "<") == 1 && strings.Count(au, ">") == 1 && strings.Count(au, " ") > 0 {
				attribution = au + " " + ad
			} else {
				// Punt...
				parts := strings.Split(au, "@")
				au, ah := parts[0], parts[1]
				attribution = au + " <" + au + "@" + ah + "> " + ad
			}
		} else if options.Contains("--use-uuid") {
			attribution = fmt.Sprintf("%s <%s@%s> %s", au, au, sp.repo.uuid, ad)
		} else {
			attribution = fmt.Sprintf("%s <%s> %s", au, au, ad)
		}
		newattr, err := newAttribution(attribution)
		if err != nil {
			panic(throw("parse", "impossibly ill-formed attribution in dump stream at r%d", record.revision))
		}
		commit.committer = *newattr
		// Use this with just-generated input streams
		// that have wall times in them.
		if control.flagOptions["testmode"] {
			commit.committer.fullname = "Fred J. Foonly"
			commit.committer.email = "foonly@foo.com"
			commit.committer.date.timestamp = time.Unix(int64(ri*360), 0)
			commit.committer.date.setTZ("UTC")
		}
		if record.props.Len() > 0 {
			commit.properties = &record.props
			record.props.Clear()
		}

		commit.legacyID = fmt.Sprintf("%d", record.revision)

		for _, node := range record.nodes {
			if node.action == sdNONE {
				continue
			}

			if node.hasProperties() {
				if node.props.has("cvs2svn:cvs-rev") {
					cvskey := fmt.Sprintf("CVS:%s:%s", node.path, node.props.get("cvs2svn:cvs-rev"))
					sp.repo.legacyMap[cvskey] = commit
					node.props.delete("cvs2svn:cvs-rev")
				}
			}
			var ancestor *NodeAction
			if node.action == sdNUKE {
				logit(logEXTRACT, "r%d: deleteall %s", record.revision, node.path)
				// Generate a deletall operation, but with a path, contrary to
				// the git-fast-import specification. This is so that the pass
				// splitting the commits and setting the branch from the paths
				// will be able to affect this deleteall to the correct branch
				// then remove the spec-violating path.
				fileop := newFileOp(sp.repo)
				fileop.construct(deleteall)
				fileop.Path = node.path
				commit.appendOperation(fileop)
			} else if node.kind == sdFILE {
				// All .cvsignores should be ignored as remnants from
				// a previous up-conversion to Subversion.
				// This is a philosophical choice; we're taking the
				//users' Subversion settings as authoritative
				// rather than trying to mimic the exact CVS behavior.
				if strings.HasSuffix(node.path, ".cvsignore") && !options.Contains("--cvsignores") {
					continue
				}
				// Ignore and complain about explicit .gitignores
				// created, e.g, by git-svn.  In an ideal world we
				// would merge these with svn:ignore properties. but
				// this would be hairy and bug-prone. So we give
				// the user a heads-up and expect these to be
				// merged by hand.
				if strings.HasSuffix(node.path, ".gitignore") && !options.Contains("--user-ignores") {
					logit(logSHOUT, "r%d~%s: user-created .gitignore ignored.",
						node.revision, node.path)
					continue
				}
				if node.fromRev > 0 && node.fromIdx > 0 {
					ancestor = sp.revisions[node.fromRev].nodes[node.fromIdx-1]
				}
				// Propagate properties from the ancestor.
				if (node.action == sdADD || node.action == sdCHANGE) && ancestor != nil && !node.propchange {
					node.props = ancestor.props
				}
				if node.action == sdDELETE {
					//assert node.blob == nil
					fileop := newFileOp(sp.repo)
					fileop.construct(opD, node.path)
					logit(logEXTRACT, "%s turns off TRIVIAL", fileop)
					commit.appendOperation(fileop)
				} else if node.action == sdADD || node.action == sdCHANGE || node.action == sdREPLACE {
					if node.blob != nil {
						// FIXME: This ought to have been done earlier, during node expansion
						if lookback, ok := sp.hashmap[node.contentHash]; ok {
							logit(logEXTRACT, "r%d: blob of %s matches existing hash %s, assigning '%s' from %s",
								record.revision, node, node.contentHash, lookback.blobmark.String(), lookback)
							// Blob matches an existing one -
							// node was created by a
							// non-Subversion copy followed by
							// add.  Get the ancestry right,
							// otherwise parent pointers won't
							// be computed properly.
							ancestor = lookback
							node.fromPath = ancestor.fromPath
							node.fromRev = ancestor.fromRev
							node.blobmark = ancestor.blobmark
						}
						if node.blobmark == emptyMark {
							// This is the normal way new blobs get created
							node.blobmark = markNumber(node.blob.setMark(sp.repo.newmark()))
							logit(logEXTRACT, "r%d: %s gets new blob '%s'",
								record.revision, node, node.blobmark.String())
							// Blobs generated by reposurgeon
							// (e.g .gitignore content) have no
							// content hash.  Don't record
							// them, otherwise they'll all
							// collide :-)
							if node.contentHash != "" {
								sp.hashmap[node.contentHash] = node
							}
							sp.repo.addEvent(node.blob)
							sp.repo.declareSequenceMutation("adding new blob")
						}
					} else if ancestor != nil {
						node.blobmark = ancestor.blobmark
						logit(logEXTRACT, "r%d: %s gets blob '%s' from ancestor %s",
							record.revision, node, node.blobmark.String(), ancestor)
					} else {
						// This should never happen. If we can't find an ancesor for any node
						// it means the dumpfile is malformed.
						logit(logSHOUT, "r%d~%s: ancestor node is missing.",
							node.revision, node.path)
						continue
					}
					// This should never happen.  It indicates that file content is missing from the stream.
					if node.blobmark == emptyMark {
						logit(logSHOUT, "r%d: %s gets impossibly empty blob mark from ancestor %s, skipping",
							record.revision, node, ancestor)
						continue
					}

					// Time for fileop generation.
					fileop := newFileOp(sp.repo)
					fileop.construct(opM,
						nodePermissions(*node),
						node.blobmark.String(),
						node.path)
					commit.appendOperation(fileop)
					sp.repo.markToEvent(fileop.ref).(*Blob).addalias(node.path)

					// Sanity check: should be the case that
					// 1. The node is an add.  This sweeps
					// in several cases: normal creation of
					// a new file, expansion of a directory
					// copy, an explicit Subversion file (not
					// directory) copy (in which case it has
					// an MD5 hash that points back to a
					// source.)  Or,
					// 2. There is new content. This sweeps in change
					// nodes with attached blobs. Or,
					// 3. The permissions for this path have changed;
					// we need to generate a modify with an old mark
					// but new permissions.
					if logEnable(logEXTRACT) {
						if !(node.action == sdADD || (node.blob != nil) || node.propchange) {
							logit(logEXTRACT, "r%d~%s: unmodified", node.revision, node.path)
						}
					}
				}
			}
			baton.twirl()
		}

		// This early in processing, a commit with zero
		// fileops can only represent a dumpfile revision with
		// no nodes. This can happen if the corresponding
		// revision is a pure property change.  The initial
		// directory creations in a Subversion repository
		// with standard layout also look like this.
		//
		// to avoid proliferating code paths and auxiliary
		// data structures, we're going to punt the theoretical
		// case of a smultaneous propert change on multiple
		// directories.
		if len(commit.fileops) == 0 {
			// A directory-only commit at position one pretty much has to be
			// trunk and branches creation.  If we were to tagify it there
			// would be no place to put it. Also avoid really empty revisions
			if ri == 1 || len(record.nodes) == 0 {
				continue
			}
			var foundbranch string
			tooMany := false
			for _, node := range record.nodes {
				var branch string
				if node.kind == sdDIR && isDeclaredBranch(node.path) {
					branch = node.path
				} else {
					branch, _ = splitSVNBranchPath(node.path)
				}
				if branch != "" && foundbranch != "" && branch != foundbranch {
					tooMany = true
					break
				}
			}
			if tooMany {
				logit(logEXTRACT, "pathological empty revision at <%d>, comment %q, skipping.",
					ri, commit.Comment)
				continue
			}
			// No fileops, just directory nodes in a single branch, pass it
			// through.  Later we'll use this node path for branch assignment.
		}

		// We're not trying to do branch structure yet.
		// Everything becomes a directory tree on master.
		// And because we don't know what the branches
		// are, we don't want to sort the fileops into
		// git canonical order yet, either.
		commit.setBranch("refs/heads/master")

		// No branching, therefore linear history.
		// If we do branch analysis in a later phase
		// (that is, unless --nobranch is on) we will
		// create a new set of parent links.
		if lastcommit != nil {
			commit.setParents([]CommitLike{lastcommit})
		}

		commit.setMark(sp.repo.newmark())
		sp.repo.addEvent(commit)
		sp.repo.declareSequenceMutation("adding new commit")

		lastcommit = commit
		sp.repo.legacyMap["SVN:"+commit.legacyID] = commit

		baton.percentProgress(uint64(ri))
	}
	baton.endProgress()

	// We don't need the revision maps after this
	sp.history = nil
}

func svnSplitResolve(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase 6:
	// Split mixed commits (that is, commits with file paths on
	// multiple Subversion branches). Needs to be done before
	// branch assignment, Use parallelized search to find them,
	// but the mutation of the event list has to be serialized
	// else havoc will ensue.
	//
	// The exit contract for this phase is that every commit has
	// all its fileops on the same Subversion branch.  In addition,
	// the Source and Target member of each file have been filled
	// with the fileop path's branch and (sub-branch) filename.
	//
	// A side-effect of this pass is that fileops are sorted by
	// lexicographic order of pathname.
	//
	if options.Contains("--nobranch") {
		logit(logEXTRACT, "SVN Phase 6: split resolution (skipped due to --nobranch)")
		return
	}
	defer trace.StartRegion(ctx, "SVN Phase 6: split resolution").End()
	logit(logEXTRACT, "SVN Phase 6: split resolution")

	type splitRequest struct {
		loc    int
		splits []int
	}
	splits := make([]splitRequest, 0)
	var reqlock sync.Mutex

	baton.startProgress("SVN phase 6a: split detection", uint64(len(sp.repo.events)))
	walkEvents(sp.repo.events, func(i int, event Event) {
		if commit, ok := event.(*Commit); ok {
			var oldbranch string
			cliqueIndices := make([]int, 0)
			// We only generated M and D ops, or special deleteall
			// ops with their path set, therefore every
			// fileop has a Path member.  Wacky hack: by stashing
			// the split components in the unused Source and Target
			// nembers, we avoid having to recompute these when we
			// actually have to use tem
			for j, fileop := range commit.fileops {
				commit.fileops[j].Source, commit.fileops[j].Target = splitSVNBranchPath(fileop.Path)
				if j == 0 || commit.fileops[j].Source != oldbranch {
					cliqueIndices = append([]int{j}, cliqueIndices...)
					oldbranch = commit.fileops[j].Source
				}
			}
			if len(cliqueIndices) > 1 {
				reqlock.Lock()
				splits = append([]splitRequest{splitRequest{i, cliqueIndices[:len(cliqueIndices)-1]}}, splits...)
				reqlock.Unlock()
			}
		}
		// Clique indices and requests were generated back to front
		// so that when we process them we never have to worry about
		// a commit index changing due to insertion.
		baton.percentProgress(uint64(i) + 1)
	})
	baton.endProgress()

	baton.startProgress("SVN phase 6b: split resolution", uint64(len(splits)))
	// Can't parallelize this. That's OK, should be an unusual case.
	// Sort the splits in case parallel execution generatesd them out of order.
	const splitwarn = "\n[[Split portion of a mixed commit.]]\n"
	sort.Slice(splits, func(i, j int) bool { return splits[i].loc > splits[j].loc })
	for i, split := range splits {
		base := sp.repo.events[split.loc].(*Commit)
		logit(logEXTRACT, "split commit at %s <%s> resolving to %d commits",
			base.mark, base.legacyID, len(split.splits)+1)
		for _, idx := range split.splits {
			sp.repo.splitCommitByIndex(split.loc, idx)
		}
		baseID := base.legacyID
		base.Comment += splitwarn
		base.legacyID += ".1"
		sp.repo.legacyMap["SVN:"+base.legacyID] = base
		delete(sp.repo.legacyMap, "SVN:"+baseID)
		for j := 1; j <= len(split.splits); j++ {
			fragment := sp.repo.events[split.loc+j].(*Commit)
			fragment.legacyID = baseID + "." + strconv.Itoa(j+1)
			sp.repo.legacyMap["SVN:"+fragment.legacyID] = fragment
			fragment.Comment += splitwarn
			sp.splitCommits[intToRevidx(i)]++
			baton.twirl()
		}
		baton.percentProgress(uint64(i) + 1)
	}
	baton.endProgress()
}

func svnProcessBranches(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase 7:
	// Rewrite branch names from Subversion form to Git form.  The
	// previous phase did the analysis into branch and filename
	// because it had to; the first thing we have to do here is
	// shuffle those strings into place.
	//
	// That does not yet put the branchames in final form, however.
	// To get there we need to perform any branch mappings the user
	// requested, then massage the branchname into the reference form
	// that Git wants.
	//
	// After this phase branchnames are immutable and almost define the
	// topology, but parent marks have not yet been fixed up.
	//
	if options.Contains("--nobranch") {
		logit(logEXTRACT, "SVN Phase 7: branch renames (skipped due to --nobranch)")
		return
	}
	defer trace.StartRegion(ctx, "SVN Phase 7: branch renames").End()
	logit(logEXTRACT, "SVN Phase 7: branch renames")
	baton.startProgress("SVN phase 7: branch renames", uint64(len(sp.repo.events)))
	var maplock sync.Mutex
	sp.markToSVNBranch = make(map[string]string)
	walkEvents(sp.repo.events, func(i int, event Event) {
		if commit, ok := event.(*Commit); ok {
			if len(commit.fileops) == 0 {
				// Wacky special case -- corresponding revision has exacly one node
				n, err := strconv.Atoi(commit.legacyID)
				if err != nil {
					// Has to be sometghing weirder than a split commit going on - zero-op
					// commits on multiople branches are filtered out before this.
					panic(fmt.Errorf("Unexpectedly ill-formed legacy-id %s", commit.legacyID))
				}
				// Contiguity assumption
				node := sp.revisions[n].nodes[0]
				if node.kind == sdDIR && isDeclaredBranch(node.path) {
					commit.Branch = node.path
					if strings.HasSuffix(commit.Branch, svnSep) {
						commit.Branch = commit.Branch[:len(commit.Branch)-1]
					}
				} else {
					commit.Branch, _ = splitSVNBranchPath(node.path)
				}
			} else {
				// Normal case
				commit.simplify()
				for i := range commit.fileops {
					fileop := commit.fileops[i]
					commit.Branch = fileop.Source
					fileop.Source = ""
					fileop.Path = fileop.Target
					fileop.Target = ""
				}
			}
			maplock.Lock()
			sp.markToSVNBranch[commit.mark] = commit.Branch
			maplock.Unlock()
			matched := false
			for _, item := range control.branchMappings {
				result := GoReplacer(item.match, commit.Branch+svnSep, item.replace)
				if result != commit.Branch+svnSep {
					matched = true
					commit.setBranch(filepath.Join("refs", result))
					break
				}
				baton.twirl()
			}
			if !matched {
				if commit.Branch == "" {
					// File or directory is not under any recognizable branch.
					// Shuffle it off to a root branch.
					commit.setBranch(filepath.Join("refs", "heads", "root"))
				} else if commit.Branch == "trunk" {
					commit.setBranch(filepath.Join("refs", "heads", "master"))
				} else if strings.HasPrefix(commit.Branch, "tags/") {
					commit.setBranch(filepath.Join("refs", commit.Branch))
				} else if strings.HasPrefix(commit.Branch, "branches/") {
					commit.setBranch(filepath.Join("refs", "heads", commit.Branch[9:]))
				} else {
					// Uh oh
					commit.setBranch(filepath.Join("refs", "heads", commit.Branch))
					logit(logEXTRACT, "nonstandard branch %s at %s", commit.Branch, commit.idMe())
				}
			}
		}
		baton.percentProgress(uint64(i) + 1)
	})

	// If we were going to add an end reset per branch, this would
	// be the place to do it.  Current versions of git do not
	// require this; they will automatically create tip references
	// for each branch.

	baton.endProgress()
}

// Return the last commit with legacyID in (0;maxrev] whose SVN branch is equal
// to branch, or nil if not found.  It needs sp.lastCommitOnBranchAt to be
// filled, so can only be used after phase 8a has run.
func lastRelevantCommit(sp *StreamParser, maxrev revidx, branch string) *Commit {
	if list, ok := sp.lastCommitOnBranchAt[trimSep(branch)]; ok {
		l := revidx(len(list)) - 1
		if maxrev > l {
			maxrev = l
		}
		return list[maxrev]
	}
	return nil
}

func svnDisambiguateRefs(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase 8:
	// Intervene to prevent lossage from tag/branch/trunk deletions.
	//
	// The Subversion data model is that a history is a sequence of surgical
	// operations on a tree, and a tag is just another branch of the tree.
	// Tag/branch deletions are a place where this clashes badly with the
	// changeset-DAG model used by git and oter DVCSes, especially if the same
	// tag/branch is recreated later.
	//
	// To avoid losing history, when a tag or branch is deleted we can move it to
	// the refs/deleted/ namespace, with a suffix in case of clashes. A branch
	// is considered deleted when we encounter a commit with a single deleteall
	// fileop.
	defer trace.StartRegion(ctx, "SVN Phase 8: disambiguate deleted refs.").End()
	logit(logEXTRACT, "SVN Phase 8: disambiguate deleted refs.")
	// First we build a map from branches to commits with that branch, to avoid
	// an O(n^2) computation cost.
	baton.startProgress("SVN phase 8a: precompute branch map.", uint64(len(sp.repo.events)))
	branchToCommits := map[string][]*Commit{}
	commitCount := 0
	for idx, event := range sp.repo.events {
		if commit, ok := event.(*Commit); ok {
			branchToCommits[commit.Branch] = append(branchToCommits[commit.Branch], commit)
			commitCount++
		}
		baton.percentProgress(uint64(idx) + 1)
	}
	baton.endProgress()
	// Rename refs/heads/root to refs/heads/master if the latter doesn't exist
	baton.startProgress("SVN phase 8b: rename branch 'root' to 'master' if there is none",
		uint64(len(branchToCommits["refs/heads/root"])))
	if _, hasMaster := branchToCommits["refs/heads/master"]; !hasMaster {
		for i, commit := range branchToCommits["refs/heads/root"] {
			commit.setBranch("refs/heads/master")
			baton.percentProgress(uint64(i) + 1)
		}
		branchToCommits["refs/heads/master"] = branchToCommits["refs/heads/root"]
		delete(branchToCommits, "refs/heads/root")
	}
	baton.endProgress()
	// For each branch, iterate through commits with that branch, searching for
	// deleteall-only commits that mean the branch is being deleted.
	usedRefs := map[string]int{}
	processed := 0
	seen := 0
	baton.startProgress("SVN phase 8c: disambiguate deleted refs.", uint64(commitCount))
	for branch, commits := range branchToCommits {
		lastFixed := -1
		for i, commit := range commits {
			ops := commit.operations()
			if len(ops) > 0 && ops[len(ops)-1].op == deleteall {
				// Fix the branch of all the previous commits whose branch has
				// not yet been fixed.
				if !strings.HasPrefix(branch, "refs/") {
					croak("r%s (%s): Impossible branch %s",
						commit.legacyID, commit.mark, branch)
				}
				newname := fmt.Sprintf("refs/deleted/r%s/%s", commit.legacyID, branch[len("refs/"):])
				used := usedRefs[newname]
				usedRefs[newname]++
				if used > 0 {
					newname += fmt.Sprintf("-%d", used)
				}
				for j := lastFixed + 1; j <= i; j++ {
					commits[j].setBranch(newname)
				}
				lastFixed = i
				logit(logTAGFIX, "r%s (%s): deleted ref %s renamed to %s.",
					commit.legacyID, commit.mark, branch, newname)
				processed++
			}
			seen++
			baton.percentProgress(uint64(seen) + 1)
		}
	}
	logit(logTAGFIX, "%d deleted refs were put away.", processed)
	baton.endProgress()
}

func svnLinkFixups(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase 9:
	// The branches we colored in during the last phase almost
	// completely define the topology of the DAG, except for the
	// location of their root points. At first sight computing the
	// root points seems tricky, since a branch root revision can
	// be the target of multiple copies from different revision
	// and they can be a mix of directory and file copies.
	//
	// All of those copies need to be re-played to compute thee
	// content at each revision properly, but in computing branch
	// links it's the location of the *last copy* to to the root
	// commit of each branch that we want.
	//
	// If there was only ever one Subversion directory copy life
	// is easy - at every revision the copy point looks the same.
	// Looking for the last copy will pick that up.
	//
	// The tricky cases are:
	//
	// 1. Botched Subversion branch creation. This is a revision
	// consisting of a directory add, or possibly directory copy,
	// followed by a one or more file copies to the new branch
	// directory *not* using svn cp. Some of the file copies look
	// like adds in the dumpfile but can be matched up to their
	// source by hash. There's no ambiguity about where the link is.
	// We need not even complain about these.
	//
	// 2. Subversion branch creation, followed by deletion,
	// followed by recreation by a copy from a later revision
	// under the same name. Due to the branch recoloring in
	// Phase 2 the deleted branch can't cause confusion here.
	//
	// 3. Branch or tag creations followed by partial updates.
	// There's a case like this in tagpollute.svn in the test
	// suite. There is no ideal answer here; choosing the source
	// revision of the last partial update recreates the view from
	// the future.
	//
	// 4. Subversion dumpfile traces left by cv2svn's attempt
	// to synthesize Subversion branches fromn CVS branch creations.
	// These have no directory copy operations at all.
	// When cvs2svn created branches, it tried to copy each file
	// from the commit corresponding to the CVS revision where the
	// file was last changed before the branch creation, which
	// could potentually be a different revision for each file in
	// the new branch. And CVS didn't actually record branch
	// creation times.  But the branch creation can't have been
	// before the last copy.
	//
	// These cases are rebarbative. Dealing with them is by far the
	// most likely source of bugs in the analyzer.
	//
	if options.Contains("--nobranch") {
		logit(logEXTRACT, "SVN Phase 9: parent link fixups (skipped due to --nobranch)")
		// There is only one branch root: the very first commit
		sp.branchRoots = make(map[string][]*Commit)
		for _, event := range sp.repo.events {
			if commit, ok := event.(*Commit); ok {
				sp.branchRoots[""] = []*Commit{commit}
				break
			}
		}
		return
	}
	defer trace.StartRegion(ctx, "SVN Phase : parent link fixups").End()
	logit(logEXTRACT, "SVN Phase 9a: make content-changing links")
	baton.startProgress("SVN phase 9a: make content-chsnging links",
		uint64(len(sp.repo.events)))
	sp.lastCommitOnBranchAt = make(map[string][]*Commit)
	sp.branchRoots = make(map[string][]*Commit)
	totalroots := 0
	for index, event := range sp.repo.events {
		if commit, ok := event.(*Commit); ok {
			// Remember the last commit on every branch at each revision
			rev, _ := strconv.Atoi(strings.Split(commit.legacyID, ".")[0])
			branch := sp.markToSVNBranch[commit.mark]
			list, found := sp.lastCommitOnBranchAt[branch]
			lastrev := -1
			var prev *Commit
			if found {
				lastrev = len(list) - 1
				prev = list[lastrev]
			} else {
				list = make([]*Commit, rev+1, len(sp.revisions))
			}
			list = list[:rev+1] // enlarge the list to go up to rev
			for i := lastrev + 1; i < rev; i++ {
				list[i] = prev
			}
			list[rev] = commit
			sp.lastCommitOnBranchAt[branch] = list
			// Set the commit parent to the last of the history chain
			if prev != nil {
				ops := prev.operations()
				if len(ops) > 0 && ops[len(ops)-1].op == deleteall {
					// The previous commit deletes its branch and is
					// thus not part of the same history chain.
					prev = nil
				}
			}
			if prev != nil {
				commit.setParents([]CommitLike{prev})
			} else {
				commit.setParents(nil)
				sp.branchRoots[branch] = append(sp.branchRoots[branch], commit)
				totalroots++
			}
		}
		baton.percentProgress(uint64(index) + 1)
	}
	baton.endProgress()
	logit(logEXTRACT, "SVN Phase 9b: find branch root parents")
	baton.startProgress("SVN phase 9b: find branch root parents", uint64(totalroots))
	var parentlock sync.Mutex
	reparent := func(commit, parent *Commit) {
		// Prepend a deleteall to avoid inheriting our new parent's content
		parentlock.Lock()
		ops := commit.operations()
		if len(ops) == 0 || ops[0].op != deleteall {
			fileop := newFileOp(sp.repo)
			fileop.construct(deleteall)
			commit.prependOperation(fileop)
		}
		commit.setParents([]CommitLike{parent})
		parentlock.Unlock()
	}
	count := 0
	for branch, roots := range sp.branchRoots {
		for _, commit := range roots {
			rev, _ := strconv.Atoi(strings.Split(commit.legacyID, ".")[0])
			if rev > 0 && rev < len(sp.revisions) {
				record := sp.revisions[rev]
				for _, node := range record.nodes {
					if node.kind == sdDIR && node.fromRev != 0 &&
						trimSep(node.path) == branch {
						frombranch := node.fromPath
						if !isDeclaredBranch(frombranch) {
							frombranch, _ = splitSVNBranchPath(node.fromPath)
						}
						parent := lastRelevantCommit(sp, node.fromRev, frombranch)
						if parent != nil {
							logit(logTOPOLOGY,
								"Link from %s <%s> to %s <%s> found by copy-from",
								parent.mark, parent.legacyID, commit.mark, commit.legacyID)
							if strings.Split(parent.legacyID, ".")[0] != fmt.Sprintf("%d", node.fromRev) {
								logit(logTOPOLOGY,
									"(fromRev was r%d)",
									node.fromRev)
							}
							reparent(commit, parent)
							goto next
						}
					}
					baton.twirl()
				}
				// Try to detect file-based copies, like what CVS can generate
				// Remember the maximum value of fromRev in all nodes, or 0 if
				// the file nodes don't all have a fromRev. We also record the
				// minimum value, to warn if they are different.
				maxfrom, minfrom := revidx(0), revidx(len(sp.revisions))
				var frombranch string
				for _, node := range record.nodes {
					// Don't check for isDeclaredBranch because we only use
					// file nodes (maybe expanded from a dir copy). If the
					// branch dir creation node had a fromRev it would have
					// been catched by the normal logic above.
					destbranch, _ := splitSVNBranchPath(trimSep(node.path))
					if node.kind == sdFILE && node.action == sdADD && destbranch == branch &&
						!strings.HasSuffix(node.path, ".gitignore") {
						if node.fromRev == 0 {
							maxfrom = 0
							break
						}
						newfrom, _ := splitSVNBranchPath(trimSep(node.fromPath))
						if frombranch == "" {
							frombranch = newfrom
						} else if frombranch != newfrom {
							logit(logWARN,
								"Link detection for %s <%s> failed: file copies from multiple branches",
								commit.mark, commit.legacyID)
							maxfrom = 0
							break
						}
						if node.fromRev > maxfrom {
							maxfrom = node.fromRev
						}
						if node.fromRev < minfrom {
							minfrom = node.fromRev
						}
					}
				}
				if maxfrom > 0 {
					parent := lastRelevantCommit(sp, maxfrom, frombranch)
					if parent != nil {
						if minfrom == maxfrom {
							logit(logTOPOLOGY,
								"Link from %s <%s> to %s <%s> found by file copies",
								parent.mark, parent.legacyID, commit.mark, commit.legacyID)
						} else {
							logit(logWARN,
								"Detected link from %s <%s> to %s <%s> might be dubious (from-rev range %d:%d)",
								parent.mark, parent.legacyID, commit.mark, commit.legacyID,
								minfrom, maxfrom)
						}
						reparent(commit, parent)
						goto next
					}
				}
			}
		next:
			count++
			baton.percentProgress(uint64(count))
		}
	}
	baton.endProgress()

	if logEnable(logEXTRACT) {
		logit(logEXTRACT, "after branch analysis")
		for _, event := range sp.repo.events {
			commit, ok := event.(*Commit)
			if !ok {
				continue
			}
			var ancestorID string
			ancestors := commit.parents()
			if len(ancestors) == 0 {
				ancestorID = "-"
			} else {
				ancestorID = ancestors[0].getMark()
			}
			proplen := 0
			if commit.hasProperties() {
				proplen = commit.properties.Len()
			}
			logit(logSHOUT, "r%-4s %4s %4s %2d %2d '%s'",
				commit.legacyID,
				commit.mark, ancestorID,
				len(commit.operations()),
				proplen,
				commit.Branch)
			baton.twirl()
		}
	}

	// We could make branch-tip resets here.  Older versions of
	// git might have required one per branch tip.  We chose not
	// to so the resets that are really visible die to tag
	// reduction will stand out.
}

func svnProcessMergeinfos(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	defer trace.StartRegion(ctx, "SVN Phase A: mergeinfo processing").End()
	logit(logEXTRACT, "SVN Phase A: mergeinfo processing")
	baton.startProgress("SVN phase A: mergeinfo processing", uint64(len(sp.revisions)))

	type RevRange struct {
		min int
		max int
	}

	parseMergeInfo := func(info string) map[string][]RevRange {
		mergeinfo := make(map[string][]RevRange)
		for _, line := range strings.Split(info, "\n") {
			fields := strings.Split(line, ":")
			if len(fields) != 2 {
				continue
			}
			// One path, one range list
			branch, ranges := fields[0], fields[1]
			branch = trimSep(branch)
			revs := mergeinfo[branch]
			for _, span := range strings.Split(ranges, ",") {
				// Ignore non-inheritable merges, they represent
				// partial merges or cherry-picks.
				if strings.HasSuffix(span, "*") {
					continue
				}
				fields = strings.Split(span, "-")
				if len(fields) == 1 {
					i, _ := strconv.Atoi(fields[0])
					revs = append(revs, RevRange{i, i})
				} else if len(fields) == 2 {
					minRev, _ := strconv.Atoi(fields[0])
					maxRev, _ := strconv.Atoi(fields[1])
					revs = append(revs, RevRange{minRev, maxRev})
				}
			}
			mergeinfo[branch] = revs
		}
		for branch, revs := range mergeinfo {
			sort.Slice(revs, func(i, j int) bool {
				return revs[i].min < revs[j].min ||
					(revs[i].min == revs[j].min && revs[i].max < revs[j].max)
			})
			last := 0
			for i := 1; i < len(revs); i++ {
				if revs[i].min <= revs[last].max+1 {
					// Express the union as a single range
					if revs[last].max < revs[i].max {
						revs[last].max = revs[i].max
					}
				} else {
					// There is a gap, add a range to the union
					last++
					revs[last] = revs[i]
				}
			}
			mergeinfo[branch] = revs[:last+1]
		}
		return mergeinfo
	}
	forkIndices := func(commit *Commit) map[string][]int {
		// Compute all fork points from a root to the branch
		branch := sp.markToSVNBranch[commit.mark]
		result := make(map[string][]int)
		index := sp.repo.eventToIndex(commit)
		for commit != nil {
			// Find the last branch root before commit
			for _, root := range sp.branchRoots[branch] {
				if sp.repo.eventToIndex(root) > index {
					break
				}
				commit = root
			}
			// The first parent is the fork point
			var fork *Commit
			if commit.hasParents() {
				fork, _ = commit.parents()[0].(*Commit)
			}
			if fork == nil {
				break // We didn't fork from anything
			}
			branch = sp.markToSVNBranch[fork.mark]
			if branch == "" {
				break
			}
			index = sp.repo.eventToIndex(fork)
			result[branch] = append(result[branch], index)
			commit = fork
		}
		return result
	}
	type mergeDesc struct {
		dest   string
		source string
		index  int
	}
	seenMerges := make(map[mergeDesc]bool)
	for revision, record := range sp.revisions {
		for _, node := range record.nodes {
			baton.twirl()
			// We're only looking at directory nodes with new properties
			if !(node.kind == sdDIR && node.propchange && node.hasProperties()) {
				continue
			}
			info := node.props.get("svn:mergeinfo")
			info2 := node.props.get("svnmerge-integrated")
			if info == "" {
				info = info2
			} else if info2 != "" {
				info = info + "\n" + info2
			}
			if info == "" {
				continue
			}
			// We can only process mergeinfo if we find a commit
			// corresponding to the revision on the branch whose
			// mergeinfo has been modified
			branch := trimSep(node.path)
			if !isDeclaredBranch(branch) {
				continue
			}
			commit := lastRelevantCommit(sp, revidx(revision), branch)
			if commit == nil {
				logit(logWARN,
					"Cannot resolve mergeinfo for r%d which has no commit in branch %s",
					revision, branch)
				continue
			}
			realrev, _ := strconv.Atoi(strings.Split(commit.legacyID, ".")[0])
			if realrev != revision {
				logit(logWARN, "Resolving mergeinfo targeting r%d on %s <%s> instead",
					revision, commit.mark, commit.legacyID)
			}
			// Now parse the mergeinfo, and find commits for the merge points
			logit(logTOPOLOGY, "mergeinfo for %s <%s> on %s is: %s",
				commit.mark, commit.legacyID, branch, info)
			newMerges := parseMergeInfo(info)
			mergeSources := make(map[int]bool, len(newMerges))
			// SVN tends to not put in mergeinfo the revisions that
			// predate the merge base of the source and dest branch
			// tips. Computing a merge base would be costly, but we
			// can make a poor man's one by checking the fork points
			// that is the first parent of the branch root, and that
			// of the obtained commit, recursively.
			destIndex := sp.repo.eventToIndex(commit)
			forks := forkIndices(commit)
			// Start of the loop over the mergeinfo
			minIndex := int(^uint(0) >> 2)
			for fromPath, revs := range newMerges {
				baton.twirl()
				fromPath = trimSep(fromPath)
				if !isDeclaredBranch(fromPath) {
					continue
				}
				// Ranges were unified when parsing if they were
				// contiguous in terms of revisions. Now unify
				// consecutive ranges if they are contiguous in
				// terms of commits, that is no commit on the branch
				// separates them. Also, only keep ranges when the
				// last commit just before the range is nil or a
				// deleteall, which means the range is from the
				// source branch start. We also accept a range if
				// the previous commit is earlier than the branch
				// base, due to SVN sometimes omitting revisions
				// prior to the merge base.
				i, lastGood := 0, -1
				count := len(revs)
				for i < count {
					// Skip all ranges not starting at the right place
					// We accept a range [m;M] if the commit just
					// before the range is:
					// a) nil, if the branch started to exist at
					//    revision m.
					// b) a deleteall, if the branch was recreated at
					//    revision m.
					// c) the branch root, in case people used -r
					//    <branch-root-rev>:<last-merged-rev> where SVN
					//    in its deep wisdom decides to start the
					//    mergeinfo from <branch-root-rev> + 1
					// d) a commit *before or equal* the fork point
					//    from the source to the destination branch,
					//    or the branch it forked from, and so on,
					//    if any exists. It means that *at least* the
					//    revisions following the fork point are
					//    merged (SVN sometimes omits revisions prior
					//    to the merge base).
					for ; i < count; i++ {
						baton.twirl()
						// Find the last commit just before the range
						before := lastRelevantCommit(sp, revidx(revs[i].min-1), fromPath)
						if before == nil { // a)
							break
						}
						ops := before.operations()
						if len(ops) == 1 && ops[0].op == deleteall { // b)
							break
						}
						index := sp.repo.eventToIndex(before)
						// c) is a bit more costly
						var branchRoot *Commit
						for _, root := range sp.branchRoots[fromPath] {
							if sp.repo.eventToIndex(root) > index {
								break
							}
							branchRoot = root
						}
						if before == branchRoot {
							break
						}
						// and d) too
						endIndex := -1
						if end := lastRelevantCommit(sp, revidx(revs[i].max), fromPath); end != nil {
							endIndex = sp.repo.eventToIndex(end)
						}
						baseIndex := -1
						if forkIndices, ok := forks[fromPath]; ok {
							for _, forkIndex := range forkIndices {
								// They are sorted in reverse order
								baseIndex = forkIndex
								if forkIndex <= endIndex {
									break
								}
							}
						}
						if index <= baseIndex {
							break
						}
					}
					if i >= count {
						break
					}
					lastGood++
					revs[lastGood] = revs[i]
					// Unify the following ranges as long as we can
					i++
					for ; i < count; i++ {
						// Find the last commit in the current "good" range
						last := lastRelevantCommit(sp, revidx(revs[lastGood].max), fromPath)
						// and the last commit just before the next range
						beforeNext := lastRelevantCommit(sp, revidx(revs[i].min-1), fromPath)
						if last != beforeNext {
							break
						}
						revs[lastGood].max = revs[i].max
					}
				}
				revs := revs[:lastGood+1]
				// Now we process the merges
				for _, rng := range revs {
					baton.twirl()
					// Now that ranges are unified, there is a gap
					// between all of them. Everything on the source
					// branch after the gap is most probably coming
					// from cherry-picks. The last commit in this range
					// is a good merge source candidate.
					last := lastRelevantCommit(sp, revidx(rng.max), fromPath)
					if last == nil {
						continue
					}
					lastrev, _ := strconv.Atoi(strings.Split(last.legacyID, ".")[0])
					if lastrev < rng.min {
						// Snapping the revisions to existing commits
						// went past the minimum revision in the range
						logit(logWARN, "Ignoring bogus mergeinfo with no valid commit in the range")
						continue
					}
					index := sp.repo.eventToIndex(last)
					desc := mergeDesc{branch, fromPath, index}
					if _, ok := seenMerges[desc]; ok {
						continue
					}
					seenMerges[desc] = true
					logit(logTOPOLOGY,
						"mergeinfo says %s is merged up to %s <%s> in %s <%s>",
						fromPath, last.mark, last.legacyID, commit.mark, commit.legacyID)
					if index >= destIndex {
						logit(logWARN, "Ignoring bogus mergeinfo trying to create a forward merge")
						continue
					}
					mergeSources[index] = true
					if index < minIndex {
						minIndex = index
					}
				}
			}
			// Check if we need to prepend a deleteall
			ops := commit.operations()
			needDeleteAll := !commit.hasParents() && (len(ops) == 0 || ops[0].op != deleteall)
			// Weed out already merged commits, then perform the merge
			// of the highest commit still present, rinse and repeat
			stack := []*Commit{commit}
			for len(mergeSources) > 0 {
				baton.twirl()
				// Walk the ancestry, forgetting already merged marks
				seen := map[int]bool{}
				for len(stack) > 0 && len(mergeSources) > 0 {
					var current *Commit
					// pop a CommitLike from the stack
					stack, current = stack[:len(stack)-1], stack[len(stack)-1]
					index := sp.repo.eventToIndex(current)
					if _, ok := seen[index]; ok {
						continue
					}
					seen[index] = true
					// We could reach the commit from the source, remove it
					// from the merge sources. Only continue the traversal
					// when the current index is high enough for ancestors
					// to potentially be in sourceMerges.
					if index >= minIndex {
						delete(mergeSources, index)
						// add all parents to the "todo" stack
						for _, parent := range current.parents() {
							if c, ok := parent.(*Commit); ok {
								stack = append(stack, c)
							}
						}
					}
				}
				// Now perform the merge from the highest index
				// since it cannot be a descendent of the other
				highIndex := 0
				for index := range mergeSources {
					if index > highIndex {
						highIndex = index
					}
				}
				delete(mergeSources, highIndex)
				if source, ok := sp.repo.events[highIndex].(*Commit); ok {
					if needDeleteAll {
						fileop := newFileOp(sp.repo)
						fileop.construct(deleteall)
						commit.prependOperation(fileop)
						needDeleteAll = false
					}
					logit(logEXTRACT, "Merge found from %s <%s> to %s <%s>",
						source.mark, source.legacyID, commit.mark, commit.legacyID)
					commit.addParentCommit(source)
					stack = append(stack, source)
				}
			}
		}
		baton.percentProgress(uint64(revision) + 1)
	}
	baton.endProgress()
}

func svnProcessIgnores(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase A: convert svn:ignore properties on directory nodes to .gitignore files
	defer trace.StartRegion(ctx, "SVN Phase B: Conversion from svn:ignore to .gitignore").End()
	logit(logEXTRACT, "SVN Phase B: Conversion from svn:ignore to .gitignore.")
	if options.Contains("--no-automatic-ignores") {
		logit(logEXTRACT, "Skipped due to --no-automatic-ignores option.")
		return
	}

	isRoot := func(commit *Commit) bool {
		branch := sp.markToSVNBranch[commit.mark]
		for _, root := range sp.branchRoots[branch] {
			if root == commit {
				return true
			}
		}
		return false
	}

	defaultIgnoreMark := ""
	ignoreOp := func(nodepath string, explicit string) *FileOp {
		var buf bytes.Buffer
		if nodepath == ".gitignore" {
			buf.WriteString(subversionDefaultIgnores)
		}
		for _, line := range strings.SplitAfter(explicit, "\n") {
			if line != "" {
				buf.WriteByte(svnSep[0])
				buf.WriteString(line)
			}
		}
		ignores := buf.Bytes()
		op := newFileOp(sp.repo)
		if len(ignores) == 0 {
			op.construct(opD, nodepath)
		} else if explicit != "" {
			op.construct(opM, "100644", "inline", nodepath)
			op.inline = ignores
		} else {
			if defaultIgnoreMark == "" {
				defaultIgnoreMark = sp.repo.newmark()
			}
			op.construct(opM, "100644", defaultIgnoreMark, nodepath)
		}
		return op
	}

	existingIgnores := make(map[int]*PathMap)
	baton.startProgress("SVN phase B: Conversion from svn:ignore to .gitignore",
		uint64(len(sp.repo.events)))
	for index, event := range sp.repo.events {
		commit, ok := event.(*Commit)
		if !ok {
			continue
		}
		revision, _ := strconv.Atoi(strings.Split(commit.legacyID, ".")[0])
		if revision < 1 || revision >= len(sp.revisions) {
			continue
		}
		var currentIgnores *PathMap
		if commit.hasParents() {
			if parent, ok := commit.parents()[0].(*Commit); ok {
				currentIgnores = existingIgnores[sp.repo.eventToIndex(parent)]
			}
		}
		if currentIgnores == nil {
			currentIgnores = newPathMap()
		}
		mybranch := sp.markToSVNBranch[commit.mark]
		unchanged := true
		hasTopLevel := false
		for _, node := range sp.revisions[revision].nodes {
			if node.kind != sdDIR {
				continue
			}
			path := filepath.Join(trimSep(node.path), ".gitignore")
			branch := ""
			branch, path = splitSVNBranchPath(path)
			if branch != mybranch {
				continue
			}
			oldvalue := ""
			if obj, ok := currentIgnores.get(path); ok {
				oldvalue = obj.(string)
			}
			newvalue := ""
			if node.hasProperties() && node.props.has("svn:ignore") {
				newvalue = node.props.get("svn:ignore")
			}
			if node.action == sdDELETE {
				_, dirpath := splitSVNBranchPath(node.path)
				// Also remove all subdirectory .gitignores
				currentIgnores.iter(func(childPath string, _ interface{}) {
					if strings.HasPrefix(childPath, dirpath) {
						if unchanged {
							currentIgnores = currentIgnores.snapshot()
							unchanged = false
						}
						currentIgnores.remove(childPath)
						commit.fileops = append(commit.fileops, ignoreOp(childPath, ""))
					}
				})
			}
			if oldvalue == newvalue {
				continue
			}
			if unchanged {
				currentIgnores = currentIgnores.snapshot()
				unchanged = false
			}
			if newvalue == "" {
				currentIgnores.remove(path)
			} else {
				currentIgnores.set(path, newvalue)
			}
			commit.fileops = append(commit.fileops, ignoreOp(path, newvalue))
			if path == ".gitignore" {
				hasTopLevel = true
			}
		}
		// If the commit misses a default root .gitignore, create it. Don't do
		// that for non-branch roots since they inherit their toplevel one.
		// Also avoid polluting tipdeletes.
		if !hasTopLevel && isRoot(commit) &&
			!(len(commit.fileops) == 1 &&
				commit.fileops[0].op == deleteall &&
				!commit.hasChildren()) {
			commit.fileops = append(commit.fileops, ignoreOp(".gitignore", ""))
		}
		existingIgnores[index] = currentIgnores
		commit.simplify()
		baton.percentProgress(uint64(index) + 1)
	}

	if defaultIgnoreMark != "" {
		blob := newBlob(sp.repo)
		blob.setContent([]byte(subversionDefaultIgnores), noOffset)
		blob.setMark(defaultIgnoreMark)
		sp.repo.insertEvent(blob, len(sp.repo.frontEvents()),
			"creating default ignore")
	}

	baton.endProgress()
}

func svnProcessJunk(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase C:
	defer trace.StartRegion(ctx, "SVN Phase C: de-junking").End()
	logit(logEXTRACT, "SVN Phase C: de-junking")
	// If asked to, purge commits on deleted refs, but remember the original
	// branch for tagification purposes.
	baton.startProgress("SVN phase C1: purge deleted refs", uint64(len(sp.repo.events)))
	// compute a map from original branches to their tip
	branchtips := sp.repo.branchmap()
	// Remember the original branch only if purging.
	origBranches := make(map[string]string)
	preserve := options.Contains("--preserve")
	if !preserve {
		for index := range sp.repo.events {
			if commit, ok := sp.repo.events[index].(*Commit); ok {
				if strings.HasPrefix(commit.Branch, "refs/deleted/") {
					origBranches[commit.mark] = commit.Branch
				}
			}
		}
		sp.repo.deleteBranch(nil, func(branch string) bool {
			return strings.HasPrefix(branch, "refs/deleted/")
		})
	}
	baton.endProgress()
	// Canonicalize all commits except all-deletes
	baton.startProgress("SVN phase C2: canonicalize commits", uint64(len(sp.repo.events)))
	sp.repo.walkManifests(func(index int, commit *Commit, _ int, _ *Commit) {
		baton.percentProgress(uint64(index) + 1)
		origbranch := commit.Branch
		if branch, ok := origBranches[commit.mark]; ok {
			origbranch = branch
		}
		tip, _ := sp.repo.markToEvent(branchtips[origbranch]).(*Commit)
		tipIsDelete := (tip != nil && len(tip.operations()) == 1 &&
			tip.operations()[0].op == deleteall)
		// Do not canonicalize tipdeletes
		if commit != tip || !tipIsDelete {
			commit.canonicalize()
		}
	})
	baton.endProgress()
	// Now we need to tagify all other commits without fileops, because they
	// don't fit well in a git model. In most cases we create an annotated tag
	// pointing to their first parent, to keep any interesting metadata.
	//
	// * Commits from tag creation often have no real fileops since they come
	//   from a directory copy.
	//
	// * Same for branch-root commits. The tag name is the basename of the
	//   branch directory in SVN with "-root" appended to distinguish them
	//   from SVN tags.
	//
	// * All other commits without fileops get turned into an annotated tag
	//   with name "emptycommit-<revision>".
	//
	// * Commits at a branch tip that consist only of deleteall are also
	//   tagified if --nobranch is on, because having a commit at the branch
	//   tip that removes all files is less than useful. Such commits should
	//   almost all be pruned because they put their branch in the
	//   /refs/deleted namespace, but they can be kept if they are part of
	//   another branch history (which would be a bit strange) or if the
	//   --preserve option is used.
	rootmarks := newOrderedStringSet()
	for _, roots := range sp.branchRoots {
		for _, root := range roots {
			rootmarks.Add(root.mark)
		}
	}

	// What should a tag made from the argument commit be named?
	tagname := func(commit *Commit) string {
		// Give branch and tag roots a special name.
		origbranch := commit.Branch
		if branch, ok := origBranches[commit.mark]; ok {
			origbranch = branch
		}
		prefix, branch := "", origbranch
		if strings.HasPrefix(branch, "refs/deleted/") {
			// Commit comes from a deleted branch
			split := strings.IndexRune(branch[len("refs/deleted/"):], '/') +
				len("refs/deleted/") + 1
			prefix = branch[len("refs/"):split]
			branch = "refs/" + branch[split:]
		}
		name := prefix + branchbase(branch)
		tip, _ := sp.repo.markToEvent(branchtips[origbranch]).(*Commit)
		tipIsDelete := (tip != nil && len(tip.operations()) == 1 &&
			tip.operations()[0].op == deleteall)
		if (!tipIsDelete && tip == commit) ||
			(tipIsDelete && tip.hasParents() && tip.parents()[0] == commit) {
			if strings.HasPrefix(branch, "refs/tags/") {
				// The empty commit is a tip but not a tipdelete, or is the
				// last commit before the tipdelete. The tag name should be
				// kept so that the annotated commit has the exact name of
				// the tag.
				return name
			}
		}
		if tipIsDelete && tip == commit {
			return name + "-tipdelete"
		}
		if rootmarks.Contains(commit.mark) {
			return name + "-root"
		}
		// Fall back to emptycommit-revision
		return "emptycommit-" + commit.legacyID
	}

	// What distinguishing element should we generate for a tag made from the argument commit?
	taglegend := func(commit *Commit) string {
		// Only real tip deletes still have a single "deleteall", because other
		// commits have been canonicalized.
		isTipDelete := (len(commit.operations()) == 1 &&
			commit.operations()[0].op == deleteall)
		// Tipdelete commits and branch roots don't get any legend.
		if isTipDelete || rootmarks.Contains(commit.mark) {
			return ""
		}
		// Otherwise, generate one for inspection.
		return fmt.Sprintf("[[Tag from zero-fileop commit at Subversion r%s]]\n",
			commit.legacyID)
	}

	// Should the argument commit be tagified?
	doignores := !options.Contains("--no-automatic-ignore")
	tagifyable := func(commit *Commit) bool {
		// Tagify empty commits
		if len(commit.operations()) == 0 {
			return true
		}
		// Commits with a deletall only were generated in early phases to map
		// SVN deletions of a whole branch. This has already been mapped in git
		// land by stashing deleted refs away, and even removing all commits
		// reachable only from them if the --preserve option was not given.
		// Any "alldeletes" commit remaining can now be tagified, and should,
		// so that there are no remnants of the SVN way to delete refs.
		// After canonicalization, no other commit can have a single deleteall.
		if len(commit.operations()) == 1 &&
			commit.operations()[0].op == deleteall {
			return true
		}
		// If the commit is the first of its branch and only introduces the
		// default gitignore, tagify it.
		if doignores && rootmarks.Contains(commit.mark) {
			if len(commit.operations()) == 1 {
				op := commit.operations()[0]
				if op.Path == ".gitignore" {
					blob, ok := sp.repo.markToEvent(op.ref).(*Blob)
					if ok && string(blob.getContent()) == subversionDefaultIgnores {
						return true
					}
				}
			}
		}
		return false
	}

	deletia := make([]int, 0)
	// Do not parallelize, it will cause tags to be created in a nondeterministic order.
	// There is probably not much to be gained here, anyway.
	baton.startProgress("SVN phase C2: tagify empty commits", uint64(len(sp.repo.events)))
	for index := range sp.repo.events {
		//logit(logEXTRACT, "looking at %s", sp.repo.events[index].idMe())
		commit, ok := sp.repo.events[index].(*Commit)
		if !ok {
			continue
		}
		if tagifyable(commit) {
			logit(logEXTRACT, "%s might be tag-eligible", commit.idMe())
			if cvs2svnTagBranchRE.MatchString(commit.Comment) {
				// Nothing to do, but we don't want to create an annotated tag
				// because messages from cvs2svn are not useful.
			} else if commit.hasParents() {
				if len(commit.parents()) > 1 {
					continue
				}
				sp.repo.tagifyNoCheck(commit,
					tagname(commit),
					commit.getMark(),
					taglegend(commit),
					false)
			} else {
				msg := ""
				if commit.legacyID != "" {
					msg = fmt.Sprintf("r%s:", commit.legacyID)
				} else if commit.mark != "" {
					msg = fmt.Sprintf("'%s':", commit.mark)
				}
				msg += " deleting parentless "
				if len(commit.operations()) > 0 && commit.alldeletes(deleteall) {
					msg += fmt.Sprintf("tip delete of %s.", commit.Branch)
				} else {
					msg += fmt.Sprintf("zero-op commit on %s.", commit.Branch)
				}
				logit(logEXTRACT, msg)
			}
			commit.Comment = "" // avoid composing with the children
			deletia = append(deletia, index)
		}
		baton.percentProgress(uint64(index) + 1)
	}
	sp.repo.delete(deletia, []string{"--pushforward", "--tagback"})
	baton.endProgress()
}

func svnProcessDebubble(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase D:
	// Remove spurious parent links caused by random cvs2svn file copies.
	defer trace.StartRegion(ctx, "SVN Phase D: remove duplicate parent marks").End()
	logit(logEXTRACT, "SVN Phase D: remove duplicate parent marks")
	baton.startProgress("SVN phase D: remove duplicate parent marks", uint64(len(sp.repo.events)))
	walkEvents(sp.repo.events, func(idx int, event Event) {
		commit, ok := event.(*Commit)
		if !ok {
			return
		}
		parents := commit.parents()
		if len(parents) != 2 {
			return
		}
		a, ok1 := parents[0].(*Commit)
		b, ok2 := parents[1].(*Commit)
		if !ok1 || !ok2 {
			return
		}
		if a.getMark() == b.getMark() {
			logit(logSHOUT, "r%s: duplicate parent marks", commit.legacyID)
		} else if a.Branch == commit.Branch && b.Branch == commit.Branch {
			if b.committer.date.Before(a.committer.date) {
				a, b = b, a
			}
			if b.descendedFrom(a) {
				commit.removeParent(a)
			}
		}
		baton.percentProgress(uint64(idx) + 1)
	})
	baton.endProgress()
}

func svnProcessRenumber(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase E:
	// Renumber all commits and add an end event.
	// FIXME: Enable adding end events after anything else stabilizes.
	defer trace.StartRegion(ctx, "SVN Phase E: renumber").End()
	logit(logEXTRACT, "SVN Phase E: renumber")
	sp.repo.renumber(1, baton)
	//sp.repo.events = append(sp.repo.events, newPassthrough(sp.repo, "end\n"))
}

// end
