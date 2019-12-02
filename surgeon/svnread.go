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
	"crypto/md5"
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

	trie "github.com/acomagu/trie"
)

// FIXME: When we merge to master, move this to reposugeon.go
// and remove the "common" member of the Commit structure.
// Also remove the copyOperations method
const colorGEN = 4

type branchMeta struct {
	root *Commit
	tip *Commit
}

type revlink struct {
	source revidx
	target revidx
	copycount int
}

type svnReader struct {
	revisions            []RevisionRecord
	streamview           []*NodeAction // All nodes in stream order
	hashmap              map[string]*NodeAction
	history              *History
	branchlinks          map[revidx]revidx
	branches             map[string]*branchMeta // Points to branch root commits
	_branchesSorted      trie.Tree
	splitCommits         map[revidx]int
}

// Helpers for branch analysis

func (sp *StreamParser) addBranch(name string) {
	sp.branches[name] = nil
	sp._branchesSorted = nil
	return
}

// isDeclaredBranch returns true iff the user requested that this path be treated as a branch or tag.
func isDeclaredBranch(path string) bool {
	np := path
	if !strings.HasSuffix(path, svnSep) {
		np += svnSep
	}
	for _, trial := range control.listOptions["svn_branchify"] {
		if !strings.Contains(trial, "*") && trial == path {
			return true
		} else if strings.HasSuffix(trial, svnSep+"*") && filepath.Dir(trial) == filepath.Dir(path) && !control.listOptions["svn_branchify"].Contains(np+"*") {
			return true
		} else if trial == "*" && !control.listOptions["svn_branchify"].Contains(np+"*") && strings.Count(path, svnSep) < 1 {
			return true
		}
	}
	return false
}

// splitSVNBranchPath splits a node path into the part that identifies the branch and the rest, as determined by the current branch map
func splitSVNBranchPath(path string) (string, string) {
	segments := strings.Split(path, svnSep)
	for i := len(segments) - 1; i >= 0; i-- {
		candidate := strings.Join(segments[0:i], svnSep)
		if isDeclaredBranch(candidate) {
			return candidate, strings.Join(segments[i:], svnSep)
		}
	}
	return "", path
}

// Fast branch lookup and retrieval

func (sp *StreamParser) isBranch(pathname string) bool {
	// FIXME: not used. Can we replace isXeclaredBranch() ca;;s with this?
	_, ok := sp.branches[pathname]
	return ok
}

func (sp *StreamParser) branchtrie() trie.Tree {
	//The branch list in deterministic order, most specific branches first.
	if len(sp.branches) == 0 {
		return nil
	}
	if sp._branchesSorted != nil {
		return sp._branchesSorted
	}
	branches := make([][]byte, len(sp.branches))
	branchIndexes := make([]interface{}, len(branches))
	idx := 0
	for key := range sp.branches {
		branches[idx] = []byte(key)
		branchIndexes[idx] = true // we don't care about the value we put into the trie
		idx++
	}
	sp._branchesSorted = trie.New(branches, branchIndexes)
	return sp._branchesSorted
}

func longestPrefix(t trie.Tree, key []byte) []byte {
	var prefix []byte
	if t == nil {
		return prefix
	}
	for i, c := range []byte(key) {
		if t = t.TraceByte(c); t == nil {
			break
		}
		if _, ok := t.Terminal(); ok {
			prefix = key[:i+1]
		}
	}
	return prefix
}

// A type to manage a collection of PathMaps used as a history of file visibility.

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
var actionValues = []string{"none", "add", "delete", "change", "replace"}
var pathTypeValues = []string{"none", "file", "dir", "ILLEGAL-TYPE"}

// The reason for these suppressions is to avoid a huge volume of
// junk file properties - cvs2svn in particular generates them like
// mad.  We want to let through other properties that might carry
// useful information.
var ignoreProperties = map[string]bool{
	"svn:mime-type":   true,
	"svn:keywords":    true,
	"svn:needs-lock":  true,
	"svn:eol-style":   true, // Don't want to suppress, but cvs2svn floods these.
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
	// FIXME Ugh...any way to avoid all this conversion?
	return []byte(strings.TrimSpace(strings.SplitN(string(line), ":", 2)[1]))
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
	defer trace.StartRegion(ctx, "SVN Phase 1: read dump file").End()
	sp.revisions = make([]RevisionRecord, 0)
	sp.hashmap = make(map[string]*NodeAction)
	sp.branches = make(map[string]*branchMeta)
	sp._branchesSorted = nil
	sp.splitCommits = make(map[revidx]int)

	trackSymlinks := newOrderedStringSet()
	propertyStash := make(map[string]*OrderedMap)

	baton.startProgress("SVN Phase 1: read dump file", uint64(filesize))
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
							propertyStash[node.path] = node.props
							// ...exceopt for this one.  Later we're going to want
							// to interpret these only at the revisions where they
							// are actually set.
							propertyStash[node.path].delete("svn:ignore")
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
						} else {
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
					node.path = intern(string(sdBody(line)))
					plen = -1
					tlen = -1
				} else if bytes.HasPrefix(line, []byte("Node-kind: ")) {
					// svndumpfilter sometimes emits output
					// with the node kind first
					if node == nil {
						node = new(NodeAction)
					}
					kind := string(sdBody(line))
					for i, v := range pathTypeValues {
						if v == kind {
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
					action := string(sdBody(line))
					for i, v := range actionValues {
						if v == action {
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
					node.fromPath = intern(string(sdBody(line)))
				} else if bytes.HasPrefix(line, []byte("Text-copy-source-md5: ")) {
					if node == nil {
						node = new(NodeAction)
					}
					node.fromHash = intern(string(sdBody(line)))
				} else if bytes.HasPrefix(line, []byte("Text-content-md5: ")) {
					node.contentHash = intern(string(sdBody(line)))
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
	fromHash    string
	blob        *Blob
	props       *OrderedMap
	fromSet     *PathMap
	blobmark    markidx
	revision    revidx
	fromRev     revidx
	index       nodeidx
	kind        uint8
	action      uint8 // initially sdNONE
	generated   bool
	propchange  bool
}

func (action NodeAction) String() string {
	out := "<NodeAction: "
	out += fmt.Sprintf("r%d-%d", action.revision, action.index)
	out += " " + actionValues[action.action]
	out += " " + pathTypeValues[action.kind]
	out += " '" + action.path + "'"
	if action.fromRev != 0 {
		out += fmt.Sprintf(" from=%d", action.fromRev) + "~" + action.fromPath
	}
	//if action.fromSet != nil && !action.fromSet.isEmpty() {
	//	out += " sources=" + action.fromSet.String()
	//}
	if action.generated {
		out += " generated"
	}
	if action.hasProperties() {
		out += " props=" + action.props.vcString()
	}
	return out + ">"
}

func (action NodeAction) hasProperties() bool {
	return action.props != nil
}

func (action NodeAction) isCopy() bool {
	return action.fromRev > 0
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
	for n := 0; n < maxWorkers; n++ { <-done }
}

// Cruft recognizers
var cvs2svnTagRE = regexp.MustCompile("This commit was manufactured by cvs2svn to create tag.*'([^']*)'")
var cvs2svnBranchRE = regexp.MustCompile("This commit was manufactured by cvs2svn to create branch.*'([^']*)'")

var blankline = regexp.MustCompile(`(?m:^\s*\n)`)

// Separator used for split part in a processed Subversion ID.
const splitSep = "."

// Path separator as found in Subversion dump files. Isolated because
// it might be "\" on OSes not to be mentioned in polite company.
var svnSep = string([]byte{os.PathSeparator})

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
func (sp *StreamParser) seekAncestor(node *NodeAction) *NodeAction {
	// Easy case: dump stream has intact hashes, and there is one.
	// This should handle file copies.
	if node.fromHash != "" {
		ancestor, ok := sp.hashmap[node.fromHash]
		if ok {
			logit(logTOPOLOGY, "r%d~%s -> %s (via hashmap)",
				node.revision, node.path, ancestor)
			return ancestor
		}
		logit(logTOPOLOGY, "r%d~%s -> expected node from-hash is missing - stream may be corrupt",
			node.revision, node.path)
	}

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
		// Ordinary inheritance, no node copy.
		// Contiguity assumption here
		lookback = sp.history.getActionNode(node.revision-1, node.path)
	}

	// We reach here with lookback still nil if the node is a non-copy add.
	if lookback == nil && node.isCopy() && !strings.HasSuffix(node.path, ".gitignore") {
		sp.shout(fmt.Sprintf("r%d~%s: missing ancestor node for non-.gitignore",
			node.revision, node.path))
	}
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
	timeit("filemaps")
	svnGenerateCommits(ctx, sp, options, baton)
	timeit("commits")
	svnSplitResolve(ctx, sp, options, baton)
	timeit("splits")
	svnProcessBranches(ctx, sp, options, baton)
	timeit("branches")
	svnLinkFixups(ctx, sp, options, baton)
	timeit("links")
	svnProcessJunk(ctx, sp, options, baton)
	timeit("dejunk")
	svnProcessTagEmpties(ctx, sp, options, baton)
	sp.timeMark("tagifying")
	svnProcessMergeinfos(ctx, sp, options, baton)
	sp.timeMark("merfwinfo")
	svnProcessCleanTags(ctx, sp, options, baton)
	timeit("tagcleaning")
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
	// FIXME: Profile this to see if it should be parallelized.
	//
	defer trace.StartRegion(ctx, "SVN Phase 2: filter properties").End()
	logit(logEXTRACT, "SVN Phase 2: filter properties")
	baton.startProgress("process SVN, phase 2: filter properties", uint64(len(sp.streamview)))
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
	baton.startProgress("process SVN, phase 3: build filemaps", uint64(len(sp.revisions)))
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
	// the first fileop, abd only at branch roots.
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
	baton.startProgress("process SVN, phase 4: directory copy expansion", uint64(len(sp.revisions)))

	ignorenode := func(nodepath string, explicit string) *NodeAction {
		blob := newBlob(sp.repo)
		ignores := subversionDefaultIgnores + explicit
		blob.setContent([]byte(ignores), noOffset)
		subnode := new(NodeAction)
		subnode.path = filepath.Join(nodepath, ".gitignore")
		subnode.action = sdADD
		subnode.kind = sdFILE
		subnode.blob = blob
		subnode.contentHash = fmt.Sprintf("%x", md5.Sum([]byte(ignores)))
		subnode.generated = true
		return subnode
	}

	nobranch := options.Contains("--nobranch")
	branchLatch := newStringSet()
	fileLatch := false
	for ri, record := range sp.revisions {
		expandedNodes := make([]*NodeAction, 0)
		for _, node := range record.nodes {
			appendExpanded := func(newnode *NodeAction) {
				newnode.index = intToNodeidx(len(expandedNodes) + 1)
				newnode.revision = intToRevidx(ri)
				expandedNodes = append(expandedNodes, newnode)
			}
			prependExpanded := func(newnode *NodeAction) {
				newnode.index = intToNodeidx(len(expandedNodes) + 1)
				newnode.revision = intToRevidx(ri)
				expandedNodes = append([]*NodeAction{newnode}, expandedNodes...)
			}
			// Starting with the nodes in the Subversion
			// dump, expand them into a set that unpacks
			// all directory operations into equivalent
			// sets of file operations.
			//
			// Set up default ignores just before the first file node
			// of each branch
			if node.kind == sdFILE && (!fileLatch || (isDeclaredBranch(filepath.Dir(node.path)) && !branchLatch.Contains(node.path))) {
				prependExpanded(ignorenode(filepath.Dir(node.path), ""))
				branchLatch.Add(node.path)
				fileLatch = true
			}
			// We always preserve the unexpanded directory
			// node. Many of these won't have an explicit
			// gitspace representation, but they may carry
			// properties that we will require in later
			// phases.
			expandedNodes = append(expandedNodes, node)
			if node.kind == sdDIR {
				// svnSep is appended to avoid collisions with path
				// prefixes.
				node.path += svnSep
				if node.fromPath != "" {
					node.fromPath += svnSep
				}
				// Whenever an svn:ignore property is set on a directory,
				// we want to generate a corresponding .gitignore
				if node.hasProperties() && node.props.has("svn:ignore") {
					prependExpanded(ignorenode(node.path, node.props.get("svn:ignore")))
					node.props.delete("svn:ignore")
				}
				// No special actions need to be taken when directories are added or changed, but see below for actions
				// that are taken in all cases.  The reason we suppress expansion on a declared branch is that
				// we are later going to turn this directory delete into a git deleteall for the branch.
				if (node.action == sdDELETE && (nobranch || !isDeclaredBranch(node.path))) || node.action == sdREPLACE {
					// A delete or replace with no from set
					// can occur if the directory is empty.
					// We can just ignore that case. Otherwise...
					if node.fromSet != nil {
						for _, child := range node.fromSet.pathnames() {
							logit(logEXTRACT, "r%d-%d~%s: deleting %s", node.revision, node.index, node.path, child)
							newnode := new(NodeAction)
							newnode.path = child
							newnode.revision = node.revision
							newnode.action = sdDELETE
							newnode.kind = sdFILE
							newnode.generated = true
							appendExpanded(newnode)
						}
					}
				}
				// Handle directory copies.
				if node.fromPath != "" {
					logit(logEXTRACT, "r%d-%d: directory copy to %s from r%d~%s",
						node.revision, node.index, node.path, node.fromRev, node.fromPath)
					// Now generate copies for all files in the
					// copy source directory.
					for _, source := range node.fromSet.pathnames() {
						found := sp.history.getActionNode(node.fromRev, source)
						if found == nil {
							logit(logSHOUT, "r%d-%d: can't find ancestor of %s at r%d",
								node.revision, node.index, source, node.fromRev)
							continue
						}
						subnode := new(NodeAction)
						subnode.path = node.path + source[len(node.fromPath):]
						subnode.revision = node.revision
						subnode.fromPath = found.path
						subnode.fromRev = found.revision
						subnode.fromHash = found.contentHash
						subnode.props = found.props
						subnode.action = sdADD
						subnode.kind = sdFILE
						subnode.generated = true
						logit(logTOPOLOGY, "r%d-%d: %s generated copy r%d~%s -> %s %s",
							node.revision, node.index, node.path, subnode.fromRev, subnode.fromPath, subnode.path, subnode)
						appendExpanded(subnode)
					}
				}
				// Allow GC to reclaim fromSet storage, we no longer need it
				node.fromSet = nil
			}
		}
		sp.revisions[ri].nodes = expandedNodes
	}

	baton.endProgress()
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
	baton.startProgress("process SVN, phase 5: build commits", uint64(len(sp.revisions)))

	var lastmark string
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
		sp.repo.legacyMap["SVN:" + commit.legacyID] = commit
		commit.setColor(colorGEN)
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
			if node.kind == sdDIR && isDeclaredBranch(node.path) {
				fileop := newFileOp(sp.repo)
				fileop.construct(deleteall, node.path)
				if !node.generated {
					commit.setColor(colorNONE)
				}
				commit.appendOperation(fileop)
			} else if node.kind == sdFILE {
				// All .cvsignores should be ignored as remnants from
				// a previous up-conversion to Subversion.
				// This is a philosophical choice; we're taking the
				//users' Subversion settings as authoritative
				// rather than trying to mimic the exact CVS behavior.
				if strings.HasSuffix(node.path, ".cvsignore") {
					continue
				}
				// Ignore and complain about explicit .gitignores
				// created, e.g, by git-svn.  In an ideal world we
				// would merge these with svn:ignore properties. but
				// this would be hairy and bug-prone. So we give
				// the user a heads-up and expect these to be
				// merged by hand.
				if strings.HasSuffix(node.path, ".gitignore") {
					if !node.generated &&
						!options.Contains("--user-ignores") {
						sp.shout(fmt.Sprintf("r%d~%s: user-created .gitignore ignored.",
							node.revision, node.path))
						continue
					}
				}
				ancestor = sp.seekAncestor(node)
				if node.action == sdDELETE {
					//assert node.blob == nil
					fileop := newFileOp(sp.repo)
					fileop.construct(opD, node.path)
					if !node.generated {
						commit.setColor(colorNONE)
					}
					commit.appendOperation(fileop)
				} else if node.action == sdADD || node.action == sdCHANGE || node.action == sdREPLACE {
					if node.blob != nil {
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
						// No ancestor, no blob. Has to be a
						// pure property change.  There's no
						// way to figure out what mark to use
						// in a fileop.
						logit(logWARN, "r%d~%s: permission information may be lost.",
							node.revision, node.path)
						continue
					}
					if node.blobmark == emptyMark {
						logit(logEXTRACT, "r%d: %s gets impossibly empty blob mark from ancestor %s, skipping",
							record.revision, node, ancestor)
						continue
					}

					if !node.hasProperties() && ancestor != nil && ancestor.hasProperties() {
						node.props = ancestor.props
					}

					// Time for fileop generation.
					fileop := newFileOp(sp.repo)
					fileop.construct(opM,
						nodePermissions(*node),
						node.blobmark.String(),
						node.path)
					if !node.generated {
						commit.setColor(colorNONE)
					}
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
			} else if node.action == sdDELETE || node.action == sdREPLACE {
				// These are directory actions.
				logit(logEXTRACT, "r%d: deleteall %s", record.revision, node.path)
				fileop := newFileOp(sp.repo)
				fileop.construct(deleteall)
				if !node.generated {
					commit.setColor(colorNONE)
				}
				commit.appendOperation(fileop)
			}
			baton.twirl()
		}

		// This early in processing, a commit with zero
		// fileops can only represent a dumpfile revision with
		// no nodes. This is pathological and probably means
		// the dump has been hand-edited, probably in a
		// well-meant attempt to produce a minimal test case.
		//
		// Wer log this as an error and do not generate a commit
		// for it.  That way we know that every commit has at
		// last one fileop.  It's a shame that we lose the
		// comment, but without at least fileoop we can't even
		// assign the commit to a branch, a defect which would cause
		// a lot of complications in the analysis later on.
		if len(commit.fileops) == 0 {
			logit(logEXTRACT, "empty revision at <%d>, comment %s, skipping.",
				ri, strconv.Quote(commit.Comment))
			continue
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
		if lastmark != "" {
			commit.setParentMarks([]string{lastmark})
		}
		lastmark = commit.mark

		commit.setMark(sp.repo.newmark())
		sp.repo.addEvent(commit)
		sp.repo.declareSequenceMutation("adding new commit")
	}
	baton.endProgress()
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
		loc int
		splits []int
	}
	splits := make([]splitRequest, 0)
	var reqlock sync.Mutex

	baton.startProgress("process SVN, phase 6a: split detection", uint64(len(sp.repo.events)))
	walkEvents(sp.repo.events, func(i int, event Event) {
		if commit, ok := event.(*Commit); ok {
			commit.sortOperations()
			var oldbranch string
			cliqueIndices := make([]int, 0)
			// We only generated M and D ops.  Therefore every
			// fileop has a Path member.  Wacky hack: by stashing
			// the split components in the unused Source and Target
			// nembers, we avoid having to recompute these when we
			// actually have to use tem
			for j, fileop := range commit.fileops {
				commit.fileops[j].Source, commit.fileops[j].Target = splitSVNBranchPath(fileop.Path)
				if commit.fileops[j].Source != oldbranch {
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

	baton.startProgress("process SVN, phase 6b: split resolution", uint64(len(splits)))
	// Can't parallelize this. That's OK, should be an unusual case.
	// Sort the splits in case parallel execution generatesd them out of order.
	const splitwarn = "\n[[Split portion of a mixed commit.]]\n"
	sort.Slice(splits, func(i, j int) bool {return splits[i].loc > splits[j].loc})
	for i, split := range splits {
		logit(logEXTRACT, "split commit at %d resolving to %d commits", split.loc, len(split.splits)+1)
		for _, idx := range split.splits {
			sp.repo.splitCommitByIndex(split.loc, idx)
		}
		base := sp.repo.events[split.loc].(*Commit)
		baseID := base.legacyID
		base.Comment += splitwarn
		base.legacyID += ".1"
		for j := 1; j <= len(split.splits); j++ {
			fragment := sp.repo.events[split.loc+j].(*Commit)
			fragment.legacyID = baseID + "." + strconv.Itoa(j+1)
			sp.repo.legacyMap["SVN:" + fragment.legacyID] = fragment
			fragment.Comment += splitwarn
			sp.splitCommits[intToRevidx(i)]++
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
	walkEvents(sp.repo.events, func(i int, event Event) {
		if commit, ok := event.(*Commit); ok {
			for i := range commit.fileops {
				fileop := commit.fileops[i]
				commit.Branch = fileop.Source
				fileop.Source = ""
				fileop.Path = fileop.Target
				fileop.Target = ""
			}
			matched := false
			for _, item := range control.branchMappings {
				result := GoReplacer(item.match, commit.Branch + svnSep, item.replace)
				if result != commit.Branch {
					matched = true
					commit.setBranch(filepath.Join("refs", result))
					break
				}
			}
			if !matched {
				if commit.Branch == "" {
					// File or directory is not under any recognizable branch.
					// Shuffle it off to a root branch.
					commit.setBranch(filepath.Join("refs", "heads", "root"))
				} else if commit.Branch == "trunk" {
					commit.setBranch(filepath.Join("refs", "heads", "master"))
				} else if strings.HasPrefix(commit.Branch, "tags") {
					commit.setBranch(filepath.Join("refs", commit.Branch))
				} else if strings.HasPrefix(commit.Branch, "branches") {
					commit.setBranch(filepath.Join("refs", "heads", commit.Branch[9:]))
				} else {
					// Uh oh
					commit.setBranch(filepath.Join("refs", "heads", commit.Branch))
					logit(logEXTRACT, "nonstandard branch %s at %s", commit.Branch, commit.idMe())
				}
			}
		}
	})
}

func svnLinkFixups(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	defer trace.StartRegion(ctx, "SVN Phase 8: parent link fixups").End()
	// Phase 8:
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
	// under the same name.  There really is no right answer here
	// - that is, no way to emulate Subversion's view of versions
	// from before the recreation in a Git DAG.  Choosing that
	// second (re-creating) branch copy favors the view from the
	// future.
	//
	// 3. Branch or tag creations followed by partial updates.
	// There's a case like this in tagpollute.svn in the test
	// suite.  Again, there is no ideal answer here, for the same
	// reason as in case 2.  And choosing the source revision of
	// the last partial update recreates the view from the future.
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
		logit(logEXTRACT, "SVN Phase 8: parent link fixups (skipped due to --nobranch)")
		return
	}
	logit(logEXTRACT, "SVN Phase 8a: branch link compilation")
	baton.startProgress("process SVN, phase 8a: branch link compilation", uint64(len(sp.streamview)))
	lastcopy := make(map[string]revlink)
	for index, node := range sp.streamview {
		if node.isCopy() {
			// Record branch copies in a form that is convenient for dealing with
			// improper tag copies like the tagpollute.svn testload.
			var targetbranch string
			if sp.isBranch(node.path) {
				targetbranch = node.path
			} else {
				branch := longestPrefix(sp.branchtrie(), []byte(node.path))
				if branch != nil {
					targetbranch = string(branch)
					logit(logEXTRACT, "r%d#%d: impure branch copy %s corrected to %s",
						node.revision, node.index, node.path, targetbranch)
				}
			}
			if targetbranch != "" {
				oldlink := lastcopy[targetbranch]
				// Record the last copy to the target branch.  Copies to subdirectories
				// are mapped to the most specific including branch.  These branch paths
				// wpuld have to be remapped before they can be used in gitspace, but this
				// should be all the information required to make gitspace branch links.
				// Ugh...unless a copy is based on a nontrivially split commit!
				var increment int
				if oldlink.source != node.fromRev {
					increment++
				}
				lastcopy[targetbranch] = revlink{source:node.fromRev,
					target:node.revision,
					copycount:oldlink.copycount+increment}
			}
		}
		baton.percentProgress(uint64(index) + 1)
	}

	// Now that we've collected all these connections, we can throw out the actual branches
	// and index by the way we're going to need to look these up.
	for _, v := range lastcopy {
		if v.copycount > 1 {
			logit(logSHOUT, "dubious copy set with links from %d revisions has target <%d>", v.copycount, v.target)
		}
		sp.branchlinks[v.target] = v.source
	}
	logit(logEXTRACT, "branchlinks are %v", sp.branchlinks)

	logit(logEXTRACT, "SVN Phase 8b: parent link fixups")
	baton.startProgress("process SVN, phase 8b: parent link fixups", uint64(len(sp.repo.events)))
	for index, event := range sp.repo.events {
		commit, ok := event.(*Commit)
		if !ok {
			continue
		}
		if sp.branches[commit.Branch] == nil {
			logit(logEXTRACT, "commit %s branch %s is rootless", commit.mark, commit.Branch)
			sp.branches[commit.Branch] = new(branchMeta)
			sp.branches[commit.Branch].root = commit
			rootmark, err := strconv.Atoi(commit.mark[1:])
			if err != nil {
				logit(logEXTRACT, "ill-formed mark %s at branch root of %s", commit.mark, commit)
				continue
			} else {
				parent := sp.branchlinks[intToRevidx(rootmark)]
				if parent == 0 {
					logit(logEXTRACT, "missing parent for %s", commit.idMe())
					// Must do this explicitly, because a default parent
					// mark was set back in Phase 4.
					commit.setParentMarks(nil)
				} else {
					// Because there is no revidxToMarkidx
					commit.setParentMarks([]string{fmt.Sprintf(":%d", rootmark)})
				}
			}
		} else {
			logit(logEXTRACT, "commit %s has parent %s on branch %s", commit.mark, sp.branches[commit.Branch].tip.mark, commit.Branch)
			commit.setParents([]CommitLike{sp.branches[commit.Branch].tip})
		}
		sp.branches[commit.Branch].tip = commit
		baton.percentProgress(uint64(index) + 1)
	}
	baton.endProgress()
	// FIXME: Make branch-tip resets
}

func svnProcessJunk(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	defer trace.StartRegion(ctx, "SVN Phase 9: de-junking").End()
	logit(logEXTRACT, "SVN Phase 9: de-junking")
	// Now clean up junk commits generated by cvs2svn.
	deleteables := make([]int, 0)
	newtags := make([]Event, 0)
	var mutex sync.Mutex
	safedelete := func(i int) {
		mutex.Lock()
		deleteables = append(deleteables, i)
		mutex.Unlock()
	}
	baton.startProgress("process SVN, phase 9: de-junking", uint64(len(sp.repo.events)))
	walkEvents(sp.repo.events, func(i int, event Event) {
		if commit, ok := event.(*Commit); ok {
			// It is possible for commit.Comment to be None if
			// the repository has been dumpfiltered and has
			// empty commits.  If that's the case it can't very
			// well have CVS artifacts in it.
			if commit.Comment == "" {
				sp.shout(fmt.Sprintf("r%s has no comment", commit.legacyID))
				goto loopend
			}
			// Commits that cvs2svn created as tag surrogates
			// get turned into actual tags.
			m := cvs2svnTagRE.FindStringSubmatch(commit.Comment)
			if len(m) > 1 && !commit.hasChildren() {
				fulltag := filepath.Join("refs", "tags", m[1])
				newtags = append(newtags, newReset(sp.repo, fulltag,
					commit.parentMarks()[0]))
				safedelete(i)
			}
			// cvs2svn-generated branch commits carry no informationn,
			// and just get removed.
			m = cvs2svnBranchRE.FindStringSubmatch(commit.Comment)
			if len(m) > 0 && !commit.hasChildren() {
				safedelete(i)
			}
			// Branch copies with no later commits on the branch should
			// lose their fileops so they'll be tagified in a later phase.
			if !commit.hasChildren() && len(commit.operations()) > 0  && commit.getColor() == colorGEN {
				logit(logEXTRACT, "pruning empty branch copy commit %s", commit.idMe())
				commit.setOperations(nil)
			}
		}
	loopend:
		baton.percentProgress(uint64(i) + 1)
	})
	baton.endProgress()
	sp.repo.delete(deleteables, []string{"--tagback"})
	sp.repo.events = append(sp.repo.events, newtags...)
}


func svnProcessMergeinfos(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	defer trace.StartRegion(ctx, "SVN Phase A: mergeinfo processing").End()
	logit(logEXTRACT, "SVN Phase A: mergeinfo processing")
	baton.startProgress("process SVN, phase A: mergeinfo pocessing", uint64(len(sp.revisions)))

	lastRelevantCommit := func(sp *StreamParser, maxRev revidx, path string, attr string) *Commit {
		// Make path look like a branch
		if path[:1] == svnSep {
			path = path[1:]
		}
		if path[len(path)-1] != svnSep[0] {
			path = path + svnSep
		}
		//logit(logEXTRACT, "looking back, maxRev=%d, path='%s', attr='%s'", maxRev, path, attr)
		// If the revision is split, try from the last split commit
		var legacyID string
		if sp.splitCommits[maxRev] == 0 {
			legacyID = fmt.Sprintf("SVN:%d", maxRev)
		} else {
			legacyID = fmt.Sprintf("SVN:%d.%d", maxRev, sp.splitCommits[maxRev])
		}
		// Find the commit object...
		obj, ok := sp.repo.legacyMap[legacyID]
		if !ok {
			return nil
		}
		for revision := sp.repo.eventToIndex(obj); revision > 0; revision-- {
			event := sp.repo.events[revision]
			if commit, ok := event.(*Commit); ok {
				b, ok := getAttr(commit, attr)
				//logit(logEXTRACT, "looking back examines %s looking for '%s'", commit.mark, b)
				if ok && b != "" && strings.HasPrefix(path, b) {
					//logit(logEXTRACT, "looking back returns %s", commit.mark)
					return commit
				}
			}
		}
		return nil
	}

	// Add links due to svn:mergeinfo and svnmerge-integrated properties
	mergeinfo := newPathMap()
	mergeinfos := make(map[revidx]*PathMap)
	getMerges := func(minfo *PathMap, path string) orderedStringSet {
		rawOldMerges, _ := minfo.get(path)
		var eMerges orderedStringSet
		if rawOldMerges == nil {
			eMerges = newOrderedStringSet()
		} else {
			eMerges = *rawOldMerges.(*orderedStringSet)
		}
		return eMerges
	}

	for revision, record := range sp.revisions {
		for _, node := range record.nodes {
			// We're only looking at directory nodes
			if node.kind != sdDIR {
				continue
			}
			// Mutate the mergeinfo according to copies
			if node.fromRev != 0 {
				//assert parseInt(node.fromRev) < parseInt(revision)
				fromMerges := mergeinfos[node.fromRev]
				if fromMerges == nil {
					fromMerges = newPathMap()
				}
				mergeinfo.copyFrom(node.path, fromMerges, node.fromPath)
				logit(logEXTRACT, "r%d~%s mergeinfo copied to %s",
					node.fromRev, node.fromPath, node.path)
			}
			// Mutate the filemap according to current mergeinfo.
			// The general case is multiline: each line may describe
			// multiple spans merging to this revision; we only consider
			// the end revision of each span.
			// Because svn:mergeinfo will persist like other properties,
			// we need to compare with the already present mergeinfo and
			// only take new entries into account when creating merge
			// links. Also, since merging will also inherit the
			// mergeinfo entries of the source path, we also need to
			// gather and ignore those.
			existingMerges := getMerges(mergeinfo, node.path)
			ownMerges := newOrderedStringSet()
			if node.hasProperties() {
				info := node.props.get("svn:mergeinfo")
				if info == "" {
					info = node.props.get("svnmerge-integrated")
				}
				if info != "" {
					for _, line := range strings.Split(info, "\n") {
						fields := strings.Split(line, ":")
						if len(fields) != 2 {
							continue
						}
						// One path, one range list
						fromPath, ranges := fields[0], fields[1]
						for _, span := range strings.Split(ranges, ",") {
							// Ignore single-rev fields, they are cherry-picks.
							// TODO: maybe we should even test if minRev
							// corresponds to some fromRev + 1 to ensure no
							// commit has been skipped.
							fields = strings.Split(span, "-")
							if len(fields) != 2 {
								continue
							}
							minRev, fromRev := fields[0], fields[1]
							// ignore non-inheritable revision ranges
							if fromRev[len(fromRev)-1] == '*' {
								fromRev = fromRev[:len(fromRev)-1]
							}
							// Import mergeinfo from merged branches
							past, ok := mergeinfos[intToRevidx(parseInt(fromRev))]
							if !ok {
								past = newPathMap()
							}
							pastMerges := getMerges(past, fromPath)
							existingMerges = existingMerges.Union(pastMerges)
							// SVN doesn't fit the merge range to commits on
							// the source branch; we need to find the latest
							// commit between minRev and fromRev made on
							// that branch.
							fromCommit := lastRelevantCommit(sp, intToRevidx(parseInt(fromRev)), fromPath, "Branch")
							if fromCommit == nil {
								sp.shout(fmt.Sprintf("cannot resolve mergeinfo source from revision %s for path %s.",
									fromRev, node.path))
							} else {
								legacyFields := strings.Split(fromCommit.legacyID, ".")
								if parseInt(legacyFields[0]) >= parseInt(minRev) {
									ownMerges.Add(fromCommit.mark)
								}
							}
						}
					}
				}
			}
			mergeinfo.set(node.path, &ownMerges)
			newMerges := ownMerges.Subtract(existingMerges)
			if len(newMerges) == 0 {
				continue
			}
			// Find the correct commit in the split case
			commit := lastRelevantCommit(sp, intToRevidx(revision), node.path, "Branch")
			if commit == nil || !strings.HasPrefix(commit.legacyID, fmt.Sprintf("%d", record.revision)) {
				// The reverse lookup went past the target revision
				sp.shout(fmt.Sprintf("cannot resolve mergeinfo destination to revision %d for path %s.",
					revision, node.path))
				continue
			}
			// Alter the DAG to express merges.
			nodups := make(map[string]bool)
			for _, mark := range newMerges {
				if nodups[mark] {
					continue
				}
				nodups[mark] = true
				parent := sp.repo.markToEvent(mark).(*Commit)
				commit.addParentCommit(parent)
				logit(logTOPOLOGY, "processed new mergeinfo from r%s to r%s.", parent.legacyID, commit.legacyID)
			}
			nodups = nil // Not necessary, but explicit is good
		}
		mergeinfos[intToRevidx(revision)] = mergeinfo.snapshot()
		baton.percentProgress(uint64(revision) + 1)
	}
	baton.endProgress()
}

func svnProcessTagEmpties(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase B:
	// Now we need to tagify all other commits without fileops, because git
	// is going to just discard them when we build a live repo and they
	// might possibly contain interesting metadata.
	//
	// * Commits from tag creation often have no real fileops since they come
	//   from a directory copy in Subversion and have their fileops removed
	//   in the de-junking phase. The annotated tag name is the basename
	//   of the SVN tag directory.  Note: This code relies on the previous
	//   pass to remove the fileeops from generated commits.
	//
	// * Same for branch-root commits. The tag name is the basename of the
	//   branch directory in SVN, with "-root" appended to distinguish them
	//   from SVN tags.
	//
	// * Commits at a branch tip that consist only of deleteall are also
	//   tagified if --nobranch is on.  It behaves as a directiobve to
	//   preserve as much as possible of the tree structure for postprocessing.
	//
	// * All other commits without fileops get turned into an annotated tag
	//   with name "emptycommit-<revision>".
	//
	defer trace.StartRegion(ctx, "SVN Phase B: tagify empty commits").End()
	logit(logEXTRACT, "SVN Phase B: tagify empty commits")
	baton.twirl()

	rootmarks := newOrderedStringSet() // stays empty if nobranch
	for _, meta := range sp.branches {
		if meta != nil {	// This condition skips dead branches
			rootmarks.Add(meta.root.mark)
		}
	}
	rootskip := newOrderedStringSet()
	rootskip.Add("trunk" + svnSep)
	rootskip.Add("root")
	tagname := func(commit *Commit) string {
		// Give branch and tag roots a special name, except for "trunk" and
		// "root" which do not come from a regular branch copy.
		if rootmarks.Contains(commit.mark) {
			name := branchbase(commit.Branch)
			if !rootskip.Contains(name) {
				if strings.HasPrefix(commit.Branch, "refs/tags/") {
					return name
				}
				return name + "-root"
			}
		}
		// Fallback to standard rules.
		return ""
	}
	taglegend := func(commit *Commit) string {
		// Tipdelete commits and branch roots don't get any legend.
		if len(commit.operations()) > 0 || (rootmarks.Contains(commit.mark) && !rootskip.Contains(branchbase(commit.Branch))) {
			return ""
		}
		// Otherwise, generate one for inspection.
		legend := []string{fmt.Sprintf("[[Tag from zero-fileop commit at Subversion r%s", commit.legacyID)}
		legend = append(legend, "]]\n")
		return strings.Join(legend, "")
	}
	sp.repo.tagifyEmpty(nil,
		/* tipdeletes */ options.Contains("--nobranch"),
		/* tagifyMerges */  false,
		/* canonicalize */  false,
		/* nameFunc */ tagname,
		/* legendFunc */  taglegend,
		/* createTags */ true,
		/* gripe */ sp.shout)
}

func svnProcessCleanTags(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase C:
	// cvs2svn likes to crap out sequences of deletes followed by
	// filecopies on the same node when it's generating tag commits.
	// These are lots of examples of this in the nut.svn test load.
	// These show up as redundant (D, M) fileop pairs.
	defer trace.StartRegion(ctx, "SVN Phase C: delete/copy canonicalization").End()
	logit(logEXTRACT, "SVN Phase C: delete/copy canonicalization")
	baton.startProgress("process SVN, phase C: delete/copy canonicalization", uint64(len(sp.repo.events)))
	walkEvents(sp.repo.events, func(idx int, event Event) {
		commit, ok := event.(*Commit)
		if !ok {
			return
		}
		count := 0
		for i := range commit.operations() {
			if i < len(commit.operations())-1 {
				if commit.operations()[i].op == opD && commit.operations()[i+1].op == opM {
					if commit.operations()[i].Path == commit.operations()[i+1].Path {
						commit.fileops[i].op = opX
						count++
					}
				}
			}
		}
		nonnil := make([]*FileOp, 0, len(commit.operations())-count)
		for _, op := range commit.operations() {
			if op.op != opX {
				nonnil = append(nonnil, op)
			}
		}
		commit.setOperations(nonnil)
		baton.percentProgress(uint64(idx) + 1)
	})
	baton.endProgress()
}

func svnProcessDebubble(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	// Phase D:
	// Remove spurious parent links caused by random cvs2svn file copies.
	// FIXME: Is this necessary given the way the branch links are now built?
	defer trace.StartRegion(ctx, "SVN Phase D: remove duplicate parent marks").End()
	logit(logEXTRACT, "SVN Phase D: remove duplicate parent marks")
	baton.startProgress("process SVN, phase D: remove duplicate parent marks", uint64(len(sp.repo.events)))
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
			sp.shout(fmt.Sprintf("r%s: duplicate parent marks", commit.legacyID))
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
	// renumber all commits
	defer trace.StartRegion(ctx, "SVN Phase E: renumber").End()
	logit(logEXTRACT, "SVN Phase E: renumber")
	sp.repo.renumber(1, baton)
}

// end

/*
The parts of the old code that have no equivalents in the new

type svnReader struct {
	branchlink           map[string]daglink
	branchcopies         stringSet
	generatedDeletes     []*Commit
	fileopBranchlinks    stringSet
	directoryBranchlinks stringSet
	activeGitignores     map[string]string
	large                bool
	splitCommits         map[revidx]int
	initialBranchIgnores map[string]bool // a flag for each branch where we have put the implicit svn's implicit
					     // ignore rules into a .gitignore file
}

func (action NodeAction) deleteTag() string {
	return action.path[:len(action.path)] + fmt.Sprintf("-deleted-r%d-%d", action.revision, action.index)
}

func (action NodeAction) hasDeleteTag() bool {
	return strings.Contains(action.path, "-deleted-")
}

type daglink struct {
	child  *Commit
	parent *Commit
}

// Only used in diagnostics
func (dl daglink) String() string {
	return fmt.Sprintf("%s->%s", dl.child.mark, dl.parent.mark)
}

func svnProcessClean(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	defer trace.StartRegion(ctx, "SVN Phase 2: clean tags to prevent anomalies.").End()
	logit(logEXTRACT, "SVN Phase 2: clean tags to prevent anomalies.")
	// Phase 2:
	//
	// Intervene to prevent lossage from tag/branch/trunk
	// deletions. The Subversion data model is that a history is a
	// sequence of surgical operations on a tree, and a tag is
	// just another branch of the tree. Tag/branch deletions are a
	// place where this clashes badly with the changeset-DAG model
	// used by git and oter DVCSes. Especially if the same
	// tag/branch is recreated later.  The stupid, obvious thing
	// to do would be to just nuke the tag/branch history from
	// here back to its origin point, but that will cause problems
	// if a future copy operation is ever sourced in the deleted
	// branch (and this does happen!) We deal with this by
	// renaming the deleted branch and patching any copy
	// operations from it in the future.
	//
	// Our first step is to refine our list so we only need to
	// walk through tags created more than once, otherwise this
	// pass can become a pig on large repositories.  Remember that
	// initially sp.streamview is a list of all nodes.
	//
	// The exit contract of this phase is that there (1) are no
	// branches with colliding names attached to different
	// revisions, (2) all branches but the most recent branch in a
	// collision clique get renamed in a predictable way, and (3)
	// all references to renamed tags and branches in the stream
	// are patched with the rename.
	//
	// This branch is linear-time in the number of nodes and quite
	// fast even on very large repositories.
	refcounts := make(map[string]int)
	baton.startProgress("process SVN, phase 2a: count tag references", uint64(len(sp.streamview)))
	for i, tagnode := range sp.streamview {
		if tagnode.action == sdADD && tagnode.kind == sdDIR && isDeclaredBranch(tagnode.path) {
			refcounts[tagnode.path]++
		}
		baton.percentProgress(uint64(i) + 1)
	}
	logit(logTAGFIX, "tag reference counts: %v", refcounts)
	baton.endProgress()
	// Use https://github.com/golang/go/wiki/SliceTricks recipe for filter in place
	// to select out nodes relevant to tag additions that step on each other and
	// their references.
	relevant := func(x *NodeAction) bool {
		return refcounts[x.path] > 1 || refcounts[filepath.Dir(x.path)] > 1 ||
			refcounts[x.fromPath] > 1 || refcounts[filepath.Dir(x.fromPath)] > 1
	}
	multiples := make([]*NodeAction, 0)
	oldlength := len(sp.streamview)
	baton.startProgress("process SVN, phase 2b: check tag relevance", uint64(oldlength))
	for i, x := range sp.streamview {
		if relevant(x) {
			multiples = append(multiples, x)
		}
		baton.percentProgress(uint64(i) + 1)
	}
	logit(logTAGFIX, "multiply-added directories: %v", sp.streamview)
	baton.endProgress()

	processed := 0
	logit(logTAGFIX, "before fixups: %v", sp.streamview)
	baton.startProgress("process SVN, phase 2c: recolor anomalous tags", uint64(len(sp.streamview)))
	for i := range multiples {
		srcnode := multiples[i]
		if multiples[i].kind != sdFILE && multiples[i].action == sdDELETE {
			newname := srcnode.deleteTag()
			logit(logTAGFIX, "r%d#%d~%s: tag deletion, renaming to %s.",
				srcnode.revision, srcnode.index, srcnode.path, newname)
			// First, run backward performing the branch
			// rename. Note, because we scan for deletions
			// in forward order, any previous deletions of
			// this tag have already been patched.
			for j := i - 1; j >= 0; j-- {
				tnode := multiples[j]
				if strings.HasPrefix(tnode.path, srcnode.path) && !tnode.hasDeleteTag() {
					newpath := newname + tnode.path[len(srcnode.path):]
					logit(logTAGFIX, "r%d#%d~%s: on tag deletion path mapped to %s.",
						tnode.revision, tnode.index, tnode.path, newname)
					tnode.path = newpath
				}
				baton.twirl()
			}
			// Then, run forward patching copy
			// operations.
			for j := i + 1; j < len(multiples); j++ {
				tnode := multiples[j]
				if tnode.action == sdDELETE && tnode.path == srcnode.path && !tnode.hasDeleteTag() {
					// Another deletion of this tag?  OK, stop patching copies.
					// We'll deal with it in a new pass once the outer loop gets
					// there
					logit(logTAGFIX, "r%d#%d~%s: tag patching stopping on duplicate.",
						srcnode.revision, srcnode.index, srcnode.path)
					goto breakout
				}
				if strings.HasPrefix(tnode.fromPath, srcnode.path) && !tnode.hasDeleteTag() {
					newfrom := newname + tnode.fromPath[len(srcnode.path):]
					logit(logEXTRACT, "r%d#%d~%s: on tag deletion from-path mapped to %s.",
						tnode.revision, tnode.index, tnode.fromPath, newfrom)
					tnode.fromPath = newfrom
				}
				baton.twirl()
			}
			logit(logTAGFIX, "r%d#%d: tag %s renamed to %s.",
				srcnode.revision, srcnode.index,
				srcnode.path, newname)
			srcnode.path = newname
			processed++
		}
	breakout:
		baton.percentProgress(uint64(i) + 1)
	}
	logit(logTAGFIX, "after fixups: %v", multiples)
	multiples = nil // Allow GC
	baton.endProgress()

	// Recognize branches
	if !options.Contains("--nobranch") {
		for _, node := range sp.streamview {
			if node.kind != sdFILE && node.action == sdADD && isDeclaredBranch(node.path) {
				sp.addBranch(node.path + svnSep)
				logit(logTOPOLOGY, "%s recognized as a branch", node.path+svnSep)
			}
		}
	}

	// Filter properties and build the revlinks map. This could be parallelized.
	sp.streamview = nil // Allow that view to be GCed
}

func svnProcessCommits(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	defer trace.StartRegion(ctx, "SVN Phase 4: build commits").End()
	nobranch := options.Contains("--nobranch")
	// Build commits
	logit(logEXTRACT, "SVN Phase 4: build commits")
	sp.splitCommits = make(map[revidx]int)
	baton.startProgress("process SVN, phase 4a: prepare commits and actions", uint64(len(sp.revisions)))
	type fiAction struct {
		node     *NodeAction
		ancestor *NodeAction
		fileop   *FileOp
	}
	baseCommits    := make([]*Commit,    len(sp.revisions))
	createdBlobs   := make([][]Event,    len(sp.revisions))
	createdCommits := make([][]Event,    len(sp.revisions))
	fiActions      := make([][]fiAction, len(sp.revisions))
	for ri, record := range sp.revisions {

		// Revision-property processing

		// Create actions corresponding to both
		// parsed and generated nodes.
		actions := make([]fiAction, 0)
		for _, node := range expandedNodes {
			if node.action == sdNONE {
				continue
			}
			// Ignore nodes on dead branches.  These needed
			// to be kept around as sources for branch copies but should not
			// appear in the conversion.  If there is ever going to be a
			// preserve option again it should operate here.
			if node.hasDeleteTag() {
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
			if node.kind == sdFILE {
				// All .cvsignores should be ignored as remnants from
				// a previous up-conversion to Subversion.
				// This is a philosophical choice; we're taking the
				//users' Subversion settings as authoritative
				// rather than trying to mimic the exact CVS behavior.
				if strings.HasSuffix(node.path, ".cvsignore") {
					continue
				}
				// Ignore and complain about explicit .gitignores
				// created, e.g, by git-svn.  In an ideal world we
				// would merge these with svn:ignore properties. but
				// this would be hairy and bug-prone. So we give
				// the user a heads-up and expect these to be
				// merged by hand.
				if strings.HasSuffix(node.path, ".gitignore") {
					if !node.generated &&
						!options.Contains("--user-ignores") {
						sp.shout(fmt.Sprintf("r%d~%s: user-created .gitignore ignored.",
							node.revision, node.path))
						continue
					}
				}
				ancestor = sp.seekAncestor(node)
				if node.action == sdDELETE {
					//assert node.blob == nil
					fileop := newFileOp(sp.repo)
					fileop.construct(opD, node.path)
					fileop.genflag = node.generated
					actions = append(actions, fiAction{node, ancestor, fileop})
				} else if node.action == sdADD || node.action == sdCHANGE || node.action == sdREPLACE {
					if node.blob != nil {
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
							createdBlobs[ri] = append(createdBlobs[ri], node.blob)
							// Blobs generated by reposurgeon
							// (e.g .gitignore content) have no
							// content hash.  Don't record
							// them, otherwise they'll all
							// collide :-)
							if node.contentHash != "" {
								sp.hashmap[node.contentHash] = node
							}
						}
					} else if ancestor != nil {
						node.blobmark = ancestor.blobmark
						logit(logEXTRACT, "r%d: %s gets blob '%s' from ancestor %s",
							record.revision, node, node.blobmark.String(), ancestor)
					} else {
						// No ancestor, no blob. Has to be a
						// pure property change.  There's no
						// way to figure out what mark to use
						// in a fileop.
						if !strings.HasSuffix(node.path, ".gitignore") {
							logit(logWARN, "r%d~%s: permission information may be lost.",
								node.revision, node.path)
						}
						continue
					}
					if node.blobmark == emptyMark {
						logit(logEXTRACT, "r%d: %s gets impossibly empty blob mark from ancestor %s, skipping",
							record.revision, node, ancestor)
						continue
					}

					if !node.hasProperties() && ancestor != nil && ancestor.hasProperties() {
						node.props = ancestor.props
					}

					// Time for fileop generation.
					fileop := newFileOp(sp.repo)
					fileop.construct(opM,
						nodePermissions(*node),
						node.blobmark.String(),
						node.path)
					fileop.genflag = node.generated
					actions = append(actions, fiAction{node, ancestor, fileop})
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
			} else if node.action == sdDELETE || node.action == sdREPLACE {
				// These are directory actions.
				logit(logEXTRACT, "r%d: deleteall %s", record.revision, node.path)
				fileop := newFileOp(sp.repo)
				fileop.construct(deleteall)
				fileop.genflag = node.generated
				actions = append(actions, fiAction{node, ancestor, fileop})
			}
			baton.twirl()
		}
		if logEnable(logEXTRACT) {
			logit(logEXTRACT, "Actions:")
			for _, action := range actions {
				// Format-string not \n terminated because the Node stringer does it.
				opr := strings.TrimSpace(action.fileop.String())
				logit(logEXTRACT, "reposurgeon: %v -> %v", action.node, opr)
			}
		}
		commit.setMark(sp.repo.newmark())
		baseCommits[ri] = commit
		fiActions[ri] = actions
		baton.percentProgress(uint64(ri))
	}
	baton.endProgress()
	baton.startProgress("process SVN, phase 4b: create commits from actions", uint64(len(sp.revisions)))
	var mutex sync.Mutex
	branchtrie := sp.branchtrie()
	seenRevisions := 0
	walkRevisions(sp.revisions, func(ri int, record *RevisionRecord) {
		seenRevisions++
		commit := baseCommits[ri]
		if commit == nil {
			return
		}
		actions := fiActions[ri]
		fiActions[ri] = nil
		// Time to generate commits from actions and fileops.
		// First, break the file operations into branch cliques.
		// In the normal case there will be only one such clique,
		// but in Subversion (unlike git) it is possible to make
		// a commit that modifies multiple branches.
		cliques := make(map[string][]*FileOp)
		for _, action := range actions {
			branch := string(longestPrefix(branchtrie, []byte(action.node.path)))
			cliques[branch] = append(cliques[branch], action.fileop)
			baton.twirl()
		}
		logit(logEXTRACT, "r%d: %d action(s) in %d clique(s)", record.revision, len(actions), len(cliques))
		// We say a clique is trivial if it contains a single fileop and that
		// fileop is a deleteall. We now count the number of non-trivial ones
		// and remember one of them, to use when it is in fact the only one.
		nontrivialCount := 0
		var nontrivialClique string
		for branch, ops := range cliques {
			if !(len(ops) == 1 && ops[0].op == deleteall) {
				nontrivialCount++
				nontrivialClique = branch
			}
		}
		// Create all commits corresponding to the revision
		newcommits := make([]Event, 0, len(cliques))
		commit.legacyID = fmt.Sprintf("%d", record.revision)
		if nontrivialCount == 1 || len(cliques) <= 1 {
			// If there are no cliques at all, there are no fileops, and we
			// generate a single empty commit.  If there is only a single
			// clique, we can also output a single commit.  If there are
			// multiple cliques but only one is non-trivial, it makes sense
			// to affect the corresponding fileops to the base commit.
			if nontrivialCount == 1 {
				commit.common = nontrivialClique
				commit.copyOperations(cliques[nontrivialClique])
				delete(cliques, nontrivialClique)
			} else if len(cliques) == 1 {
				for name, ops := range cliques {
					// only one iteration
					commit.common = name
					commit.copyOperations(ops)
					delete(cliques, name)
				}
			} else {
				// No file operation at all. Try nevertheless to assign a
				// common path to the commit using the longest common prefix of
				// all node paths.
				common := ""
				for i, node := range record.nodes {
					if i == 0 {
						common = node.path
					} else {
						for j := 0; j < len(common); j++ {
							if j > len(node.path) || node.path[j] != common[j] {
								common = common[:j]
								break
							}
						}
					}
				}
				// Prefix must end in a path separator
				commit.common = common[:strings.LastIndex(common, svnSep)+1]
			}
			commit.sortOperations()
			newcommits = append(newcommits, commit)
		}
		// It might be that the revision impacts several branches. If the other
		// impacted branches only are targets of a deleteall, then we already
		// added a commit to represent the meaty part of the revision. If there
		// are several non-trivial cliques, then we have no reason to treat one
		// as more important than the others, so no commit was previously
		// added. In all cases, we now create additional "split" commits
		// containing the changes from the revison separated by branches, and
		// sorted by branch name for reproducibility.
		if len(cliques) > 0 {
			cliqueBranches := make([]string, len(cliques))
			k := 0
			for branch := range cliques {
				cliqueBranches[k] = branch
				k++
			}
			sort.Strings(cliqueBranches)
			var split *Commit
			for i, branch := range cliqueBranches {
				split = commit.clone(sp.repo)
				split.common = branch
				// Sequence numbers for split commits are 1-origin
				split.legacyID += splitSep + strconv.Itoa(i+1)
				split.Comment += "\n[[Split portion of a mixed commit.]]\n"
				split.copyOperations(cliques[branch])
				split.sortOperations()
				newcommits = append(newcommits, split)
			}
		}
		// The revision is truly mixed if there is more than one clique
		// not consisting entirely of deleteall operations.
		if nontrivialCount > 1 {
			// Store the number of non-trivial splits
			mutex.Lock()
			sp.splitCommits[intToRevidx(ri)] = nontrivialCount
			mutex.Unlock()
		}
		//if len(newcommits) > 0 {
		//	logit(logEXTRACT, "New commits (%d): %v", len(newcommits), newcommits)
		//}
		createdCommits[ri] = newcommits
		baton.percentProgress(uint64(seenRevisions))
	})
	baton.endProgress()
	baton.startProgress("process SVN, phase 4c: create branchlinks and append events",
	                    uint64(len(sp.revisions)))
	for ri, record := range sp.revisions {
		// Make marks of split commits different from that of their base,
		// and populate the legacy map linearly to avoid unpredictable
		// mark creation ordering or concurrent map access.
		base := baseCommits[ri]
		for _, evt := range createdCommits[ri] {
			commit := evt.(*Commit)
			sp.repo.legacyMap[fmt.Sprintf("SVN:%s", commit.legacyID)] = commit
			if commit != base {
				commit.setMark(sp.repo.newmark())
			}
			logit(logEXTRACT, "r%d gets mark %s", record.revision, commit.mark)
		}
		// Deduce links between branches on the basis of copies. This
		// is tricky because a revision can be the target of multiple
		// copies.  Humans don't abuse this because tracking multiple
		// copies is too hard to do in a slow organic brain, but tools
		// like cvs2svn can generate large sets of them. cvs2svn seems
		// to try to copy each file && directory from the commit
		// corresponding to the CVS revision where the file was last
		// changed before the copy, which may be substantially earlier
		// than the CVS revision corresponding to the
		// copy. Fortunately, we can resolve such sets by the simple
		// expedient of picking the *latest* revision in them!
		// No code uses the result if branch analysis is turned off.
		// FIXME: Now that we have sp.revlinks, this could be simpler. 
		if !nobranch {
			for _, event := range createdCommits[ri] {
				if _, ok := sp.branchlink[base.mark]; ok {
					continue
				}
				newcommit := event.(*Commit)
				copies := make([]*NodeAction, 0)
				for _, noderef := range record.nodes {
					if noderef.fromRev != 0 && strings.HasPrefix(noderef.path, newcommit.common) {
						copies = append(copies, noderef)
					}

				}
				if len(copies) > 0 && logEnable(logTOPOLOGY) {
					logit(logSHOUT, "r%s: copy operations %s",
						newcommit.legacyID, copies)
				}
				// If the copies include one for the directory, use that as
				// the first parent: most of the files in the new branch
				// will come from that copy, and that might well be a full
				// branch copy where doing that way is needed because the
				// fileop for the copy didn't get generated and the commit
				// tree would be wrong if we didn't.
				//
				// Otherwise, user may have botched a branch creation by doing a
				// non-Subversion directory copy followed by a bunch of
				// Subversion adds. Blob hashes will match existing files,
				// but fromRev and fromPath won't be set at parse time.
				// Our code detects this case and makes file
				// backlinks, but can't deduce the directory copy.
				// Thus, we have to treat multiple file copies as
				// an instruction to create a gitspace branch.
				//
				// The guard len(copies) > 1 filters out copy op sets that are
				// *single* file copies. We're making an assumption
				// here that multiple file copies should always
				// trigger a branch link creation.  This assumption
				// could be wrong, which is why we emit a warning
				// message later on for branch links detected this
				// way
				//
				// Even with this filter you'll tend to end up with lots
				// of little merge bubbles with no commits on one side;
				// these have to be removed by a debubbling pass later.
				// I don't know what generates these things - cvs2svn, maybe.
				//
				// The second conjunct (newcommit.common not in
				// self.directoryBranchlink) filters out the
				// case where the user actually did do a previous
				// Subversion file copy to start the
				// branch, in which case we want to
				// link through that.
				var latest *NodeAction
				for _, noderef := range copies {
					if noderef.kind == sdDIR && noderef.path != "" && noderef.path == newcommit.common {
						latest = noderef
					}
				}
				if latest != nil {
					//fmt.Printf("adding directory branchlink = %s\n", newcommit.common)
					sp.directoryBranchlinks.Add(newcommit.common)
					logit(logTOPOLOGY, "r%s: directory copy with %s finds %s",
						newcommit.legacyID, copies, latest)
				} else if len(copies) > 1 && newcommit.common != "" &&
					!sp.directoryBranchlinks.Contains(newcommit.common) {
					for _, node := range copies {
						if latest == nil || node.fromRev > latest.fromRev {
							latest = node
						}
					}
					logit(logTOPOLOGY, "r%s: file copy matching %s finds %s",
						newcommit.legacyID, copies, latest)
				}
				if latest != nil {
					if latest.fromRev == 0 || latest.fromPath == "" {
						logit(logSHOUT, "r%s: copy source informatiopn invalid at %v. lookback failed", newcommit.legacyID, latest)
					} else {
						prev := sp.lastRelevantCommit(latest.fromRev, latest.fromPath, "common")
						if prev == nil {
							logit(logTOPOLOGY, "lookback for %s failed, not making branch link", latest)
						} else {
							//fmt.Printf("adding fileop branchlink = %s\n", newcommit.common)
							sp.fileopBranchlinks.Add(newcommit.common)
							sp.branchlink[newcommit.mark] = daglink{newcommit, prev}
							logit(logTOPOLOGY, "r%s: link %s (%s) back to r%d (mark=%s, common='%s')",
								newcommit.legacyID,
								newcommit.mark,
								newcommit.common,
								latest.fromRev,
								prev.mark,
								prev.common)
						}
					}
				}
				baton.twirl()
			}
		}
		// We're done, add all the new blobs and commits
		sp.repo.events = append(sp.repo.events, createdBlobs[ri]...)
		sp.repo.events = append(sp.repo.events, createdCommits[ri]...)
		createdBlobs[ri] = nil
		createdCommits[ri] = nil
		sp.repo.declareSequenceMutation("adding new commits")
		// End of processing for this Subversion revision.  If the
		// repo is large, we throw out file records for this node in
		// order to reduce the maximum working set from proportional
		// to two times the number of Subversion commits to one time.
		// What we give up is some detail in the diagnostic messages
		// on zero-fileop commits.
		if sp.large {
			sp.revisions[ri].nodes = make([]*NodeAction, 0)
			// This copy loop requires that NodeAction structures cannot contain
			// pointers to other NodeAction structures.
			for _, n := range record.nodes {
				if n.kind == sdDIR {
					sp.revisions[ri].nodes = append(sp.revisions[ri].nodes, n)
				}
			}
		}
		baton.percentProgress(uint64(ri))
	} // end of revision loop
	baton.endProgress()

	// Release history storage to be GCed
	sp.history = nil

	// Bail out if we have read no commits
	if len(sp.repo.commits(nil)) == 0 {
		sp.shout("empty stream or repository.")
		return
	}
	// Warn about dubious branch links
	sp.fileopBranchlinks.Remove("trunk" + svnSep)
}

func svnProcessRoot(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton) {
	defer trace.StartRegion(ctx, "SVN Phase 5: root tagification").End()
	logit(logEXTRACT, "SVN Phase 5: root tagification")
	baton.twirl()
	if logEnable(logEXTRACT) {
		logit(logEXTRACT, "at post-parsing time:")
		for _, commit := range sp.repo.commits(nil) {
			text := strings.TrimSpace(commit.Comment)
			if len(text) > 30 {
				text = text[:27] + "..."
			}
			proplen := 0
			if commit.hasProperties() {
				proplen = commit.properties.Len()
			}
			logit(logSHOUT, "r%-4s %4s %2d %2d '%s'",
				commit.legacyID, commit.mark,
				len(commit.operations()),
				proplen,
				text)
		}
	}
	// First, turn a no-op root commit into a tag
	if len(sp.repo.events) > 0 && len(sp.repo.earliestCommit().operations()) == 0 {
		if commits := sp.repo.commits(nil); len(commits[0].operations()) == 0 {
			if len(commits) >= 2 {
				initial, second := commits[0], commits[1]
				sp.repo.tagify(initial,
					"root",
					second.mark,
					fmt.Sprintf("[[Tag from root commit at Subversion r%s]]\n", initial.legacyID),
					true)
			}
		} else {
			sp.shout("could not tagify root commit.")
		}
	}
	baton.twirl()
}

func svnProcessBranches(ctx context.Context, sp *StreamParser, options stringSet, baton *Baton, timeit func(string)) {
	defer trace.StartRegion(ctx, "SVN Phase 5a: branch analysis").End()
	logit(logEXTRACT, "SVN Phase 5a: branch analysis")
	nobranch := options.Contains("--nobranch")

	// Computing this is expensive, so we try to do it seldom
	commits := sp.repo.commits(nil)

	// Now, branch analysis.
	if len(sp.branches) == 0 || nobranch {
		logit(logEXTRACT, "no branch analysis")
		var last *Commit
		for _, commit := range commits {
			commit.setBranch(filepath.Join("refs", "heads", "master") + svnSep)
			if last != nil {
				commit.setParents([]CommitLike{last})
			}
			last = commit
		}
	} else {
		const impossibleFilename = "//"
		// Instead, determine a branch for each commit...
		logit(logEXTRACT, fmt.Sprintf("Branches: %v", sp.branches))
		lastbranch := impossibleFilename
		branch := impossibleFilename
		baton.startProgress("process SVN, phase 5a: branch analysis", uint64(len(commits)))
		for idx, commit := range commits {
			//logit(logEXTRACT, "seeking branch assignment for %s with common prefix '%s'", commit.mark, commit.common)
			if lastbranch != impossibleFilename && strings.HasPrefix(commit.common, lastbranch) {
				logit(logEXTRACT, "branch assignment for %s from lastbranch '%s'", commit.mark, lastbranch)
				branch = lastbranch
			} else {
				// Prefer the longest possible branch
				// The branchlist is sorted, longest first
				m := longestPrefix(sp.branchtrie(), []byte(commit.common))
				if m == nil {
					branch = impossibleFilename
				} else {
					branch = string(m)
				}
			}
			logit(logEXTRACT, "branch assignment for %s is '%s'", commit.mark, branch)
			if branch != impossibleFilename {
				commit.setBranch(branch)
				for i := range commit.fileops {
					fileop := &commit.fileops[i]
					if fileop.op == opM || fileop.op == opD {
						fileop.Path = fileop.Path[len(branch):]
					} else if fileop.op == opR || fileop.op == opC {
						fileop.Source = fileop.Source[len(branch):]
						fileop.Target = fileop.Target[len(branch):]
					}
				}
			} else {
				commit.setBranch("root")
				sp.addBranch("root")
			}
			lastbranch = branch
			baton.percentProgress(uint64(idx))
		}
		baton.endProgress()
		timeit("branches")
		baton.startProgress("process SVN, phase 5b: rebuild parent links", uint64(len(commits)))
		// ...then rebuild parent links so they follow the branches
		for idx, commit := range commits {
			if sp.branches[commit.Branch] == nil {
				logit(logEXTRACT, "commit %s branch %s is rootless", commit.mark, commit.Branch)
				sp.branches[commit.Branch] = new(branchMeta)
				sp.branches[commit.Branch].root = commit
				commit.setParents(nil)
			} else {
				logit(logEXTRACT, "commit %s has parent %s on branch %s", commit.mark, sp.branches[commit.Branch].tip.mark, commit.Branch)
				commit.setParents([]CommitLike{sp.branches[commit.Branch].tip})
			}
			sp.branches[commit.Branch].tip = commit
			// Per-commit spinner disabled because this pass is fast
			baton.percentProgress(uint64(idx))
		}
		baton.endProgress()
		sp.timeMark("parents")
		baton.twirl()
		// The root branch is special. It wasn't made by a copy, so
		// we didn't get the information to connect it to trunk in the
		// last phase.
		var rootcommit *Commit
		for _, c := range commits {
			if c.Branch == "root" {
				rootcommit = c
				break
			}
		}
		if rootcommit != nil {
			earliest := sp.repo.earliestCommit()
			if rootcommit != earliest {
				sp.branchlink[rootcommit.mark] = daglink{rootcommit, earliest}
			}
		}
		timeit("root")
		// Add links due to Subversion copy operations
		if logEnable(logEXTRACT) {
			rootmarks := make([]string, 0)
			for _, meta := range sp.branches {
				rootmarks = append(rootmarks, meta.root.mark)
			}
			// Python version only displayed the branchlink values
			logit(logEXTRACT, "branch roots: %v, links: %v", rootmarks, sp.branchlink)
		}
		idx := 0
		baton.startProgress("process SVN, phase 5c: fixup branch links", uint64(len(sp.branchlink)))
		for _, item := range sp.branchlink {
			if item.parent.repo != sp.repo {
				// The parent has been deleted since, don't add the link;
				// this can only happen if parent was the now tagified root.
				continue
			}
			if !item.child.hasParents() && !sp.branchcopies.Contains(item.child.Branch) {
				// The branch wasn't created by copying another branch and
				// is instead populated by fileops. Prepend a deleteall to
				// ensure that it starts with a clean tree instead of
				// inheriting that of its soon to be added first parent.
				// The deleteall is put on the first commit of the branch
				// which has fileops or more than one child.
				commit := item.child
				for len(commit.children()) == 1 && len(commit.operations()) == 0 {
					commit = commit.firstChild()
				}
				if len(commit.operations()) > 0 || commit.hasChildren() {
					fileop := newFileOp(sp.repo)
					fileop.construct(deleteall)
					commit.prependOperation(*fileop)
					logit(logEXTRACT, "prepending delete at %s", commit.idMe())
					sp.generatedDeletes = append(sp.generatedDeletes, commit)
				}
			}
			var found bool
			for _, p := range item.child.parents() {
				if p == item.parent {
					found = true
					break
				}
			}
			if !found {
				item.child.addParentCommit(item.parent)
			}
			baton.percentProgress(uint64(idx))
			idx++
		}
		baton.endProgress()
		timeit("branchlinks")
		timeit("mergeinfo")
		if logEnable(logEXTRACT) {
			logit(logEXTRACT, "after branch analysis")
			for _, commit := range commits {
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
			}
		}
	}
	// Code controlled by --nobranch option ends.
}

*/
