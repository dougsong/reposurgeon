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
// documentation purposes, the Python convention of using leading
// underscores on field names to flag fields that should never be
// referenced outside a method of the associated struct.
//
// The capitalization of other fieldnames looks inconsistent because
// the code tries to retain the lowercase Python names and
// compartmentalize as much as possible to be visible only within the
// declaring package.  Some fields are capitalized for backwards
// compatibility with the setfield command in the Python
// implementation, others (like some members of FileOp) because
// there's an internal requirement that they be settable by the Go
// reflection primitives.
//
// Do 'help news' for a summary of recent changes.
//
// SPDX-License-Identifier: BSD-2-Clause

import (
	"archive/tar"
	"bufio"
	"bytes"
	"compress/gzip"
	"container/heap"
	"context"
	"crypto/sha1"
	"errors"
	"fmt"
	"html"
	"io"
	"io/ioutil"
	"log"
	"math"
	"net/http"
	_ "net/http/pprof"
	"os"
	"os/exec"
	"os/signal"
	"os/user"
	"path"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"runtime/debug"
	"runtime/pprof"
	"runtime/trace"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
	"unicode"
	"unicode/utf8"
	"unsafe" // Actually safe - only uses Sizeof

	shlex "github.com/anmitsu/go-shlex"
	orderedset "github.com/emirpasic/gods/sets/linkedhashset"
	difflib "github.com/ianbruene/go-difflib/difflib"
	shutil "github.com/termie/go-shutil"
	kommandant "gitlab.com/db48x/kommandant"
	terminal "golang.org/x/crypto/ssh/terminal"
	ianaindex "golang.org/x/text/encoding/ianaindex"
	fqme "gitlab.com/esr/fqme"
)

const version = "4.0-pre"

// Tuning constants and types

// Maximum number of 64-bit things (pointers) to allocate at once.
// Used in some code for efficient exponential chunk grabbing.
const maxAlloc = 100000

// Short types for these saves space in very large arrays of repository structures.
// But they're mainly here to avoid strings, which are expensive (16 bytes) in Go.
type markidx uint32 // Mark indicies
type blobidx uint32 // Blob indices. Should not be narrower than mark indices.
type revidx uint32  // Revision indices
type nodeidx uint16 // Node indices within revisions

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
// msgbox = malformed mailbox-style input.  Abort merging those changes.
//
// Unlabeled panics are presumed to be unrecoverable and intended to be
// full aborts indicating a serious internal error.  These will call a defer
// hook that nukes the on-disk storage for repositories.

type exception struct {
	class   string
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
	if err, ok := x.(*exception); ok && err.class == accept {
		return err
	}
	panic(x)
}

// Change these in the unlikely the event this is ported to Windows
const userReadWriteMode = 0644       // rw-r--r--
const userReadWriteSearchMode = 0775 // rwxrwxr-x

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

func islink(pathname string) bool {
	st, err := os.Stat(pathname)
	return err == nil && (st.Mode()&os.ModeSymlink) != 0
}

func relpath(dir string) string {
	wd, err := os.Getwd()
	if err != nil {
		panic(err)
	}
	if !strings.HasPrefix(dir, "/") {
		dir = "/" + dir
	}
	wd, err = filepath.Rel(wd, dir)
	if err != nil {
		panic(err)
	}
	return wd
}

func abspath(dir string) string {
	wd, err := os.Getwd()
	if err != nil {
		panic(err)
	}
	wd, err = filepath.Abs(dir)
	if err != nil {
		panic(err)
	}
	return wd
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

// getAttr emulates Python hasattr/getattr using the Go reflection system
// Current version can only return string-valued fields.
func getAttr(obj interface{}, fld string) (string, bool) {
	objValue := reflect.Indirect(reflect.ValueOf(obj))
	objType := objValue.Type()
	_, ok := objType.FieldByName(fld)
	if !ok {
		return "", false
	}
	return objValue.FieldByName(fld).String(), true
}

func setAttr(obj interface{}, name string, value string) error {
	rv := reflect.ValueOf(obj).Elem()

	structFieldValue := rv.FieldByName(name)

	if !structFieldValue.IsValid() {
		return fmt.Errorf("No such field: %s in obj", name)
	}
	// If obj field value is not settable an error is thrown
	if !structFieldValue.CanSet() {
		return fmt.Errorf("Cannot set %s field value", name)
	}

	f2v := rv.FieldByName(name)
	f2v.SetString(value)
	return nil
}

// stringEscape interprets backslash escapes in a token, such as is returned by
// the shlex package.  If the argument token was wrapped by Go string quotes
// they are stripped off.
func stringEscape(s string) (string, error) {
	if s[0] != '"' {
		s = `"` + s + `"`
	}
	return strconv.Unquote(s)
}

// This representation optimizes for small memory footprint at the expense
// of speed.  To make the opposite trade we would do the obvious thing with
// map[string] bool.
type orderedStringSet []string

func newOrderedStringSet(elements ...string) orderedStringSet {
	set := make([]string, 0)
	return append(set, elements...)
}

func (s orderedStringSet) Contains(item string) bool {
	for _, el := range s {
		if item == el {
			return true
		}
	}
	return false
}

func (s *orderedStringSet) Remove(item string) bool {
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

func (s *orderedStringSet) Add(item string) {
	for _, el := range *s {
		if el == item {
			return
		}
	}
	*s = append(*s, item)
}

func (s orderedStringSet) Subtract(other orderedStringSet) orderedStringSet {
	var diff orderedStringSet
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

func (s orderedStringSet) Intersection(other orderedStringSet) orderedStringSet {
	// Naive O(n**2) method - don't use on large sets if you care about speed
	var intersection orderedStringSet
	for _, item := range s {
		if other.Contains(item) {
			intersection = append(intersection, item)
		}
	}
	return intersection
}

func (s orderedStringSet) Union(other orderedStringSet) orderedStringSet {
	var union orderedStringSet
	union = s[:]
	for _, item := range other {
		if !s.Contains(item) {
			union = append(union, item)
		}
	}
	return union
}

func (s orderedStringSet) String() string {
	if len(s) == 0 {
		return "[]"
	}
	rep := "["
	for _, el := range s {
		rep += "\""
		rep += el
		rep += "\", "
	}
	return rep[0:len(rep)-2] + "]"
}

func (s orderedStringSet) Equal(other orderedStringSet) bool {
	if len(s) != len(other) {
		return false
	}
	// Naive O(n**2) method - don't use on large sets if you care about speed
	for _, item := range s {
		if !other.Contains(item) {
			return false
		}
	}
	return true
}

func (s orderedStringSet) Empty() bool {
	return len(s) == 0
}

func (s orderedStringSet) toStringSet() stringSet {
	out := newStringSet()
	for _, item := range s {
		out.store[item] = true
	}
	return out
}

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

// Elements bares the underlying map so we can iterate over its keys
func (s stringSet) Iterate() map[string]bool {
	return s.store
}

func (s stringSet) Ordered() orderedStringSet {
	oset := newOrderedStringSet()
	for item := range s.store {
		oset.Add(item)
	}
	return oset
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

func (s stringSet) toOrderedStringSet() orderedStringSet {
	ordered := make([]string, len(s.store))
	i := 0
	for el := range s.store {
		ordered[i] = el
		i++
	}
	sort.Strings(ordered)
	return ordered
}

func (s stringSet) String() string {
	if len(s.store) == 0 {
		return "[]"
	}
	// Need a stable outxput order because
	// this is used in regression tests.
	// It doesn't need to be fast.
	rep := "["
	for _, el := range s.toOrderedStringSet() {
		rep += "\""
		rep += el
		rep += "\", "
	}
	return rep[0:len(rep)-2] + "]"
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

func (s stringSet) Empty() bool {
	return len(s.store) == 0
}

func (s stringSet) Len() int {
	return len(s.store)
}

// A copy of the orderedStringSet code with the names changed to protect the innocent.
// Lack of generics is annoying.
type orderedIntSet []int

func newOrderedIntSet(elements ...int) orderedIntSet {
	set := make([]int, 0, len(elements))
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

func (s orderedIntSet) Equal(other orderedIntSet) bool {
	if len(s) != len(other) {
		return false
	}
	// Naive O(n**2) method - don't use on large sets if you care about speed
	for _, item := range s {
		if !other.Contains(item) {
			return false
		}
	}
	return true
}

func (s orderedIntSet) EqualWithOrdering(other orderedIntSet) bool {
	if len(s) != len(other) {
		return false
	}
	// Naive O(n**2) method - don't use on large sets if you care about speed
	for i := range s {
		if s[i] != other[i] {
			return false
		}
	}
	return true
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

func (s orderedIntSet) Min() int {
	var min = math.MaxInt32
	for _, v := range s {
		if v < min {
			min = v
		}
	}
	return min
}

func (s orderedIntSet) Sort() {
	sort.Slice(s, func(i, j int) bool { return s[i] < s[j] })
}

func (s *orderedIntSet) Pop() int {
	x := (*s)[len(*s)-1]
	*s = (*s)[:len(*s)-1]
	return x
}

func (s orderedIntSet) String() string {
	if len(s) == 0 {
		return "[]"
	}
	rep := "["
	for _, el := range s {
		rep += fmt.Sprintf("%d, ", el)
	}
	return rep[0:len(rep)-2] + "]"
}

/*
// FIXME: Someday, use this so reorder doesn't need to declare a separate heap type.
// Satisfy the heap interface
func (s orderedIntSet) Len() int           { return len(s) }
func (s orderedIntSet) Less(i, j int) bool { return s[i] < s[j] }
func (s orderedIntSet) Swap(i, j int)      { s[i], s[j] = s[j], s[i] }

func (s orderedIntSet) Push(x interface{}) {
	// Push and Pop use pointer receivers because they modify the
	// slice's length, not just its contents.
	s = append(s, x.(int))
}
*/

// fastOrderedIntSet is like orderedIntSet but optimizes for speed at the
// expense of space.
type fastOrderedIntSet struct{ set *orderedset.Set }

type fastOrderedIntSetIt struct{ it orderedset.Iterator }

func (x *fastOrderedIntSetIt) Next() bool {
	return x.it.Next()
}

func (x *fastOrderedIntSetIt) Index() int {
	return x.it.Index()
}

func (x *fastOrderedIntSetIt) Value() int {
	return x.it.Value().(int)
}

func newFastOrderedIntSet(x ...int) *fastOrderedIntSet {
	s := orderedset.New()
	for _, i := range x {
		s.Add(i)
	}
	return &fastOrderedIntSet{s}
}

func (s fastOrderedIntSet) Size() int {
	return s.set.Size()
}

func (s fastOrderedIntSet) Iterator() fastOrderedIntSetIt {
	return fastOrderedIntSetIt{it: s.set.Iterator()}
}

func (s fastOrderedIntSet) Values() []int {
	v := make([]int, s.Size())
	it := s.Iterator()
	for it.Next() {
		v[it.Index()] = it.Value()
	}
	return v
}

func (s fastOrderedIntSet) Contains(x int) bool {
	return s.set.Contains(x)
}

func (s *fastOrderedIntSet) Remove(x int) bool {
	if s.Contains(x) {
		s.set.Remove(x)
		return true
	}
	return false
}

func (s *fastOrderedIntSet) Add(x int) {
	s.set.Add(x)
}

func (s fastOrderedIntSet) Subtract(other *fastOrderedIntSet) *fastOrderedIntSet {
	p := orderedset.New()
	it := s.set.Iterator()
	for it.Next() {
		if !other.set.Contains(it.Value()) {
			p.Add(it.Value())
		}
	}

	return &fastOrderedIntSet{p}
}

func (s fastOrderedIntSet) Intersection(other *fastOrderedIntSet) *fastOrderedIntSet {
	p := orderedset.New()
	it := s.set.Iterator()
	for it.Next() {
		if other.set.Contains(it.Value()) {
			p.Add(it.Value())
		}
	}
	return &fastOrderedIntSet{p}
}

func (s fastOrderedIntSet) Union(other *fastOrderedIntSet) *fastOrderedIntSet {
	p := orderedset.New(s.set.Values()...)
	p.Add(other.set.Values()...)
	return &fastOrderedIntSet{p}
}

func (s fastOrderedIntSet) Sort() *fastOrderedIntSet {
	v := s.set.Values()
	sort.Slice(v, func(i, j int) bool { return v[i].(int) < v[j].(int) })
	return &fastOrderedIntSet{orderedset.New(v...)}
}

func (s fastOrderedIntSet) String() string {
	var b strings.Builder
	b.WriteRune('[')
	it := s.Iterator()
	for it.Next() {
		if it.Index() > 0 {
			b.WriteString(", ")
		}
		b.WriteString(strconv.Itoa(it.Value()))
	}
	b.WriteRune(']')
	return b.String()
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
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
// ${tempfile} in a command gets substituted with the name of a
// tempfile that the calling code will know to read or write from as
// appropriate after the command is done.  If your exporter can simply
// dump to stdout, or your importer read from stdin, leave out the
// ${tempfile}; reposurgeon will popen(3) the command, and it will
// actually be slightly faster (especially on large repos) because it
// won't have to wait for the tempfile I/O to complete.
//
// ${basename} is replaced with the basename of the repo directory.

// VCS is a class representing a version-control system.
type VCS struct {
	name         string
	subdirectory string
	exporter     string
	styleflags   orderedStringSet
	extensions   orderedStringSet
	initializer  string
	lister       string
	importer     string
	checkout     string
	preserve     orderedStringSet
	prenuke      orderedStringSet
	authormap    string
	ignorename   string
	dfltignores  string
	cookies      []regexp.Regexp
	project      string
	notes        string
}

// Constants needed in VCS class methods
const suffixNumeric = `[0-9]+(\s|[.]\n)`
const tokenNumeric = `\s` + suffixNumeric
const dottedNumeric = `\s[0-9]+(\.[0-9]+)`

func (vcs VCS) String() string {
	realignores := newOrderedStringSet()
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
		fmt.Sprintf("      Prenuke: %s\n", vcs.prenuke.String()) +
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
	for i := range vcs.cookies {
		if vcs.cookies[i].Find(comment) != nil {
			return true
		}
	}
	return false
}

type Importer struct {
	name    string    // importer name
	visible bool      // should it be selectable?
	engine  Extractor // Import engine, either a VCS or extractor class
	basevcs *VCS      // Underlying VCS if engine is an extractor
}

var vcstypes []VCS
var importers []Importer
var nullStringSet stringSet
var nullOrderedStringSet orderedStringSet

// This one is special because it's used directly in the Subversion
// dump parser, as well as in the VCS capability table.
const subversionDefaultIgnores = `# A simulation of Subversion default ignores, generated by reposurgeon.
*.o
*.lo
*.la
*.al
*.libs
*.so
*.so.[0-9]*
*.a
*.pyc
*.pyo
*.rej
*~
*.#*
.*.swp
.DS_store
# Simulated Subversion default ignores end here
`

func init() {
	vcstypes = []VCS{
		{
			name:         "git",
			subdirectory: ".git",
			exporter:     "git fast-export --signed-tags=verbatim --tag-of-filtered-object=drop --all",
			styleflags:   newOrderedStringSet(),
			extensions:   newOrderedStringSet(),
			initializer:  "git init --quiet",
			importer:     "git fast-import --quiet",
			checkout:     "git checkout",
			lister:       "git ls-files",
			prenuke:      newOrderedStringSet(".git/config", ".git/hooks"),
			preserve:     newOrderedStringSet(".git/config", ".git/hooks"),
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
			exporter:     "bzr fast-export --no-plain ${basename}",
			styleflags: newOrderedStringSet(
				"export-progress",
				"no-nl-after-commit",
				"nl-after-comment"),
			extensions: newOrderedStringSet(
				"empty-directories",
				"multiple-authors", "commit-properties"),
			initializer: "",
			lister:      "",
			importer:    "bzr fast-import -",
			checkout:    "bzr checkout",
			prenuke:     newOrderedStringSet(".bzr/plugins"),
			preserve:    newOrderedStringSet(),
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
			styleflags: newOrderedStringSet(
				"import-defaults",
				"nl-after-comment",
				"export-progress"),
			extensions:  newOrderedStringSet(),
			initializer: "hg init",
			lister:      "hg status -macn",
			importer:    "hg fastimport ${tempfile}",
			checkout:    "hg checkout",
			prenuke:     newOrderedStringSet(".hg/hgrc"),
			preserve:    newOrderedStringSet(".hg/hgrc"),
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
			styleflags:   newOrderedStringSet(),
			extensions:   newOrderedStringSet(),
			initializer:  "",
			lister:       "darcs show files",
			importer:     "darcs fastconvert import",
			checkout:     "",
			prenuke:      newOrderedStringSet(),
			preserve:     newOrderedStringSet(),
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
			styleflags:   newOrderedStringSet(),
			extensions:   newOrderedStringSet(),
			initializer:  "",
			lister:       "mtn list known",
			importer:     "",
			checkout:     "",
			prenuke:      newOrderedStringSet(),
			preserve:     newOrderedStringSet(),
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
			name:         "svn",
			subdirectory: "locks",
			exporter:     "svnadmin dump .",
			styleflags:   newOrderedStringSet("import-defaults", "export-progress"),
			extensions:   newOrderedStringSet(),
			initializer:  "svnadmin create .",
			importer:     "",
			checkout:     "",
			lister:       "",
			prenuke:      newOrderedStringSet(),
			preserve:     newOrderedStringSet("hooks"),
			authormap:    "",
			ignorename:   "",
			dfltignores: subversionDefaultIgnores,
			cookies:     reMake(`\sr?\d+([.])?\s`),
			project:     "http://subversion.apache.org/",
			notes:       "Run from the repository, not a checkout directory.",
		},
		{
			name:         "cvs",
			subdirectory: "CVSROOT", // Can't be Attic, that doesn't always exist.
			exporter:     "find . -name '*,v' -print | cvs-fast-export --reposurgeon",
			styleflags:   newOrderedStringSet("import-defaults", "export-progress"),
			extensions:   newOrderedStringSet(),
			initializer:  "",
			importer:     "",
			checkout:     "",
			lister:       "",
			prenuke:      newOrderedStringSet(),
			preserve:     newOrderedStringSet(),
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
			cookies: reMake(dottedNumeric, dottedNumeric+`\w`),
			project: "http://www.catb.org/~esr/cvs-fast-export",
			notes:   "Requires cvs-fast-export.",
		},
		{
			name:         "rcs",
			subdirectory: "RCS",
			exporter:     "find . -name '*,v' -print | cvs-fast-export --reposurgeon",
			styleflags:   newOrderedStringSet("export-progress"),
			extensions:   newOrderedStringSet(),
			initializer:  "",
			importer:     "",
			checkout:     "",
			lister:       "",
			preserve:     newOrderedStringSet(),
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
			styleflags:   newOrderedStringSet(),
			extensions:   newOrderedStringSet(),
			initializer:  "src init",
			importer:     "",
			checkout:     "",
			lister:       "src ls",
			prenuke:      newOrderedStringSet(),
			preserve:     newOrderedStringSet(),
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
			styleflags:   newOrderedStringSet(),
			extensions:   newOrderedStringSet(),
			initializer:  "", // bk setup doesn't work here
			lister:       "bk gfiles -U",
			importer:     "bk fast-import -q",
			checkout:     "",
			prenuke:      newOrderedStringSet(),
			preserve:     newOrderedStringSet(),
			authormap:    "",
			ignorename:   "BitKeeper/etc/ignore",
			dfltignores:  "",                    // Has none
			cookies:      reMake(dottedNumeric), // Same as SCCS/CVS
			project:      "https://www.bitkeeper.com/",
			// No tag support, and a tendency to core-dump
			notes: "Bitkeeper's importer is flaky and incomplete as of 7.3.1ce.",
		},
	}

	for i := range vcstypes {
		vcs := &vcstypes[i]
		importers = append(importers, Importer{
			name:    vcs.name,
			visible: true,
			engine:  nil,
			basevcs: vcs,
		})
	}
	// Append extractors to this list
	importers = append(importers, Importer{
		name:    "git-extractor",
		visible: false,
		engine:  newGitExtractor(),
		basevcs: findVCS("git"),
	})
	importers = append(importers, Importer{
		name:    "hg-extractor",
		visible: true,
		engine:  newHgExtractor(),
		basevcs: findVCS("hg"),
	})
	nullStringSet = newStringSet()
	nullOrderedStringSet = newOrderedStringSet()
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

// CommitMeta is the extractor's idea of per-commit metadata
type CommitMeta struct {
	ci     string
	ai     string
	branch string
}

// Extractor specifies common features of all VCS-specific extractor classes
type Extractor interface {
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
	checkout(string) orderedStringSet
	// Return a commit's change comment as a string.
	getComment(string) string
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
			logit(logSHOUT, "Revision %s has branch '%s'\n", rev, cm.base.meta[rev].branch)
		}
	}
	// Depends on the order of the revlist to be correct.
	// The Python gode did a sort by timestamp here -
	// not necessary id your VCS dumps branches in
	// revlist-tip order.
	for _, refname := range base.refs.keys {
		logit(logTOPOLOGY, "outside branch coloring %s %s", base.refs.get(refname), refname)
		cm._branchColor(base.refs.get(refname), refname)
	}
}

// Exact value of this constant is unimportant, it just needs to be
// absurdly far in the future so no commit can have a committer date
// that's greater.  In fact it is 292277026596-12-04 10:30:07 -0500 EST
var farFuture = time.Unix(1<<63-1, 0)

func (cm *ColorMixer) _branchColor(rev, color string) {
	if cm.base.branchesAreColored && strings.HasPrefix(color, "refs/heads/") {
		return
	}
	logit(logTOPOLOGY, "inside branch coloring %s %s", rev, color)
	// This ensures that a branch tip rev never gets colored over
	if _, ok := cm.childStamps[rev]; !ok {
		cm.childStamps[rev] = farFuture
	}
	// This is used below to ensure that a branch color is never colored
	// back to a tag
	isBranchColor := strings.HasPrefix(color, "refs/heads/")
	logit(logTOPOLOGY, "%s is-a-branch is %v", color, isBranchColor)
	unassigned := func(rev string) bool {
		u := (cm.base.meta[rev].branch == "")
		logit(logTOPOLOGY, "%s assigned is %v", rev, u)
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
		logit(logTOPOLOGY, "parents of %s (%s) before filtering %v", rev, timestamp.UTC(), cm.base.getParents(rev))
		for _, p := range cm.base.getParents(rev) {
			if unassigned(p) || ((!(isBranchColor && onTagBranch(p))) && (cm.childStamps[p].Before(timestamp))) {
				parents = append(parents, p)
			}
		}
		logit(logTOPOLOGY, "parents of %s are %v", rev, parents)

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
	return ge
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

// checkout checks the repository out to a specified revision.
func (ge *GitExtractor) checkout(rev string) orderedStringSet {
	exec.Command("git", "checkout", "--quiet", rev).Run()
	data, err := captureFromProcess("git ls-files")
	if err != nil {
		panic(throw("extractor", "Couldn't spawn git ls-files in checkout: %v", err))
	}
	manifest := strings.Split(data, "\n")
	if manifest[len(manifest)-1] == "" {
		manifest = manifest[:len(manifest)-1]
	}
	return newOrderedStringSet(manifest...)
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
}

func newHgExtractor() *HgExtractor {
	// Regardless of what revision and branch was current at
	// start, after the hg extractor runs the tip (most recent
	// revision on any branch) will be checked out.
	ge := new(HgExtractor)
	return ge
}

//gatherRevisionIDs gets the topologically-ordered list of revisions and parents.
func (he *HgExtractor) gatherRevisionIDs(rs *RepoStreamer) error {
	// Belated initalization
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
	err := lineByLine(rs,
		`hg log --template '{node|short} {p1node|short} {p2node|short}\n'`,
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
	return lineByLine(rs,
		`hg log --template '{node|short}|{sub(r"<([^>]*)>", "", author|person)} <{author|email}> {date|rfc822date}\n'`,
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

	return lineByLine(nil,
		`hg log --template '{node|short} {date|rfc3339date}\n'`,
		"hg's gatherCommitTimestamps",
		hook)
}

// gatherAllReferences finds all branch heads and tags
func (he *HgExtractor) gatherAllReferences(rs *RepoStreamer) error {
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
		rs.refs.set("refs/heads/"+n, h)
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
		err = lineByLine(rs,
			"hg bookmarks",
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
	err = lineByLine(rs,
		`hg log --rev='tag()' --template='{tags}\t{node}\n'`,
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
	err := lineByLine(nil,
		`hg log --template '{node|short} {branch}\n'`,
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
		logit(logTOPOLOGY, "setting default branch of %s to %s", h, branch)
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
		logit(logEXTRACT, "no tags or bookmarks.")
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
			logit(logTOPOLOGY, "setting branch from color items, %s to %s", h, color)
			rs.meta[h].branch = color
		}
	} else {
		// Otherwise we have to emulate the git coloring algorithm
		he.simulateGitColoring(he, rs)
	}
	return nil
}

func (he *HgExtractor) postExtract(repo *Repository) {
	he.checkout("tip")
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
	logit(logSHUFFLE, "changing directory to %s", directory)
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
func (he HgExtractor) checkout(rev string) orderedStringSet {
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
			mustCaptureFromProcess("hg debugsetparents "+rev, "extracror")
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
	return newOrderedStringSet(strings.Split(manifest, "\n")...)
}

// getComment returns a commit's change comment as a string.
func (he HgExtractor) getComment(rev string) string {
	data, err := captureFromProcess("hg log -r " + rev + ` --template '{desc}\n'`)
	if err != nil {
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
	rs.hashToMark = make(map[[sha1.Size]byte]markidx)
	rs.extractor = extractor
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

func (rs *RepoStreamer) extract(repo *Repository, vcs *VCS) (*Repository, error) {
	if !rs.extractor.isClean() {
		return nil, fmt.Errorf("repository directory has unsaved changes")
	}

	//control.baton.startProcess("Extracting", "")
	//defer rs.baton.endProcess()

	var err error
	defer func(r **Repository, e *error) {
		if thrown := catch("extractor", recover()); thrown != nil {
			if strings.HasPrefix(thrown.class, "extractor") {
				croak(thrown.message)
				*e = errors.New(thrown.message)
				*r = nil
			}
		}
	}(&repo, &err)

	repo.makedir()
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

	// these two functions should chsnge only in sync
	//shortdump := func(hash [sha1.Size]byte) string {
	//	return fmt.Sprintf("%02x%02x%02x%02x%02x%02x",
	//		hash[0], hash[1], hash[2], hash[3], hash[4], hash[5])
	//}
	trunc := func(instr string) string {
		return instr[:12]
	}

	consume := make([]string, len(rs.revlist))
	copy(consume, rs.revlist)
	for _, revision := range consume {
		commit := newCommit(repo)
		rs.baton.twirl()
		present := rs.extractor.checkout(revision)
		//logit(logEXTRACT,
		//	"%s: present %v", trunc(revision), present)
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
		//	logit(logEXTRACT,
		//		"%s: comment '%s'", trunc(revision), msg)
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

		//logit(logEXTRACT,
		//	"%s: visible files '%s'", trunc(revision), rs.visibleFiles[revision])

		if len(present) > 0 {
			removed := rs.fileSetAt(revision).Subtract(present)
			for _, pathname := range present {
				if isdir(pathname) {
					continue
				}
				if !exists(pathname) {
					croak("%s: expected path %s does not exist!",
						trunc(revision), pathname)
					continue
				}
				newsig := newSignature(pathname)
				if _, ok := rs.hashToMark[newsig.hashval]; ok {
					//if debugEnable(logEXTRACT) {
					//	logit(logSHOUT, "%s: %s has old hash %v", trunc(revision), pathname, shortdump(newsig.hashval))
					//}
					// The file's hash corresponds
					// to an existing blob;
					// generate modify, copy, or
					// rename as appropriate.
					if _, ok := rs.visibleFiles[revision][pathname]; !ok || rs.visibleFiles[revision][pathname] != *newsig {
						//logit(logEXTRACT, "%s: update for %s", trunc(revision), pathname)
						found := false
						var deletia []string
						for _, item := range deletia {
							delete(rs.visibleFiles[revision], item)
						}
						if !found {
							op := newFileOp(repo)
							op.construct(opM,
								newsig.perms,
								rs.hashToMark[newsig.hashval].String(),
								pathname)
							commit.appendOperation(*op)
						}
					}
				} else {
					// Content hash doesn't match
					// any existing blobs
					//logit(logEXTRACT, "%s: %s has new hash %v",
					//	trunc(revision), pathname, shortdump(newsig.hashval))
					blobmark := markNumber(repo.newmark())
					rs.hashToMark[newsig.hashval] = blobmark
					// Actual content enters the representation
					blob := newBlob(repo)
					blob.setMark(blobmark.String())
					//logit(logEXTRACT, "%s: blob gets mark %s", trunc(revision), blob.mark)
					nBytes, _ := filecopy(pathname, blob.getBlobfile(true))
					blob.size = nBytes
					blob.addalias(pathname)
					repo.addEvent(blob)
					// Its new fileop is added to the commit
					op := newFileOp(repo)
					op.construct(opM, newsig.perms, blobmark.String(), pathname)
					commit.appendOperation(*op)
				}
				rs.visibleFiles[revision][pathname] = *newsig
			}
			for _, tbd := range removed {
				op := newFileOp(repo)
				op.construct(opD, tbd)
				commit.appendOperation(*op)
				delete(rs.visibleFiles[revision], tbd)
			}
		}
		if len(parents) == 0 { // && commit.Branch != "refs/heads/master"
			reset := newReset(repo, commit.Branch, commit.mark)
			repo.addEvent(reset)
		}
		commit.sortOperations()
		commit.legacyID = revision
		newprops := newOrderedMap()
		commit.properties = &newprops
		rs.commitMap[revision] = commit
		commit.setMark(repo.newmark())
		//logit(logEXTRACT, "%s: commit gets mark %s (%d ops)", trunc(revision), commit.mark, len(commit.operations()))
		repo.addEvent(commit)
	}
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

			reset := newReset(repo, resetname, committish)
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

// No user-serviceable parts below this line

/*
 * Debugging and utility
 *
 * The main point of this design is to make adding abd removing log
 * classes simple enough that it can be done ad-hoc for specific
 * debugging missions.  All you need to do to create a new class is
 * add a constant to the iota initializer and a corresponding entry to
 * logtags, then yoyu can use the constant in logit() and logEnable().
 * To remove a class just delete its entry pair.
 */

const (
	logSHOUT    uint = 1 << iota // Errors and urgent messages
	logWARN                      // Exceptional condition, probably not bug
	logTAGFIX                    // Log tag fixups
	logSVNDUMP                   // Log Subversion dumping
	logTOPOLOGY                  // Log repo-extractor logic (coarse-grained)
	logEXTRACT                   // Log repo-extractor logic (fine-grained)
	logFILEMAP                   // Log building of filemaps
	logDELETE                    // Log canonicalization after deletes
	logIGNORES                   // Log ignore generation
	logSVNPARSE                  // Lower-level Subversion parsing details
	logEMAILIN                   // Log round-tripping through msg{out|in}
	logSHUFFLE                   // Log file and directory handling
	logCOMMANDS                  // Show commands as they are executed
	logUNITE                     // Log mark assignments in merging
	logLEXER                     // Log selection-language parsing
)

var logtags = map[string]uint{
	"shout":    logSHOUT,
	"warn":     logWARN,
	"tagfix":   logTAGFIX,
	"svndump":  logSVNDUMP,
	"topology": logTOPOLOGY,
	"extract":  logEXTRACT,
	"filemap":  logFILEMAP,
	"delete":   logDELETE,
	"ignores":  logIGNORES,
	"svnparse": logSVNPARSE,
	"emailin":  logEMAILIN,
	"shuffle":  logSHUFFLE,
	"commands": logCOMMANDS,
	"unite":    logUNITE,
	"lexer":    logLEXER,
}

var optionFlags = [...][2]string{
	{"bigprofile",
		`Extra profiling for large repositories.  Mainly of interest to reposurgeon
developers.
`},
	{"canonicalize",
		`If set, import stream reads and msgin and edit will canonicalize
comments by replacing CR-LF with LF, stripping leading and trailing whitespace,
and then appending a LF.
`},
	{"compressblobs",
		`Use compression for on-disk copies of blobs. Accepts an increase
in repository read and write time in order to reduce the amount of
disk space required while editing; this may be useful for large
repositories. No effect if the edit input was a dump stream; in that
case, reposurgeon doesn't make on-disk blob copies at all (it points
into sections of the input stream instead).
`},
	{"echo",
		`Echo commands before executing them. Setting this im test scripts may
+make the output easuer to read.
`},
	{"experimental",
		`This flag is reserved for developer use.  If you set it, it could do
anything up to and including making demons fly out of your nose.
`},
	{"interactive",
		`Enable interactive responses even when not on a tty.
`},
	{"progress",
		`Enable fancy progress messages even when not on a tty.
`},
	{"relax",
		`Continue script execution on error, do not bail out.
`},
	{"serial",
		`Disable parallelism in code. Use for generating test loads.
`},
	{"testmode",
		`Disable some features that cause output to be vary depending on wall time, 
screen width, and the ID of the invoking user. Use in regression-test loads.
`},
	{"tighten",
		`Memory is at a premium, trade higher speed for lower usage.
`},
	{"quiet",
		`Suppress time-varying parts of reports.
`},
}

/*
 * Global context. Used to be named Context until its global
 * collided with the Go context package.
 */

type Control struct {
	logmask    uint
	logfp      io.Writer
	baton      *Baton
	logcounter int
	blobseq    blobidx
	signals    chan os.Signal
	logmutex   sync.Mutex
	// The abort flag
	abortScript    bool
	abortLock      sync.Mutex
	flagOptions    map[string]bool
	listOptions    map[string]orderedStringSet
	mapOptions     map[string]map[string]string
	branchMappings []branchMapping
	readLimit      uint64
	profilename    string
}

func (ctx *Control) isInteractive() bool {
	return ctx.flagOptions["interactive"]
}

type branchMapping struct {
	match   *regexp.Regexp
	replace string
}

func (ctx *Control) init() {
	ctx.flagOptions = make(map[string]bool)
	ctx.listOptions = make(map[string]orderedStringSet)
	ctx.mapOptions = make(map[string]map[string]string)
	ctx.signals = make(chan os.Signal, 1)
	ctx.logmask = (1 << logWARN) - 1
	baton := newBaton(control.isInteractive())
	var b interface{} = baton
	ctx.logfp = b.(io.Writer)
	ctx.baton = baton
	signal.Notify(control.signals, os.Interrupt)
	go func() {
		for {
			<-control.signals
			control.setAbort(true)
			respond("Interrupt\n")
		}
	}()

}

var control Control

func (ctx *Control) getAbort() bool {
	ctx.abortLock.Lock()
	defer ctx.abortLock.Unlock()
	return ctx.abortScript
}

func (ctx *Control) setAbort(cond bool) {
	ctx.abortLock.Lock()
	defer ctx.abortLock.Unlock()
	ctx.abortScript = cond
}

// whoami - ask various programs that keep track of who you are
func whoami() (string, string) {
	if control.flagOptions["testmode"] {
		return "Fred J. Foonly", "foonly@foo.com"
	}

	name, email, err := fqme.WhoAmI()
	if err == nil {
		return name, email
	}
	
	// Out of alternatives
	log.Fatal("can't deduce user identity!")
	return "", ""
}

// screenwidth returns the current width of the terminal window.
func screenwidth() int {
	width := 80
	if !control.flagOptions["testmode"] && terminal.IsTerminal(0) {
		var err error
		width, _, err = terminal.GetSize(0)
		if err != nil {
			log.Fatal(err)
		}
	}
	return width
}

/*
 * Logging and responding
 */

// logEnable is a hook to set up log-message filtering.
func logEnable(logbits uint) bool {
	return (control.logmask & logbits) != 0
}

// nuke removes a (large) directory, reporting elapsed time.
func nuke(directory string, legend string) {
	if exists(directory) {
		if !control.flagOptions["quiet"] {
			//control.baton.startProcess(legend, "")
			//defer control.baton.endProcess()
		}
		os.RemoveAll(directory)
	}
}

func croak(msg string, args ...interface{}) {
	content := fmt.Sprintf(msg, args...)
	control.baton.printLogString("reposurgeon: " + content + "\n")
	if !control.flagOptions["relax"] {
		control.setAbort(true)
	}
}

func logit(lvl uint, msg string, args ...interface{}) {
	if logEnable(lvl) {
		var leader string
		content := fmt.Sprintf(msg, args...)
		if _, ok := control.logfp.(*os.File); ok {
			leader = rfc3339(time.Now())
		} else {
			leader = "reposurgeon"
		}
		control.logmutex.Lock()
		control.logfp.Write([]byte(leader + ": " + content + "\n"))
		control.logcounter++
		control.logmutex.Unlock()
	}
}

// respond is to be used for console messages that shouldn't be logged
func respond(msg string, args ...interface{}) {
	if control.isInteractive() {
		content := fmt.Sprintf(msg, args...)
		control.baton.printLogString("reposurgeon: " + content + "\n")
	}
}

// Utility classes

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

// OrderedMap is a map with preserved key order
type OrderedMap struct {
	keys      []string
	dict      map[string]string
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
	for _, k := range d.keys {
		if hd == k {
			return
		}
	}
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

func (d *OrderedMap) Clear() {
	// Allow the storage to be GCed
	d.keys = nil
	d.dict = nil
}

func (d OrderedMap) String() string {
	var out = "{"
	for _, el := range d.keys {
		out += "'" + el + "': '" + d.dict[el] + "', "
	}
	if len(d.keys) > 0 {
		out = out[:len(out)-2]
	}
	return out + "}"
}

func (d OrderedMap) vcString() string {
	var out = "{"
	for _, el := range d.keys {
		val := d.dict[el]
		for _, vcs := range vcstypes {
			if val == vcs.dfltignores {
				val = "{{" + vcs.name + "-defaults}}"
				break
			}
		}
		out += "'" + el + "': '" + val + "', "
	}
	if len(d.keys) > 0 {
		out = out[:len(out)-2]
	}
	return out + "}"
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

// MessageBlockDivider is the separator between messages in a message-box.
var MessageBlockDivider = bytes.Repeat([]byte("-"), 78)

// MessageBlock is similar to net/mail's type, but the body is pulled inboard
// as a string.  This is appropriate because change comments are normally short.
type MessageBlock struct {
	hdnames orderedStringSet
	header  map[string]string
	body    string
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
			panic(throw("msgbox", "Ill-formed line in mail message"))
		}
		key := data[0:colon]
		payload := strings.TrimSpace(data[colon+1:])
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
				// RFC2822 continuation
				if len(msg.hdnames) >= 1 {
					lasthdr := msg.hdnames[len(msg.hdnames)-1]
					msg.setHeader(lasthdr,
						msg.getHeader(lasthdr)+string(line))
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
					line = line[1 : len(line)-1]
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

func (msg *MessageBlock) filterHeaders(regexp *regexp.Regexp) {
	// because iterator invalidation
	tmp := make([]string, len(msg.hdnames))
	copy(tmp, msg.hdnames)
	for _, key := range tmp {
		if !regexp.MatchString(key + ":") {
			msg.deleteHeader(key)
		}
	}
}

func (msg *MessageBlock) String() string {
	hd := string(MessageBlockDivider) + "\n"
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
			croak("no country-code to timezone mapping")
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

var gitDateRE = regexp.MustCompile(`^[0-9]+\s*[+-][0-9]+$`)
var zoneOffsetRE = regexp.MustCompile(`^([-+]?[0-9]{2})([0-9]{2})$`)

// locationFromZoneOffset makes a Go location object from a [+-]hhhmmm string.
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
		// According to RFC2822/RFC1123 we could put "-0000" in here to
		// indicate invalid zone information.
		return nil, errors.New("dubious zone offset " + string(offset))
	}
	tzname := intern(offset)
	tzoff := (hours*60 + mins) * 60
	return time.FixedZone(tzname, tzoff), nil
}

// Date wraps a system time object, giving it various serialization and
// deserialization capabilities.
type Date struct {
	timestamp time.Time
}

// GitLogFormat - which git falsely claims is RFC2822-conformant.
// In reality RFC2822 would be "Mon, 02 Aug 2006 15:04:05 -0700",
// which is Go's RFC1123Z format. (We're ignoring obsolete variants
// with letter zones and two-digit years.)
//
// FIXME: Alas, we cannot yet support GitLogFormat due to an apparent
// bug in time.Parse() For bug-isolation purposes we're currently
// faking it with a format Go can handle but that has the tz and year
// swapped.
//const GitLogFormat = "Mon Jan 02 15:04:05 2006 -0700"
const GitLogFormat = "Mon Jan 02 15:04:05 -0700 2006"
const RFC1123ZNoComma = "Mon 02 Jan 2006 15:04:05 -0700"

// newDate exists mainly to wrap a parser to recognize date formats that
// exporters or email programs might emit
func newDate(text string) (Date, error) {
	var t Date
	// Special case: we may want current time in UTC
	if len(text) == 0 {
		t.timestamp = time.Now().UTC()
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
	for _, layout := range []string{time.RFC3339, time.RFC3339Nano, time.RFC1123Z, GitLogFormat, RFC1123ZNoComma} {
		trial, err3 := time.Parse(layout, string(text))
		if err3 == nil {
			// Could be Round() rather than Truncate() - it's this way
			// for compatibility with the ancestral Python.
			t.timestamp = trial.Truncate(1 * time.Second)
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

func (date Date) rfc1123() string {
	// Alas, the format Go calls RFC822 is archaic
	return date.timestamp.Format(time.RFC1123Z)
}

func (date Date) delta(other Date) time.Duration {
	return other.timestamp.Sub(date.timestamp)
}

const dayHalf = (24 * 60 * 60) / 2

// String formats a Date object as an internal Git date (Unix time in seconds
// and a hhmm offset).
func (date Date) String() string {
	return fmt.Sprintf("%d %s", date.timestamp.Unix(), date.timestamp.Format("-0700"))
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

// Attribution pins a repository event to a person and time.
type Attribution struct {
	fullname string
	email    string
	date     Date
}

var attributionRE = regexp.MustCompile(`([^<]*\s*)<([^>]*)>+(\s*.*)`)

// parseAttributionLine parses a Git attribution line into its fields
func parseAttributionLine(line string) (string, string, string, error) {
	m := attributionRE.FindSubmatch(bytes.TrimSpace([]byte(line)))
	if m != nil {
		name := string(bytes.TrimSpace(m[1]))
		address := string(bytes.TrimSpace(m[2]))
		date := string(bytes.TrimSpace(m[3]))
		return name, address, date, nil
	}
	err := fmt.Errorf("malformed attribution on '%s'", line)
	return "", "", "", err
}

func (attr *Attribution) address() (string, string) {
	return attr.fullname, attr.email
}

// newAttribution makes an Attribution from an author or committer line
func newAttribution(attrline string) (*Attribution, error) {
	attr := new(Attribution)

	if attrline != "" {
		fullname, email, datestamp, err1 := parseAttributionLine(attrline)
		if err1 != nil {
			return attr, fmt.Errorf("malformed attribution: %v", err1)
		}
		parsed, err2 := newDate(datestamp)
		if err2 != nil {
			return attr,
				fmt.Errorf("malformed attribution date '%s' in '%s': %v",
					datestamp, attrline, err2)
		}
		// Deal with a cvs2svn artifact
		if fullname == "(no author)" {
			fullname = "no-author"
		}
		attr.fullname = intern(fullname)
		attr.email = intern(email)
		attr.date = parsed
	}
	return attr, nil
}

func (attr Attribution) String() string {
	return attr.fullname + " <" + attr.email + "> " + attr.date.String()
}

func (attr *Attribution) clone() *Attribution {
	mycopy, _ := newAttribution("")
	mycopy.fullname = attr.fullname
	mycopy.email = attr.email
	mycopy.date = attr.date.clone()
	return mycopy
}

// emailOut updates a message-block object with a representation of this
// attribution object.
func (attr *Attribution) emailOut(modifiers orderedStringSet, msg *MessageBlock, hdr string) {
	msg.setHeader(hdr, attr.fullname+" <"+attr.email+">")
	msg.setHeader(hdr+"-Date", attr.date.rfc1123())
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

// Cookie describes a VCS magic cookie embedded in a source file.
type Cookie struct {
	path string
	rev  string
}

func (c Cookie) isEmpty() bool {
	return c.path == "" && c.rev == ""
}

func (c Cookie) implies() string {
	// This is historically dubious - could be RCS, but there's no way
	// to distingish that from CVS
	if strings.Contains(c.rev, ".") {
		return "CVS"
	}
	return "svn"
}

const emptyMark = markidx(0)
const maxMark = ^markidx(0)

func (m markidx) String() string {
	if m == emptyMark {
		return ""
	}
	return fmt.Sprintf(":%d", m)
}

func markNumber(markstring string) markidx {
	n, _ := strconv.Atoi(markstring[1:])
	return markidx(n & int(^markidx(0)))
}

func intToMarkidx(markint int) markidx {
	return markidx(markint & int(^markidx(0)))
}

// Blob represents a detached blob of data referenced by a mark.
type Blob struct {
	mark         string
	abspath      string
	repo         *Repository
	pathlist     []string // In-repo paths associated with this blob
	pathlistmap  map[string]bool // optimisation for the above, kept in sync
	start        int64    // Seek start if this blob refers into a dump
	size         int64    // length start if this blob refers into a dump
	_expungehook *Blob
	cookie       Cookie // CVS/SVN cookie analyzed out of this file
	blobseq      blobidx
	colors       colorSet // Scratch space for graph-coloring algorithms
	deleteme     bool
}

const noOffset = -1

func newBlob(repo *Repository) *Blob {
	b := new(Blob)
	b.repo = repo
	b.pathlist = make([]string, 0) // These have an implied sequence.
	b.pathlistmap = map[string]bool{} // optimisation for pathlist
	b.start = noOffset
	b.blobseq = control.blobseq
	control.blobseq++
	if control.blobseq == ^blobidx(0) {
		panic("blob index overflow, rebuild with a larger size")
	}
	return b
}

func (b Blob) getDelFlag() bool {
	return b.deleteme
}

func (b *Blob) setDelFlag(t bool) {
	b.deleteme = t
}

// idMe IDs this blob for humans.
func (b *Blob) idMe() string {
	return fmt.Sprintf("blob@%s", b.mark)
}

// pathlist is implemented for uniformity with commits and fileops."
func (b *Blob) paths(_pathtype orderedStringSet) orderedStringSet {
	return newOrderedStringSet(b.pathlist...)
}

func (b *Blob) addalias(argpath string) {
	if _, ok := b.pathlistmap[argpath]; ok {
		return
	}
	b.pathlist = append(b.pathlist, argpath)
	b.pathlistmap[argpath] = true
}

func (b *Blob) replacealias(pos int, argpath string) {
	delete(b.pathlistmap, b.pathlist[pos])
	b.pathlist[pos] = argpath
	b.pathlistmap[argpath] = true
}

func (b *Blob) setBlobfile(argpath string) {
	file, _ := os.Open(argpath)
	info, _ := file.Stat()
	b.size = info.Size()
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
		[]string{"blobs", stem[0:3], stem[3:6], stem[6:]}...)
	if create {
		dir := strings.Join(parts[0:len(parts)-1], "/")
		err := os.MkdirAll(filepath.FromSlash(dir), userReadWriteSearchMode)
		if err != nil {
			panic(fmt.Errorf("Blob creation: %v", err))
		}
	}
	return filepath.FromSlash(strings.Join(parts[0:], "/"))
}

// hasfile answers the question: "Does this blob have its own file?"
func (b *Blob) hasfile() bool {
	return b.repo.seekstream == nil || b.start == noOffset
}

// getContent gets the content of the blob as a string.
func (b *Blob) getContent() []byte {
	if !b.hasfile() {
		var data = make([]byte, b.size)
		_, err := b.repo.seekstream.ReadAt(data, b.start)
		if err != nil {
			panic(fmt.Errorf("Blob fetch: %v", err))
		}
		return data
	}
	var data []byte
	file, err := os.Open(b.getBlobfile(false))
	if err != nil {
		panic(fmt.Errorf("Blob read: %v", err))
	}
	defer file.Close()
	if control.flagOptions["compressblobs"] {
		input, err2 := gzip.NewReader(file)
		if err2 != nil {
			panic(err.Error())
		}
		defer input.Close()
		data, err = ioutil.ReadAll(input)
	} else {
		data, err = ioutil.ReadAll(file)
	}
	if err != nil {
		panic(fmt.Errorf("Blob read: %v", err))
	}
	return data
}

type SectionReader struct {
	*io.SectionReader
}

func NewSectionReader(r io.ReaderAt, off int64, n int64) *SectionReader {
	return &SectionReader{io.NewSectionReader(r, off, n)}
}
func (sr SectionReader) Close() error {
	return nil
}

// getContentStream gets the content of the blob as a Reader.
func (b *Blob) getContentStream() io.ReadCloser {
	if !b.hasfile() {
		return NewSectionReader(b.repo.seekstream, b.start, b.size)
	}
	file, err := os.Open(b.getBlobfile(false))
	if err != nil {
		panic(fmt.Errorf("Blob read: %v", err))
	}
	if control.flagOptions["compressblobs"] {
		input, err2 := gzip.NewReader(file)
		if err2 != nil {
			panic(err.Error())
		}
		return input
	}
	return file
}

// setContent sets the content of the blob from a string.
// tell is the start offset of the data in the input source;
// if it noOffset, there is no seek stream and creation of
// an on-disk blob is forced.
func (b *Blob) setContent(text []byte, tell int64) {
	b.start = tell
	b.size = int64(len(text))
	if b.hasfile() {
		file, err := os.OpenFile(b.getBlobfile(true),
			os.O_WRONLY|os.O_CREATE|os.O_TRUNC, userReadWriteMode)
		if err != nil {
			panic(fmt.Errorf("Blob write: %v", err))
		}
		defer file.Close()
		if control.flagOptions["compressblobs"] {
			output := gzip.NewWriter(file)

			defer output.Close()
			_, err = output.Write(text)
		} else {
			_, err = file.Write(text)
		}
		if err != nil {
			panic(fmt.Errorf("Blob writer: %v", err))
		}
	}
}

// setContent sets the content of the blob from a string.
func (b *Blob) setContentFromStream(s io.ReadCloser) {
	// maybe the caller should close it?
	defer s.Close()
	b.start = noOffset
	file, err := os.OpenFile(b.getBlobfile(true),
		os.O_WRONLY|os.O_CREATE|os.O_TRUNC, userReadWriteMode)
	if err != nil {
		panic(fmt.Errorf("Blob write: %v", err))
	}
	defer file.Close()
	var nBytes int64
	if control.flagOptions["compressblobs"] {
		output := gzip.NewWriter(file)

		defer output.Close()
		nBytes, err = io.Copy(output, s)
	} else {
		nBytes, err = io.Copy(file, s)
	}
	if err != nil {
		panic(fmt.Errorf("Blob writer: %v", err))
	}
	b.size = nBytes
}

// materialize stores this content as a separate file, if it isn't already.
func (b *Blob) materialize() string {
	if b.start != noOffset {
		b.setContentFromStream(b.getContentStream())
	}
	return b.getBlobfile(false)
}

// what to treat as a coment when message-boxing
func (b Blob) getComment() string {
	return string(b.getContent())
}

// sha returns the SHA-1 hash of the blob content. Used only for indexing,
// does not need to be crypto-quality
func (b *Blob) sha() string {
	h := sha1.New()
	io.Copy(h, b.getContentStream())
	return fmt.Sprintf("%x", h.Sum(nil))
}

// getMark returns the blob's identifying mark
func (b Blob) getMark() string {
	return b.mark
}

// setMark sets the blob's mark
func (b *Blob) setMark(mark string) string {
	if b.repo != nil && !control.flagOptions["tighten"] {
		if b.repo._eventByMark == nil {
			b.repo.memoizeMarks()
		}
		b.repo._eventByMark[mark] = b
	}
	b.mark = mark
	return mark
}

// forget de-links this commit from its repo.
func (b *Blob) forget() {
	b.repo = nil
}

func (b Blob) isCommit() bool {
	return false
}

// moveto changes the repo this blob is associated with."
func (b *Blob) moveto(repo *Repository) {
	if b.hasfile() {
		oldloc := b.getBlobfile(false)
		b.repo = repo
		newloc := b.getBlobfile(true)
		logit(logSHUFFLE,
			"blob moveto calls os.rename(%s, %s)", oldloc, newloc)
		err := os.Rename(oldloc, newloc)
		if err != nil {
			panic(err)
		}
	}
}

// clone makes a fresh (uncolored) copy of this blob, pointing at the same file."
func (b *Blob) clone(repo *Repository) *Blob {
	c := b // copy scalar fields
	c.pathlist = make([]string, len(b.pathlist))
	copy(c.pathlist, b.pathlist)
	c.pathlistmap = map[string]bool{}
	for k := range b.pathlistmap {
		c.pathlistmap[k] = true
	}
	c.colors.Clear()
	if b.hasfile() {
		logit(logSHUFFLE,
			"blob clone for %s (%s) calls os.Link(): %s -> %s", b.mark, b.pathlist, b.getBlobfile(false), c.getBlobfile(false))
		err := os.Link(b.getBlobfile(false), c.getBlobfile(true))
		if err != nil {
			panic(fmt.Errorf("Blob clone: %v", err))
		}
	} else {
		logit(logSHUFFLE,
			"blob %s is not materialized.", b.mark)
	}
	return c
}

// Examples of embedded VCS headers:
// RCS, CVS: $Revision: 1.4 $
// SVN:      $Revision: 144 $
// RCS, CVS: $Id: lofs.h,v 1.8 1992/05/30 10:05:43 jsp Exp jsp $
// SVN:      $Id: calc.c 148 2006-07-28 21:30:43Z sally $
// Note that the SVN formats are distinguished from the CVS ones by the
// absence of a dot in the revision.  The Subversion book says Revision
// can also appear under the alias "Rev" or "LastChangedRev".
var dollarID = regexp.MustCompile(`\$Id *: *([^$]+) *\$`)
var dollarRevision = regexp.MustCompile(`\$Rev(?:ision) *: *([^$]*) *\$`)
var dollarLastChanged = regexp.MustCompile(`\$LastChangedRev *: *([^$]*) *\$`)

func (b *Blob) parseCookie(content string) Cookie {
	// Parse CVS && Subversion $-headers
	// There'd better not be more than one of these per blob.
	for _, m := range dollarID.FindAllStringSubmatch(content, 0) {
		fields := strings.Fields(m[0])
		if len(fields) == 2 {
			if strings.HasSuffix(fields[1], ",v") {
				b.cookie.path = fields[1][:len(fields[1])-2]
			} else {
				b.cookie.path = stringCopy(fields[1])
			}
			b.cookie.rev = stringCopy(fields[2])
		}
	}
	for _, m := range dollarRevision.FindAllStringSubmatch(content, 0) {
		b.cookie.rev = stringCopy(strings.TrimSpace(m[1]))
	}
	for _, m := range dollarLastChanged.FindAllStringSubmatch(content, 0) {
		b.cookie.rev = stringCopy(strings.TrimSpace(m[1]))
	}
	return b.cookie
}

// Save this blob in import-stream format without constructing a string
func (b *Blob) Save(w io.Writer) {
	if b.hasfile() {
		fn := b.getBlobfile(false)
		if !exists(fn) {
			return
		}
	}
	content := b.getContentStream()
	defer content.Close()
	fmt.Fprintf(w, "blob\nmark %s\ndata %d\n", b.mark, b.size)
	io.Copy(w, content)
	w.Write([]byte{'\n'})
}

// String serializes this blob into a string
func (b Blob) String() string {
	var bld strings.Builder
	b.Save(&bld)
	return bld.String()
}

// Tag describes a a gitspace annotated tag object
type Tag struct {
	repo       *Repository
	name       string
	committish string
	tagger     *Attribution
	Comment    string
	legacyID   string
	color      colorType
	deleteme   bool
}

func newTag(repo *Repository,
	name string, committish string,
	tagger *Attribution, comment string) *Tag {
	t := new(Tag)
	t.name = name
	t.tagger = tagger
	t.Comment = comment
	t.remember(repo, committish)
	return t
}

func (t Tag) getDelFlag() bool {
	return t.deleteme
}

func (t *Tag) setDelFlag(b bool) {
	t.deleteme = b
}

// getMark returns the tag's identifying mark
// Not actually used, needed to satisfy Event interface
func (t Tag) getMark() string {
	return ""
}

// remember records an attachment to a repo and commit.
func (t *Tag) remember(repo *Repository, committish string) {
	t.repo = repo
	t.committish = committish
	if repo != nil {
		if event := repo.markToEvent(committish); event != nil {
			event.(*Commit).attach(t)
		}
	}
}

// forget removes this tag's attachment to its commit and repo.
func (t *Tag) forget() {
	if event := t.repo.markToEvent(t.committish); event != nil {
		event.(*Commit).detach(t)
	}
	t.repo = nil
}

// moveto changes the repo this tag is associated with."
func (t *Tag) moveto(repo *Repository) {
	t.repo = repo
}

// index returns our 0-origin index in our repo.
func (t *Tag) index() int {
	return t.repo.eventToIndex(t)
}

// getComment returns the comment attached to a tag
func (t Tag) getComment() string { return t.Comment }

// idMe IDs this tag for humans."
func (t *Tag) idMe() string {
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
	}
	return t.legacyID
}

// tags enables do_tags() to report tags.
func (t *Tag) tags(modifiers orderedStringSet, eventnum int, _cols int) string {
	return fmt.Sprintf("%6d\ttag\t%s", eventnum+1, t.name)
}

// emailOut enables DoMsgout() to report tag metadata
func (t *Tag) emailOut(modifiers orderedStringSet, eventnum int,
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
	check := strings.Split(t.Comment, "\n")[0]
	if len(check) > 64 {
		check = check[0:64]
	}
	msg.setHeader("Check-Text", check)
	msg.setPayload(t.Comment)
	if t.Comment != "" && !strings.HasSuffix(t.Comment, "\n") {
		croak("in tag %s, comment was not LF-terminated.", t.name)
	}
	if filterRegexp != nil {
		msg.filterHeaders(filterRegexp)
	}
	return msg.String()
}

// emailIn updates this Tag from a parsed message block.
func (t *Tag) emailIn(msg *MessageBlock, fill bool) bool {
	tagname := msg.getHeader("Tag-Name")
	if tagname == "" {
		panic(throw("msgbox", "update to tag %s is malformed", t.name))
	}
	modified := false
	if t.name != tagname {
		logit(logEMAILIN,
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
			panic(throw("msgbox", "Can't recognize address in Tagger: "+newtagger))
		} else if t.tagger.fullname != newname || t.tagger.email != newemail {
			t.tagger.fullname, t.tagger.email = newname, newemail
			logit(logEMAILIN,
				"in tag %s, Tagger is modified",
				msg.getHeader("Event-Number"))
			modified = true
		}
		if taggerdate := msg.getHeader("Tagger-Date"); taggerdate != "" {
			date, err := newDate(taggerdate)
			if err != nil {
				panic(throw("msgbox", "Malformed date %s in tag message: %v",
					taggerdate, err))
			}
			if !t.tagger.date.isZero() && !date.timestamp.Equal(t.tagger.date.timestamp) {
				// If self.repo is nil this is filling
				// in fields in a a new tag creation,
				// so suppress the usual message.
				if t.repo != nil {
					logit(logSHOUT, "in %s, Tagger-Date is modified '%v' -> '%v' (delta %v)",
						t.idMe(),
						t.tagger.date, taggerdate,
						date.timestamp.Sub(t.tagger.date.timestamp))
				}
				modified = true
			}
			t.tagger.date = date
		}
	}

	if legacy := msg.getHeader("Legacy-ID"); legacy != "" && legacy != t.legacyID {
		modified = true
		t.legacyID = legacy
	}
	newcomment := msg.getPayload()
	if control.flagOptions["canonicalize"] {
		newcomment = strings.TrimSpace(newcomment)
		newcomment = strings.Replace(newcomment, "\r\n", "\n", 1)
		newcomment += "\n"
	}
	if newcomment != t.Comment {
		logit(logEMAILIN, "in tag %s, comment is modified %q -> %q",
			msg.getHeader("Event-Number"), t.Comment, newcomment)
		modified = true
		t.Comment = newcomment
	}

	if fill && t.tagger.fullname == "" {
		t.tagger.fullname, t.tagger.email = whoami()
		modified = true
	}

	return modified
}

func (t *Tag) decodable() bool {
	valid := func(s string) bool {
		return utf8.Valid([]byte(s))
	}
	return valid(t.name) && valid(t.tagger.fullname) && valid(t.tagger.email) && valid(t.Comment)
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
func (t *Tag) stamp(_modifiers orderedStringSet, _eventnum int, cols int) string {
	report := "<" + t.tagger.actionStamp() + "> " + strings.Split(t.Comment, "\n")[0]
	if cols > 0 {
		report = report[0:cols]
	}
	return report
}

// Save this tag in import-stream format without constructing a string
func (t *Tag) Save(w io.Writer) {
	fmt.Fprintf(w, "tag %s\n", t.name)
	if t.legacyID != "" {
		fmt.Fprintf(w, "#legacy-id %s\n", t.legacyID)
	}
	fmt.Fprintf(w, "from %s\n", t.committish)
	if t.tagger != nil {
		fmt.Fprintf(w, "tagger %s\n", t.tagger)
	}
	comment := t.Comment
	if t.repo.writeOptions.Contains("--legacy") && t.legacyID != "" {
		if comment != "" {
			comment += "\n"
		}
		comment += fmt.Sprintf("Legacy-ID: %s\n", t.legacyID)
	}
	fmt.Fprintf(w, "data %d\n%s\n", len(comment), comment)
}

// String serializes this tag in import-stream format
func (t Tag) String() string {
	var bld strings.Builder
	t.Save(&bld)
	return bld.String()
}

func (t Tag) isCommit() bool {
	return false
}

// Reset represents a branch creation."
type Reset struct {
	repo       *Repository
	ref        string
	committish string
	color      string
	deleteme   bool
}

func newReset(repo *Repository, ref string, committish string) *Reset {
	reset := new(Reset)
	reset.repo = repo
	reset.ref = ref
	if committish != "" {
		reset.committish = committish
		reset.remember(repo, committish)
	}
	return reset
}

func (reset Reset) getDelFlag() bool {
	return reset.deleteme
}

func (reset *Reset) setDelFlag(b bool) {
	reset.deleteme = b
}

func (reset Reset) isCommit() bool {
	return false
}

// idMe IDs this reset for humans.
func (reset *Reset) idMe() string {
	return fmt.Sprintf("reset-%s@%d", reset.ref, reset.repo.eventToIndex(reset))
}

// getMark returns the reset's identifying mark
// Not actually used, needed to satisfy Event interface
func (reset Reset) getMark() string {
	return ""
}

// what to treat as a coment when message-boxing (dummy to satify Event)
func (reset Reset) getComment() string {
	return ""
}

// remember records an attachment to a repo and commit.
func (reset *Reset) remember(repo *Repository, committish string) {
	reset.repo = repo
	reset.committish = committish
	if event := repo.markToEvent(committish); event != nil {
		event.(*Commit).attach(reset)
	}
}

// forget loses this reset's attachment to its commit and repo.
func (reset *Reset) forget() {
	if event := reset.repo.markToEvent(reset.committish); event != nil {
		event.(*Commit).detach(reset)
	}
	reset.repo = nil
}

// moveto changes the repo this reset is associated with."
func (reset *Reset) moveto(repo *Repository) {
	reset.repo = repo
}

// tags enables do_tags() to report resets."
func (reset Reset) tags(modifiers orderedStringSet, eventnum int, _cols int) string {
	return fmt.Sprintf("%6d\treset\t%s", eventnum+1, reset.ref)
}

// Save this reset in import-stream format without constructing a string
func (reset *Reset) Save(w io.Writer) {
	if reset.repo.realized != nil {
		var branch = reset.ref
		if strings.Contains(reset.ref, "^") {
			branch = strings.Split(reset.ref, "^")[0]
		}
		reset.repo.realized[branch] = true
	}
	fmt.Fprintf(w, "reset %s\n", reset.ref)
	if reset.committish != "" {
		fmt.Fprintf(w, "from %s\n\n", reset.committish)
	}
}

// String serializes this reset into a string
func (reset Reset) String() string {
	var bld strings.Builder
	reset.Save(&bld)
	return bld.String()
}

// FileOp is a gitspace file modification attached to a commit
type FileOp struct {
	repo       *Repository
	committish string
	Source     string
	Target     string
	mode       string
	Path       string
	ref        string
	inline     []byte
	op         rune
	genflag    bool
}

func (fileop *FileOp) Equals(other *FileOp) bool {
	return fileop.repo == other.repo &&
		fileop.committish == other.committish &&
		fileop.Source == other.Source &&
		fileop.Target == other.Target &&
		fileop.mode == other.mode &&
		fileop.Path == other.Path &&
		fileop.ref == other.ref &&
		bytes.Equal(fileop.inline, other.inline) &&
		fileop.op == other.op &&
		fileop.genflag == other.genflag
}

func newFileOp(repo *Repository) *FileOp {
	op := new(FileOp)
	op.repo = repo
	return op
}

func (fileop *FileOp) setOp(op rune) {
	fileop.op = op
}

// Thiis is a space-optimization hack.  We count on the compiler to
// put each of these in the text segment and pass around just one reference each.
// If we ever think the implementation has changed to falsify this assumption,
// we'll change these to var declarations and intern these strings explicitly.
const opM = 'M'
const opD = 'D'
const opR = 'R'
const opC = 'C'
const opN = 'N'
const opX = 'X' // used as a sentry value
const deleteall = 'd'

func (fileop *FileOp) construct(op rune, opargs ...string) *FileOp {
	fileop.op = op
	if op == 'M' {
		fileop.mode = opargs[0]
		fileop.ref = opargs[1]
		fileop.Path = opargs[2]
	} else if op == 'D' {
		fileop.Path = opargs[0]
	} else if op == 'N' {
		fileop.ref = opargs[0]
		fileop.Path = opargs[1]
	} else if op == 'R' {
		fileop.Source = opargs[0]
		fileop.Target = opargs[1]
	} else if op == 'C' {
		fileop.Source = opargs[0]
		fileop.Target = opargs[1]
	} else if op == 'd' {
	} else {
		panic(throw("parse", "unexpected fileop "+string(op)))
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
	for i := range input {
		c := input[i]
		//fmt.Fprintf(os.Stderr, "State %d, byte %c\n", state, c)
		switch state {
		case 0: // ground state, in whitespace
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
		case 1: // in token
			if unicode.IsSpace(rune(c)) {
				state = toState(c, 0)
			} else {
				tokenContinue(c)
			}
		case 2: // in string
			if c == '"' {
				tokenContinue(c)
				state = toState(c, 0)
			} else if c == '\\' {
				state = toState(c, 3)
			} else {
				tokenContinue(c)
			}
		case 3: // after \ in string
			state = toState(c, 2)
			tokenContinue(c)
		}
	}

	out := make([]string, len(bufs))
	for i, tok := range bufs {
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
		fileop.Path = intern(string(fields[3]))
	} else if strings.HasPrefix(opline, "N ") {
		if len(fields) != 3 {
			panic(throw("parse", "Bad format of N line: %q", opline))
		}
		fileop.op = opN
		fileop.ref = string(fields[1])
		fileop.Path = intern(string(fields[2]))
	} else if strings.HasPrefix(opline, "D ") {
		if len(fields) != 2 {
			panic(throw("parse", "Bad format of D line: %q", opline))
		}
		fileop.op = opD
		fileop.Path = intern(string(fields[1]))
	} else if strings.HasPrefix(opline, "R ") {
		if len(fields) != 3 {
			panic(throw("parse", "Bad format of R line: %q", opline))
		}
		fileop.op = opR
		fileop.Source = intern(fields[1])
		fileop.Target = intern(fields[2])
	} else if strings.HasPrefix(opline, "C ") {
		if len(fields) != 3 {
			panic(throw("parse", "Bad format of C line: %q", opline))
		}
		fileop.op = opC
		fileop.Source = intern(fields[1])
		fileop.Target = intern(fields[2])
	} else if strings.HasPrefix(opline, "deleteall") {
		fileop.op = deleteall
	} else {
		panic(throw("parse", "Unexpected fileop while parsing %q", opline))
	}
	return fileop
}

// paths returns the set of all paths touched by this file op
func (fileop *FileOp) paths(pathtype orderedStringSet) orderedStringSet {
	if pathtype == nil {
		pathtype = orderedStringSet{string(opM), string(opD), string(opR), string(opC), string(opN)}
	}
	if !pathtype.Contains(string(fileop.op)) {
		return orderedStringSet{}
	}
	if fileop.op == opM || fileop.op == opD || fileop.op == opN {
		return orderedStringSet{fileop.Path}
	}
	if fileop.op == opR || fileop.op == opC {
		return orderedStringSet{fileop.Source, fileop.Target}
	}
	// Ugh...this isn't right for deleteall, but since we don't expect
	// to see that except at branch tips we'll ignore it for now.
	if fileop.op == deleteall {
		return orderedStringSet{}
	}
	panic("Unknown fileop type " + string(fileop.op))
}

// relevant tells if two fileops touch any of the same files
func (fileop *FileOp) relevant(other *FileOp) bool {
	if fileop.op == deleteall || other.op == deleteall {
		return true
	}
	return len(fileop.paths(nil).Intersection(other.paths(nil))) > 0
}

// String dumps this fileop in import-stream format
func (fileop *FileOp) Save(w io.Writer) {
	quotifyIfNeeded := func(cpath string) string {
		if len(strings.Fields(cpath)) > 1 {
			return strconv.Quote(cpath)
		}
		return cpath
	}
	if fileop.op == opM {
		fmt.Fprintf(w, "M %s %s %s\n", fileop.mode, fileop.ref, quotifyIfNeeded(fileop.Path))
		if fileop.ref == "inline" {
			fmt.Fprintf(w, "data %d\n%s\n", len(fileop.inline), fileop.inline)
		}
		//return parts
	} else if fileop.op == opN {
		fmt.Fprintf(w, "N %s %s\n", fileop.ref, quotifyIfNeeded(fileop.Path))
		if fileop.ref == "inline" {
			fmt.Fprintf(w, "data %d\n%s\n", len(fileop.inline), fileop.inline)
		}
		//return parts
	} else if fileop.op == opD {
		fmt.Fprintf(w, "D %s\n", quotifyIfNeeded(fileop.Path))
	} else if fileop.op == opR || fileop.op == opC {
		fmt.Fprintf(w, "%c %q %q\n", fileop.op, fileop.Source, fileop.Target)
	} else if fileop.op == deleteall {
		w.Write([]byte("deleteall\n"))
	} else if fileop.op == 0 {
		// It's a nilOp, sometimes dumped during diagnostics
		w.Write([]byte("X\n"))
	} else {
		panic(throw("command", "Unexpected op %q while writing", fileop.op))
	}
}

// String serializes this FileOp in import-stream format
func (fileop FileOp) String() string {
	var bld strings.Builder
	fileop.Save(&bld)
	return bld.String()
}

// Callout is a stub object for callout marks in incomplete repository segments.
type Callout struct {
	mark        string
	branch      string
	_childNodes []string
	color       colorType
	deleteme    bool
}

func newCallout(mark string) *Callout {
	callout := new(Callout)
	callout.mark = mark
	callout._childNodes = make([]string, 0)
	return callout
}

func (callout *Callout) children() []CommitLike {
	var out []CommitLike
	return out
}
func (callout *Callout) hasChildren() bool {
	return false
}

func (callout Callout) getDelFlag() bool {
	return callout.deleteme
}

func (callout *Callout) setDelFlag(b bool) {
	callout.deleteme = b
}
func (callout Callout) callout() string {
	return callout.mark
}

func (callout Callout) getMark() string {
	return callout.mark
}

func (callout *Callout) idMe() string {
	return fmt.Sprintf("callout-%s", callout.mark)
}

// what to treat as a coment when message-boxing (dummy to satisfy Event)
func (callout Callout) getComment() string {
	return ""
}

// Save this blob in import-stream format without constructing a string
func (callout *Callout) Save(w io.Writer) {
	fmt.Fprintf(w, "callout-%s", callout.mark)
}

// String serializes this Callout in import-stream format
func (callout Callout) String() string {
	var bld strings.Builder
	callout.Save(&bld)
	return bld.String()
}

// moveto changes the repo this callout is associated with."
func (callout *Callout) moveto(*Repository) {
	// Has no repo field
}

func (callout Callout) isCommit() bool {
	return false
}

// ManifestEntry is visibility data about a file at a commit where it has no M
type ManifestEntry struct {
	mode   string
	ref    string
	inline []byte
}

func (callout Callout) getColor() colorType {
	return callout.color
}

func (callout *Callout) setColor(color colorType) {
	callout.color = color
}

func (m ManifestEntry) String() string {
	return fmt.Sprintf("<entry mode=%q ref=%q inline=%q>",
		m.mode, m.ref, m.inline)
}

func (m *ManifestEntry) equals(other *ManifestEntry) bool {
	return m.mode == other.mode && m.ref == other.ref &&
		bytes.Equal(m.inline, other.inline)
}

const colorNONE = 0
const colorEARLY = 1
const colorLATE = 2

type colorType uint8
type colorSet uint8

func (c colorSet) Contains(a colorType) bool {
	return uint8(1<<a) != 0
}

func (c *colorSet) Add(a colorType) {
	*c |= colorSet(1 << a)
}

func (c *colorSet) Remove(a colorType) {
	*c &= colorSet(^(1 << a))
}
func (c *colorSet) Clear() {
	*c = colorSet(0)
}

// Commit represents a commit event in a fast-export stream
type Commit struct {
	legacyID     string        // Commit's ID in an alien system
	common       string        // Used only by the Subversion parser
	mark         string        // Mark name of commit (may transiently be "")
	Comment      string        // Commit comment
	Branch       string        // branch name
	authors      []Attribution // Authors of commit
	committer    Attribution   // Person responsible for committing it.
	fileops      []FileOp      // blob and file operation list
	_manifest    *PathMap      // efficient map of *ManifestEntry values
	repo         *Repository
	properties   *OrderedMap  // commit properties (extension)
	attachments  []Event      // Tags and Resets pointing at this commit
	_parentNodes []CommitLike // list of parent nodes
	_childNodes  []CommitLike // list of child nodes
	_expungehook *Commit
	color        colorType // Scratch storage for graph-coloring
	deleteme     bool      // Flag used during deletion operations
}

func (commit Commit) getDelFlag() bool {
	return commit.deleteme
}

func (commit *Commit) setDelFlag(b bool) {
	commit.deleteme = b
}

func (commit Commit) getMark() string {
	return commit.mark
}

func newCommit(repo *Repository) *Commit {
	commit := new(Commit)
	commit.repo = repo
	commit.authors = make([]Attribution, 0)
	commit.fileops = make([]FileOp, 0)
	commit.attachments = make([]Event, 0)
	commit._childNodes = make([]CommitLike, 0)
	commit._parentNodes = make([]CommitLike, 0)
	return commit
}

func (commit Commit) isCommit() bool {
	return true
}

func (commit Commit) getColor() colorType {
	return commit.color
}

func (commit *Commit) setColor(color colorType) {
	commit.color = color
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
	return commit.repo.eventToIndex(commit)
}

// getComment returns the comment attached to a commit
func (commit Commit) getComment() string { return commit.Comment }

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
	if len(commit.authors) > 0 {
		return commit.authors[0].date
	}
	return commit.committer.date
}

// setBranch sets the repo's branch field.
func (commit *Commit) setBranch(branch string) {
	commit.Branch = intern(branch)
}

// operations returns a list of ileops associated with this commit;
// it hides how this is represented.
func (commit *Commit) operations() []FileOp {
	return commit.fileops
}

// setOperations replaces the set of fileops associated with this commit.
func (commit *Commit) setOperations(ops []FileOp) {
	commit.fileops = ops
	commit.invalidateManifests()
}

// setOperations replaces the set of fileops associated with this commit.
func (commit *Commit) copyOperations(ptrs []*FileOp) {
	ops := make([]FileOp, len(ptrs))
	for idx, p := range ptrs {
		ops[idx] = *p
	}
	commit.fileops = ops
	commit.invalidateManifests()
}

// appendOperation appends to the set of fileops associated with this commit.
func (commit *Commit) appendOperation(op FileOp) {
	commit.fileops = append(commit.fileops, op)
	commit.invalidateManifests()
}

// prependOperation prepends to the set of fileops associated with this commit.
func (commit *Commit) prependOperation(op FileOp) {
	commit.fileops = append([]FileOp{op}, commit.fileops...)
	commit.invalidateManifests()
}

// sortOperations sorts fileops on a commit the same way git-fast-export does
func (commit *Commit) sortOperations() {
	pathpart := func(fileop FileOp) string {
		if fileop.Path != "" {
			return fileop.Path
		}
		if fileop.Source != "" {
			return fileop.Source
		}
		return ""
	}
	// As it says, 'Handle files below a directory first, in case they are
	// all deleted and the directory changes to a file or symlink.'  First
	// sort the deletealls first, the renames last, then sort
	// lexicographically. We check the directory depth to make sure that
	// "a/b/c" < "a/b" < "a".
	lessthan := func(i, j int) bool {
		if commit.fileops[i].op == deleteall {
			return true
		} else if commit.fileops[j].op == deleteall {
			return false
		} else if (commit.fileops[i].op != opR && commit.fileops[j].op == opR) {
			return true
		} else {
			left := pathpart(commit.fileops[i])
			right := pathpart(commit.fileops[j])
			if len(left) > len(right) {
				return left[:len(right)] <= right
			}
			return left < right[:len(left)]
		}
	}
	sort.SliceStable(commit.fileops, lessthan)
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
	var c = *commit // Was a Python deepcopy
	c.authors = make([]Attribution, len(commit.authors))
	copy(c.authors, commit.authors)
	c.setOperations(nil)
	//c.filemap = nil
	c.color = colorNONE
	if repo != nil {
		c.repo = repo
	}
	c._childNodes = nil
	// use the encapsulation to set parents instead of relying
	// on the copy, so that Commit can do its bookkeeping.
	c._parentNodes = nil // avoid confusing set_parents()
	c.setParents(commit.parents())
	c.attachments = nil
	return &c
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

func (commit *Commit) hasProperties() bool {
	return commit.properties != nil
}

// lister enables do_list() to report commits.
func (commit *Commit) lister(_modifiers orderedStringSet, eventnum int, cols int) string {
	topline := strings.Split(commit.Comment, "\n")[0]
	summary := fmt.Sprintf("%6d %s %6s ",
		eventnum+1, commit.date().rfc3339(), commit.mark)
	if commit.legacyID != "" {
		legacy := fmt.Sprintf("<%s>", commit.legacyID)
		summary += fmt.Sprintf("%6s ", legacy)
	}
	report := summary + topline
	if cols > 0 && len(report) > cols {
		report = report[:cols]
	}
	return report
}

// stamp enables do_stamp() to report action stamps.
func (commit *Commit) stamp(modifiers orderedStringSet, _eventnum int, cols int) string {
	report := "<" + commit.actionStamp() + "> " + strings.Split(commit.Comment, "\n")[0]
	if cols > 0 && len(report) > cols {
		report = report[:cols]
	}
	return report
}

// tags enables do_tags() to report tag tip commits.
func (commit *Commit) tags(_modifiers orderedStringSet, eventnum int, _cols int) string {
	if commit.Branch == "" || !strings.Contains(commit.Branch, "/tags/") {
		return ""
	}
	if commit.hasChildren() {
		successorBranches := newStringSet()
		for _, child := range commit.children() {
			switch child.(type) {
			case *Commit:
				successorBranches.Add(child.(*Commit).Branch)
			case *Callout:
				croak("internal error: callouts do not have branches: %s",
					child.idMe())
			default:
				panic("In tags method, unexpected type in child list")
			}
		}
		if successorBranches.Len() == 1 && successorBranches.Contains(commit.Branch) {
			return ""
		}
	}
	return fmt.Sprintf("%6d\tcommit\t%s", eventnum+1, commit.Branch)
}

// emailOut enables DoMsgout() to report commit metadata.
func (commit *Commit) emailOut(modifiers orderedStringSet,
	eventnum int, filterRegexp *regexp.Regexp) string {
	msg, _ := newMessageBlock(nil)
	msg.setHeader("Event-Number", fmt.Sprintf("%d", eventnum+1))
	msg.setHeader("Event-Mark", commit.mark)
	msg.setHeader("Branch", commit.Branch)
	msg.setHeader("Parents", strings.Join(commit.parentMarks(), " "))
	commit.committer.emailOut(modifiers, msg, "Committer")
	if len(commit.authors) > 0 {
		commit.authors[0].emailOut(modifiers, msg, "Author")
		for i, coauthor := range commit.authors[1:] {
			coauthor.emailOut(modifiers, msg, "Author"+fmt.Sprintf("%d", 2+i))
		}
	}
	if commit.legacyID != "" {
		msg.setHeader("Legacy-ID", commit.legacyID)
	}
	if commit.hasProperties() && len(commit.properties.keys) > 0 {
		for _, name := range commit.properties.keys {
			hdr := ""
			for _, s := range strings.Split(name, "-") {
				hdr += strings.Title(s)
			}
			value := commit.properties.get(name)
			value = strings.Replace(value, "\n", `\n`, 0)
			value = strings.Replace(value, "\t", `\t`, 0)
			msg.setHeader("Property-"+hdr, value)
		}
	}
	check := strings.Split(commit.Comment, "\n")[0]
	if len(check) > 54 {
		check = check[0:54]
	}
	msg.setHeader("Check-Text", check)
	msg.setPayload(commit.Comment)
	if !strings.HasSuffix(commit.Comment, "\n") {
		croak("in commit %s, comment was not LF-terminated.",
			commit.mark)
	}

	if filterRegexp != nil {
		msg.filterHeaders(filterRegexp)
	}

	return msg.String()
}

// actionStamp controls how a commit stamp is made.
func (commit *Commit) actionStamp() string {
	// Prefer the author stamp because that doesn't change when patches
	// are replayed onto a repository, while the commit stamp will.
	if len(commit.authors) > 0 {
		return commit.authors[0].actionStamp()
	}
	return commit.committer.actionStamp()
}

func stringSliceEqual(a, b []string) bool {
	// If one is nil, the other must also be nil.
	if (a == nil) != (b == nil) {
		return false
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
	if newbranch != "" && commit.Branch != newbranch {
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
			panic(throw("msgbox", "bad attribution: %v", err2))
		}
		if c.fullname != newfullname || c.email != newemail {
			c.fullname, c.email = newfullname, newemail
			if commit.repo != nil {
				logit(logEMAILIN, "in %s, Committer is modified", commit.idMe())
			}
			modified = true
		}
	}
	rawdate := msg.getHeader("Committer-Date")
	if rawdate != "" {
		newcommitdate, err := newDate(rawdate)
		if err != nil {
			panic(throw("msgbox", "Bad Committer-Date: %#v (%v)", msg.getHeader("Committer-Date"), err))
		}
		if !c.date.isZero() && !newcommitdate.Equal(c.date) {
			if commit.repo != nil {
				logit(logEMAILIN, "in %s, Committer-Date is modified '%s' -> '%s' (delta %d)",
					commit.idMe(),
					c.date, newcommitdate,
					c.date.delta(newcommitdate))
			}
			modified = true
		}
		c.date = newcommitdate
	}
	newauthor := msg.getHeader("Author")
	if newauthor != "" {
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
		for i := 0; i < len(authorkeys)-len(commit.authors); i++ {
			attrib, err := newAttribution(msg.getHeader(authorkeys[i]))
			if err != nil {
				panic(throw("msgbox", "bad author field: %v", err))
			}
			commit.authors = append(commit.authors, *attrib)
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
				panic(throw("msgbox", "bad attribution: %v", err))
			}
			if c.fullname != newfullname || c.email != newemail {
				c.fullname, c.email = newfullname, newemail
				logit(logEMAILIN,
					"in commit %s, Author #%d is modified",
					msg.getHeader("Event-Number"), i+1)
				modified = true
			}
			newdate := msg.getHeader(hdr + "-Date")
			if newdate != "" {
				date, err := newDate(newdate)
				if err != nil {
					panic(throw("msgbox", "Bad Author-Date: %v", err))
				}
				if !c.date.isZero() && !date.Equal(c.date) {
					eventnum := msg.getHeader("Event-Number")
					if commit.repo != nil && eventnum != "" {
						logit(logEMAILIN,
							"in event %s, %s-Date #%d is modified",
							eventnum, hdr, i+1)
					}
					modified = true
				}
				c.date = date
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
	propsModified := (!commit.hasProperties() && newprops.Len() == 0) || !reflect.DeepEqual(newprops, commit.properties)
	if propsModified {
		commit.properties = &newprops
		modified = true
	}
	newcomment := msg.getPayload()
	if control.flagOptions["canonicalize"] {
		newcomment = strings.TrimSpace(newcomment)
		newcomment = strings.Replace(newcomment, "\r\n", "\n", 1)
		newcomment += "\n"
	}
	if newcomment != commit.Comment {
		logit(logEMAILIN, "in %s, comment is modified %q -> %q",
			commit.idMe(), commit.Comment, newcomment)
		modified = true
		commit.Comment = newcomment
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

// setMark sets the commit's mark
func (commit *Commit) setMark(mark string) string {
	if commit.repo != nil && !control.flagOptions["tighten"] {
		commit.repo.maplock.Lock()
		defer commit.repo.maplock.Unlock()
		if commit.repo._eventByMark == nil {
			commit.repo.memoizeMarks()
		}
		commit.repo._eventByMark[mark] = commit
	}
	commit.mark = mark
	return mark
}

// forget de-links this commit from its parents.
func (commit *Commit) forget() {
	commit.setParents([]CommitLike{})
	for _, fileop := range commit.operations() {
		if fileop.op == opN {
			commit.repo.inlines--
		}
	}
	commit.repo = nil
}

// moveto changes the repo this commit is associated with.
func (commit *Commit) moveto(repo *Repository) {
	for _, fileop := range commit.operations() {
		fileop.repo = repo
		if fileop.op == opN {
			commit.repo.inlines--
			repo.inlines++
		}
	}
	commit.repo = repo
}

// parents gets a list of this commit's parents.
func (commit *Commit) parents() []CommitLike {
	return commit._parentNodes
}

// invalidateManifests cleans out manifests in this commit and all descendants
func (commit *Commit) invalidateManifests() {
	// Do a traversal of the descendent graph, depth-first because it is the
	// most efficient with a slice as the queue.
	stack := []CommitLike{commit}
	for len(stack) > 0 {
		var current CommitLike
		// pop a CommitLike from the stack
		stack, current = stack[:len(stack)-1], stack[len(stack)-1]
		// remove the memoized manifest
		if c, ok := current.(*Commit); ok {
			if c._manifest == nil {
				// Because manifests are always generated recursively backwards
				// when one is requested and doesn't exist, if this commit's
				// manifest cache is nil none of its children can need clearing.
				continue
			}
			c._manifest = nil
		}
		// and add all children to the "todo" stack
		for _, child := range current.children() {
			stack = append(stack, child)
		}
	}
}

// listMarks is only used for logging
func listMarks(items []CommitLike) []string {
	var out []string
	for _, x := range items {
		if x == nil {
			out = append(out, "nil")
		} else {
			out = append(out, x.getMark())
		}
	}
	return out
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
func commitRemove(commitlist []CommitLike, commit CommitLike) []CommitLike {
	out := make([]CommitLike, 0)
	for i := range commitlist {
		if commitlist[i] != commit {
			out = append(out, commitlist[i])
		}
	}
	return out
}

func (commit *Commit) setParents(parents []CommitLike) {
	for _, parent := range commit._parentNodes {
		// remove all occurrences of self in old parent's children cache
		switch parent.(type) {
		case *Commit:
			parent.(*Commit)._childNodes = commitRemove(parent.(*Commit)._childNodes, commit)
		case *Callout:
			croak("not removing callout %s", parent.(*Callout).mark)
		}
	}
	for _, c := range parents {
		if c == nil {
			panic("null commit in setParents()")
		}
	}
	commit._parentNodes = parents
	for _, parent := range commit._parentNodes {
		switch parent.(type) {
		case *Commit:
			parent.(*Commit)._childNodes = append(parent.(*Commit)._childNodes, commit)
		case *Callout:
			// do nothing
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
	newparent := commit.repo.markToEvent(mark)
	if newparent == nil {
		panic("Ill-formed stream: cannot resolve " + mark)
	}
	commit.addParentCommit(newparent.(*Commit))
}

// callout generates a callout cookie for this commit.
func (commit Commit) callout() string {
	result := commit.actionStamp()
	return result
}

// is_callot tells if the specified mark field a callout?"
func isCallout(mark string) bool {
	return strings.Contains(mark, "!")
}

func (commit *Commit) addCallout(mark string) {
	commit._parentNodes = append(commit._parentNodes, newCallout(mark))
}

func (commit *Commit) insertParent(idx int, mark string) {
	newparent := commit.repo.markToEvent(mark)
	if newparent == nil {
		croak("invalid mark %s passed to insertParent", mark)
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

func (commit *Commit) removeParent(event CommitLike) {
	// remove *all* occurences of event in parents
	commit._parentNodes = commitRemove(commit._parentNodes, event)
	// and all occurences of self in event's children
	if commit, ok := event.(*Commit); ok {
		commit._childNodes = commitRemove(commit._childNodes, commit)
		commit.invalidateManifests()
	}
}

func (commit *Commit) replaceParent(e1, e2 *Commit) {
	if e2 == nil {
		panic("null commit in replaceParents()")
	}
	for i, item := range commit._parentNodes {
		if item == e1 {
			commit._parentNodes[i] = e2
			e1._childNodes = commitRemove(e1._childNodes, commit)
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
		case *Callout:
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
			_, ok := cliques[fileop.Path]
			if !ok {
				cliques[fileop.Path] = make([]int, 0)
			}
			cliques[fileop.Path] = append(cliques[fileop.Path], i)
		}
	}
	return cliques
}

// fileopDump reports file ops without data or inlines; used for logging only.
func (commit *Commit) fileopDump() {
	fmt.Fprintf(control.baton, "commit %d, mark %s:\n", commit.repo.markToIndex(commit.mark)+1, commit.mark)
	for i, op := range commit.operations() {
		fmt.Fprintf(control.baton, "%d: %s", i, op.String())
	}
}

// paths returns the set of all paths touched by this commit.
func (commit *Commit) paths(pathtype orderedStringSet) orderedStringSet {
	pathset := newOrderedStringSet()
	for _, fileop := range commit.operations() {
		for _, item := range fileop.paths(pathtype) {
			pathset.Add(item)
		}
	}
	return pathset
}

// visible tells if a path is modified and not deleted in the ancestors
func (commit *Commit) visible(argpath string) *Commit {
	ancestor := commit
	for {
		parents := ancestor.parents()
		if len(parents) == 0 {
			return nil
		}
		switch parents[0].(type) {
		case *Callout:
			return nil
		case *Commit:
			ancestor = parents[0].(*Commit)
			// This loop assumes that the op sequence has no
			// M/C/R foo after D foo pairs. If this condition
			// is violated it can throw false negatives.
			for _, fileop := range ancestor.operations() {
				if fileop.op == opD && fileop.Path == argpath {
					return nil
				} else if fileop.op == opM && fileop.Path == argpath {
					return ancestor
				} else if (fileop.op == opR || fileop.op == opC) && fileop.Target == argpath {
					return ancestor
				}
			}
		}
	}
	// unreachable
}

// manifest returns a map from all pathnames visible at this commit
// to ManifestEntry structures. The map contents is shared as much as
// possible with manifests from previous commits to keep working-set
// size to a minimum.
func (commit *Commit) manifest() *PathMap {
	// yeah, baby this operation is *so* memoized...
	if commit._manifest != nil {
		return commit._manifest
	}
	// Git only inherits files from the first parent of a commit.
	// The simplest idea is to ask the first parent to compute its manifest,
	// which will ask its own first parent recursively back to the root commit,
	// or thanks to memoization, a commit whose manifest is already known.
	// Since this might exceed the recursion depth limit, a more robust way is
	// to walk the chain of "first parents" until a commit whose manifest is
	// known, remembering which commits need to have their manifest computed.
	commitsToHandle := []*Commit{}
	ancestor := commit
	for ancestor._manifest == nil {
		commitsToHandle = append(commitsToHandle, ancestor)
		if !ancestor.hasParents() {
			break
		}
		switch p := ancestor.parents()[0].(type) {
		case *Commit:
			ancestor = p
		case *Callout:
			croak("internal error: can't get through a callout")
			break
		default:
			panic("manifest() found unexpected type in parent list")
		}
	}
	// commitsToHandle now contains all the commits whose manifest need to be
	// computed to be able to compute the one initially asked for.
	// By construction, each commit in that list is the child of the next, and
	// if ancestor._manifest is not nil, then ancestor is the parent of the
	// last commit in commitsToHandle, and ancestor._manifest should be
	// inherited by that last commit.
	// Else, ancestor._manifest is nil and the loop was broken because the last
	// commit in commitsToHandle has no parent or a non-commit first parent. In
	// that case the manifest inherited by the last commit is just empty.
	manifest := ancestor._manifest
	if manifest == nil {
		manifest = newPathMap()
	}
	// Now loop over commitsToHandle, starting from the end. At the start of each iteration,
	// manifest contains the manifest inherited from the first parent, if any.
	for k := len(commitsToHandle) - 1; k >= 0; k-- {
		// Take a snapshot of the manifest
		manifest = manifest.snapshot()
		// Take own fileops into account.
		commit := commitsToHandle[k]
		for _, fileop := range commit.operations() {
			if fileop.op == opM {
				manifest.set(fileop.Path, &ManifestEntry{fileop.mode, fileop.ref, fileop.inline})
			} else if fileop.op == opD {
				manifest.remove(fileop.Path)
			} else if fileop.op == opC {
				manifest.copyFrom(fileop.Target, manifest, fileop.Source)
			} else if fileop.op == opR {
				manifest.copyFrom(fileop.Target, manifest, fileop.Source)
				manifest.remove(fileop.Source)
			} else if fileop.op == deleteall {
				manifest = newPathMap()
			}
		}
		commit._manifest = manifest
	}
	return manifest
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
	ops := commit.operations()
	if len(ops) == 0 || ops[0].op == deleteall {
		return
	}
	// Get paths touched by non-deleteall operations.
	paths := commit.paths(nil)
	// Fetch the tree state before us...
	var previous *PathMap
	if !commit.hasParents() {
		previous = newPathMap()
	} else {
		p := commit.parents()[0]
		switch p.(type) {
		case *Commit:
			previous = p.(*Commit).manifest()
		case *Callout:
			croak("internal error: can't get through a callout")
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
			_, old := previous.get(cpath)
			_, new := current.get(cpath)
			if old && !new {
				fileop := newFileOp(commit.repo)
				fileop.construct(opD, cpath)
				newops = append(newops, *fileop)
			}
		}
	}
	// Generate needed M fileops.
	// Only paths touched by non-deleteall ops can be changed.
	for _, cpath := range paths {
		ioe, oldok := previous.get(cpath)
		ine, newok := current.get(cpath)
		oe, _ := ioe.(*ManifestEntry)
		ne, _ := ine.(*ManifestEntry)
		if newok && !(oldok && oe.equals(ne)) {
			fileop := newFileOp(commit.repo)
			fileop.construct(opM, ne.mode, ne.ref, cpath)
			if ne.ref == "inline" {
				fileop.inline = ne.inline
			}
			newops = append(newops, *fileop)
		}
	}
	commit.setOperations(newops)
	// Finishing touches.  Sorting always has to be done
	commit.sortOperations()
}

// alldeletes is a predicate: is this an all-deletes commit?
func (commit *Commit) alldeletes(killset ...rune) bool {
	if killset == nil {
		killset = []rune{opD, deleteall}
	}
	for _, fileop := range commit.operations() {
		match := false
		for _, op := range killset {
			if fileop.op == op {
				match = true
				break
			}
		}
		if !match {
			return false
		}
	}

	return true
}

// checkout makes a directory with links to files in a specified checkout.
func (commit *Commit) checkout(directory string) string {
	if directory == "" {
		directory = filepath.FromSlash(commit.repo.subdir("") + "/" + commit.mark)
	}
	if !exists(directory) {
		commit.repo.makedir()
		os.Mkdir(directory, userReadWriteSearchMode)
	}

	defer func() {
		if r := recover(); r != nil {
			croak("could not create checkout directory or files: %v.", r)
		}
	}()

	for _, pitem := range commit.manifest().items() {
		cpath, entry := pitem.name, pitem.value.(*ManifestEntry)
		fullpath := filepath.FromSlash(directory +
			"/" + cpath + "/" + entry.ref)
		if !exists(fullpath) {
			parts := strings.Split(fullpath, "/")
			// os.MkdirAll is broken and rpike says they
			// won't fix it.
			// https://github.com/golang/go/issues/22323
			var dpath string
			for i := range parts[0 : len(parts)-1] {
				dpath = filepath.FromSlash(strings.Join(parts[:i+1], "/"))
				err := os.Mkdir(dpath, userReadWriteSearchMode)
				if err != nil && !os.IsExist(err) {
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
					os.O_WRONLY|os.O_CREATE|os.O_TRUNC, mode)
				if err3 != nil {
					panic(fmt.Errorf("File creation for inline failed during checkout: %v", err3))
				}
				file.Write([]byte(entry.inline))
				blob.size = int64(len(entry.inline))
				file.Close()
			} else {
				if blob.hasfile() {
					os.Link(blob.getBlobfile(false), fullpath)
				} else {
					file, err4 := os.OpenFile(blob.getBlobfile(true),
						os.O_WRONLY|os.O_CREATE|os.O_TRUNC, mode)
					if err4 != nil {
						panic(fmt.Errorf("File creation failed during checkout: %v", err4))
					}
					content := blob.getContent()
					file.Write(content)
					blob.size = int64(len(content))
					file.Close()
				}
			}
		}
	}
	return directory
}

// head returns the branch to which this commit belongs.
func (commit *Commit) head() string {
	if strings.HasPrefix(commit.Branch, "refs/heads/") || !commit.hasChildren() {
		return commit.Branch
	}
	rank := 0
	var child Event
	for rank, child = range commit.children() {
		switch child.(type) {
		case *Commit:
			if child.(*Commit).Branch == commit.Branch {
				return child.(*Commit).head()
			}
		case *Callout:
			croak("internal error: callouts do not have branches: %s",
				child.idMe())
		}
	}
	if rank == 0 {
		switch child.(type) {
		case *Commit:
			return child.(*Commit).head() // there was only one child
		case *Callout:
			croak("internal error: callouts do not have branches: %s",
				child.idMe())
		}
	}
	croak("Can't deduce a branch head for %s", commit.mark)
	return ""
}

// tip enables do_tip() to report deduced branch tips.
func (commit *Commit) tip(_modifiers orderedStringSet, eventnum int, cols int) string {
	summary := fmt.Sprintf("%6d %s %6s ",
		eventnum+1, commit.date().rfc3339(), commit.mark)
	report := summary + commit.head()
	if cols > 0 && len(report) > cols {
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
func (commit *Commit) blobByName(pathname string) ([]byte, bool) {
	value, ok := commit.manifest().get(pathname)
	if !ok {
		return []byte{}, false
	}
	entry := value.(*ManifestEntry)
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

// decodable tells whether this commi us enriirely composed of decodable UTF-8.
func (commit *Commit) decodable() bool {
	valid := func(s string) bool {
		return utf8.Valid([]byte(s))
	}
	if !(valid(commit.committer.fullname) && valid(commit.committer.email) && valid(commit.Comment)) {
		return false
	}
	for _, author := range commit.authors {
		if !valid(author.fullname) || !valid(author.email) {
			return false
		}
	}
	return true
}

// delete severs this commit from its repository.
func (commit *Commit) delete(policy orderedStringSet) {
	commit.repo.delete([]int{commit.index()}, policy)
}

// Save this commit to a stream in fast-import format
func (commit *Commit) Save(w io.Writer) {
	vcs := commit.repo.preferred
	if vcs == nil && commit.repo.vcs != nil && commit.repo.vcs.importer != "" {
		vcs = commit.repo.vcs
	}
	incremental := false
	if !commit.repo.writeOptions.Contains("--noincremental") {
		if commit.repo.realized != nil && commit.hasParents() {
			if _, ok := commit.repo.realized[commit.Branch]; !ok {
				parent := commit.parents()[0]
				switch parent.(type) {
				case *Commit:
					pbranch := parent.(*Commit).Branch
					if !commit.repo.realized[pbranch] {
						incremental = true
					}
				}
			}
		}
	}
	if incremental {
		fmt.Fprintf(w, "reset %s^0\n\n", commit.Branch)
	}
	fmt.Fprintf(w, "commit %s\n", commit.Branch)
	if commit.legacyID != "" {
		fmt.Fprintf(w, "#legacy-id %s\n", commit.legacyID)
	}
	if commit.repo.realized != nil {
		commit.repo.realized[commit.Branch] = true
	}
	if commit.mark != "" {
		fmt.Fprintf(w, "mark %s\n", commit.mark)
	}
	if len(commit.authors) > 0 {
		for _, author := range commit.authors {
			fmt.Fprintf(w, "author %s\n", author)
		}
	}
	if commit.committer.fullname != "" {
		fmt.Fprintf(w, "committer %s\n", commit.committer)
	}
	// As of git 2.13.6 (possibly earlier) the comment field of
	// commit is no longer optional - you have to emit data 0 if there
	// is no comment, otherwise the importer gets confused.
	comment := commit.Comment
	if commit.repo.writeOptions.Contains("--legacy") && commit.legacyID != "" {
		if comment != "" {
			comment += "\n"
		}
		comment += fmt.Sprintf("Legacy-ID: %s\n", commit.legacyID)
	}
	fmt.Fprintf(w, "data %d\n%s", len(comment), comment)
	if commit.repo.exportStyle().Contains("nl-after-comment") {
		w.Write([]byte{'\n'})
	}
	parents := commit.parents()
	doCallouts := commit.repo.writeOptions.Contains("--callout")
	if len(parents) > 0 {
		ancestor := parents[0]
		if (commit.repo.internals == nil && !incremental) || commit.repo.internals.Contains(ancestor.getMark()) {
			fmt.Fprintf(w, "from %s\n", ancestor.getMark())
		} else if doCallouts {
			fmt.Fprintf(w, "from %s\n", ancestor.callout())
		}
		for _, ancestor := range parents[1:] {
			var nugget string
			if commit.repo.internals == nil || commit.repo.internals.Contains(ancestor.getMark()) {
				nugget = ancestor.getMark()
			} else if doCallouts {
				nugget = ancestor.callout()
			}
			if nugget != "" {
				fmt.Fprintf(w, "merge %s\n", nugget)
			}
		}
	}
	if vcs != nil && vcs.extensions.Contains("commit-properties") {
		if commit.hasProperties() && len(commit.properties.keys) > 0 {
			for _, name := range commit.properties.keys {
				value := commit.properties.get(name)
				if value == "true" || value == "false" {
					if value != "" {
						fmt.Fprintf(w, "property %s\n", name)
					}
				} else {
					fmt.Fprintf(w, "property %s %d %s\n", name, len(value), value)
				}
			}
		}
	}
	for _, op := range commit.operations() {
		w.Write([]byte(op.String()))
	}
	if !commit.repo.exportStyle().Contains("no-nl-after-commit") {
		w.Write([]byte{'\n'})
	}
}

// String serializes this commit in import-stream format
func (commit Commit) String() string {
	var bld strings.Builder
	commit.Save(&bld)
	return bld.String()
}

//Passthrough represents a passthrough line.
type Passthrough struct {
	repo     *Repository
	text     string
	color    string
	deleteme bool
}

func (p Passthrough) getDelFlag() bool {
	return p.deleteme
}

func (p *Passthrough) setDelFlag(b bool) {
	p.deleteme = b
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

// emailOut enables DoMsgout() to report these.
func (p *Passthrough) emailOut(_modifiers orderedStringSet,
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
func (p *Passthrough) idMe() string {
	return fmt.Sprintf("passthrough@%d", p.repo.eventToIndex(p))
}

//getMark is a stub required for the Event interface
func (p Passthrough) getMark() string {
	return ""
}

// getComment returns the text attached to a passthrough
func (p Passthrough) getComment() string { return p.text }

// String reports this passthrough in import-stream format.
func (p Passthrough) String() string {
	return p.text
}

// Save reports this passthrough in import-stream format.
func (p *Passthrough) Save(w io.Writer) {
	w.Write([]byte(p.text))
}

// moveto changes the repo this passthrough is associated with."
func (p *Passthrough) moveto(*Repository) {
	// Has no repo field
}

func (p Passthrough) isCommit() bool {
	return false
}

// Generic extractor code begins here

// signature is a file signature - path, hash value of content and permissions."
type signature struct {
	//pathname string
	hashval [sha1.Size]byte
	perms   string
}

func newSignature(path string) *signature {
	file, err1 := os.Open(path)
	if err1 != nil {
		panic(throw("extractor", "Can't open %q\n", path))
	}
	defer file.Close()
	st, err2 := file.Stat()
	if err2 != nil {
		panic(throw("extractor", "Can't stat %q\n", path))
	}

	ps := new(signature)
	if !st.IsDir() {
		h := sha1.New()
		if _, err := io.Copy(h, file); err != nil {
			log.Fatal(err)
		}
		// WARNING: as of 2019-09-25 the actual interface of Sum()
		// does not match the documentation at
		// https://golang.org/pkg/crypto/sha1
		// This interface might be unstable.
		for i, v := range h.Sum(nil) {
			ps.hashval[i] = v
		}
		perms := st.Mode()
		// Map to the restricted set of modes that are allowed in
		// the stream format.
		if (perms & 0000700) == 0000700 {
			perms = 0100755
		} else if (perms & 0000600) == 0000600 {
			perms = 0100644
		}
		ps.perms = fmt.Sprintf("%06o", perms)
	}
	return ps
}

func (s signature) String() string {
	return fmt.Sprintf("<%s:%02x%02x%02x%02x%02x%02x>",
		s.perms, s.hashval[0], s.hashval[1], s.hashval[2], s.hashval[3], s.hashval[4], s.hashval[5])
}

func (s signature) Equal(other signature) bool {
	return s.hashval == other.hashval && s.perms == other.perms
}

// capture runs a specified command, capturing the output.
func captureFromProcess(command string) (string, error) {
	logit(logCOMMANDS, "%s: capturing %s", rfc3339(time.Now()), command)
	cmd := exec.Command("sh", "-c", command)
	content, err := cmd.CombinedOutput()
	if logEnable(logCOMMANDS) {
		control.baton.printLog(content)
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

// A PathMap represents a mapping from a set of filenames visible in a
// Subversion revision to some kind of value object.  The main use is
// by the dumpfile parser, in which the value object is a NodeAction.
//
// The reason to prefer this over a naive implementation is that
// without the copy-on-write storage sharing of snapshots, the
// cost to keep a per-revision array of snapshots can blow up
// pretty badly.

type pathMapItem struct {
	name  string
	value interface{}
}

type PathMap struct {
	dirs   map[string]*PathMap
	blobs  map[string]interface{}
	shared bool
}

func newPathMap() *PathMap {
	pm := new(PathMap)
	pm.dirs = make(map[string]*PathMap)
	pm.blobs = make(map[string]interface{})
	pm.shared = false
	return pm
}

// _markShared sets the shared attribute on all PathMaps in the hierarchy
// When pm.shared is true, at least two Pathmaps have pm in their hierarchy,
// which means that pm should be replaced by a snapshot before any
// modification.
// It is not part of the interface, but a convenience helper
func (pm *PathMap) _markShared() {
	// We make use of the fact that pm.shared is made true only via this
	// function, and that it is never reset to false (In new snapshots it
	// will be false of course). In particular, if pm.shared is already
	// true, there is no need to recurse.
	if !pm.shared {
		pm.shared = true
		for _, v := range pm.dirs {
			v._markShared()
		}
	}
}

// snapshot returns a snapshot of the current state of an evolving filemap.
func (pm *PathMap) snapshot() *PathMap {
	// The shapshot will share its direct children with the source PathMap.
	// Mark every PathMap in the hierarchy as shared so that they are
	// considered immutable and a snapshot will be made before any
	// modification.
	r := newPathMap()
	for k, v := range pm.dirs {
		r.dirs[k] = v
		v._markShared()
	}
	for k, v := range pm.blobs {
		r.blobs[k] = v
	}
	return r
}

// _unshare returns a PathMap representing the same tree as the PathMap it is
// called on, ensuring that the returned PathMap is not shared with any other
// PathMap, so that it can be modified without impacting other trees.
// When the shared attribute of the PathMap is false, _unshare returns that
// PathMap unchanged. If the shared attribute is true, _unshare returns a
// snapshot of the PathMap.
// It is not part of the interface, but a convenience helper
func (pm *PathMap) _unshare() *PathMap {
	if pm.shared {
		return pm.snapshot()
	}
	return pm
}

// _createTree ensures the hierarchy contains the directory whose path is given
// as a slice of components, creating and snapshotting PathMaps as needed.
// It is not part of the interface, but a convenience helper
func (pm *PathMap) _createTree(path []string) *PathMap {
	tree := pm
	for _, component := range path {
		subtree, ok := tree.dirs[component]
		if ok {
			// The component already exists. Unshare it so that
			// it can be modified without messing with other PathMaps
			subtree = subtree._unshare()
		} else {
			// Create the component as a directory
			subtree = newPathMap()
		}
		// Put the new or snapshot tree in place, and go down a level
		tree.dirs[component] = subtree
		tree = subtree
	}
	return tree
}

// copyFrom inserts at targetPath a copy of sourcePath in sourcePathMap.
// If targetPath is empty, then sourcePath must point to a directory in
// sourcePathMap, and the contents of pm are replaced by those of that
// directory, sharing the inner PathMaps for efficiency (pm itself cannot be
// replaced since it is a toplevel PathMap owned by calling code).
// If targetPath is empty, then sourcePath might point to a value and/or a
// directory in sourcePathMap. Both will be copied over if existing.
// The directory will be shared with sourcePathMap unless sourcePath is empty,
// in which case a snapshot of sourcePathMap is used so that sourcePathMap, a
// toplevel PathMap, is not shared.
func (pm *PathMap) copyFrom(targetPath string, sourcePathMap *PathMap, sourcePath string) {
	parts := strings.Split(sourcePath, svnSep)
	sourceDir, sourceName := parts[:len(parts)-1], parts[len(parts)-1]
	// Walk along the "dirname" in sourcePath
	sourceParent := sourcePathMap
	for _, component := range sourceDir {
		var ok bool
		if sourceParent, ok = sourceParent.dirs[component]; !ok {
			// The source path does not exist, bail out
			// FIXME: should we warn ? panic ? return false ?
			return
		}
	}
	if targetPath == "" {
		var tree *PathMap
		if sourcePath == "" {
			tree = sourceParent // no need to snapshot, it will not be shared
		} else {
			var ok bool
			tree, ok = sourceParent.dirs[sourceName]
			if !ok {
				// The source path does not exist, bail out
				// FIXME: should we warn ? panic ? return false ?
				return
			}
		}
		// Same as if we were doing a new snapshot, but in place.
		dirs := make(map[string]*PathMap)
		blobs := make(map[string]interface{})
		for k, v := range tree.dirs {
			dirs[k] = v
			v._markShared()
		}
		for k, v := range tree.blobs {
			blobs[k] = v
		}
		pm.dirs = dirs
		pm.blobs = blobs
	} else {
		// Decompose targetPath into components
		parts = strings.Split(targetPath, svnSep)
		targetDir, targetName := parts[:len(parts)-1], parts[len(parts)-1]
		// And perform the copy. In normal cases, only one of the dir and file exist
		if sourcePath == "" {
			// use a snapshot instead of marking as shared, since toplevel PathMaps
			// are never expected to be shared.
			pm._createTree(targetDir).dirs[targetName] = sourceParent.snapshot()
		} else {
			if tree, ok := sourceParent.dirs[sourceName]; ok {
				tree._markShared()
				pm._createTree(targetDir).dirs[targetName] = tree
			}
			if blob, ok := sourceParent.blobs[sourceName]; ok {
				pm._createTree(targetDir).blobs[targetName] = blob
			}
		}
		// When the last component of sourcePath does not exist, we do nothing
		// FIXME: should we warn ? panic ? return false ?
	}
}

// get takes a path as argument, and returns the file that is stored at that
// path, if any. In that case the second return value is the boolean true.
// If there is no file in the PathMap corresponding to that path, the first
// return value is nil (the null value of the interface{} type) and the second
// return value is the boolean false
func (pm *PathMap) get(path string) (interface{}, bool) {
	components := strings.Split(path, svnSep)
	// Walk along the "dirname"
	parent := pm
	for _, component := range components[:len(components)-1] {
		var ok bool
		if parent, ok = parent.dirs[component]; !ok {
			return nil, false
		}
	}
	// Now fetch the "basename"
	element, ok := parent.blobs[components[len(components)-1]]
	return element, ok
}

// set adds a filename to the map, with associated value.
func (pm *PathMap) set(path string, value interface{}) {
	parts := strings.Split(path, svnSep)
	dir, name := parts[:len(parts)-1], parts[len(parts)-1]
	pm._createTree(dir).blobs[name] = value
}

// remove removes a filename, or all descendents of a directory name, from the map.
func (pm *PathMap) remove(path string) {
	// Separate the first component and the rest in the path
	components := strings.SplitN(path, svnSep, 2)
	component := components[0]
	if len(components) == 1 {
		// The path to delete is at pm's toplevel
		delete(pm.dirs, component)
		delete(pm.blobs, component)
	} else {
		// Try to go down a level
		subtree, ok := pm.dirs[component]
		if !ok {
			// A component in the path doesn't exist as a directory; bail out
			// FIXME: should we warn ? panic ? return false ?
			return
		}
		// The component exists. Unshare it so that
		// it can be modified without messing with other PathMaps
		subtree = subtree._unshare()
		pm.dirs[component] = subtree
		// Now ask the subdir to do the removal, using the rest of the path
		subtree.remove(components[1])
		// Do not keep empty subdirectories around
		if subtree.isEmpty() {
			delete(pm.dirs, component)
		}
	}
}

// _itemsInner recursively walks the pathMap CoW tree estracting its items
func (pm *PathMap) _itemsInner(items []pathMapItem, prefix string) []pathMapItem {
	for cmp1, subdir := range pm.dirs {
		items = subdir._itemsInner(items, prefix+cmp1+svnSep)
	}
	for cmp1, elt := range pm.blobs {
		items = append(items, pathMapItem{prefix + cmp1, elt})
	}
	return items
}

func (pm *PathMap) items() []pathMapItem {
	items := make([]pathMapItem, 0)
	items = pm._itemsInner(items, "")
	sort.Slice(items, func(i, j int) bool {
		return items[i].name < items[j].name
	})
	return items
}

func (pm *PathMap) size() int {
	size := len(pm.blobs)
	for _, subdir := range pm.dirs {
		size += subdir.size()
	}
	return size
}

// isEmpty returns true iff the PathMap contains no file
func (pm *PathMap) isEmpty() bool {
	return len(pm.dirs)+len(pm.blobs) == 0
}

// Derived PathMap code, independent of the store implementation

func (pm *PathMap) String() string {
	out := "{"
	for _, item := range pm.items() {
		out += fmt.Sprintf("%s: %v, ", item.name, item.value)
	}
	if pm.size() > 0 {
		out = out[:len(out)-2]
	}
	return out + "}"
}

// names returns a sorted list of the pathnames in the set
func (pm *PathMap) pathnames() []string {
	items := pm.items()
	v := make([]string, len(items))
	for i := 0; i < len(items); i++ {
		v[i] = items[i].name
	}
	return v
}

// StreamParser parses a fast-import stream or Subversion dump to
// populate a Repository.
type StreamParser struct {
	repo        *Repository
	fp          *bufio.Reader // Can't be os.File, unit tests will fail
	source      string
	importLine  int
	ccount      int64
	linebuffers [][]byte
	lastcookie  Cookie
	svnReader		// Opaque state of the Subversion dump reader
}

// newSteamParser parses a fast-import stream or Subversion dump to a Repository.
func newStreamParser(repo *Repository) *StreamParser {
	sp := new(StreamParser)
	sp.repo = repo
	sp.linebuffers = make([][]byte, 0)
	return sp
}

func (sp *StreamParser) addBranch(name string) {
	sp.branches[name] = nil
	sp._branchesSorted = nil
	return
}

func (sp *StreamParser) error(msg string) {
	// Throw fatal error during parsing.
	panic(throw("parse", "%d: %s", sp.importLine, msg))
}

func (sp *StreamParser) errorLocation() string {
	// Alas, must use old format here because of the leading log tag
	if sp.importLine > 0 {
		leader := ""
		if sp.source != "" {
			leader = fmt.Sprintf(`"%s", `, sp.source)
		}
		return fmt.Sprintf(leader+"line %d: ", sp.importLine)
	}
	return ""
}

func (sp *StreamParser) warn(msg string) {
	// Display a parse warning associated with a line but don't error out.
	logit(logWARN, sp.errorLocation()+msg)
}

func (sp *StreamParser) shout(msg string) {
	// A gripe with line number
	logit(logSHOUT, sp.errorLocation()+msg)

}

func (sp *StreamParser) read(n int) []byte {
	// Read possibly binary data
	buf := make([]byte, n)
	_, err := io.ReadFull(sp.fp, buf)
	if err != nil {
		sp.error("bad read in data")
	}
	sp.ccount += int64(n)
	sp.importLine += bytes.Count(buf, []byte("\n"))
	return buf
}

func (sp *StreamParser) readline() []byte {
	// Read a newline-terminated string, returning "" at EOF
	var line []byte
	if len(sp.linebuffers) > 0 {
		line = []byte(sp.linebuffers[0])
		sp.linebuffers = sp.linebuffers[1:]
	} else {
		var err error
		line, err = sp.fp.ReadBytes('\n')
		if err != nil {
			if err == io.EOF {
				line = []byte{}
			} else {
				panic(throw("parse", "in readline(): %v", err))
			}
		}
	}
	sp.ccount += int64(len(line))
	sp.importLine++
	return line
}

func (sp *StreamParser) tell() int64 {
	// Return the current read offset in the source stream.
	if sp.fp == nil {
		return noOffset
	}
	return sp.ccount
}

func (sp *StreamParser) pushback(line []byte) {
	sp.ccount -= int64(len(line))
	sp.importLine--
	sp.linebuffers = append(sp.linebuffers, line)
}

// Helpers for import-stream files

func (sp *StreamParser) fiReadline() []byte {
	// Read a line, stashing comments as we go.
	for {
		line := sp.readline()
		if len(line) > 0 && bytes.HasPrefix(line, []byte("#")) && !bytes.HasPrefix(line, []byte("#legacy-id")) {
			sp.repo.addEvent(newPassthrough(sp.repo, string(line)))
			if bytes.HasPrefix(line, []byte("#reposurgeon")) {
				// Extension command generated by some exporter's
				// --reposurgeon mode.
				fields := strings.Fields(string(line))
				if fields[1] == "sourcetype" && len(fields) == 3 {
					sp.repo.hint("", fields[2], true)
				}
			}
			continue
		} else {
			return line
		}
	}
}

func (sp *StreamParser) fiReadData(line []byte) ([]byte, int64) {
	// Read a fast-import data section.
	if len(line) == 0 {
		line = sp.fiReadline()
	}
	data := make([]byte, 0)
	var start int64
	if bytes.HasPrefix(line, []byte("data <<")) {
		delim := line[7:]
		start = sp.ccount
		for {
			dataline := sp.readline()
			if string(dataline) == string(delim) {
				break
			} else if len(dataline) == 0 {
				sp.error("EOF while reading blob")
			} else {
				data = append(data, dataline...)
			}
		}
	} else if bytes.HasPrefix(line, []byte("data")) {
		count, err := strconv.Atoi(strings.TrimSpace(string(line[5:])))
		if err != nil {
			sp.error("bad count in data: " + string(line[5:]))
		}
		start = sp.ccount
		data = sp.read(count)
	} else if bytes.HasPrefix(line, []byte("property")) {
		line = line[9:]                          // Skip this token
		line = line[bytes.IndexByte(line, ' '):] // Skip the property name
		nextws := bytes.IndexByte(line, ' ')
		count, err := strconv.Atoi(strings.TrimSpace(string(line[:nextws-1])))
		if err != nil {
			sp.error("bad count in property")
		}
		start = sp.ccount
		buf := sp.read(count)
		data = append(line[nextws:], buf...)
	} else {
		sp.error("malformed data header")
	}
	line = sp.readline()
	if string(line) != "\n" {
		sp.pushback(line) // Data commands optionally end with LF
	}
	return data, start
}

func (sp *StreamParser) fiParseFileop(fileop *FileOp) {
	// Read a fast-import fileop
	if fileop.ref[0] == ':' {
		return
	} else if fileop.ref == "inline" {
		data, _ := sp.fiReadData([]byte{})
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

func (sp *StreamParser) parseFastImport(options stringSet, baton *Baton, filesize int64) {
	// Beginning of fast-import stream parsing
	commitcount := 0
	baton.startProgress("parse fast import stream", uint64(filesize))
	for {
		line := sp.fiReadline()
		if len(line) == 0 {
			break
		} else if len(bytes.TrimSpace(line)) == 0 {
			continue
		} else if bytes.HasPrefix(line, []byte("blob")) {
			blob := newBlob(sp.repo)
			line = sp.fiReadline()
			if bytes.HasPrefix(line, []byte("mark")) {
				sp.repo.markseq++
				blob.setMark(strings.TrimSpace(string(line[5:])))
				blobcontent, blobstart := sp.fiReadData([]byte{})
				blob.setContent(blobcontent, blobstart)
				sp.lastcookie = blob.parseCookie(string(blobcontent))
			} else {
				sp.error("missing mark after blob")
			}
			sp.repo.addEvent(blob)
			baton.twirl()
		} else if bytes.HasPrefix(line, []byte("data")) {
			sp.error("unexpected data object")
		} else if bytes.HasPrefix(line, []byte("commit")) {
			baton.twirl()
			commitbegin := sp.importLine
			commit := newCommit(sp.repo)
			commit.setBranch(strings.Fields(string(line))[1])
			for {
				line = sp.fiReadline()
				if len(line) == 0 {
					break
				} else if bytes.HasPrefix(line, []byte("#legacy-id")) {
					// reposurgeon extension, expected to
					// be immediately after "commit" if present
					commit.legacyID = string(bytes.Fields(line)[1])
					if sp.repo.vcs != nil {
						sp.repo.legacyMap[strings.ToUpper(sp.repo.vcs.name)+":"+commit.legacyID] = commit
					} else {
						sp.repo.legacyMap[commit.legacyID] = commit
					}
				} else if bytes.HasPrefix(line, []byte("mark")) {
					sp.repo.markseq++
					commit.setMark(string(bytes.TrimSpace(line[5:])))
				} else if bytes.HasPrefix(line, []byte("author")) {
					attrib, err := newAttribution(string(line[7:]))
					if err != nil {
						panic(throw("parse", "in author field: %v", err))
					}
					commit.authors = append(commit.authors, *attrib)
					sp.repo.tzmap[attrib.email] = attrib.date.timestamp.Location()
				} else if bytes.HasPrefix(line, []byte("committer")) {
					attrib, err := newAttribution(string(line[10:]))
					if err != nil {
						panic(throw("parse", "in committer field: %v", err))
					}
					commit.committer = *attrib
					sp.repo.tzmap[attrib.email] = attrib.date.timestamp.Location()
				} else if bytes.HasPrefix(line, []byte("property")) {
					newprops := newOrderedMap()
					commit.properties = &newprops
					fields := bytes.Split(line, []byte(" "))
					if len(fields) < 3 {
						sp.error("malformed property line")
					} else if len(fields) == 3 {
						commit.properties.set(string(fields[1]), "true")
					} else {
						name := fields[1]
						length := parseInt(string(fields[2]))
						value := bytes.Join(fields[3:], []byte(" "))
						if len(value) < length {
							value = append(value, sp.read(length-len(value))...)
							if string(sp.read(1)) != "\n" {
								sp.error("trailing junk on property value")
							}
						} else if len(value) == length+1 {
							value = value[:len(value)-1] // Trim '\n'
						} else {
							value = append(value, sp.read(length-len(value))...)
							if string(sp.read(1)) != "\n" {
								sp.error("newline not found where expected")
							}
						}
						commit.properties.set(string(name), string(value))
						// Generated by cvs-fast-export
						if string(name) == "cvs-revisions" {
							if !sp.repo.stronghint {
								logit(logSHOUT, "cvs_revisions property hints at CVS.")
							}
							sp.repo.hint("cvs", "", true)
							for _, line := range strings.Split(string(value), "\n") {
								if line != "" {
									sp.repo.legacyMap["CVS:"+line] = commit
								}
							}
						}
					}
				} else if bytes.HasPrefix(line, []byte("data")) {
					d, _ := sp.fiReadData(line)
					commit.Comment = string(d)
					if control.flagOptions["canonicalize"] {
						commit.Comment = strings.Replace(strings.TrimSpace(commit.Comment), "\r\n", "\n", -1) + "\n"
					}
				} else if bytes.HasPrefix(line, []byte("from")) || bytes.HasPrefix(line, []byte("merge")) {
					mark := string(bytes.Fields(line)[1])
					if isCallout(mark) {
						commit.addCallout(mark)
					} else {
						commit.addParentByMark(mark)
					}
				} else if line[0] == 'C' || line[0] == 'D' || line[0] == 'R' {
					commit.appendOperation(*newFileOp(sp.repo).parse(string(line)))
				} else if string(line) == "deleteall\n" {
					commit.appendOperation(*newFileOp(sp.repo).parse(string(line)))
				} else if line[0] == opM {
					fileop := newFileOp(sp.repo).parse(string(line))
					if fileop.ref != "inline" {
						ref := sp.repo.markToEvent(fileop.ref)
						if ref != nil {
							ref.(*Blob).addalias(fileop.Path)
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
					if fileop.mode == "160000" {
						// This is a submodule
						// link.  The ref
						// field is a SHA1
						// hash and the path is
						// an external
						// reference name.
						// Don't try to
						// collect data, just
						// pass it through.
						//sp.warn("submodule link")
					} else {
						// 100644, 100755, 120000.
						sp.fiParseFileop(fileop)
					}
					commit.appendOperation(*fileop)
				} else if line[0] == opN {
					fileop := newFileOp(sp.repo).parse(string(line))
					commit.appendOperation(*fileop)
					sp.fiParseFileop(fileop)
					sp.repo.inlines++
				} else if len(bytes.TrimSpace(line)) == 0 {
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
						if commit.hasProperties() && commit.properties.has("branch-nick") {
							sp.repo.hint("", "bzr", true)
						}
					}
					sp.pushback(line)
					break
				}
				baton.twirl()
			}
			if !(commit.mark != "" && commit.committer.fullname != "") {
				sp.importLine = commitbegin
				sp.error("missing required fields in commit")
			}
			if commit.mark == "" {
				sp.warn("unmarked commit")
			}
			sp.repo.addEvent(commit)
			commitcount++
			baton.twirl()
		} else if bytes.HasPrefix(line, []byte("reset")) {
			reset := newReset(sp.repo, "", "")
			reset.ref = string(bytes.TrimSpace(line[6:]))
			line = sp.fiReadline()
			if bytes.HasPrefix(line, []byte("from")) {
				committish := string(bytes.TrimSpace(line[5:]))
				reset.remember(sp.repo, committish)
			} else {
				sp.pushback(line)
			}
			sp.repo.addEvent(reset)
			baton.twirl()
		} else if bytes.HasPrefix(line, []byte("tag")) {
			var tagger *Attribution
			tagname := string(bytes.TrimSpace(line[4:]))
			line = sp.fiReadline()
			legacyID := ""
			if bytes.HasPrefix(line, []byte("#legacy-id ")) {
				// reposurgeon extension, expected to
				// be immediately after "tag" line if
				// present
				legacyID = string(bytes.Fields(line)[1])
				line = sp.fiReadline()
			}
			var referent string
			if bytes.HasPrefix(line, []byte("from")) {
				referent = string(bytes.TrimSpace(line[5:]))
			} else {
				sp.error("missing from after tag")
			}
			line = sp.fiReadline()
			if bytes.HasPrefix(line, []byte("tagger")) {
				var err error
				tagger, err = newAttribution(string(line[7:]))
				if err != nil {
					panic(throw("parse", "in tagger field: %v", err))
				}
			} else {
				sp.warn("missing tagger after from in tag")
				sp.pushback(line)
			}
			d, _ := sp.fiReadData([]byte{})
			tag := newTag(sp.repo, tagname, referent, tagger, string(d))
			tag.legacyID = legacyID
			sp.repo.addEvent(tag)
		} else {
			// Simply pass through any line we do not understand.
			sp.repo.addEvent(newPassthrough(sp.repo, string(line)))
		}
		baton.percentProgress(uint64(sp.ccount))
		if control.readLimit > 0 && uint64(commitcount) >= control.readLimit {
			logit(logSHOUT, "read limit %d reached", control.readLimit)
			break
		}
	}
	baton.endProgress()
	if control.readLimit > 0 && uint64(commitcount) < control.readLimit {
		logit(logSHOUT, "EOF before readlimit.")
	}
	for _, event := range sp.repo.events {
		switch event.(type) {
		case *Reset:
			reset := event.(*Reset)
			if reset.committish != "" {
				commit := sp.repo.markToEvent(reset.committish).(*Commit)
				if commit == nil {

					sp.shout(fmt.Sprintf("unresolved committish in reset %s", reset.committish))
				}
				commit.attach(reset)
			}
		case *Tag:
			tag := event.(*Tag)
			if tag.committish != "" {
				commit := sp.repo.markToEvent(tag.committish).(*Commit)
				if commit == nil {
					sp.shout(fmt.Sprintf("unresolved committish in tag %s", tag.committish))
				}
				commit.attach(tag)
			}
		}
	}
	if !sp.lastcookie.isEmpty() {
		sp.repo.hint("", sp.lastcookie.implies(), false)
	}
}

//
// The main event
//

func (sp *StreamParser) fastImport(ctx context.Context, fp io.Reader, options stringSet, source string) {
	// Initialize the repo from a fast-import stream or Subversion dump.
	sp.timeMark("start")
	var filesize int64
	sp.fp = bufio.NewReader(fp)
	fileobj, ok := fp.(*os.File)
	// Optimization: if we're reading from a plain stream dump,
	// no need to clone all the blobs.
	if ok && isfile(fileobj.Name()) {
		sp.repo.seekstream = fileobj
		filesize = getsize(sp.repo.seekstream.Name())
	}
	if source == "" && sp.repo.seekstream != nil {
		source = sp.repo.seekstream.Name()
	}
	sp.source = source
	baton := control.baton
	//baton.startProcess(fmt.Sprintf("reposurgeon: from %s", source), "")
	sp.repo.legacyCount = 0
	// First, determine the input type
	line := sp.readline()
	rate := func(count int) string {
		if baton != nil {
			elapsed := time.Since(baton.progress.start)
			return fmt.Sprintf("%dK/s", int(float64(elapsed)/float64(count*1000)))
		}
		return ""
	}
	if bytes.HasPrefix(line, []byte("SVN-fs-dump-format-version: ")) {
		body := string(sdBody(line))
		if body != "1" && body != "2" {
			sp.error("unsupported dump format version " + body)
		}
		// Beginning of Subversion dump parsing
		sp.parseSubversion(ctx, &options, baton, filesize)
		// End of Subversion dump parsing
		if control.flagOptions["progress"] {
			fmt.Fprintf(baton, "%d svn revisions (%s)",
				sp.repo.legacyCount, rate(sp.repo.legacyCount*1000))
		}
	} else {
		sp.pushback(line)
		sp.parseFastImport(options, baton, filesize)
		sp.timeMark("parsing")
		if control.flagOptions["progress"] {
			if sp.repo.stronghint {
				fmt.Fprintf(baton, "%d %s events (%s)",
					len(sp.repo.events), sp.repo.vcs.name, rate(len(sp.repo.events)))
			} else {
				fmt.Fprintf(baton, "%d events (%s)",
					len(sp.repo.events), rate(len(sp.repo.events)))
			}
		}
	}
	//baton.endProcess()
	baton = nil
	sp.importLine = 0
	if len(sp.repo.events) == 0 {
		sp.error("ignoring empty repository")
	}

	// FIXME: Fire the defer on signal. First attempt at this failed.
	defer func() {
		if e := catch("parse", recover()); e != nil {
			if baton != nil {
				//baton.endProcess("interrupted by error")
			}
			croak(e.message)
			nuke(sp.repo.subdir(""), fmt.Sprintf("import interrupted, removing %s", sp.repo.subdir("")))
		}
	}()
}


// Generic repository-manipulation code begins here

// Event is an operation in a repository's time sequence of modifications.
type Event interface {
	idMe() string
	getMark() string
	getComment() string
	String() string
	Save(io.Writer)
	moveto(*Repository)
	getDelFlag() bool
	setDelFlag(bool)
	isCommit() bool
}

// walkEvents walks an event list applying a hook function.
// This is intended to be parallelized.  Apply only when the
// computation has no dependency on the order in which commits
// are processed.
//
// Note: There's a clone of this code that walks selection sets.
// Go is not quite generic enough to make unifying the two convenient.
// We need to make sure they stay in sync.
func walkEvents(events []Event, hook func(int, Event)) {
	if control.flagOptions["serial"] {
		for i, e := range events {
			hook(i, e)
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
				hook(i, events[i])
			}
			done <- true
		}()
	}

	// Populate the channel with the events
	for i := range events {
		channel <- i
	}
	close(channel)

	// Wait for all workers to finish
	for n := 0; n < maxWorkers; n++ { <-done }
}

// CommitLike is a Commit or Callout
type CommitLike interface {
	idMe() string
	getMark() string
	hasChildren() bool
	children() []CommitLike
	getComment() string
	callout() string
	String() string
	Save(io.Writer)
	moveto(*Repository)
	getDelFlag() bool
	setDelFlag(bool)
	getColor() colorType
	setColor(colorType)
	isCommit() bool
}

// Contributor - associate a username with a DVCS-style ID and timezone
type Contributor struct {
	local    string
	fullname string
	email    string
	timezone string
}

// ContributorID identifies a contributor for purposes of aliasing
type ContributorID struct {
	fullname string
	email    string
}

func (c Contributor) isEmpty() bool {
	return c.local == ""
}

func (c ContributorID) resolve(repo *Repository) ContributorID {
	for {
		found, ok := repo.aliases[c]
		if ok && !((c.fullname == "" || c.fullname == found.fullname) && c.email == found.email) {
			c = repo.aliases[c]
			continue
		}
		break
	}
	return c
}

// TimeMark is an elapsed-time record for profiling
type TimeMark struct {
	label string
	stamp time.Time
}

// Repository is the entire state of a version-control repository
type Repository struct {
	name         string
	readtime     time.Time
	vcs          *VCS
	stronghint   bool
	hintlist     []Hint
	sourcedir    string
	seekstream   *os.File
	events       []Event // A list of the events encountered, in order
	_markToIndex map[string]int
	_eventByMark map[string]Event
	_namecache   map[string][]int
	preserveSet  orderedStringSet
	caseCoverage orderedIntSet
	basedir      string
	uuid         string
	writeLegacy  bool
	dollarMap    sync.Map // From dollar cookies in files
	dollarOnce   sync.Once
	legacyMap    map[string]*Commit // From anything that doesn't survive rebuild
	legacyCount  int
	timings      []TimeMark
	assignments  map[string]orderedIntSet
	inlines      int
	uniqueness   string // "committer_date", "committer_stamp", or ""
	markseq      int
	authormap    map[string]Contributor
	tzmap        map[string]*time.Location // most recent email address to timezone
	aliases      map[ContributorID]ContributorID
	maplock      sync.Mutex
	// Write control - set, if required, before each dump
	preferred    *VCS             // overrides vcs slot for writes
	realized     map[string]bool  // clear and remake this before each dump
	writeOptions stringSet        // options requested on this write
	internals    orderedStringSet // export code computes this itself
}

func newRepository(name string) *Repository {
	repo := new(Repository)
	repo.name = name
	repo.readtime = time.Now()
	repo.hintlist = make([]Hint, 0)
	repo.preserveSet = newOrderedStringSet()
	repo.caseCoverage = newOrderedIntSet()
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

// memoizeMarks rebuilds the mark cache
func (repo *Repository) memoizeMarks() {
	if !control.flagOptions["tighten"] {
		repo._eventByMark = make(map[string]Event)
		for _, event := range repo.events {
			key := event.getMark()
			if key != "" {
				repo._eventByMark[key] = event
			}
		}
	}
}

// markToEvent finds an object by mark
func (repo *Repository) markToEvent(mark string) Event {
	if control.flagOptions["tighten"] {
		if mark == "" {
			return nil
		}
		for _, event := range repo.events {
			if event.getMark() == mark {
				return event
			}
		}
	} else {
		repo.maplock.Lock()
		defer repo.maplock.Unlock()
		if repo._eventByMark == nil {
			repo.memoizeMarks()
		}
		d, ok := repo._eventByMark[mark]
		if ok {
			return d
		}
	}
	return nil
}

// returns the index of the specified object in the main event list
func (repo *Repository) eventToIndex(obj Event) int {
	mark := obj.getMark()
	if len(mark) != 0 {
		ind := repo.markToIndex(mark)
		if ind >= 0 {
			return ind
		}
	}
	for ind, event := range repo.events {
		if event == obj {
			return ind
		}
	}
	// Alas, we can't use Id() here without infinite recursion
	panic(fmt.Sprintf("Internal error: object %q not matched in repository %s", fmt.Sprintf("%v", obj), repo.name))
}

// gets an object index from its mark, or -1 if not found
func (repo *Repository) markToIndex(mark string) int {
	if repo._markToIndex != nil {
		return repo._markToIndex[mark] - 1
	}
	for ind, event := range repo.events {
		if event.getMark() == mark {
			return ind
		}
	}
	return -1
}

func (repo *Repository) cacheMarkToIndex() {
	if control.flagOptions["tighten"] {
		return
	}
	repo._markToIndex = make(map[string]int)
	for ind, event := range repo.events {
		mark := event.getMark()
		if mark != "" {
			repo._markToIndex[mark] = ind + 1
		}
	}
}

func (repo *Repository) newmark() string {
	repo.markseq++
	mark := ":" + fmt.Sprintf("%d", repo.markseq)
	return mark
}

func (repo *Repository) makedir() {
	target := repo.subdir("")
	logit(logSHUFFLE, "repository fast import creates "+target)
	if _, err1 := os.Stat(target); os.IsNotExist(err1) {
		err2 := os.Mkdir(target, userReadWriteSearchMode)
		if err2 != nil {
			panic("Can't create repository directory")
		}
	} else if err1 != nil {
		panic(fmt.Errorf("Can't stat %s: %v", target, err1))
	}
}

// Hint is a hint about what kind of VCS we're in from looking at magic cookies.
type Hint struct {
	cookie string
	vcs    string
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
		logit(logSHOUT, "new hint %s conficts with old %s",
			clue1, repo.hintlist[len(repo.hintlist)-1])
		return false
	}
	if !repo.stronghint && clue2 != "" {
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

func (repo *Repository) branchset() orderedStringSet {
	// branchset returns a set of all branchnames appearing in this repo.
	branches := newOrderedStringSet()
	for _, e := range repo.events {
		switch e.(type) {
		case *Reset:
			if e.(*Reset).committish != "" {
				branches.Add(e.(*Reset).ref)
			}
		case *Commit:
			branches.Add(e.(*Commit).Branch)
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
			brmap[e.(*Commit).Branch] = e.(*Commit).mark
		}
	}
	return brmap
}

// FIXME: with the compile/exec code, should be possible to do this more cheaply
func (repo *Repository) all() orderedIntSet {
	// Return a set that selects the entire repository.
	s := make([]int, len(repo.events))
	for i := range repo.events {
		s[i] = i
	}
	return s
}

func (repo *Repository) _buildNamecache() {
	// Avoid repeated O(n**2) lookups.
	repo._namecache = make(map[string][]int)
	commitcount := 0
	for i, event := range repo.events {
		switch event.(type) {
		case *Commit:
			commitcount++
			repo._namecache[fmt.Sprintf("#%d", commitcount)] = []int{i}
			commit := event.(*Commit)
			legacyID := commit.legacyID
			if legacyID != "" {
				repo._namecache[legacyID] = []int{i}
			}
			committerStamp := commit.committer.actionStamp()
			var authorStamp string
			if len(commit.authors) > 0 {
				authorStamp = commit.authors[0].actionStamp()
				if authorStamp == committerStamp {
					continue
				} else if _, ok := repo._namecache[authorStamp]; !ok {
					repo._namecache[authorStamp] = []int{i}
				} else {
					repo._namecache[authorStamp] = append(repo._namecache[authorStamp], i)
				}
			}
			if _, ok := repo._namecache[committerStamp]; !ok {
				repo._namecache[committerStamp] = []int{i}
			} else {
				repo._namecache[committerStamp] = append(repo._namecache[committerStamp], i)
			}
		case *Tag:
			repo._namecache[event.(*Tag).name] = []int{i}
		case *Reset:
			repo._namecache["reset@"+filepath.Base(event.(*Reset).ref)] = []int{i}
		}
	}
}

func (repo *Repository) invalidateNamecache() {
	repo._namecache = nil
}

func (repo *Repository) named(ref string) orderedIntSet {
	// Resolve named reference in the control of this repository.
	selection := newOrderedIntSet()
	// For matches that require iterating across the entire event
	// sequence, building an entire name lookup table is !much
	// more expensive in time than doing a single lookup. Avoid
	// lots of O(n**2) searches by building a lookup cache, at the
	// expense of increased working set for the hash table.
	if repo._namecache == nil {
		repo._buildNamecache()
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
					if event.(*Commit).Branch == symbol {
						loc = i
					}
				}
			}
			if loc == -1 {
				panic(throw("command", "branch name %s points to hyperspace", symbol))
			} else {
				return newOrderedIntSet(loc)
			}
		}
	}
	// Next, assignments
	lookup, ok := repo.assignments[ref]
	if ok {
		return lookup
	}
	// Might be a date or action stamp (though action stamps should
	// be in the name cache already).  First, peel off an optional
	// ordinal suffix.
	var ordinal = -1
	stamp := ref
	m := regexp.MustCompile("#[0-9]+$").Find([]byte(ref))
	if m != nil {
		n, _ := strconv.Atoi(string(m[1:]))
		ordinal = n
		stamp = ref[:len(ref)-len(m)]
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
		if err3 == nil {
			datematch = func(u Date) bool {
				d := u.timestamp.Sub(daymark).Hours()
				return d >= 0 && d < 24
			}
		}
	}
	emailID := ""
	resolveAlias := func(a string) string {
		return ContributorID{"", intern(a)}.resolve(repo).email
	}
	if err2 == nil && bang > -1 {
		emailID = resolveAlias(ref[bang+1:])
	}
	matches := newOrderedIntSet()
	if datematch != nil {
		for ei, event := range repo.events {
			switch event.(type) {
			case *Commit:
				commit := event.(*Commit)
				if !datematch(commit.committer.date) {
					continue
				}
				if len(emailID) != 0 && resolveAlias(commit.committer.email) != emailID {
					continue
				} else {
					matches.Add(ei)
				}
			case *Tag:
				tag := event.(*Tag)
				if !datematch(tag.tagger.date) {
					continue
				} else if len(emailID) != 0 && resolveAlias(tag.tagger.email) != emailID {
					continue
				} else {
					matches.Add(ei)
				}
			}
		}
		if len(matches) < 1 {
			panic(throw("command", "no events match %s", ref))
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
	// Force an object-map rebuild on the next mark lookup or mark set.
	repo._eventByMark = nil
}

func (repo *Repository) readAuthorMap(selection orderedIntSet, fp io.Reader) error {
	// Read an author-mapping file and apply it to the repo.
	scanner := bufio.NewScanner(fp)
	var principal Contributor
	var currentLineNumber uint64
	complain := func (msg string, args ...interface{}) {
		logit(logSHOUT, "in readAuthorMap, while parsing line %d: " + msg, append([]interface{}{currentLineNumber}, args)...)
	}
	for scanner.Scan() {
		currentLineNumber++
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		if strings.Contains(line, "=") {
			fields := strings.Split(line, "=")
			local := strings.TrimSpace(fields[0])
			netwide := strings.TrimSpace(fields[1])
			name, mail, timezone, err := parseAttributionLine(netwide)
			if err != nil {
				complain("%v", err)
				continue
			}
			if mail == "" {
				complain("can't recognize address in '%s'", netwide)
				continue
			}
			if timezone != "" {
				loc, err2 := time.LoadLocation(timezone)
				if err2 != nil {
					loc, err2 = locationFromZoneOffset(timezone)
					if err2 != nil {
						complain("timezone lookup: %v", err2)
						continue
					}
				}
				repo.tzmap[mail] = loc
			}
			key := strings.ToLower(local)
			principal = Contributor{local, name, mail, timezone}
			repo.authormap[key] = principal
		}
		// Process aliases gathered from Changelog entries
		if line[0] == '+' {
			if principal.isEmpty() {
				complain("alias entry before any principal")
				continue
			}
			line = strings.TrimSpace(line[1:])
			aname, aemail, atimezone, aerr := parseAttributionLine(line)
			if aerr != nil {
				complain("bad contributor alias: %v", aerr)
				continue
			}
			repo.aliases[ContributorID{aname, aemail}] = ContributorID{principal.fullname, principal.email}
			if atimezone != "" {
				loc, err2 := time.LoadLocation(atimezone)
				if err2 != nil {
					loc, err2 = locationFromZoneOffset(atimezone)
					if err2 != nil {
						complain("timezone lookup: %v", err2)
						continue
					}
				}
				repo.tzmap[aemail] = loc
			}
		}
	}

	repo.walkEvents(selection, func(idx int, event Event) {
		switch event.(type) {
		case *Commit:
			c := event.(*Commit)
			c.committer.remap(repo.authormap)
			for ai := range c.authors {
				c.authors[ai].remap(repo.authormap)
			}
		case *Tag:
			event.(*Tag).tagger.remap(repo.authormap)
		}
	})
	// Email addresses have changed.
	// Force rebuild of action-stamp mapping on next lookup
	repo.invalidateNamecache()

	return nil
}

// List the identities we know.
func (repo *Repository) writeAuthorMap(selection orderedIntSet, fp io.Writer) error {
	contributors := make(map[string]string)
	for _, ei := range selection {
		event := repo.events[ei]
		switch event.(type) {
		case *Commit:
			commit := event.(*Commit)
			contributors[commit.committer.userid()] = commit.committer.who()
			for _, author := range commit.authors {
				contributors[author.userid()] = author.who()
			}
		case *Tag:
			tag := event.(*Tag)
			contributors[tag.tagger.userid()] = tag.tagger.who()
		}
	}
	for userid, cid := range contributors {
		_, err := fmt.Fprintf(fp, "%s = %s\n", userid, cid)
		if err != nil {
			return fmt.Errorf("in writeAuthorMap: %v", err)
		}
	}
	return nil
}

func (repo *Repository) byCommit(hook func(commit *Commit)) {
	for _, event := range repo.events {
		switch event.(type) {
		case *Commit:
			hook(event.(*Commit))
		}
	}
}

// Read a legacy-references dump and use it to initialize the repo's legacy map.
func (repo *Repository) readLegacyMap(fp io.Reader) error {
	type dyad struct {
		a string
		b string
	}
	commitMap := make(map[dyad][]*Commit)
	repo.byCommit(func(commit *Commit) {
		key := dyad{commit.committer.date.timestamp.String(), commit.committer.email}
		if _, ok := commitMap[key]; !ok {
			commitMap[key] = make([]*Commit, 0)
		}
		commitMap[key] = append(commitMap[key], commit)
	})

	linecount := 0
	matched := 0
	unmatched := 0

	scanner := bufio.NewScanner(fp)
	for scanner.Scan() {
		linecount++
		line := scanner.Text()

		lineError := func(legend string) error {
			return fmt.Errorf(legend+": line %d %q\n", linecount, line)
		}

		if strings.HasPrefix(line, "#") {
			continue
		}
		fields := strings.Fields(line)
		if len(fields) != 2 {
			return lineError("bad line syntax in legacy map")
		}
		legacy, stamp := fields[0], fields[1]
		parts := strings.Split(stamp, "!")
		if len(fields) != 2 {
			return lineError("bad action stamp syntax in legacy map.")
		}
		var seq int
		var person, seqstr string
		timefield, person := parts[0], parts[1]
		if strings.Contains(person, ":") {
			fields = strings.Split(person, ":")
			person, seqstr = fields[0], fields[1]
			d, err := strconv.Atoi(seqstr)
			if err != nil {
				lineError("bad sequence number")
			}
			seq = d - 1
		} else {
			seq = 0
		}
		if legacy == "" || timefield == "" || person == "" {
			lineError("entry has blank fields")
		}
		when, err2 := newDate(timefield)
		if err2 != nil {
			return lineError(err2.Error())
		}
		whenWho := dyad{when.timestamp.String(), person}
		if _, ok := commitMap[whenWho]; ok {
			repo.legacyMap[legacy] = commitMap[whenWho][seq]
			if strings.HasPrefix(legacy, "SVN:") {
				commitMap[whenWho][seq].legacyID = legacy[4:]
			}
			matched++
		} else {
			unmatched++
		}
		control.baton.twirl()
	}

	respond("%d matched, %d unmatched, %d total",
		matched, unmatched, matched+unmatched)
	return nil
}

// commits returns a slice of the commits in a specified selection set
// or all commits if the selection set is nil.
func (repo *Repository) commits(selection orderedIntSet) []*Commit {
	out := make([]*Commit, 0)
	if selection == nil {
		for _, event := range repo.events {
			commit, ok := event.(*Commit)
			if ok {
				out = append(out, commit)
			}
		}
	} else {
		for _, idx := range selection {
			event := repo.events[idx]
			commit, ok := event.(*Commit)
			if ok {
				out = append(out, commit)
			}
		}
	}
	return out
}

// Dump legacy references.
func (repo *Repository) writeLegacyMap(fp io.Writer) error {
	keylist := make([]string, 0)
	for key := range repo.legacyMap {
		keylist = append(keylist, key)
	}
	sort.Slice(keylist, func(i, j int) bool {
		return keylist[i] < keylist[j]
	})
	for _, cookie := range keylist {
		commit := repo.legacyMap[cookie]
		var serial string
		if strings.Contains(cookie, "SVN") && strings.Contains(cookie, splitSep) {
			serial = ":" + strings.Split(cookie, splitSep)[1]
		} else {
			serial = ""
		}
		// The markToEvent test is needed in case this
		// repo is an expunge fragment with a copied
		// legacy map.  It's a simple substitute for
		// partitioning the map at expunge time.
		if repo.markToEvent(commit.mark) != nil && commit.legacyID != "" {
			// Someday check errors here?
			fmt.Fprintf(fp, "%s\t%s!%s%s\n", cookie,
				commit.committer.date.rfc3339(),
				commit.committer.email,
				serial)
		}
		control.baton.twirl()
	}
	return nil
}

// Turn a commit into a tag.
func (repo *Repository) tagify(commit *Commit, name string, target string, legend string, delete bool) {
	if logEnable(logEXTRACT) {
		commitID := commit.mark
		if commit.legacyID != "" {
			commitID += fmt.Sprintf(" <%s>", commit.legacyID)
		}
		logit(logSHOUT, fmt.Sprintf("tagifying: %s -> %s", commitID, name))
	}
	if len(commit.operations()) > 0 {
		panic("Attempting to tagify a commit with fileops.")
	}
	var pref string
	if commit.Comment == "" {
		pref = ""
	} else {
		pref = commit.Comment
		if legend != "" || !strings.HasSuffix(pref, "\n") {
			pref += "\n"
		}
	}
	tag := newTag(commit.repo, name, target, &commit.committer, pref+legend)
	tag.legacyID = commit.legacyID
	repo.addEvent(tag)
	if delete {
		commit.delete([]string{"--tagback"})
	}
}

// Default scheme to name tags generated from empty commits
func defaultEmptyTagName(commit *Commit) string {
	if len(commit.operations()) > 0 {
		branch := commit.Branch
		if strings.HasSuffix(branch, svnSep) {
			branch = branch[:len(branch)-1]
		}
		return "tipdelete-" + branchbase(branch)
	}
	if commit.legacyID != "" {
		return "emptycommit-" + commit.legacyID
	} else if commit.mark != "" {
		return "emptycommit-mark" + commit.mark[1:]
	} else {
		return fmt.Sprintf("emptycommit-index%d", commit.index())
	}
}

/*
   func tagifyEmpty(self, commits = nil,
                          tipdeletes = false,
                          tagifyMerges = false,
                          canonicalize = true,
                          nameFunc = nil,
                          legendFunc = nil,
                          createTags = true,
                          gripe = complain
                         ):
           Arguments: * commits:       nil for all, or a set of event indices
                                       tagifyEmpty() ignores non-commits
                      * tipdeletes:    whether tipdeletes should be tagified
                      * canonicalize:  whether to canonicalize fileops first
                      * nameFunc:      custom function for choosing the tag
                                       name; if it returns an emoty string,
                                       a default scheme is used
                      * legendFunc:    custom function for choosing the legend
                                       of a tag; no fallback is provided. By
                                       default it always returns "".
                      * createTags    whether to create tags.
*/

func (repo *Repository) tagifyEmpty(selection orderedIntSet, tipdeletes bool, tagifyMerges bool, canonicalize bool, nameFunc func(*Commit) string, legendFunc func(*Commit) string, createTags bool, gripe func(string)) {
	// Turn into tags commits without (meaningful) fileops.
	// Use a separate loop because delete() invalidates manifests.
	if canonicalize {
		for _, commit := range repo.commits(selection) {
			commit.canonicalize()
		}
	}
	if gripe == nil {
		gripe = func(msg string) { logit(logEXTRACT, msg) }
	}
	// Tagify commits without fileops
	var isTipdelete = func(commit *Commit) bool { return false }
	if tipdeletes {
		isTipdelete = func(c *Commit) bool {
			return c.alldeletes(deleteall) && !c.hasChildren()
		}
	}
	deletia := make([]int, 0)
	tagifyEvent := func(index int) {
		commit, ok := repo.events[index].(*Commit)
		if !ok {
			return
		}
		var name string
		if len(commit.operations()) == 0 || isTipdelete(commit) {
			if commit.hasParents() {
				if len(commit.parents()) > 1 && !tagifyMerges {
					return
				}
				if nameFunc != nil {
					name = nameFunc(commit)
					if name == "" {
						name = defaultEmptyTagName(commit)
					}
				} else {
					name = defaultEmptyTagName(commit)
				}
				//for repo.named(name) != nil {
				//	name += "-displaced"
				//}
				legend := ""
				if legendFunc != nil {
					legend = legendFunc(commit)
				}
				commit.setOperations(nil)
				if createTags {
					repo.tagify(commit,
						name,
						commit.parents()[0].getMark(),
						legend,
						false)
				}
				deletia = append(deletia, index)
			} else {
				if commit.Branch != "refs/heads/master" {
					msg := ""
					if commit.legacyID != "" && repo.vcs != nil && repo.vcs.name == "svn" {
						msg += fmt.Sprintf(" r%s:", commit.legacyID)
					} else if commit.mark != "" {
						msg += fmt.Sprintf(" '%s':", commit.mark)
					}
					msg += " deleting parentless "
					if len(commit.operations()) > 0 {
						msg += fmt.Sprintf("tip delete of %s.", commit.Branch)
					} else {
						msg += fmt.Sprintf("zero-op commit on %s.", commit.Branch)
					}
					gripe(msg[1:])
					deletia = append(deletia, index)
				}
			}
		}

	}

	if len(selection) == 0 {
		for index := range repo.events {
			tagifyEvent(index)
		}
	} else {
		for _, index := range selection {
			tagifyEvent(index)
		}
	}
	repo.delete(deletia, []string{"--tagback", "--tagify"})
}

// Read a stream file and use it to populate the repo.
func (repo *Repository) fastImport(ctx context.Context, fp io.Reader, options stringSet, source string) {
	newStreamParser(repo).fastImport(ctx, fp, options, source)
	repo.readtime = time.Now()
}

// Extract info about legacy references from CVS/SVN header cookies.
func (repo *Repository) parseDollarCookies() {
	// Set commit legacy properties from $Id$ && $Subversion$
	// cookies in blobs. In order to throw away stale headers from
	// after, e.g., a CVS-to-SVN or SVN-to-git conversion, we
	// ignore duplicate keys - note this assumes commits are properly
	// time-ordered, which is true for SVN but maybe not for
	// CVS. Might be we should explicitly time-check in the latter
	// case, but CVS timestamps aren't reliable so it might not
	// include conversion quality any.
	walkEvents(repo.events, func(idx int, event Event) {
		commit, iscommit := event.(*Commit)
		if !iscommit {
			return
		}
		for _, fileop := range commit.operations() {
			if fileop.op != opM {
				continue
			}
			blob := repo.markToEvent(fileop.ref).(*Blob)
			if commit.hasProperties() && commit.properties.get("legacy") != "" {
				croak("legacy property of %s overwritten",
					commit.mark)
			}
			if blob.cookie.implies() == "SVN" {
				svnkey := "SVN:" + blob.cookie.rev
				repo.dollarMap.LoadOrStore(svnkey, commit)
			} else if !blob.cookie.isEmpty() {
				if filepath.Base(fileop.Path) != blob.cookie.path {
					// Usually the
					// harmless result of
					// a file move or copy
					// that cvs2svn or
					// git-svn didn't pick
					// up on.
					croak("mismatched CVS header path '%s' in %s vs '%s' in %s",
						fileop.Path, commit.mark, blob.cookie.path, blob.mark)
				}
				cvskey := fmt.Sprintf("CVS:%s:%s", fileop.Path, blob.cookie.path)
				repo.dollarMap.LoadOrStore(cvskey, commit)
			}
		}
	})
}

// Audit the repository for uniqueness properties.
func (repo *Repository) checkUniqueness(chatty bool, logHook func(string)) {
	repo.uniqueness = ""
	timecheck := make(map[string]Event)
	timeCollisions := make(map[string][]Event)
	// Not worth parallelizing this loop, there isn't enough going on
	// outside of the actual mapn accesses - which must be locked and
	// serialized.
	commits := repo.commits(nil)
	for _, event := range commits {
		when := event.when().String()
		if _, recorded := timecheck[when]; recorded {
			if _, ok := timeCollisions[when]; !ok {
				timeCollisions[when] = []Event{}
			}
			timeCollisions[when] = append(timeCollisions[when], event)
		}
		timecheck[when] = event
	}
	if len(timeCollisions) == 0 {
		repo.uniqueness = "committer_date"
		if chatty {
			logHook("All commit times in this repository are unique.")
		}
		return
	}
	if logHook != nil {
		reps := make([]string, 0)
		for k := range timeCollisions {
			reps = append(reps, k)
		}
		logHook("These timestamps have multiple commits: %s" +
			strings.Join(reps, " "))
	}
	stampCollisions := newOrderedStringSet()
	for _, clique := range timeCollisions {
		stampcheck := make(map[string]string)
		for _, event := range clique {
			commit, ok := event.(*Commit)
			if !ok {
				continue
			}
			stamp, ok := stampcheck[commit.actionStamp()]
			if ok {
				stampCollisions.Add(stamp)
				//stampCollisions.Add(commit.mark)
			}
			stampcheck[stamp] = commit.mark
		}
	}
	if len(stampCollisions) == 0 {
		repo.uniqueness = "committer_stamp"
		if logHook != nil {
			logHook("All commit stamps in this repository are unique.")
		}
		return
	}
	if logHook != nil {
		logHook("These marks are in stamp collisions: " +
			strings.Join(stampCollisions, " "))
	}
}

// exportStyle says how we should we tune the export dump format.
func (repo *Repository) exportStyle() orderedStringSet {
	if repo.vcs != nil {
		return repo.vcs.styleflags
	}
	// Default to git style
	return orderedStringSet{"nl-after-commit"}
}

// Dump the repo object in Subversion dump or fast-export format.
func (repo *Repository) fastExport(selection orderedIntSet,
	fp io.Writer, options stringSet, target *VCS) error {
	repo.writeOptions = options
	repo.preferred = target
	repo.internals = nil
	// Select all blobs implied by the commits in the range. If we ever
	// go to a representation where fileops are inline this logic will need
	// to be modified.
	if selection == nil {
		selection = repo.all()
	} else {
		repo.internals = newOrderedStringSet()
		for _, ei := range selection {
			event := repo.events[ei]
			if mark := event.getMark(); mark != "" {
				repo.internals.Add(mark)
			}
			if commit, ok := event.(*Commit); ok {
				for _, fileop := range commit.operations() {
					if fileop.op == opM {
						idx := repo.markToIndex(fileop.ref)
						if fileop.ref != "inline" {
							selection.Add(idx)
						}
					}
				}
				for _, tag := range commit.attachments {
					selection.Add(repo.eventToIndex(tag))
				}
			}
			control.baton.twirl()
		}
		selection.Sort()
	}
	repo.realized = make(map[string]bool) // Track what branches are made
	baton := control.baton
	baton.startProgress("export", uint64(len(repo.events)))
	for idx, ei := range selection {
		baton.twirl()
		event := repo.events[ei]
		if passthrough, ok := event.(*Passthrough); ok {
			// Support writing bzr repos to plain git if they don't
			// actually have the extension features their export
			// streams declare.  Without this check git fast-import
			// barfs on declarations for unused features.
			if strings.HasPrefix(passthrough.text, "feature") && !target.extensions.Contains(strings.Fields(passthrough.text)[1]) {
				continue
			}
		}
		if logEnable(logUNITE) {
			if event.getMark() != "" {
				logit(logSHOUT, fmt.Sprintf("writing %d %s", ei, event.getMark()))
			}
		}
		event.Save(fp)
		baton.percentProgress(uint64(idx) + 1)
	}
	baton.endProgress()
	repo.realized = nil
	return nil
}

// Add a path to the preserve set, to be copied back on rebuild.
func (repo *Repository) preserve(filename string) error {
	if exists(filename) {
		repo.preserveSet.Add(filename)
	} else {
		return fmt.Errorf("%s doesn't exist", filename)
	}
	return nil
}

// Remove a path from the preserve set.
func (repo *Repository) unpreserve(filename string) error {
	if repo.preserveSet.Contains(filename) {
		repo.preserveSet.Remove(filename)
	} else {
		return fmt.Errorf("%s is not preserved", filename)
	}
	return nil
}

// Return the repo's preserve set.
func (repo *Repository) preservable() orderedStringSet {
	return repo.preserveSet
}

// Rename the repo.
func (repo *Repository) rename(newname string) error {
	// Can fail if the target directory exists.
	if exists(repo.subdir("")) {
		logit(logSHUFFLE, fmt.Sprintf("repository rename %s->%s calls os.Rename(%q, %q)", repo.name, newname, repo.subdir(""), repo.subdir(newname)))
		err := os.Rename(repo.subdir(""), repo.subdir(newname))
		if err != nil {
			return fmt.Errorf("repo rename %s -> %s failed: %s", repo.subdir(""), repo.subdir(newname), err)
		}
	}
	repo.name = newname
	return nil
}

// Fast append avoids doing a full copy of the slice on every allocation
// Code trivially modified from AppendByte on "Go Slices: usage and internals".
func appendEvents(slice []Event, data ...Event) []Event {
	m := len(slice)
	n := m + len(data)
	if n > cap(slice) { // if necessary, reallocate
		// allocate double what's needed, for future growth.
		newSlice := make([]Event, max((n+1)*2, maxAlloc))
		copy(newSlice, slice)
		slice = newSlice
	}
	slice = slice[0:n]
	copy(slice[m:n], data)
	return slice
}

// Insert an event just before the specified index.
func (repo *Repository) insertEvent(event Event, where int, legend string) {
	// No-alloc insert: https://github.com/golang/go/wiki/SliceTricks
	repo.events = appendEvents(repo.events, nil)
	copy(repo.events[where+1:], repo.events[where:])
	repo.events[where] = event
	repo.declareSequenceMutation(legend)
}

func (repo *Repository) addEvent(event Event) {
	isDone := func(event Event) bool {
		passthrough, ok := event.(*Passthrough)
		return ok && passthrough.text == "done"
	}
	if len(repo.events) > 0 && isDone(repo.events[len(repo.events)-1]) {
		repo.insertEvent(event, len(repo.events)-1, "")
	} else {
		repo.events = append(repo.events, event)
	}
	repo.declareSequenceMutation("")
}

// Filter assignments, warning if any of them goes empty.
func (repo *Repository) filterAssignments(f func(Event) bool) {
	intContains := func(list []int, val int) bool {
		for _, v := range list {
			if v == val {
				return true
			}
		}
		return false
	}
	for name, values := range repo.assignments {
		newassigns := make([]int, 0)
		dc := 0
		for i, e := range repo.events {
			if f(e) {
				dc++
			} else if intContains(values, i) {
				newassigns = append(newassigns, i-dc)
			}
		}
		if len(values) > 0 && len(newassigns) == 0 {
			croak(fmt.Sprintf("sequence modification left %s empty", name))
		}
		repo.assignments[name] = newassigns
	}
}

// Mark the repo event sequence modified.
func (repo *Repository) declareSequenceMutation(warning string) {
	repo._markToIndex = nil
	repo._namecache = nil
	if len(repo.assignments) > 0 && warning != "" {
		repo.assignments = nil
		croak("assignments invalidated by " + warning)
	}
}

// Return the earliest commit.
func (repo *Repository) earliestCommit() *Commit {
	for _, event := range repo.events {
		commit, ok := event.(*Commit)
		if ok {
			return commit
		}
	}
	panic(throw("command", "repository has no commits"))
}

// Return the date of earliest commit.
func (repo *Repository) earliest() time.Time {
	return repo.earliestCommit().committer.date.timestamp
}

// Return ancestors of an event, in reverse order.
func (repo *Repository) ancestors(ei int) orderedIntSet {
	trail := newOrderedIntSet()
	for {
		commit, ok := repo.events[ei].(*Commit)
		if !ok {
			panic(throw("command", "ancestors() reached non-commit event %d", ei))
		}
		if !commit.hasParents() {
			break
		} else {
			efrom := repo.markToIndex(commit.parentMarks()[0])
			trail.Add(efrom)
			ei = efrom
		}
	}
	return trail
}

//
// Delete machinery begins here
//
// Count modifications of a path in this commit && its ancestors.
func (commit *Commit) ancestorCount(path string) int {
	count := 0
	for {
		for _, fileop := range commit.operations() {
			if fileop.op == opM && fileop.Path == path {
				count++
				break
			}
		}
		// 0, 1, && >1 are the interesting cases
		if count > 1 {
			return count
		}
		if commit.hasParents() {
			event := commit.parents()[0]
			lst, ok := event.(*Commit)
			if !ok {
				// Could be a Callout object
				break
			}
			commit = lst
		} else {
			break
		}
	}
	return count
}

var nilOp FileOp // Zero fileop, to be used as a deletion marker

// Compose two relevant fileops.
// Here's what the fields in the return value mean:
// 0: Was this a modification
// 1: Op to replace the first with (nil means delete)
// 2: Op to replace the second with (nil means delete)
// 3: string: if nomempty, a warning to emit
// 4: Case number, for coverage analysis
func (commit *Commit) _compose(left FileOp, right FileOp) (bool, FileOp, FileOp, string, int) {
	pair := [2]rune{left.op, right.op}
	//
	// First op M
	//
	if pair == [2]rune{opM, opM} {
		// Leave these in place, they get handled later.
		return false, left, right, "", 0
	} else if left.op == opM && right.op == opD {
		// M a + D a -> D a
		// Or, could reduce to nothing if M a was the only modify..
		if commit.ancestorCount(left.Path) == 1 {
			return true, nilOp, nilOp, "", 1
		}
		return true, right, nilOp, "", 2
	} else if left.op == opM && right.op == opR {
		// M a + R a b -> R a b M b, so R falls towards start of list
		if left.Path == right.Source {
			if commit.ancestorCount(left.Path) == 1 {
				// M a has no ancestors, preceding R can be dropped
				left.Path = right.Target
				return true, left, nilOp, "", 3
			}
			// M a has ancestors, R is still needed
			left.Path = right.Target
			return true, right, left, "", 4
		} else if left.Path == right.Target {
			// M b + R a b can't happen.  If you try to
			// generate this with git mv it throws an
			// error.  An ordinary mv results in D b M a.
			return true, right, nilOp, "M followed by R to the M operand?", -1
		}
	} else if left.op == opM && right.op == opC {
		// Correct reduction for this would be M a + C a b ->
		// C a b + M a + M b, that is we'd have to duplicate
		// the modify. We'll leave it in place for now.
		return false, left, right, "", 5
	} else if pair == [2]rune{opD, opM} {
		//
		// First op D || deleteall
		//
		// Delete followed by modify undoes delete, since M
		// carries whole files.
		return true, nilOp, right, "", 6
	} else if pair == [2]rune{deleteall, opM} {
		// But we have to leave deletealls in place, since
		// they affect right ops
		return false, left, right, "", 7
	} else if left.op == deleteall && right.op != opM {
		// These cases should be impossible.  But cvs2svn
		// actually generates adjacent deletes into Subversion
		// dumpfiles which turn into (D, D).
		return false, left, right,
			"Non-M operation after deleteall?", -1
	} else if left.op == opD && right.op == opD {
		return true, left, nilOp, "", -2
	} else if left.op == opD && (right.op == opR || right.op == opC) {
		if left.Path == right.Source {
			return false, left, right,
				fmt.Sprintf("R or C of %s after deletion?", left.Path), -3
		}
		return false, left, right, "", 8
	} else if pair == [2]rune{opR, opD} {
		//
		// First op R
		//
		if left.Target == right.Path {
			// Rename followed by delete of target
			// composes to source delete
			right.Path = left.Source
			return true, nilOp, right, "", 9
		}
		// On rename followed by delete of source
		// discard the delete but user should be
		// warned.
		return false, left, nilOp, fmt.Sprintf("delete of %s after renaming to %s?", right.Path, left.Source), -4

	} else if pair == [2]rune{opR, deleteall} && left.Target == right.Path {
		// Rename followed by deleteall shouldn't be possible
		return false, nilOp, right,
			"rename before deleteall not removed?", -5
	} else if pair == [2]rune{opR, opM} || pair == [2]rune{opC, opM} {
		// Leave rename || copy followed by modify alone
		return false, left, right, "", 10
	} else if left.op == opR && right.op == opR {
		// Compose renames where possible
		if left.Target == right.Source {
			left.Target = right.Target
			return true, left, nilOp, "", 11
		}
		return false, left, right, fmt.Sprintf("R %s %s is inconsistent with following operation", left.Source, left.Target), -6
	}
	// We could do R a b + C b c -> C a c + R a b, but why?
	if left.op == opR && right.op == opC {
		return false, left, right, "", 12
	} else if pair == [2]rune{opC, opD} {
		//
		// First op C
		//
		if left.Source == right.Path {
			// Copy followed by delete of the source is a rename.
			left.setOp(opR)
			return true, left, nilOp, "", 13
		} else if left.Target == right.Path {
			// This delete undoes the copy
			return true, nilOp, nilOp, "", 14
		}
	} else if pair == [2]rune{opC, opR} {
		if left.Source == right.Source {
			// No reduction
			return false, left, right, "", 15
		}
		// Copy followed by a rename of the target reduces to single copy
		if left.Target == right.Source {
			left.Target = right.Target
			return true, left, nilOp, "", 16
		}
	} else if pair == [2]rune{opC, opC} {
		// No reduction
		return false, left, right, "", 17
	}
	//
	// Case not covered
	//
	panic(throw("command", "in %s, can't compose op '%s' and '%s'", commit.idMe(), left, right))
}

// Simplify the list of file operations in this commit.
func (commit *Commit) simplify() orderedIntSet {
	// Doesn't need to be ordered, but I'm not going to write a whole
	// 'nother set class just for this.
	coverage := newOrderedIntSet()
	// Handling deleteall operations is simple
	lastdeleteall := -1
	for i, a := range commit.operations() {
		if a.op == deleteall {
			lastdeleteall = i
		}
	}
	if lastdeleteall != -1 {
		logit(logDELETE, "removing all before rightmost deleteall")
		commit.setOperations(commit.operations()[lastdeleteall:])
	}
	// Composition in the general case is trickier.
	for {
		// Keep making passes until nothing mutates
		mutated := false
		for i := range commit.operations() {
			for j := i + 1; j < len(commit.operations()); j++ {
				a := commit.operations()[i]
				b := commit.operations()[j]
				if !a.Equals(&nilOp) && !b.Equals(&nilOp) && a.relevant(&b) {
					modified, newa, newb, warn, cn := commit._compose(a, b)
					logit(logDELETE, fmt.Sprintf("Reduction case %d fired on (%d, %d)", cn, i, j))
					if modified {
						mutated = true
						commit.operations()[i] = newa
						commit.operations()[j] = newb
						if logEnable(logDELETE) {
							logit(logDELETE, "During canonicalization:")
							commit.fileopDump()
						}
						if warn != "" {
							croak(warn)
						}
						coverage.Add(cn)
					}
				}
			}
		}
		if !mutated {
			break
		}
		newOps := make([]FileOp, 0)
		for _, x := range commit.operations() {
			if !x.Equals(&nilOp) {
				newOps = append(newOps, x)
			}
		}
		commit.setOperations(newOps)
	}
	return coverage
}

var allPolicies = orderedStringSet{
	"--complain",
	"--coalesce",
	"--delete",
	"--empty-only",
	"--pushback",
	"--pushforward",
	"--tagify",
	"--tagback",
	"--tagforward",
	"--quiet",
}

// Delete a set of events, or rearrange it forward or backwards.
func (repo *Repository) squash(selected orderedIntSet, policy orderedStringSet) error {
	logit(logDELETE, "Deletion list is %v", selected)
	for _, qualifier := range policy {
		if !allPolicies.Contains(qualifier) {
			return errors.New("no such deletion modifier as " + qualifier)
		}
	}
	// For --pushback, it is critical that deletions take place
	// from lowest event number to highest since --pushback often
	// involves re-ordering events even as it is iterating over
	// the "selected" list. Only events earlier than the event
	// currently being processed are re-ordered, however, so the
	// operation is safe as long as events are visited lowest to
	// highest. (For --pushforward, iteration order is immaterial
	// since it does no event re-ordering and actual deletion is
	// delayed until after iteration is finished.)
	selected.Sort()
	dquiet := policy.Contains("--quiet")
	delete := policy.Contains("--delete")
	tagify := policy.Contains("--tagify")
	tagback := policy.Contains("--tagback")
	tagforward := policy.Contains("--tagforward") || (!delete && !tagback)
	pushback := policy.Contains("--pushback")
	pushforward := policy.Contains("--pushforward") || (!delete && !pushback)
	// Sanity checks
	if !dquiet {
		for _, ei := range selected {
			event := repo.events[ei]
			commit, ok := event.(*Commit)
			if !ok {
				continue
			}
			if delete {
				speak := fmt.Sprintf("warning: commit %s to be deleted has ", commit.mark)
				if strings.Contains(commit.Branch, "/") && !strings.Contains(commit.Branch, "/heads/") {
					logit(logWARN, speak+fmt.Sprintf("non-head branch attribute %s", commit.Branch))
				}
				if !commit.alldeletes(opD, deleteall) {
					logit(logWARN, speak+"non-delete fileops.")
				}
			}
			if !delete {
				if pushback && !commit.hasParents() {
					croak("warning: pushback of parentless commit %s", commit.mark)
				}
				if pushforward && !commit.hasChildren() {
					croak("warning: pushforward of childless commit %s", commit.mark)
				}
			}
		}
	}
	altered := make([]*Commit, 0)
	// Here are the deletions
	for _, event := range repo.events {
		event.setDelFlag(false)
	}
	var newTarget *Commit
	for _, ei := range selected {
		event := repo.events[ei]
		switch event.(type) {
		case *Blob:
			// Never delete a blob except as a side effect of
			// deleting a commit.
			event.setDelFlag(false)
		case *Tag:
			event.setDelFlag(delete)
		case *Reset:
			event.setDelFlag(delete)
		case *Passthrough:
			event.setDelFlag(delete)
		case *Commit:
			event.setDelFlag(true)
			commit := event.(*Commit)
			// Decide the new target for tags
			filterOnly := true
			if tagforward && commit.hasChildren() {
				filterOnly = false
				newTarget = commit.firstChild()
			} else if tagback && commit.hasParents() {
				noncallout, ok := commit.parents()[0].(*Commit)
				if ok {
					filterOnly = false
					newTarget = noncallout
				}
			}
			if newTarget != nil {
				logit(logDELETE, "new target for tags and resets is %s", newTarget.getMark())
			}
			// Reparent each child.  Concatenate comments,
			// ignoring empty-log-message markers.
			composeComment := func(a string, b string) string {
				if a == b {
					return a
				}
				aEmpty := emptyComment(a)
				bEmpty := emptyComment(b)
				if aEmpty && bEmpty {
					return ""
				} else if aEmpty && !bEmpty {
					return b
				} else if !aEmpty && bEmpty {
					return a
				}
				return a + "\n" + b
			}
			// FIXME: effectively duplicates listMarks
			listCommitsByMark := func(items []CommitLike) []string {
				// Used for diagnostics
				marks := make([]string, 0)
				for _, item := range items {
					var legend string
					if item == nil {
						legend = "nil"
					} else {
						legend = fmt.Sprintf("%s", item.getMark())
					}
					marks = append(marks, legend)
				}
				return marks
			}
			//logit(logDELETE, "deleting %s requires %v to be reparented.", commit.getMark(), commit.childMarks())
			for _, cchild := range commit.childMarks() {
				if isCallout(cchild) {
					continue
				}
				child := repo.markToEvent(cchild).(*Commit)
				// Insert commit's parents in place of
				// commit in child's parent list. We
				// keep existing duplicates in case
				// they are wanted, <s>but ensure we
				// don't introduce new ones.</s> -
				// that was true in Python but no
				// longer unless it induces a bug.
				oldParents := child.parents()
				eventPos := 0
				for i, p := range oldParents {
					if p == commit {
						eventPos = i
						break
					}
				}
				//logit(logDELETE, "reparenting: %s", child.getMark())
				// Start with existing parents before us,
				// including existing duplicates
				newParents := make([]CommitLike, len(oldParents)-1+len(commit.parents()))
				newParentIndex := 0
				newParentIndex += copy(newParents, oldParents[:eventPos])
				// Add our parents. The Python version
				// tossed out duplicates of preceding
				// parents.  Skip callouts.
				for _, ancestor := range commit.parents() {
					newParents[newParentIndex] = ancestor
					newParentIndex++
				}
				// In Python, we "Avoid duplicates due to
				// commit.parents() insertion." Requires some
				// odd contortions in Go so we won't do it
				// unless there's a bug case.
				if len(oldParents) > eventPos {
					copy(newParents[newParentIndex:], oldParents[eventPos+1:])
				}
				// Prepend a copy of this event's file ops to
				// all children with the event as their first
				// parent,and mark each such child as needing
				// resolution.
				if pushforward && child.parents()[0] == commit {
					newops := make([]FileOp, len(commit.operations()))
					copy(newops, commit.operations())
					newops = append(newops, child.operations()...)
					child.setOperations(newops)
					// Also prepend event's
					// comment, ignoring empty log
					// messages.
					if policy.Contains("--empty-only") && !emptyComment(child.Comment) {
						croak(fmt.Sprintf("--empty is on and %s comment is nonempty", child.idMe()))
					}
					child.Comment = composeComment(commit.Comment,
						child.Comment)
					altered = append(altered, child)
				}
				// Really set the parents to the newly
				// constructed list
				logit(logDELETE, "Parents of %s changed from %v to %v",
					child.getMark(), listCommitsByMark(oldParents), listCommitsByMark(newParents))
				child.setParents(newParents)
				// If event was the first parent of
				// child yet has no parents of its
				// own, then child's first parent has
				// changed.  Prepend a deleteall to
				// child's fileops to ensure it starts
				// with an empty tree (as event does)
				// instead of inheriting that of its
				// new first parent.
				if eventPos == 0 && !commit.hasParents() {
					fileop := newFileOp(repo)
					fileop.construct(deleteall)
					child.prependOperation(*fileop)
					altered = append(altered, child)
				}
			}
			// OK, we're done manipulating commit's children.
			// We might be trying to hand the commit's
			// fileops to its primary parent.
			if pushback && commit.hasParents() {
				// Append a copy of this event's file
				// ops to its primary parent fileop
				// list and mark the parent as needing
				// resolution.
				cparent := commit.parents()[0]
				parent, ok := cparent.(*Commit)
				if !ok {
					continue // Ignore callouts
				}
				parent.fileops = append(parent.fileops, commit.fileops...)
				// Also append child"s comment to its parent"s
				if policy.Contains("--empty-only") && !emptyComment(parent.Comment) {
					croak(fmt.Sprintf("--empty is on and %s comment is nonempty", parent.idMe()))
				}
				parent.Comment = composeComment(parent.Comment,
					commit.Comment)
				altered = append(altered, parent)
				// We need to ensure all fileop blobs
				// are defined before the
				// corresponding fileop, in other
				// words ensure that the blobs appear
				// before the primary parent in the
				// stream.  Easiest way to do this is
				// shift the range of events between
				// commit and parent down and put
				// parent just before commit.
				earliest := parent.index()
				latest := commit.index()
				for i := earliest; i < latest; i++ {
					repo.events[i] = repo.events[i+1]
				}
				repo.events[latest-1] = parent
				repo.declareSequenceMutation("squash pushback")
			}

			// Move tags && attachments
			if filterOnly {
				for _, e := range commit.attachments {
					e.setDelFlag(true)
				}
			} else {
				if !tagify && strings.Contains(commit.Branch, "/tags/") && newTarget.Branch != commit.Branch {
					// By deleting the commit, we would
					// lose the fact that it moves its
					// branch (to create a lightweight tag
					// for instance): replace it by a
					// Reset which will save this very
					// information. The following loop
					// will take care of moving the
					// attachment to the new target.
					reset := newReset(repo,
						commit.Branch, commit.mark)
					repo.events[ei] = reset
				}
				// use a copy of attachments since it
				// will be mutated
				attachmentsCopy := make([]Event, 0)
				for _, e := range commit.attachments {
					attachmentsCopy = append(attachmentsCopy, e)
				}
				for _, e := range attachmentsCopy {
					logit(logDELETE, "moving attachment %s of %s to %s", commit.mark, e.idMe(), newTarget.getMark())
					switch e.(type) {
					case *Tag:
						e.(*Tag).remember(repo, newTarget.getMark())
					case *Reset:
						e.(*Reset).remember(repo, newTarget.getMark())
					}
				}
			}
			// And forget the deleted event
			commit.forget()
		}
	}
	// Preserve assignments
	repo.filterAssignments(func(e Event) bool { return e.getDelFlag() })
	// Do the actual deletions
	var count int64
	for _, e := range repo.events {
		if !e.getDelFlag() {
			count++
		}
	}
	survivors := make([]Event, 0, count)
	for _, e := range repo.events {
		if !e.getDelFlag() {
			survivors = append(survivors, e)
		}
	}
	repo.events = survivors
	repo.declareSequenceMutation("")
	// Canonicalize all the commits that got ops pushed to them
	if !delete {
		for _, commit := range altered {
			if commit.getDelFlag() {
				continue
			}
			if logEnable(logDELETE) {
				logit(logDELETE, "Before canonicalization:")
				commit.fileopDump()
			}
			repo.caseCoverage = repo.caseCoverage.Union(commit.simplify())
			if logEnable(logDELETE) {
				logit(logDELETE, "After canonicalization:")
				commit.fileopDump()
			}
			// Now apply policy in the multiple-M case
			cliques := commit.cliques()
			if (!policy.Contains("--coalesce") && !delete) || logEnable(logDELETE) {
				for path, oplist := range cliques {
					if len(oplist) > 1 && !dquiet {
						logit(logWARN, "commit %s has multiple Ms for %s", commit.mark, path)
					}
				}
			}

			if policy.Contains("--coalesce") {
				// Only keep last M of each clique,
				// leaving other ops alone
				newOps := make([]FileOp, 0)
				for i, op := range commit.operations() {
					if op.op != opM {
						newOps = append(newOps, op)
						continue
					}
					myclique := cliques[op.Path]
					if i == myclique[len(myclique)-1] {
						newOps = append(newOps, op)
						continue
					}
				}
				commit.setOperations(newOps)
			}

			if logEnable(logDELETE) {
				logit(logDELETE, fmt.Sprintf("%s, after applying policy:", commit.idMe()))
				commit.fileopDump()
			}
		}
	}

	// Cleanup
	repo.gcBlobs()
	return nil
}

// Delete a set of events.
func (repo *Repository) delete(selected orderedIntSet, policy orderedStringSet) {
	options := append(orderedStringSet{"--delete", "--quiet"}, policy...)
	repo.squash(selected, options)
}

// Replace references to duplicate blobs according to the given dup_map,
// which maps marks of duplicate blobs to canonical marks`
func (repo *Repository) dedup(dupMap map[string]string) {
	walkEvents(repo.events, func(idx int, event Event) {
		commit, ok := event.(*Commit)
		if !ok {
			return
		}
		for _, fileop := range commit.operations() {
			if fileop.op == opM && dupMap[fileop.ref] != "" {
				fileop.ref = dupMap[fileop.ref]
			}
		}
	})
	repo.gcBlobs()
}

// Garbage-collect blobs that no longer have references.
func (repo *Repository) gcBlobs() {
	backreferences := make(map[string]bool)
	for _, commit := range repo.commits(nil) {
		for _, fileop := range commit.operations() {
			if fileop.op == opM {
				backreferences[fileop.ref] = true
			}
		}
	}
	eligible := func(event Event) bool {
		blob, ok := event.(*Blob)
		return ok && !backreferences[blob.mark]
	}
	repo.filterAssignments(eligible)
	// Apply the filter-without-allocate hack from Slice Tricks
	newEvents := repo.events[:0]
	for _, x := range repo.events {
		if !eligible(x) {
			newEvents = append(newEvents, x)
		}
	}
	repo.events = newEvents
	repo.declareSequenceMutation("GC")
}

//
// Delete machinery ends here
//

// Return options and features.  Makes a copy slice.
func (repo *Repository) frontEvents() []Event {
	var front = make([]Event, 0)
	for _, event := range repo.events {
		passthrough, ok := event.(*Passthrough)
		if !ok {
			break
		}
		front = append(front, passthrough)
	}
	return front
}

type DAGedges struct {
	eout orderedIntSet
	ein  orderedIntSet
}

func (d DAGedges) String() string {
	return fmt.Sprintf("<%v | %v>", d.ein, d.eout)
}

type DAG map[int]*DAGedges

func (d *DAG) setdefault(key int, e *DAGedges) *DAGedges {
	_, ok := (*d)[key]
	if !ok {
		(*d)[key] = e
	}
	return (*d)[key]
}

// From https://golang.org/pkg/container/heap/#example__intHeap

// An IntHeap is a min-heap of ints.
type IntHeap []int

func (h IntHeap) Len() int           { return len(h) }
func (h IntHeap) Less(i, j int) bool { return h[i] < h[j] }
func (h IntHeap) Swap(i, j int)      { h[i], h[j] = h[j], h[i] }

func (h *IntHeap) Push(x interface{}) {
	// Push and Pop use pointer receivers because they modify the slice's length,
	// not just its contents.
	*h = append(*h, x.(int))
}

func (h *IntHeap) Pop() interface{} {
	old := *h
	n := len(old)
	x := old[n-1]
	*h = old[0 : n-1]
	return x
}

// resort topologically sorts the events in this repository.
// It reorders self.events so that objects referenced by other objects
// appear first.  The sort is stable to avoid unnecessary churn.
func (repo *Repository) resort() {
	var dag DAG = make(map[int]*DAGedges)
	start := repo.all()

	// helper for constructing the dag
	handle := func(x int, ymark string) {
		//assert(ymark != nil)
		if ymark == "inline" {
			return
		}
		//assert(ymark[0] == ":")
		y := repo.markToIndex(ymark)
		//assert(y != nil)
		//assert(x != y)
		start.Remove(x)
		dag.setdefault(x, new(DAGedges)).eout.Add(y)
		dag.setdefault(y, new(DAGedges)).ein.Add(x)
	}

	// construct the DAG
	for n, node := range repo.events {
		edges := dag.setdefault(n, new(DAGedges))
		switch node.(type) {
		case *Commit:
			commit := node.(*Commit)
			for _, parent := range commit.parents() {
				p := repo.eventToIndex(parent)
				//assert(n != p)
				start.Remove(n)
				edges.eout.Add(p)
				dag.setdefault(p, new(DAGedges)).ein.Add(n)
			}
			for _, o := range commit.operations() {
				if o.op == opM {
					handle(n, o.ref)
				} else if o.op == opN {
					handle(n, o.ref)
					handle(n, o.committish)
				}
			}
		case *Blob:
			continue
		case *Tag:
			handle(n, node.(*Tag).committish)
		case *Reset:
			reset := node.(*Reset)
			if reset.committish != "" {
				t := repo.markToIndex(reset.committish)
				//assert(n != t)
				start.Remove(n)
				edges.eout.Add(t)
				dag.setdefault(t, new(DAGedges)).ein.Add(n)
			}
		case *Passthrough:
			continue
		default:
			panic("unexpected event type")

		}
	}
	// now topologically sort the dag, using a priority queue to
	// provide a stable topological sort (each event's priority is
	// its original index)
	s := new(IntHeap)
	heap.Init(s)
	for _, elt := range start {
		heap.Push(s, elt)
	}
	tsorted := newOrderedIntSet()
	oldIndexToNew := make(map[int]int)
	for len(*s) > 0 {
		n := heap.Pop(s).(int)
		//assert n not in old_index_to_new
		oldIndexToNew[n] = len(tsorted)
		tsorted.Add(n)
		ein := dag[n].ein
		for len(ein) > 0 {
			m := ein.Pop()
			medges := dag[m]
			medges.eout.Remove(n)
			if len(medges.eout) == 0 {
				heap.Push(s, m)
			}
		}
	}

	orig := repo.all()
	//assert len(t) == len(tsorted)
	if !tsorted.EqualWithOrdering(orig) {
		//fmt.Sprintf("Sort order: %v\n", tsorted)
		//assert len(t - o) == 0
		leftout := orig.Subtract(tsorted)
		if len(leftout) > 0 {
			croak("event re-sort failed due to one or more dependency cycles involving the following events: %v", leftout)
			return
		}
		newEvents := make([]Event, len(repo.events))
		for i, j := range tsorted {
			newEvents[i] = repo.events[j]
		}
		repo.events = newEvents
		respond("re-sorted events")
		// assignments will be fixed so don't pass anything to
		// declareSequenceMutation() to tell it to warn about
		// invalidated assignments
		repo.declareSequenceMutation("")
		for k, v := range repo.assignments {
			old := v
			repo.assignments[k] = make([]int, len(v))
			for i := range v {
				repo.assignments[k][i] = oldIndexToNew[old[i]]
			}
		}
	}
}

// Re-order a contiguous range of commits.
func (repo *Repository) reorderCommits(v []int, bequiet bool) {
	if len(v) <= 1 {
		return
	}
	events := make([]*Commit, len(v))
	for i, e := range v {
		commit, ok := repo.events[e].(*Commit)
		if ok {
			events[i] = commit
		}
	}
	sortedEvents := make([]*Commit, len(v))
	sort.Sort(sort.IntSlice(v))
	for i, e := range v {
		commit, ok := repo.events[e].(*Commit)
		if ok {
			sortedEvents[i] = commit
		}
	}
	commitSliceEqual := func(a, b []*Commit) bool {
		if len(a) != len(b) {
			return false
		}
		for i := range a {
			if a[i].String() != b[i].String() {
				return false
			}
		}
		return true
	}
	for _, e := range sortedEvents[1:] {
		if len(e.parents()) > 1 {
			croak("non-linear history detected, multiple parents at %s", e.idMe())
			return
		}
	}
	for _, e := range sortedEvents[:len(sortedEvents)-1] {
		if len(e.children()) > 1 {
			croak("non-linear history detected, multiple children at %s", e.idMe())
			return
		}
	}
	isChildOf := func(later, earlier *Commit) bool {
		for _, c := range later.parents() {
			if c.getMark() == earlier.getMark() {
				return true
			}
		}
		return false
	}
	for i := 0; i < len(sortedEvents)-1; i++ {
		if !isChildOf(sortedEvents[i+1], sortedEvents[i]) {
			croak("selected commit range not contiguous")
			return
		}
	}
	if commitSliceEqual(events, sortedEvents) {
		croak("commits already in desired order")
		return
	}
	lastEvent := sortedEvents[len(sortedEvents)-1]
	events[0].setParents(sortedEvents[0].parents())
	for _, e := range lastEvent.children() {
		e.(*Commit).replaceParent(lastEvent, events[len(events)-1])
	}
	for i, e := range events[:len(events)-1] {
		events[i+1].setParents([]CommitLike{e})
	}
	fileopSliceEqual := func(a, b []FileOp) bool {
		if len(a) != len(b) {
			return false
		}
		for i := range a {
			if a[i].String() != b[i].String() {
				return false
			}
		}
		return true
	}
	// Check if fileops still make sense after re-ordering events.
	// FIXME: The Python used to check child events too.
	for _, c := range events {
		ops := make([]FileOp, 0)
		for _, op := range c.operations() {
			var path string
			if op.op == opD {
				path = op.Path
			} else if op.op == opR || op.op == opC {
				path = op.Source
			}
			if path != "" && c.visible(path) == nil {
				if !bequiet {
					croak("%s '%c' fileop references non-existent '%s' after re-order", c.idMe(), op.op, path)
				}
				continue
			}
			ops = append(ops, op)
		}
		if !fileopSliceEqual(ops, c.operations()) {
			c.setOperations(ops)
			if !bequiet && len(ops) == 0 {
				logit(logWARN, "%s no fileops remain after re-order", c.idMe())
			}
		}
	}
	repo.resort()
}

// Renumber the marks in a repo starting from a specified origin.
func (repo *Repository) renumber(origin int, baton *Baton) {
	markmap := make(map[string]int)
	remark := func(m string, id string) string {
		_, ok := markmap[m]
		if ok {
			return fmt.Sprintf(":%d", markmap[m])
		}
		panic(fmt.Sprintf("unknown mark %s in %s cannot be renumbered!", m, id))
	}
	repo.markseq = 0
	for _, event := range repo.events {
		switch event.(type) {
		case *Blob:
			blob := event.(*Blob)
			if blob.mark == "" {
				continue
			} else if !strings.HasPrefix(blob.mark, ":") {
				panic("field not in mark format")
			} else {
				markmap[blob.mark] = origin + repo.markseq
				repo.markseq++
			}
		case *Commit:
			commit := event.(*Commit)
			if commit.mark == "" {
				continue
			} else if !strings.HasPrefix(commit.mark, ":") {
				panic("field not in mark format")
			} else {
				markmap[commit.mark] = origin + repo.markseq
				repo.markseq++
			}
		}
	}
	var old string
	var newmark string
	for _, event := range repo.events {
		switch event.(type) {
		case *Blob:
			blob := event.(*Blob)
			old = blob.mark
			if old != "" {
				newmark := remark(old, event.idMe())
				logit(logUNITE, "renumbering %s -> %s in blob mark", old, newmark)
				blob.mark = newmark
			}
		case *Commit:
			commit := event.(*Commit)
			old = commit.mark
			if old != "" {
				newmark := remark(old, event.idMe())
				logit(logUNITE, "renumbering %s -> %s in commit mark", old, newmark)
				commit.mark = newmark
			}
		case *Tag:
			tag := event.(*Tag)
			old = tag.committish
			if old != "" {
				newmark := remark(old, event.idMe())
				logit(logUNITE, "renumbering %s -> %s in tag committish", old, newmark)
				tag.committish = newmark
			}
		case *Reset:
			reset := event.(*Reset)
			old = reset.committish
			if old != "" {
				newmark := remark(old, event.idMe())
				logit(logUNITE, "renumbering %s -> %s in reset committish", old, newmark)
				reset.committish = newmark
			}
		}
	}
	if baton != nil {
		count := len(repo.commits(nil))
		baton.startcounter("renumbering %d of "+fmt.Sprintf("%d", count)+" commits", 0)
	}
	for _, commit := range repo.commits(nil) {
		for i, fileop := range commit.operations() {
			if fileop.op == opM && strings.HasPrefix(fileop.ref, ":") {
				newmark = remark(fileop.ref, "fileop")
				logit(logUNITE, fmt.Sprintf("renumbering %s -> %s in fileop", fileop.ref, newmark))
				commit.fileops[i].ref = newmark
			}
		}
		if baton != nil {
			baton.bumpcounter()
		}
	}
	// Prevent result from having multiple 'done' trailers.
	origLen := len(repo.events)
	var newEvents = make([]Event, 0)
	for _, event := range repo.events {
		passthrough, ok := event.(*Passthrough)
		if ok && passthrough.text == "done\n" {
			continue
		}
		newEvents = append(newEvents, event)
	}
	if len(repo.events) != origLen {
		repo.events = append(repo.events, newPassthrough(repo, "done\n"))
		repo.declareSequenceMutation("")
	}
	// Previous maps won't be valid
	repo.invalidateObjectMap()
	repo._markToIndex = nil
	if baton != nil {
		baton.endcounter()
	}
}

// Disambiguate branches, tags, and marks using the specified label.
func (repo *Repository) uniquify(color string, persist map[string]string) map[string]string {
	makename := func(oldname string, obj string, fld string, reverse bool) string {
		newname := ""
		if persist == nil {
			// we're not trying to preserve names
			if reverse {
				newname = color + "-" + oldname
			} else {
				newname = oldname + "-" + color
			}
		} else if _, ok := persist[oldname]; !ok {
			// record name as belonging to this repo
			persist[oldname] = color
			return oldname
		} else if persist[oldname] == color {
			// name belongs here, do nothing
			return oldname
		} else {
			// collision - oldname belongs to a different repo
			if reverse {
				newname = color + "-" + oldname
			} else {
				newname = oldname + "-" + color
			}
		}
		if newname != "" {
			logit(logUNITE, "moving %s -> %s in %s.%s", oldname, newname, obj, fld)
			if persist != nil {
				persist[newname] = color
			}
			return newname
		}
		return oldname
	}
	makemark := func(oldname string, obj string, fld string) string {
		if oldname == "" {
			return ""
		}
		if !strings.HasPrefix(oldname, ":") {
			panic("field not in mark format")
		}
		newname := oldname + "-" + color
		logit(logUNITE, "moving %s -> %s in %s.%s",
			oldname, newname, obj, fld)
		return newname
	}
	for _, event := range repo.events {
		switch event.(type) {
		case *Blob:
			blob := event.(*Blob)
			blob.setMark(makemark(blob.mark, "blob", "mark"))
		case *Commit:
			commit := event.(*Commit)
			commit.Branch = makename(commit.Branch,
				"commit", "branch", false)
			commit.setMark(makemark(commit.mark, "commit", "mark"))
			for i, fileop := range commit.fileops {
				if fileop.op == opM && strings.HasPrefix(fileop.ref, ":") {
					newname := fileop.ref + "-" + color
					logit(logUNITE,
						"moving %s -> %s in fileop",
						fileop.ref, newname)
					commit.fileops[i].ref = newname
				}
			}
		case *Reset:
			reset := event.(*Reset)
			reset.ref = makename(reset.ref, "reset", "ref", false)
			reset.committish = makemark(reset.committish, "tag", "committish")
		case *Tag:
			tag := event.(*Tag)
			tag.name = makename(tag.name, "tag", "name", true)
			tag.committish = makemark(tag.committish, "tag", "committish")
		}
	}
	repo.invalidateObjectMap()
	return persist
}

// Absorb all events from the repository OTHER into SELF.
// Only vcstype, sourcedir, and basedir are not copied here
// Marks and tag/branch names must have been uniquified first,
// otherwise name collisions could occur in the merged repo.
func (repo *Repository) absorb(other *Repository) {
	repo.preserveSet = repo.preserveSet.Union(other.preserveSet)
	repo.caseCoverage = repo.caseCoverage.Union(other.caseCoverage)
	// Strip feature events off the front, they have to stay in front.
	front := len(repo.frontEvents())
	for {
		passthrough, ok := other.events[0].(*Passthrough)
		if ok {
			repo.insertEvent(passthrough, front, "moving passthroughs")
			front++
			// FIXME: Leaks an array slot. See
			// https://github.com/golang/go/wiki/SliceTricks
			// for a better way.
			other.events[0] = nil // Prevent memory leak
			other.events = other.events[1:]
		} else {
			break
		}
	}
	// Merge in the non-feature events and blobs
	for _, event := range other.events {
		event.moveto(repo)
	}
	repo.events = append(repo.events, other.events...)
	repo.declareSequenceMutation("absorb")
	other.events = nil
	other.cleanup()
}

const invalidGraftIndex = -1

// Graft a repo on to this one at a specified point.
func (repo *Repository) graft(graftRepo *Repository, graftPoint int, options stringSet) error {
	var persist map[string]string
	var anchor *Commit
	var ok bool
	if graftPoint == invalidGraftIndex {
		persist = make(map[string]string)
	} else {
		persist = nil
		where := repo.events[graftPoint]
		anchor, ok = where.(*Commit)
		if !ok {
			return fmt.Errorf("%s in %s is not a commit",
				where.idMe(), repo.name)
		}
	}
	// Errors aren't recoverable after this
	graftRepo.uniquify(graftRepo.name, persist)
	var graftroot *Commit
	if graftPoint != invalidGraftIndex {
		graftroot = graftRepo.earliestCommit()
	}
	repo.absorb(graftRepo)
	if graftPoint != invalidGraftIndex {
		graftroot.addParentByMark(anchor.mark)

	}
	if options.Contains("--prune") {
		// Prepend a deleteall. Roots have nothing upline to preserve.
		delop := newFileOp(repo)
		delop.construct(deleteall)
		graftroot.prependOperation(*delop)
	}
	repo.renumber(1, nil)
	// Resolve all callouts
	unresolved := make([]string, 0)
	for _, commit := range repo.commits(nil) {
		for idx, parent := range commit.parents() {
			parentMark := parent.getMark()
			if isCallout(parentMark) {
				attach := repo.named(parentMark)
				if len(attach) == 1 {
					commit.removeParent(parent)
					newparent := repo.events[attach[0]]
					commit.insertParent(idx, newparent.getMark())
				} else {
					unresolved = append(unresolved, parentMark)
				}
			}
		}
	}
	if len(unresolved) > 0 {
		return fmt.Errorf("unresolved callouts: %v", unresolved)
	}
	return nil
}

// Apply a hook to all paths, returning the set of modified paths.
func (repo *Repository) pathWalk(selection orderedIntSet, hook func(string) string) orderedStringSet {
	if hook == nil {
		hook = func(s string) string { return s }
	}
	modified := newOrderedStringSet()
	for _, ei := range selection {
		event := repo.events[ei]
		if commit, ok := event.(*Commit); ok {
			for i, fileop := range commit.operations() {
				if fileop.op == opM || fileop.op == opD {
					newpath := hook(fileop.Path)
					if newpath != fileop.Path {
						modified.Add(newpath)
					}
					commit.fileops[i].Path = newpath
				} else if fileop.op == opR || fileop.op == opC {
					newpath := hook(fileop.Source)
					if newpath != fileop.Source {
						modified.Add(newpath)
					}
					fileop.Source = newpath
					newpath = hook(fileop.Target)
					if newpath != fileop.Target {
						modified.Add(newpath)
					}
					commit.fileops[i].Target = newpath
				}
			}
		}
	}
	sort.Strings(modified)
	return modified
}

func (repo *Repository) splitCommit(where int, splitfunc func([]FileOp) ([]FileOp, []FileOp, error)) error {
	event := repo.events[where]
	// Fileop split happens here
	commit, ok := event.(*Commit)
	if !ok {
		return fmt.Errorf("split location %s is not a commit", event.idMe())
	}
	fileops, fileops2, err := splitfunc(commit.operations())
	if err != nil {
		return err
	}
	if len(fileops) == 0 || len(fileops2) == 0 {
		return errors.New("no-op commit split, repo unchanged")
	}
	repo.insertEvent(commit.clone(repo), where+1, "commit split")
	repo.declareSequenceMutation("commit split")
	commit2 := repo.events[where+1].(*Commit)
	// need a new mark
	//assert(commit.mark == commit2.mark)
	commit2.setMark(commit.repo.newmark())
	repo.invalidateObjectMap()
	// Fix up parent/child relationships
	for _, child := range commit.children() {
		child.(*Commit).replaceParent(commit, commit2)
	}
	commit2.setParents([]CommitLike{commit})
	// and then finalize the ops
	commit2.setOperations(fileops2)
	commit.setOperations(fileops)
	// Avoid duplicates in the legacy-ID map
	if commit2.legacyID != "" {
		commit2.legacyID += ".split"
	}
	return nil
}

func (repo *Repository) splitCommitByIndex(where int, splitpoint int) error {
	// FIXME: validity-check the split index
	return repo.splitCommit(where,
		func(ops []FileOp) ([]FileOp, []FileOp, error) {
			return ops[:splitpoint], ops[splitpoint:], nil
		})
}

func (repo *Repository) splitCommitByPrefix(where int, prefix string) error {
	return repo.splitCommit(where,
		func(ops []FileOp) ([]FileOp, []FileOp, error) {
			var without []FileOp
			var with []FileOp
			err := fmt.Errorf("couldn't find '%s' in a fileop path", prefix)
			for _, op := range ops {
				// In Python: lambda ops: ([op for op
				// in ops if
				// !strings.HasPrefix(op.Path,
				// prefix)],
				// [op for op in ops if (op.Path || op.Target)
				// and (op.Path || op.Target).startswith(prefix)]))
				if strings.HasPrefix(op.Path, prefix) {
					with = append(with, op)
					err = nil
				} else if strings.HasPrefix(op.Target, prefix) {
					with = append(with, op)
				} else {
					without = append(without, op)
				}
			}

			return without, with, err
		})
}

// Return blob for the nearest ancestor to COMMIT of the specified PATH.
func (repo *Repository) blobAncestor(commit *Commit, path string) *Blob {
	var ok bool
	ancestor := commit
	for {
		back := ancestor.parents()
		if len(back) == 0 {
			break
		}
		trial := back[0]
		if ancestor, ok = trial.(*Commit); !ok {
			break // could be a callout
		}
		for _, op := range ancestor.operations() {
			if op.Path == path {
				if op.op == opD {
					// Path had no ancestor after
					// last delete
					return nil
				} else if op.op == opR || op.op == opC {
					path = op.Source
				} else if op.op == opM {
					// Buglet: if this path has
					// multiple ops, we'd probably
					// prefer the last to the
					// first.
					return repo.markToEvent(op.ref).(*Blob)
				}
			}
		}
	}
	return nil
}

func (repo *Repository) dumptimes(w io.Writer) {
	total := repo.timings[len(repo.timings)-1].stamp.Sub(repo.timings[0].stamp)
	commitCount := len(repo.commits(nil))
	if repo.legacyCount <= 0 {
		fmt.Fprintf(w, "        commits:\t%d\n", commitCount)
	} else {
		fmt.Fprintf(w, "        commits:\t%d\t(from %d)\n", commitCount, repo.legacyCount)
	}
	totalf := float64(total)
	for i := range repo.timings {
		if i > 0 {
			interval := repo.timings[i].stamp.Sub(repo.timings[i-1].stamp)
			phase := repo.timings[i].label
			intervalf := float64(interval)
			fmt.Fprintf(w, "%15s:\t%2.2f%%\t%v\n",
				phase, (intervalf*100)/totalf, interval)
		}
	}
	fmt.Fprintf(w, "          total:\t%d/sec\t%v\n",
		int(float64(time.Duration(commitCount)*time.Second)/float64(total)),
		total)
}

// Read a repository using fast-import.
func readRepo(source string, options stringSet, preferred *VCS, extractor Extractor, quiet bool) (*Repository, error) {
	if logEnable(logSHUFFLE) {
		legend := "nil"
		if extractor != nil {
			legend = "non-nil"
		}
		if preferred != nil {
			respond("looking for a %s repo st %s (extractor %s...", preferred.name, source, legend)
		} else {
			respond("reposurgeon: looking for any repo at %s (extractor %s)...", source, legend)
		}
	}
	// Trickier-than-it-looks department:
	// There are three cases here.
	// 1. extractor and preferred both non-nil.  Use the extractor if there's a matching repo here.
	// 2. preferred is non-nil.  Use that type if there's a matching repo here.
	// 3. extractor and preferred both nil. Look for anything we can read.
	baseMatch := func(vcs *VCS) bool {
		subdir := source + "/" + vcs.subdirectory
		subdir = filepath.FromSlash(subdir)
		return exists(subdir) && isdir(subdir)
	}

	var vcs *VCS
	if extractor != nil || preferred != nil {
		if baseMatch(preferred) {
			vcs = preferred // if extractor is non-null it gets picked up below
		} else {
			return nil, fmt.Errorf("couldn't find a repo of desiret type %s under %s", preferred.name, abspath(source))
		}
	} else {
		hitcount := 0
		for i, possible := range vcstypes {
			if baseMatch(&possible) {
				vcs = &vcstypes[i]
				hitcount++
			}
		}
		if hitcount == 0 {
			return nil, fmt.Errorf("couldn't find a repo under %s", abspath(source))
		} else if hitcount > 1 {
			return nil, fmt.Errorf("too many repos (%d) under %s", hitcount, abspath(source))
		}
		// There's only one base match, and vcs is set.  Forward to a matching extractor if need be
		if vcs.exporter == "" {
			for _, possible := range importers {
				if baseMatch(possible.basevcs) {
					extractor = possible.engine
				}
			}
			if extractor == nil {
				return nil, fmt.Errorf("couldn't find an exporter matching %s under %s", vcs.name, abspath(source))
			}
		}
	}
	if logEnable(logSHUFFLE) {
		legend := "base"
		if extractor != nil {
			legend = "extractor"
		}
		logit(logSHUFFLE, "found %s repository (%s)", vcs.name, legend)
	}
	repo := newRepository("")
	repo.sourcedir = source
	here, err := os.Getwd()
	if err != nil {
		return nil, fmt.Errorf("readRepo is disoriented: %v", err)
	}
	logit(logSHUFFLE, "current directory is %q", here)
	chdir := func(directory string, legend string) {
		os.Chdir(directory)
		logit(logSHUFFLE, "changing directory to %s: %s", legend, directory)
	}
	defer chdir(here, "original")
	chdir(repo.sourcedir, "repository directory")
	// We found a matching custom extractor
	if extractor != nil {
		repo.stronghint = true
		streamer := newRepoStreamer(extractor)
		repo, err := streamer.extract(repo, vcs)
		return repo, err
	}
	// We found a matching VCS type
	if vcs != nil {
		repo.hint("", vcs.name, true)
		repo.preserveSet = vcs.preserve
		suppressBaton := control.flagOptions["progress"] && repo.exportStyle().Contains("export-progress")
		commandControl := map[string]string{"basename": filepath.Base(repo.sourcedir)}
		mapper := func(sub string) string {
			for k, v := range commandControl {
				from := "${" + k + "}"
				sub = strings.Replace(sub, from, v, -1)
			}
			return sub
		}
		if strings.Contains(repo.vcs.exporter, "${tempfile}") {
			tfdesc, err := ioutil.TempFile("", "rst")
			if err != nil {
				return nil, err
			}
			defer tfdesc.Close()
			defer os.Remove(tfdesc.Name())
			commandControl["tempfile"] = tfdesc.Name()
			cmd := os.Expand(repo.vcs.exporter, mapper)
			runProcess(cmd, "repository export")
			tfdesc.Close()
			tp, err := os.Open(tfdesc.Name())
			if err != nil {
				return nil, err
			}
			repo.fastImport(context.TODO(), tp, options, source)
			tp.Close()
		} else {
			cmd := os.Expand(repo.vcs.exporter, mapper)
			tp, _, err := readFromProcess(cmd)
			if err != nil {
				return nil, err
			}
			repo.fastImport(context.TODO(), tp, options, source)
			tp.Close()
		}
		if suppressBaton {
			control.flagOptions["progress"] = true
		}
		if repo.vcs.authormap != "" && exists(repo.vcs.authormap) {
			logit(logSHOUT, "reading author map.")
			fp, err := os.Open(repo.vcs.authormap)
			if err != nil {
				return nil, err
			}
			repo.readAuthorMap(repo.all(), fp)
			fp.Close()
		}
		legacyMap := vcs.subdirectory + "/legacy_map"
		legacyMap = filepath.FromSlash(legacyMap)
		if exists(legacyMap) {
			rfp, err := os.Open(legacyMap)
			if err != nil {
				return nil, err
			}
			repo.readLegacyMap(rfp)
			rfp.Close()
		}
		if vcs.lister != "" {
			registered := newOrderedStringSet()
			stdout, cmd, err := readFromProcess(vcs.lister)
			if err != nil {
				return nil, err
			}
			// Get the names of all files under version control
			r := bufio.NewReader(stdout)
			for {
				line, err2 := r.ReadString(byte('\n'))
				if err2 == io.EOF {
					if cmd != nil {
						cmd.Wait()
					}
					break
				} else if err2 != nil {
					return nil, fmt.Errorf("while collecting file manifestL %v", err2)
				}
				registered = append(registered, strings.TrimSpace(line))
			}
			stdout.Close()
			// Get the names of all files except those in the
			// repository metadata directory and reposurgeon
			// scratch directories
			var allfiles = newOrderedStringSet()
			err = filepath.Walk(".", func(path string, info os.FileInfo, err error) error {
				if err != nil {
					croak("path access failure %q: %v", path, err)
					return err
				}
				if info.IsDir() && (info.Name() == vcs.subdirectory || strings.HasPrefix(info.Name(), ".rs")) {
					return filepath.SkipDir
				}
				allfiles = append(allfiles, path)
				return nil
			})
			// Compute the things to preserve
			repo.preserveSet = repo.preserveSet.Union(allfiles.Subtract(registered))
		}
		// kluge: git-specific hook
		if repo.vcs.name == "git" {
			if exists(".git/cvs-revisions") {
				logit(logSHOUT, "reading cvs-revisions map.")
				type pathRev struct {
					path string
					rev  string
				}
				pathRevToHash := make(map[pathRev]string)
				// Pass 1: Get git's path/revision to
				// hash mapping
				fp, err := os.Open(".git/cvs-revisions")
				if err != nil {
					return nil, err
				}
				defer fp.Close()
				r := bufio.NewReader(fp)
				for {
					line, err1 := r.ReadString(byte('\n'))
					if err1 == io.EOF {
						break
					} else if err1 != nil {
						return nil, fmt.Errorf("reading cvs-revisions map: %v", err1)
					}

					fields := strings.Fields(line)
					pathrev := pathRev{fields[0], fields[1]}
					hashv := fields[2]
					pathRevToHash[pathrev] = hashv
				}
				// Pass 2: get git's hash to
				// (time,person) mapping
				hashToAction := make(map[string]string)
				stampSet := make(map[string]bool)
				fp2, _, err2 := readFromProcess("git log --all --format='%H %ct %ce'")
				if err2 != nil {
					return nil, err2
				}
				r2 := bufio.NewReader(fp2)
				for {
					line, err2 := r2.ReadString(byte('\n'))
					if err2 == io.EOF {
						break
					} else if err2 != nil {
						return nil, fmt.Errorf("reading cvs-revisions map: %v", err2)
					}

					fields := strings.Fields(line)
					hashv := fields[0]
					ctime := fields[1]
					cperson := fields[2]
					inttime, err3 := strconv.Atoi(ctime)
					if err3 != nil {
						return nil, fmt.Errorf("while reang git hash mapping: %v", err3)
					}
					stamp := rfc3339(time.Unix(int64(inttime), 0))
					stamp += "!" + cperson
					if stampSet[stamp] {
						croak("more than one commit matches %s (%s)",
							stamp, hashv)

						delete(hashToAction, hashv)
					} else {
						hashToAction[hashv] = stamp
						stampSet[stamp] = true
					}
				}
				// Pass 3: build a time+person
				// to commit mapping.
				actionToCommit := make(map[string]*Commit)
				for _, commit := range repo.commits(nil) {
					actionToCommit[commit.committer.actionStamp()] = commit
				}
				// Pass 4: use it to set commit properties
				for pathrev, value := range pathRevToHash {
					if stamp, ok := hashToAction[value]; ok {
						actionToCommit[stamp].legacyID = fmt.Sprintf("CVS:%s:%s", pathrev.path, pathrev.rev)
					}
				}
			}
		}
	}
	return repo, nil
}

// Rebuild a repository from the captured state.
func (repo *Repository) rebuildRepo(target string, options stringSet,
	preferred *VCS) error {
	if target == "" && repo.sourcedir != "" {
		target = repo.sourcedir
	}
	if target != "" {
		var err error
		target, err = filepath.Abs(target)
		if err != nil {
			return fmt.Errorf("while computing target: %v", err)
		}
	} else {
		return errors.New("no default destination for rebuild")
	}
	vcs := preferred
	if vcs == nil {
		vcs = repo.vcs
	}
	if vcs == nil {
		return errors.New("please prefer a repo type first")
	}
	if vcs.importer == "" {
		return fmt.Errorf("%s repositories supported for read only",
			vcs.name)

	}
	if preferred.name == "git" && !repo.branchset().Contains("refs/heads/master") {
		return fmt.Errorf("%s has no master branch and thus will not rebuild properly", repo.name)
	}
	chdir := func(directory string, legend string) {
		os.Chdir(directory)
		logit(logSHUFFLE, "changing directory to %s: %s", legend, directory)
	}
	// Create a new empty directory to do the rebuild in
	var staging string
	if !exists(target) {
		staging = target
		err := os.Mkdir(target, userReadWriteSearchMode)
		if err != nil {
			return fmt.Errorf("target directory creation failed: %v", err)
		}
	} else {
		staging = fmt.Sprintf("%s-stage%d", target, os.Getpid())
		if !filepath.IsAbs(target) || !filepath.IsAbs(staging) {
			return fmt.Errorf("internal error: target (%s) and staging paths (%s) should be absolute", target, staging)
		}
		err := os.Mkdir(staging, userReadWriteSearchMode)
		if err != nil {
			return fmt.Errorf("staging directory creation failed: %v", err)
		}
	}
	// Try the rebuild in the empty staging directory
	here, err2 := os.Getwd()
	if err2 != nil {
		return fmt.Errorf("buildRepo is disoriented: %v", err2)
	}
	chdir(staging, "staging")
	defer func() {
		chdir(here, "original")
		if staging != target {
			nuke(staging, "reposurgeon: removing staging directory")
		}
	}()

	if vcs.initializer != "" {
		runProcess(vcs.initializer, "repository initialization")
	}
	params := map[string]string{"basename": filepath.Base(target)}
	mapper := func(sub string) string {
		for k, v := range params {
			from := "${" + k + "}"
			sub = strings.Replace(sub, from, v, -1)
		}
		return sub
	}
	if strings.Contains(vcs.importer, "${tempfile}") {
		tfdesc, err := ioutil.TempFile("", "rst")
		if err != nil {
			return err
		}
		// Ship to the tempfile
		repo.fastExport(repo.all(), tfdesc, options, preferred)
		tfdesc.Close()
		// Pick up the tempfile
		params["tempfile"] = tfdesc.Name()
		cmd := os.Expand(repo.vcs.importer, mapper)
		runProcess(cmd, "repository import")
		os.Remove(tfdesc.Name())
	} else {
		cmd := os.Expand(vcs.importer, mapper)
		tp, cls, err := writeToProcess(cmd)
		if err != nil {
			return err
		}
		repo.fastExport(repo.all(), tp, options, preferred)
		tp.Close()
		cls.Wait()
	}
	if repo.writeLegacy {
		legacyfile := filepath.FromSlash(vcs.subdirectory + "/legacy-map")
		wfp, err := os.OpenFile(legacyfile,
			os.O_WRONLY|os.O_CREATE|os.O_TRUNC, userReadWriteMode)
		if err != nil {
			return fmt.Errorf("legacy-map file %s could not be written: %v",
				legacyfile, err)
		}
		defer wfp.Close()
		err = repo.writeLegacyMap(wfp)
		if err != nil {
			return err
		}
	}
	if vcs.checkout != "" {
		runProcess(vcs.checkout, "repository checkout")
	} else {
		croak("checkout not supported for %s skipping", vcs.name)

	}
	respond("rebuild is complete.")
	ljoin := func(sup string, sub string) string {
		return filepath.FromSlash(sup + "/" + sub)
	}
	chdir(here, "original")
	var savedir string
	if staging == target {
		// For preservation purposes
		savedir = here
	} else {
		// Rebuild succeeded - make an empty backup directory
		backupcount := 1
		for {
			savedir = target + (fmt.Sprintf(".~%d~", backupcount))
			if exists(savedir) {
				backupcount++
			} else {
				break
			}
		}
		if !filepath.IsAbs(savedir) {
			return fmt.Errorf("internal error, savedir %q should be absolute", savedir)
		}
		os.Mkdir(savedir, userReadWriteSearchMode)

		// This is a critical region.  Ignore all signals
		// until we're done.
		//
		// Move the unmodified repo contents in target to the
		// backup directory, leaving a copy of the VCS config
		// in place.  Then move the staging contents
		// (*excluding* the VCS config) to the target
		// directory.  Finally, restore designated files from
		// backup to target.
		entries, err := ioutil.ReadDir(target)
		if err != nil {
			return err
		}
		logit(logSHUFFLE, "Target %s to backup%s", target, savedir)
		for _, sub := range entries {
			src := ljoin(target, sub.Name())
			dst := ljoin(savedir, sub.Name())
			logit(logSHUFFLE, "%s -> %s", src, dst)
			if sub.Name() == vcs.subdirectory {
				shutil.CopyTree(src, dst, nil)
			} else {
				os.Rename(src, dst)
			}
		}
		respond("repo backed up to %s.", relpath(savedir))
		entries, err = ioutil.ReadDir(staging)
		if err != nil {
			return err
		}
		logit(logSHUFFLE, "Copy staging %s to target %s (excluding %s)", staging, target, vcs.subdirectory)
		for _, sub := range entries {
			if sub.Name() == vcs.subdirectory {
				continue
			}
			logit(logSHUFFLE, "%s -> %s",
				ljoin(staging, sub.Name()),
				ljoin(target, sub.Name()))
			os.Rename(ljoin(staging, sub.Name()),
				ljoin(target, sub.Name()))
		}
		respond("modified repo moved to %s.", target)
		// Critical region ends
	}
	// This is how we clear away hooks directories in
	// newly-created repos
	logit(logSHUFFLE, "Nuking %v from staging %s", vcs.prenuke, staging)
	if vcs.prenuke != nil {
		for _, path := range vcs.prenuke {
			os.RemoveAll(ljoin(staging, path))
		}
	}
	if len(repo.preserveSet) > 0 {
		preserveMe := repo.preserveSet
		if repo.vcs.authormap != "" {
			preserveMe = append(preserveMe, repo.vcs.authormap)
		}
		logit(logSHUFFLE, "Copy preservation set %v from backup %s to target %s", preserveMe, savedir, target)
		for _, sub := range repo.preserveSet {
			src := ljoin(savedir, sub)
			dst := ljoin(target, sub)
			// Beware of adding a target-noxesistence check here,
			// if you do that the VCS config won't get copied because
			// the newly-created one will block it.
			if exists(src) {
				dstdir := filepath.Dir(dst)
				if !exists(dstdir) {
					os.MkdirAll(dstdir, userReadWriteSearchMode)
				}
				if isdir(src) {
					shutil.CopyTree(src, dst, nil)
				} else {
					shutil.Copy(src, dst, false)
				}
			}
		}
		respond("preserved files restored.")
	} else {
		respond("no preservations.")
	}
	return nil
}

// Either execute a command or raise a fatal exception.
func runProcess(dcmd string, legend string) error {
	if legend != "" {
		legend = " " + legend
	}
	logit(logCOMMANDS, "executing '%s'%s", dcmd, legend)
	words, err := shlex.Split(dcmd, true)
	if err != nil {
		return fmt.Errorf("preparing %q for execution: %v", dcmd, err)
	}
	cmd := exec.Command(words[0], words[1:]...)
	cmd.Stdin = os.Stdin
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	err = cmd.Run()
	if err != nil {
		return fmt.Errorf("executing %q: %v", dcmd, err)
	}
	return nil
}

func readFromProcess(command string) (io.ReadCloser, *exec.Cmd, error) {
	cmd := exec.Command("sh", "-c", command+" 2>&1")
	cmd.Stdin = os.Stdin
	cmd.Stderr = os.Stderr
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return nil, nil, err
	}
	if logEnable(logCOMMANDS) {
		croak("%s: reading from '%s'\n",
			rfc3339(time.Now()), command)
	}
	err = cmd.Start()
	if err != nil {
		return nil, nil, err
	}
	// Pass back cmd so we can call Wait on it and get the error status.
	return stdout, cmd, err
}

func writeToProcess(command string) (io.WriteCloser, *exec.Cmd, error) {
	cmd := exec.Command("sh", "-c", command+" 2>&1")
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	stdout, err := cmd.StdinPipe()
	if err != nil {
		return nil, nil, err
	}
	if logEnable(logCOMMANDS) {
		croak("%s: writing to '%s'\n",
			rfc3339(time.Now()), command)
	}
	err = cmd.Start()
	if err != nil {
		return nil, nil, err
	}
	// Pass back cmd so we can call Wait on it and get the error status.
	return stdout, cmd, err
}

// A RepositoryList is a repository list with selection and access by name.
type RepositoryList struct {
	repo     *Repository
	repolist []*Repository
	cutIndex int
}

func (rl *RepositoryList) chosen() *Repository {
	return rl.repo
}

func (rl *RepositoryList) choose(repo *Repository) {
	rl.repo = repo
}

func (rl *RepositoryList) unchoose() {
	rl.repo = nil
}

// Unstreamify any repo about to be stepped on by a stream output.
func (rl *RepositoryList) writeNotify(filename string) {
	for _, repo := range rl.repolist {
		if repo.name == filename || strings.Contains(filename, repo.name+".") {
			for _, event := range repo.events {
				if blob, ok := event.(*Blob); ok {
					blob.materialize()
				}
			}
		}
	}
}

// Return a list of the names of all repositories.
func (rl *RepositoryList) reponames() orderedStringSet {
	var lst = make([]string, len(rl.repolist))
	for i, repo := range rl.repolist {
		lst[i] = repo.name
	}
	return lst
}

// Uniquify a repo name in the repo list.
func (rl *RepositoryList) uniquify(name string) string {
	if strings.HasSuffix(name, ".fi") {
		name = name[:len(name)-3]
	} else if strings.HasSuffix(name, ".svn") {
		name = name[:len(name)-4]
	}
	// repo "foo" is #1
	for seq := 1; ; seq++ {
		var trial string
		if seq == 1 {
			trial = name
		} else {
			trial = name + fmt.Sprintf("%d", seq)
		}
		collision := false
		for _, repo := range rl.repolist {
			if repo.name == trial {
				collision = true
			}
		}
		if !collision {
			return trial
		}
	}
}

// Retrieve a repo by name.
func (rl *RepositoryList) repoByName(name string) *Repository {
	for _, repo := range rl.repolist {
		if repo.name == name {
			return repo
		}
	}
	panic(throw("command", "no repository named %s is loaded.", name))
}

// Remove a repo by name.
func (rl *RepositoryList) removeByName(name string) {
	if rl.repo != nil && rl.repo.name == name {
		rl.unchoose()
	}
	newList := make([]*Repository, 0)
	for _, repo := range rl.repolist {
		if repo.name != name {
			newList = append(newList, repo)
		}
	}
	rl.repolist = newList
}

// Apply a graph-coloring algorithm to see if the repo can be split here.
func (rl *RepositoryList) cutConflict(early *Commit, late *Commit) (bool, int, error) {
	cutIndex := -1
	for i, m := range late.parentMarks() {
		if m == early.mark {
			cutIndex = i
			break
		}
	}
	if cutIndex == -1 {
		err := fmt.Errorf("commit %s is not a parent of commit %s", early.mark, late.mark)
		return false, -1, err
	}
	late.removeParent(early)
	doColor := func(commitlike CommitLike, color colorType) {
		commitlike.setColor(color)
		if commit, ok := commitlike.(*Commit); ok {
			for _, fileop := range commit.operations() {
				if fileop.op == opM && fileop.ref != "inline" {
					blob := rl.repo.markToEvent(fileop.ref)
					//assert isinstance(repo.repo[blob], Blob)
					blob.(*Blob).colors.Add(color)
				}
			}
		}
	}
	doColor(early, colorEARLY)
	doColor(late, colorLATE)
	conflict := false
	keepgoing := true
	for keepgoing && !conflict {
		keepgoing = false
		for _, event := range rl.repo.commits(nil) {
			if event.color != 0 {
				for _, neighbor := range event.parents() {
					if neighbor.getColor() == colorNONE {
						doColor(neighbor, event.color)
						keepgoing = true
						break
					} else if neighbor.getColor() != event.color {
						conflict = true
						break
					}
				}
				for _, neighbor := range event.children() {
					if neighbor.getColor() == colorNONE {
						doColor(neighbor, event.color)
						keepgoing = true
						break
					} else if neighbor.getColor() != event.color {
						conflict = true
						break
					}
				}
			}
		}
	}
	return conflict, cutIndex, nil
}

// Undo a cut operation and clear all colors.
func (repo *Repository) cutClear(early *Commit, late *Commit, cutIndex int) {
	late.insertParent(cutIndex, early.mark)
	for _, event := range repo.events {
		switch event.(type) {
		case *Blob:
			event.(*Blob).colors.Clear()
		case *Commit:
			event.(*Commit).color = colorNONE
		}
	}
}

// Attempt to topologically cut the selected repo.
func (rl *RepositoryList) cut(early *Commit, late *Commit) bool {
	ok, idx, err := rl.cutConflict(early, late)
	if !ok {
		rl.repo.cutClear(early, late, idx)
		return false
	}
	if err != nil {
		croak(err.Error())
	}
	// Repo can be split, so we need to color tags
	for _, event := range rl.repo.events {
		t, ok := event.(*Tag)
		if ok {
			for _, c := range rl.repo.commits(nil) {
				if c.mark == t.committish {
					t.color = c.color
				}
			}
		}
	}
	// Front events go with early segment, they'll be copied to late one.
	for _, event := range rl.repo.frontEvents() {
		if passthrough, ok := event.(*Passthrough); ok {
			passthrough.color = "early"
		}
	}
	//assert all(hasattr(x, "color") || hasattr(x, "colors") || isinstance(x, Reset) for x in rl.repo)
	// Resets are tricky.  One may have both colors.
	// Blobs can have both colors too, through references in
	// commits on both sides of the cut, but we took care
	// of that earlier.
	earlyBranches := newOrderedStringSet()
	lateBranches := newOrderedStringSet()
	for _, commit := range rl.repo.commits(nil) {
		if commit.color == colorNONE {
			croak(fmt.Sprintf("%s is uncolored!", commit.mark))
		} else if commit.color == colorEARLY {
			earlyBranches.Add(commit.Branch)
		} else if commit.color == colorLATE {
			lateBranches.Add(commit.Branch)
		}
	}
	// Now it's time to do the actual partitioning
	earlyPart := newRepository(rl.repo.name + "-early")
	os.Mkdir(earlyPart.subdir(""), userReadWriteSearchMode)
	latePart := newRepository(rl.repo.name + "-late")
	os.Mkdir(latePart.subdir(""), userReadWriteSearchMode)
	for _, event := range rl.repo.events {
		if reset, ok := event.(*Reset); ok {
			if earlyBranches.Contains(reset.ref) {
				earlyPart.addEvent(reset)
			}
			if lateBranches.Contains(reset.ref) {
				latePart.addEvent(reset)
			}
		} else if blob, ok := event.(*Blob); ok {
			if blob.colors.Contains(colorEARLY) {
				earlyPart.addEvent(blob.clone(earlyPart))
			}
			if blob.colors.Contains(colorLATE) {
				latePart.addEvent(blob.clone(latePart))
			}
		} else {
			if passthrough, ok := event.(*Passthrough); ok {
				if passthrough.color == "early" {
					passthrough.moveto(earlyPart)
					earlyPart.addEvent(passthrough)
				} else if passthrough.color == "late" {
					passthrough.moveto(latePart)
					latePart.addEvent(passthrough)
				} else {
					// TODO: Someday, color passthroughs
					// that aren't fronted.
					panic(fmt.Sprintf("coloring algorithm failed on %s", event.idMe()))
				}
			} else if commit, ok := event.(*Commit); ok {
				if commit.color == colorEARLY {
					commit.moveto(earlyPart)
					earlyPart.addEvent(commit)
				} else if commit.color == colorLATE {
					commit.moveto(latePart)
					latePart.addEvent(commit)
				} else {
					panic(fmt.Sprintf("coloring algorithm failed on %s", event.idMe()))
				}
			} else if tag, ok := event.(*Tag); ok {
				if tag.color == colorEARLY {
					tag.moveto(earlyPart)
					earlyPart.addEvent(tag)
				} else if tag.color == colorLATE {
					tag.moveto(latePart)
					latePart.addEvent(tag)
				} else {
					panic(fmt.Sprintf("coloring algorithm failed on %s", event.idMe()))
				}
			}
		}
	}
	// Options and features may need to be copied to the late fragment.
	// It's crucial here that frontEvents() returns a copy, not a reference.
	latePart.events = append(earlyPart.frontEvents(), latePart.events...)
	latePart.declareSequenceMutation("cut operation")
	// Add the split results to the repo list.
	rl.repolist = append(rl.repolist, earlyPart)
	rl.repolist = append(rl.repolist, latePart)
	rl.repo.cleanup()
	rl.removeByName(rl.repo.name)
	return true
}

// Unite multiple repos into a union repo.
func (rl *RepositoryList) unite(factors []*Repository, options stringSet) {
	for _, x := range factors {
		if len(x.commits(nil)) == 0 {
			croak(fmt.Sprintf("empty factor %s", x.name))
			return
		}
	}
	// Forward time order
	sort.Slice(factors, func(i, j int) bool {
		return factors[i].earliest().Before(factors[j].earliest())
	})
	roots := make([]*Commit, 0)
	uname := ""
	for _, x := range factors {
		roots = append(roots, x.earliestCommit())
		uname += "+" + x.name
	}
	union := newRepository(uname[1:])
	os.Mkdir(union.subdir(""), userReadWriteSearchMode)
	factorOrder := func(i, j int) bool {
		return !factors[i].earliest().After(factors[j].earliest())
	}
	// Reverse time order
	sort.SliceStable(factors, func(i, j int) bool {
		return factorOrder(j, i)
	})
	persist := make(map[string]string)
	for _, factor := range factors {
		persist = factor.uniquify(factor.name, persist)
	}
	// Forward time order
	sort.SliceStable(factors, func(i, j int) bool {
		return factorOrder(i, j)
	})
	roots = make([]*Commit, 0)
	for _, x := range factors {
		roots = append(roots, x.earliestCommit())
	}
	for _, factor := range factors {
		union.absorb(factor)
		rl.removeByName(factor.name)
	}
	//dumpEvents := func(repo *Repository) []string {
	//	var out []string
	//	for _, commit := range repo.commits(nil) {
	//		out = append(out, commit.getMark())
	//	}
	//	return out
	//}
	// Renumber all events
	union.renumber(1, nil)
	// Sort out the root grafts. The way we used to do this
	// involved sorting the union commits by timestamp, but this
	// fails because in real-world repos timestamp order may not
	// coincide with mark order - leading to "mark not defined"
	// errors from the importer at rebuild time. Instead we graft
	// each root just after the last commit in the dump sequence
	// with a date prior to it.  This method gives less intuitive
	// results, but at least means we never need to reorder
	// commits.
	commits := union.commits(nil)
	for _, root := range roots[1:] {
		// Get last commit such that it and all before it are
		// earlier than the root.  Never raises IndexError since
		// union.earliestCommit() is root[0] which satisfies
		// earlier() thanks to factors sorting.
		mostRecent := union.earliestCommit()
		for idx, event := range commits {
			if root.when().After(event.when()) {
				mostRecent = event
				continue
			} else if idx > 0 {
				break
			}
		}
		root.addParentByMark(mostRecent.mark)
		// We may not want files from the
		// ancestral stock to persist in the
		// grafted branch unless they have
		// modify ops in the branch root.
		if options.Contains("--prune") {
			deletes := make([]FileOp, 0)
			for _, elt := range mostRecent.manifest().items() {
				fileop := newFileOp(union)
				fileop.construct(opD, elt.name)
				deletes = append(deletes, *fileop)
			}
			root.setOperations(append(deletes, root.operations()...))
			root.canonicalize()
		}
	}
	// Put the result on the load list
	rl.repolist = append(rl.repolist, union)
	rl.choose(union)
}

// Expunge a set of files from the commits in the selection set.
func (rl *RepositoryList) expunge(selection orderedIntSet, matchers []string) {
	digest := func(toklist []string) (*regexp.Regexp, bool) {
		digested := make([]string, 0)
		notagify := false
		for _, s := range toklist {
			if strings.HasPrefix(s, "/") && strings.HasSuffix(s, "/") {
				digested = append(digested, "(?:"+s[1:len(s)-1]+")")
			} else if s == "--notagify" {
				notagify = true
			} else {
				digested = append(digested, "^"+regexp.QuoteMeta(s)+"$")
			}
		}
		return regexp.MustCompile(strings.Join(digested, "|")), notagify
	}
	// Save a copy of all parent-child relationships, we'll need it later
	parentage := make(map[string][]string)
	for _, commit := range rl.repo.commits(nil) {
		parentage[commit.mark] = commit.parentMarks()
	}
	// First pass: compute fileop deletions
	alterations := make([][]int, 0)
	expunge, notagify := digest(matchers)
	for _, ei := range selection {
		event := rl.repo.events[ei]
		deletia := make([]int, 0)
		commit, ok := event.(*Commit)
		if ok {
			for i, fileop := range commit.operations() {
				logit(logDELETE, fileop.String()+"\n")
				if fileop.op == opD || fileop.op == opM {
					if expunge.MatchString(fileop.Path) {
						deletia = append(deletia, i)
					}
				} else if fileop.op == opR || fileop.op == opC {
					sourcedelete := expunge.MatchString(fileop.Source)
					targetdelete := expunge.MatchString(fileop.Target)
					if sourcedelete {
						deletia = append(deletia, i)
						//logit(logSHOUT, "following %s of %s to %s", fileop.op, fileop.Source, fileop.Target)
						if fileop.op == opR {
							newmatchers := make([]string, 0)
							for _, m := range matchers {
								if m != "^"+fileop.Source+"$" {
									newmatchers = append(newmatchers, m)
								}
							}
							matchers = newmatchers
						}
						matchers = append(matchers, "^"+fileop.Target+"$")
						expunge, notagify = digest(matchers)
					} else if targetdelete {
						if fileop.op == opR {
							fileop.op = opD
						} else if fileop.op == opC {
							deletia = append(deletia, i)
						}
						matchers = append(matchers, "^"+fileop.Target+"$")
						expunge, notagify = digest(matchers)
					}
				}
			}
		}
		alterations = append(alterations, deletia)
	}
	// Second pass: perform actual fileop expunges
	expunged := newRepository(rl.repo.name + "-expunges")
	expunged.seekstream = rl.repo.seekstream
	expunged.makedir()
	for _, event := range rl.repo.events {
		switch event.(type) {
		case *Blob:
			blob := event.(*Blob)
			blob._expungehook = nil
		case *Commit:
			commit := event.(*Commit)
			commit._expungehook = nil
		}
	}
	for i, ei := range selection {
		deletia := alterations[i]
		if len(deletia) == 0 {
			continue
		}
		commit := rl.repo.events[ei].(*Commit)
		keepers := make([]FileOp, 0)
		blobs := make([]*Blob, 0)
		for _, j := range deletia {
			fileop := commit.fileops[j]
			var sourcedelete bool
			var targetdelete bool
			if fileop.op == opD {
				keepers = append(keepers, fileop)
				respond("at %d, expunging D %s",
					ei+1, fileop.Path)
			} else if fileop.op == opM {
				keepers = append(keepers, fileop)
				if fileop.ref != "inline" {
					bi := rl.repo.markToIndex(fileop.ref)
					blob := rl.repo.events[bi].(*Blob)
					//assert(isinstance(blob, Blob))
					blobs = append(blobs, blob)
				}
				respond("at %d, expunging M %s", ei+1, fileop.Path)
			} else if fileop.op == opR || fileop.op == opC {
				//assert(sourcedelete || targetdelete)
				if sourcedelete && targetdelete {
					keepers = append(keepers, fileop)
				}
			}
		}

		nondeletia := make([]FileOp, 0)
		deletiaSet := newOrderedIntSet(deletia...)
		for i, op := range commit.operations() {
			if !deletiaSet.Contains(i) {
				nondeletia = append(nondeletia, op)
			}
		}
		commit.setOperations(nondeletia)
		// If there are any keeper fileops, hang them them and
		// their blobs on keeps, cloning the commit() for them.
		if len(keepers) > 0 {
			newcommit := commit.clone(expunged)
			newcommit.setOperations(keepers)
			for _, blob := range blobs {
				blob._expungehook = blob.clone(rl.repo)
			}
			commit._expungehook = newcommit
		}
	}
	// Build the new repo and hook it into the load list
	expunged.events = rl.repo.frontEvents()
	expunged.declareSequenceMutation("expunge operation")
	expungedBranches := expunged.branchset()
	expungedMarks := orderedStringSet(nil)
	for _, event := range rl.repo.events {
		switch event.(type) {
		case *Blob:
			blob := event.(*Blob)
			if blob._expungehook != nil {
				blob._expungehook.materialize()
				blob._expungehook.moveto(expunged)
				expunged.addEvent(blob._expungehook)
				blob._expungehook = nil
				expungedMarks.Add(blob.mark)
			}
		case *Commit:
			commit := event.(*Commit)
			if commit._expungehook != nil {
				expunged.addEvent(commit._expungehook)
				commit._expungehook = nil
				expungedMarks.Add(commit.mark)
			}
		case *Reset:
			reset := event.(*Reset)
			if expungedBranches.Contains(reset.ref) {
				expunged.addEvent(reset)
				reset.repo = expunged
			}
		case *Tag:
			tag := event.(*Tag)
			target := rl.repo.markToEvent(tag.committish).(*Commit)
			if target._expungehook != nil {
				expunged.addEvent(tag)
				tag.repo = expunged
			}
		}
	}
	// Patch together ancestry chains in the expunged repo
	for _, commit := range expunged.commits(nil) {
		commit.setParents(nil)
		oldparents := rl.repo.markToEvent(commit.mark).(*Commit).parentMarks()
		for _, parent := range oldparents {
			backto := parent
			for len(parentage[backto]) > 0 {
				// Could we preserve merge parent relationship here?
				if expungedMarks.Contains(parentage[backto][0]) {
					commit.addParentByMark(parentage[backto][0])
					break
				} else {
					backto = parentage[backto][0]
				}
			}
		}
	}
	backreferences := make(map[string]int)
	for _, commit := range rl.repo.commits(nil) {
		for _, fileop := range commit.operations() {
			if fileop.op == opM {
				backreferences[fileop.ref]++
			}
		}
	}
	// Now remove commits that no longer have fileops, and released blobs.
	// Logit events that will be deleted.
	if logEnable(logDELETE) {
		toDelete := make([]int, 0)
		for i, event := range rl.repo.events {
			switch event.(type) {
			case *Blob:
				blob := event.(*Blob)
				if backreferences[blob.mark] == 0 {
					toDelete = append(toDelete, i+1)
				}
			case *Commit:
				commit := event.(*Commit)
				if len(commit.operations()) == 0 {
					toDelete = append(toDelete, i+1)
				}
			}
		}
		if len(toDelete) == 0 {
			respond("deletion set is empty.")
		} else {
			respond("deleting blobs and empty commits %v", toDelete)
		}
	}
	// First delete the blobs.  Use the SliceTricks idiom for filtering
	// in place so no additional allocation is required.
	filtered := rl.repo.events[:0]
	for _, event := range rl.repo.events {
		blob, ok := event.(*Blob)
		if !ok || backreferences[blob.mark] > 0 {
			filtered = append(filtered, event)
		}
	}
	rl.repo.events = filtered
	rl.repo.tagifyEmpty(nil, false, false, false, nil, nil, !notagify, nil)
	// And tell we changed the manifests and the event sequence.
	//rl.repo.invalidateManifests()
	rl.repo.declareSequenceMutation("expunge cleanup")
	// At last, add the expunged repository to the loaded list.
	rl.repolist = append(rl.repolist, expunged)
}

type selEvalState interface {
	nItems() int
	allItems() *fastOrderedIntSet
	release()
}

type selEvaluator func(selEvalState, *fastOrderedIntSet) *fastOrderedIntSet

type selParser interface {
	compile(line string) (selEvaluator, string)
	evaluate(selEvaluator, selEvalState) []int
	parse(string, selEvalState) ([]int, string)
	parseExpression() selEvaluator
	parseDisjunct() selEvaluator
	evalDisjunct(selEvalState, *fastOrderedIntSet, selEvaluator, selEvaluator) *fastOrderedIntSet
	parseConjunct() selEvaluator
	evalConjunct(selEvalState, *fastOrderedIntSet, selEvaluator, selEvaluator) *fastOrderedIntSet
	parseTerm() selEvaluator
	evalTermNegate(selEvalState, *fastOrderedIntSet, selEvaluator) *fastOrderedIntSet
	parseVisibility() selEvaluator
	evalVisibility(selEvalState, *fastOrderedIntSet, string) *fastOrderedIntSet
	parsePolyrange() selEvaluator
	polyrangeInitials() string
	possiblePolyrange() bool
	evalPolyrange(selEvalState, *fastOrderedIntSet, []selEvaluator) *fastOrderedIntSet
	parseAtom() selEvaluator
	parseTextSearch() selEvaluator
	parseFuncall() selEvaluator
}

// SelectionParser parses the selection set language
type SelectionParser struct {
	subclass selParser
	line     string
	nitems   int
}

func (p *SelectionParser) imp() selParser {
	if p.subclass != nil {
		return p.subclass
	}
	return p
}

func (p *SelectionParser) evalState(nitems int) selEvalState {
	p.nitems = nitems
	return p
}

func (p *SelectionParser) release() { p.nitems = 0 }

func (p *SelectionParser) nItems() int { return p.nitems }

func (p *SelectionParser) allItems() *fastOrderedIntSet {
	s := newFastOrderedIntSet()
	for i := 0; i < p.nitems; i++ {
		s.Add(i)
	}
	return s
}

func eatWS(s string) string {
	return strings.TrimLeft(s, " \t")
}

func (p *SelectionParser) eatWS() {
	p.line = eatWS(p.line)
}

// compile compiles expression and return remainder of line with expression
// removed
func (p *SelectionParser) compile(line string) (selEvaluator, string) {
	orig := line
	p.line = line
	machine := p.imp().parseExpression()
	line = eatWS(p.line)
	p.line = ""
	if line == eatWS(orig) {
		machine = nil
	}
	return machine, line
}

// evaluate evaluates a pre-compiled selection query against item list
func (p *SelectionParser) evaluate(machine selEvaluator, state selEvalState) []int {
	if machine == nil {
		return nil
	}
	return machine(state, p.allItems()).Values()
}

// parse parses selection and returns remainder of line with selection removed
func (p *SelectionParser) parse(line string, state selEvalState) ([]int, string) {
	machine, rest := p.imp().compile(line)
	return p.imp().evaluate(machine, state), rest
}

func (p *SelectionParser) peek() rune {
	if len(p.line) == 0 {
		return utf8.RuneError
	}
	r, _ := utf8.DecodeRuneInString(p.line)
	return r
}

func (p *SelectionParser) pop() rune {
	if len(p.line) == 0 {
		return utf8.RuneError
	}
	r, n := utf8.DecodeRuneInString(p.line)
	p.line = p.line[n:]
	return r
}

func (p *SelectionParser) parseExpression() selEvaluator {
	p.eatWS()
	return p.imp().parseDisjunct()
}

// parseDisjunct parses a disjunctive expression (| has lowest precedence)
func (p *SelectionParser) parseDisjunct() selEvaluator {
	p.eatWS()
	op := p.imp().parseConjunct()
	if op == nil {
		return nil
	}
	for {
		p.eatWS()
		if p.peek() != '|' {
			break
		}
		p.pop()
		op2 := p.imp().parseConjunct()
		if op2 == nil {
			break
		}
		op1 := op
		op = func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
			return p.imp().evalDisjunct(x, s, op1, op2)
		}
	}
	return op
}

// evalDisjunct evaluates a disjunctive expression
func (p *SelectionParser) evalDisjunct(state selEvalState,
	preselection *fastOrderedIntSet, op1, op2 selEvaluator) *fastOrderedIntSet {
	selected := newFastOrderedIntSet()
	conjunct := op1(state, preselection)
	if conjunct != nil {
		selected = selected.Union(conjunct)
		conjunct = op2(state, preselection)
		if conjunct != nil {
			selected = selected.Union(conjunct)
		}
	}
	return selected
}

// parseConjunct parses a conjunctive expression (and has higher precedence)
func (p *SelectionParser) parseConjunct() selEvaluator {
	p.eatWS()
	op := p.imp().parseTerm()
	if op == nil {
		return nil
	}
	for {
		p.eatWS()
		if p.peek() != '&' {
			break
		}
		p.pop()
		op2 := p.imp().parseTerm()
		if op2 == nil {
			break
		}
		op1 := op
		op = func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
			return p.imp().evalConjunct(x, s, op1, op2)
		}
	}
	return op
}

// evalConjunct evaluates a conjunctive expression
func (p *SelectionParser) evalConjunct(state selEvalState,
	preselection *fastOrderedIntSet, op1, op2 selEvaluator) *fastOrderedIntSet {
	// assign term before intersecting with preselection so
	// that the order specified by the user's first term is
	// preserved
	conjunct := op1(state, preselection)
	if conjunct == nil {
		conjunct = preselection
	} else {
		// this line is necessary if the user specified only
		// polyranges because evalPolyrange() ignores the
		// preselection
		conjunct = conjunct.Intersection(preselection)
		term := op2(state, preselection)
		if term != nil {
			conjunct = conjunct.Intersection(term)
		}
	}
	return conjunct
}

func (p *SelectionParser) parseTerm() selEvaluator {
	var term selEvaluator
	p.eatWS()
	if p.peek() == '~' {
		p.pop()
		op := p.imp().parseExpression()
		term = func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
			return p.imp().evalTermNegate(x, s, op)
		}
	} else if p.peek() == '(' {
		p.pop()
		term = p.imp().parseExpression()
		p.eatWS()
		if p.peek() != ')' {
			panic(throw("command", "trailing junk on inner expression"))
		} else {
			p.pop()
		}
	} else {
		term = p.imp().parseVisibility()
		if term == nil {
			term = p.imp().parsePolyrange()
			if term == nil {
				term = p.imp().parseTextSearch()
				if term == nil {
					term = p.imp().parseFuncall()
				}
			}
		}
	}
	return term
}

func (p *SelectionParser) evalTermNegate(state selEvalState,
	preselection *fastOrderedIntSet, op selEvaluator) *fastOrderedIntSet {
	negated := op(state, state.allItems())
	remainder := newFastOrderedIntSet()
	for i, n := 0, state.nItems(); i < n; i++ {
		if !negated.Contains(i) {
			remainder.Add(i)
		}
	}
	return remainder
}

// parseVisibility parses a visibility spec
func (p *SelectionParser) parseVisibility() selEvaluator {
	p.eatWS()
	var visibility selEvaluator
	type typelettersGetter interface {
		visibilityTypeletters() map[rune]func(int) bool
	}
	getter, ok := p.subclass.(typelettersGetter)
	if !ok {
		visibility = nil
	} else if p.peek() != '=' {
		visibility = nil
	} else {
		var visible string
		p.pop()
		typeletters := getter.visibilityTypeletters()
		for {
			if _, ok := typeletters[p.peek()]; !ok {
				break
			}
			c := p.pop()
			if !strings.ContainsRune(visible, c) {
				visible += string(c)
			}
		}
		// We need a special check here because these expressions
		// could otherwise run onto the text part of the command.
		if !strings.ContainsRune("()|& ", p.peek()) {
			panic(throw("command", "garbled type mask at '%s'", p.line))
		}
		visibility = func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
			return p.imp().evalVisibility(x, s, visible)
		}
	}
	return visibility
}

// evalVisibility evaluates a visibility spec
func (p *SelectionParser) evalVisibility(state selEvalState,
	preselection *fastOrderedIntSet, visible string) *fastOrderedIntSet {
	type typelettersGetter interface {
		visibilityTypeletters() map[rune]func(int) bool
	}
	typeletters := p.subclass.(typelettersGetter).visibilityTypeletters()
	predicates := make([]func(int) bool, len(visible))
	for i, r := range visible {
		predicates[i] = typeletters[r]
	}
	visibility := newFastOrderedIntSet()
	it := preselection.Iterator()
	for it.Next() {
		for _, f := range predicates {
			if f(it.Value()) {
				visibility.Add(it.Value())
				break
			}
		}
	}
	return visibility
}

func (p *SelectionParser) polyrangeInitials() string {
	return "0123456789$"
}

// Does the input look like a possible polyrange?
func (p *SelectionParser) possiblePolyrange() bool {
	return strings.ContainsRune(p.imp().polyrangeInitials(), p.peek())
}

// parsePolyrange parses a polyrange specification (list of intervals)
func (p *SelectionParser) parsePolyrange() selEvaluator {
	var polyrange selEvaluator
	p.eatWS()
	if !p.imp().possiblePolyrange() {
		polyrange = nil
	} else {
		var ops []selEvaluator
		polychars := p.imp().polyrangeInitials() + ".,"
		for {
			if !strings.ContainsRune(polychars, p.peek()) {
				break
			}
			if op := p.imp().parseAtom(); op != nil {
				ops = append(ops, op)
			}
		}
		polyrange = func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
			return p.imp().evalPolyrange(x, s, ops)
		}
	}
	return polyrange
}

const polyrangeRange = math.MinInt64
const polyrangeDollar = math.MaxInt64

// evalPolyrange evaluates a polyrange specification (list of intervals)
func (p *SelectionParser) evalPolyrange(state selEvalState,
	preselection *fastOrderedIntSet, ops []selEvaluator) *fastOrderedIntSet {
	// preselection is not used since it is perfectly legal to have range
	// bounds be outside of the reduced set.
	selection := newFastOrderedIntSet()
	for _, op := range ops {
		sel := op(state, preselection)
		if sel != nil {
			selection = selection.Union(sel)
		}
	}
	// Resolve spans
	resolved := newFastOrderedIntSet()
	last := int(math.MinInt64)
	spanning := false
	it := selection.Iterator()
	for it.Next() {
		i := it.Value()
		if i == polyrangeDollar { // "$"
			i = state.nItems() - 1
		}
		if i == polyrangeRange { // ".."
			if last == math.MinInt64 {
				panic(throw("command", "start of span is missing"))
			}
			spanning = true
		} else {
			if spanning {
				for j := last + 1; j < i+1; j++ {
					resolved.Add(j)
				}
				spanning = false
			} else {
				resolved.Add(i)
			}
			last = i
		}
	}
	// Sanity checks
	if spanning {
		panic(throw("command", "incomplete range expression"))
	}
	lim := state.nItems() - 1
	it = resolved.Iterator()
	for it.Next() {
		i := it.Value()
		if i < 0 || i > lim {
			panic(throw("command", "element %d out of range", i+1))
		}
	}
	return resolved
}

var atomNumRE = regexp.MustCompile(`^[0-9]+`)

func (p *SelectionParser) parseAtom() selEvaluator {
	p.eatWS()
	var op selEvaluator
	// First, literal command numbers (1-origin)
	match := atomNumRE.FindString(p.line)
	if len(match) > 0 {
		number, err := strconv.Atoi(match)
		if err != nil {
			panic(throw("command", "Atoi(%q) failed: %v", match, err))
		}
		op = func(selEvalState, *fastOrderedIntSet) *fastOrderedIntSet {
			return newFastOrderedIntSet(number - 1)
		}
		p.line = p.line[len(match):]
	} else if p.peek() == '$' { // $ means last commit, a la ed(1).
		op = func(selEvalState, *fastOrderedIntSet) *fastOrderedIntSet {
			return newFastOrderedIntSet(polyrangeDollar)
		}
		p.pop()
	} else if p.peek() == ',' { // Comma just delimits a location spec
		p.pop()
	} else if strings.HasPrefix(p.line, "..") { // Following ".." means a span
		op = func(selEvalState, *fastOrderedIntSet) *fastOrderedIntSet {
			return newFastOrderedIntSet(polyrangeRange)
		}
		p.line = p.line[len(".."):]
	} else if p.peek() == '.' {
		panic(throw("command", "malformed span"))
	}
	return op
}

// parseTextSearch parses a text search specification
func (p *SelectionParser) parseTextSearch() selEvaluator {
	p.eatWS()
	type textSearcher interface {
		evalTextSearch(selEvalState, *fastOrderedIntSet, *regexp.Regexp, string) *fastOrderedIntSet
	}
	searcher, ok := p.subclass.(textSearcher)
	if !ok {
		return nil
	} else if p.peek() != '/' {
		return nil
	} else if !strings.ContainsRune(p.line[1:], '/') {
		panic(throw("command", "malformed text search specifier"))
	} else {
		p.pop() // skip opening "/"
		endat := strings.IndexRune(p.line, '/')
		pattern := p.line[:endat]
		re, err := regexp.Compile(pattern)
		if err != nil {
			panic(throw("command", "invalid regular expression: /%s/ (%v)", pattern, err))
		}
		p.line = p.line[endat+1:]
		seen := make(map[rune]struct{})
		for unicode.IsLetter(p.peek()) {
			seen[p.pop()] = struct{}{}
		}
		var modifiers strings.Builder
		for x := range seen {
			modifiers.WriteRune(x)
		}
		return func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
			return searcher.evalTextSearch(x, s, re, modifiers.String())
		}
	}
}

// parseFuncall parses a function call
func (p *SelectionParser) parseFuncall() selEvaluator {
	p.eatWS()
	if p.peek() != '@' {
		return nil
	}
	p.pop()
	var funname strings.Builder
	for p.peek() == '_' || unicode.IsLetter(p.peek()) {
		funname.WriteRune(p.pop())
	}
	if funname.Len() == 0 || p.peek() != '(' {
		return nil
	}
	// The "(" && ")" after the function name are different than
	// the parentheses used to override operator precedence, so we
	// must handle them here.  If we let parse_expression() handle
	// the parentheses, it will process characters beyond the
	// closing parenthesis as if they were part of the function's
	// argument.  For example, if we let parse_expression() handle
	// the parentheses, then the following expression:
	//     @max(~$)|$
	// would be processed as if this was the argument to max():
	//     (~$)|$
	// when the actual argument is:
	//     ~$
	p.pop()
	subarg := p.imp().parseExpression()
	p.eatWS()
	if p.peek() != ')' {
		panic(throw("command", "missing close parenthesis for function call"))
	}
	p.pop()

	type extraFuncs interface {
		functions() map[string]selEvaluator
	}
	var op selEvaluator
	if q, ok := p.subclass.(extraFuncs); ok {
		op = q.functions()[funname.String()]
	}
	if op == nil {
		op = selFuncs[funname.String()]
	}
	if op == nil {
		panic(throw("command", "no such function @%s()", funname.String()))
	}
	return func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
		return op(x, subarg(x, s))
	}
}

var selFuncs = map[string]selEvaluator{
	"min": minHandler,
	"max": maxHandler,
	"amp": ampHandler,
	"pre": preHandler,
	"suc": sucHandler,
	"srt": srtHandler,
	"rev": revHandler,
}

func selMin(s *fastOrderedIntSet) int {
	if s.Size() == 0 {
		panic(throw("command", "cannot take minimum of empty set"))
	}
	it := s.Iterator()
	it.Next()
	n := it.Value()
	for it.Next() {
		if it.Value() < n {
			n = it.Value()
		}
	}
	return n
}

func selMax(s *fastOrderedIntSet) int {
	if s.Size() == 0 {
		panic(throw("command", "cannot take maximum of empty set"))
	}
	it := s.Iterator()
	it.Next()
	n := it.Value()
	for it.Next() {
		if it.Value() > n {
			n = it.Value()
		}
	}
	return n
}

// Minimum member of a selection set.
func minHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	return newFastOrderedIntSet(selMin(subarg))
}

// Maximum member of a selection set.
func maxHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	return newFastOrderedIntSet(selMax(subarg))
}

// Amplify - map empty set to empty, nonempty set to all.
func ampHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	if subarg.Size() != 0 {
		return state.allItems()
	}
	return newFastOrderedIntSet()
}

// Predecessors function; all elements previous to argument set.
func preHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	pre := newFastOrderedIntSet()
	if subarg.Size() == 0 {
		return pre
	}
	n := selMin(subarg)
	if n == 0 {
		return pre
	}
	for i := 0; i < n; i++ {
		pre.Add(i)
	}
	return pre
}

// Successors function; all elements following argument set.
func sucHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	suc := newFastOrderedIntSet()
	if subarg.Size() == 0 {
		return suc
	}
	nitems := state.nItems()
	n := selMax(subarg)
	if n >= nitems-1 {
		return suc
	}
	for i := n + 1; i < nitems; i++ {
		suc.Add(i)
	}
	return suc
}

// Sort the argument set.
func srtHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	return subarg.Sort()
}

// Reverse the argument set.
func revHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	n := subarg.Size()
	v := make([]int, n)
	it := subarg.Iterator()
	for it.Next() {
		v[n-it.Index()-1] = it.Value()
	}
	return newFastOrderedIntSet(v...)
}

type attrEditAttr interface {
	String() string
	desc() string
	name() string
	email() string
	date() Date
	assign(name, email string, date Date)
	remove(Event)
	insert(after bool, e Event, a Attribution)
}

type attrEditMixin struct {
	a *Attribution
}

func (p *attrEditMixin) String() string {
	return p.a.String()
}

func (p *attrEditMixin) name() string  { return p.a.fullname }
func (p *attrEditMixin) email() string { return p.a.email }
func (p *attrEditMixin) date() Date    { return p.a.date }

func (p *attrEditMixin) assign(name, email string, date Date) {
	if len(name) != 0 {
		p.a.fullname = name
	}
	if len(email) != 0 {
		p.a.email = email
	}
	if !date.isZero() {
		p.a.date = date
	}
}

func (p *attrEditMixin) minOne(desc string) {
	panic(throw("command", "unable to delete %s (1 needed)", desc))
}

func (p *attrEditMixin) maxOne(desc string) {
	panic(throw("command", "unable to add %s (only 1 allowed)", desc))
}

type attrEditCommitter struct {
	attrEditMixin
}

func newAttrEditCommitter(a *Attribution) *attrEditCommitter {
	return &attrEditCommitter{attrEditMixin{a}}
}

func (p *attrEditCommitter) desc() string { return "committer" }

func (p *attrEditCommitter) remove(e Event) {
	p.minOne(p.desc())
}

func (p *attrEditCommitter) insert(after bool, e Event, a Attribution) {
	p.maxOne(p.desc())
}

type attrEditAuthor struct {
	attrEditMixin
	pos int
}

func newAttrEditAuthor(a *Attribution, pos int) *attrEditAuthor {
	return &attrEditAuthor{attrEditMixin{a}, pos}
}

func (p *attrEditAuthor) desc() string { return "author" }

func (p *attrEditAuthor) remove(e Event) {
	c := e.(*Commit)
	v := c.authors
	copy(v[p.pos:], v[p.pos+1:])
	v[len(v)-1] = Attribution{}
	c.authors = v[:len(v)-1]
}

func (p *attrEditAuthor) insert(after bool, e Event, a Attribution) {
	c := e.(*Commit)
	newpos := p.pos
	if after {
		newpos++
	}
	v := append(c.authors, Attribution{})
	if newpos < len(v)-1 {
		copy(v[newpos+1:], v[newpos:])
	}
	v[newpos] = a
	c.authors = v
}

type attrEditTagger struct {
	attrEditMixin
}

func newAttrEditTagger(a *Attribution) *attrEditTagger {
	return &attrEditTagger{attrEditMixin{a}}
}

func (p *attrEditTagger) desc() string { return "tagger" }

func (p *attrEditTagger) remove(e Event) {
	p.minOne(p.desc())
}

func (p *attrEditTagger) insert(after bool, e Event, a Attribution) {
	p.maxOne(p.desc())
}

type attrEditSelParser struct {
	SelectionParser
	attributions []attrEditAttr
}

func newAttrEditSelParser() *attrEditSelParser {
	p := new(attrEditSelParser)
	p.SelectionParser.subclass = p
	return p
}

func (p *attrEditSelParser) evalState(v []attrEditAttr) selEvalState {
	p.attributions = v
	return p.SelectionParser.evalState(len(v))
}

func (p *attrEditSelParser) release() {
	p.attributions = nil
	p.SelectionParser.release()
}

func (p *attrEditSelParser) visibilityTypeletters() map[rune]func(int) bool {
	return map[rune]func(int) bool{
		'C': func(i int) bool { _, ok := p.attributions[i].(*attrEditCommitter); return ok },
		'A': func(i int) bool { _, ok := p.attributions[i].(*attrEditAuthor); return ok },
		'T': func(i int) bool { _, ok := p.attributions[i].(*attrEditTagger); return ok },
	}
}

func (p *attrEditSelParser) evalTextSearch(state selEvalState,
	preselection *fastOrderedIntSet,
	search *regexp.Regexp, modifiers string) *fastOrderedIntSet {
	var checkName, checkEmail bool
	if len(modifiers) == 0 {
		checkName, checkEmail = true, true
	} else {
		for _, m := range modifiers {
			if m == 'n' {
				checkName = true
			} else if m == 'e' {
				checkEmail = true
			} else {
				panic(throw("command", "unknown textsearch flag"))
			}
		}
	}
	found := newFastOrderedIntSet()
	it := preselection.Iterator()
	for it.Next() {
		a := p.attributions[it.Value()]
		if (checkName && search.MatchString(a.name())) ||
			(checkEmail && search.MatchString(a.email())) {
			found.Add(it.Value())
		}
	}
	return found
}

// AttributionEditor inspects and edits committer, author, tagger attributions
type AttributionEditor struct {
	eventSel []int
	events   []Event
	machine  func([]attrEditAttr) []int
}

func newAttributionEditor(sel []int, events []Event, machine func([]attrEditAttr) []int) *AttributionEditor {
	return &AttributionEditor{sel, events, machine}
}

func (p *AttributionEditor) attributions(e Event) []attrEditAttr {
	switch x := e.(type) {
	case *Commit:
		v := make([]attrEditAttr, 1+len(x.authors))
		v[0] = newAttrEditCommitter(&x.committer)
		for i := range x.authors {
			v[i+1] = newAttrEditAuthor(&x.authors[i], i)
		}
		return v
	case *Tag:
		return []attrEditAttr{newAttrEditTagger(x.tagger)}
	default:
		panic(fmt.Sprintf("unexpected event type: %T", e))
	}
}

func (p *AttributionEditor) authorIndices(attrs []attrEditAttr) []int {
	v := make([]int, 0, len(attrs))
	for i, a := range attrs {
		if _, ok := a.(*attrEditAuthor); ok {
			v = append(v, i)
		}
	}
	return v
}

func (p *AttributionEditor) getMark(e Event) string {
	m := e.getMark()
	if len(m) == 0 {
		m = "-"
	}
	return m
}

func (p *AttributionEditor) apply(f func(p *AttributionEditor, eventNo int, e Event, attrs []attrEditAttr, sel []int, extra ...interface{}), extra ...interface{}) {
	for _, i := range p.eventSel {
		e := p.events[i]
		attrs := p.attributions(e)
		var sel []int
		func() {
			defer func() {
				if x := catch("command", recover()); x != nil {
					panic(throw("command", "%s (event %d, mark %s)",
						x.Error(), i+1, p.getMark(e)))
				}
			}()
			sel = p.machine(attrs)
		}()
		f(p, i, e, attrs, sel, extra...)
	}
}

func (p *AttributionEditor) infer(attrs []attrEditAttr, preferred int,
	name, email string, date Date) (string, string, Date) {
	if len(name) == 0 && len(email) == 0 {
		panic(throw("command", "unable to infer missing name and email"))
	}
	if preferred > 0 {
		attrs = append([]attrEditAttr{attrs[preferred]}, attrs...)
	}
	if len(name) == 0 {
		for _, a := range attrs {
			if a.email() == email {
				name = a.name()
				break
			}
		}
		if len(name) == 0 {
			panic(throw("command", "unable to infer name for %s", email))
		}
	}
	if len(email) == 0 {
		for _, a := range attrs {
			if a.name() == name {
				email = a.email()
				break
			}
		}
		if len(email) == 0 {
			panic(throw("command", "unable to infer email for %s", name))
		}
	}
	if date.isZero() {
		if len(attrs) != 0 {
			date = attrs[0].date()
		} else {
			panic(throw("command", "unable to infer date"))
		}
	}
	return name, email, date
}

func (p *AttributionEditor) glean(args []string) (string, string, Date) {
	var name, email string
	var date Date
	for _, x := range args {
		if d, err := newDate(x); err == nil {

			if !date.isZero() {
				panic(throw("command", "extra timestamp: %s", x))
			}
			date = d
		} else if strings.ContainsRune(x, '@') {
			if len(email) != 0 {
				panic(throw("command", "extra email: %s", x))
			}
			email = x
		} else {
			if len(name) != 0 {
				panic(throw("command", "extra name: %s", x))
			}
			name = x
		}
	}
	return name, email, date
}

func (p *AttributionEditor) inspect(w io.Writer) {
	p.apply((*AttributionEditor).doInspect, w)
}

func (p *AttributionEditor) doInspect(eventNo int, e Event, attrs []attrEditAttr, sel []int, extra ...interface{}) {
	w := extra[0].(io.Writer)
	mark := p.getMark(e)
	if sel == nil {
		sel = make([]int, len(attrs))
		for i := range attrs {
			sel[i] = i
		}
	}
	for _, i := range sel {
		a := attrs[i]
		io.WriteString(w, fmt.Sprintf("%6d %6s %2d:%-9s %s\n", eventNo+1, mark, i+1, a.desc(), a))
	}
}

func (p *AttributionEditor) assign(args []string) {
	name, email, date := p.glean(args)
	p.apply((*AttributionEditor).doAssign, name, email, date)
}

func (p *AttributionEditor) doAssign(eventNo int, e Event, attrs []attrEditAttr, sel []int, extra ...interface{}) {
	name := extra[0].(string)
	email := extra[1].(string)
	date := extra[2].(Date)
	if sel == nil {
		panic(throw("command", "no attribution selected"))
	}
	for _, i := range sel {
		attrs[i].assign(name, email, date)
	}
}

func (p *AttributionEditor) remove() {
	p.apply((*AttributionEditor).doRemove)
}

func (p *AttributionEditor) doRemove(eventNo int, e Event, attrs []attrEditAttr, sel []int, extra ...interface{}) {
	if sel == nil {
		sel = p.authorIndices(attrs)
	}
	rev := make([]int, len(sel))
	copy(rev, sel)
	sort.Stable(sort.Reverse(sort.IntSlice(rev)))
	for _, i := range rev {
		attrs[i].remove(e)
	}
}

func (p *AttributionEditor) insert(args []string, after bool) {
	name, email, date := p.glean(args)
	p.apply((*AttributionEditor).doInsert, after, name, email, date)
}

func (p *AttributionEditor) doInsert(eventNo int, e Event, attrs []attrEditAttr, sel []int, extra ...interface{}) {
	after := extra[0].(bool)
	name := extra[1].(string)
	email := extra[2].(string)
	date := extra[3].(Date)
	if sel == nil {
		sel = p.authorIndices(attrs)
	}
	var basis = -1
	if len(sel) != 0 {
		if after {
			basis = sel[len(sel)-1]
		} else {
			basis = sel[0]
		}
	}
	var a Attribution
	a.fullname, a.email, a.date = p.infer(attrs, basis, name, email, date)
	if basis >= 0 {
		attrs[basis].insert(after, e, a)
	} else if c, ok := e.(*Commit); ok {
		c.authors = append(c.authors, a)
	} else {
		panic(throw("command", "unable to add author to %s",
			strings.ToLower(reflect.TypeOf(e).Elem().Name())))
	}
}

func (p *AttributionEditor) resolve(w io.Writer, label string) {
	p.apply((*AttributionEditor).doResolve, w, label)
}

func (p *AttributionEditor) doResolve(eventNo int, e Event, attrs []attrEditAttr, sel []int, extra ...interface{}) {
	w := extra[0].(io.Writer)
	label := extra[1].(string)
	if sel == nil {
		panic(throw("command", "no attribution selected"))
	}
	var b strings.Builder
	if len(label) != 0 {
		b.WriteString(fmt.Sprintf("%s: ", label))
	}
	b.WriteString(fmt.Sprintf("%6d %6s [", eventNo+1, p.getMark(e)))
	for i, n := range sel {
		if i > 0 {
			b.WriteString(", ")
		}
		b.WriteString(strconv.Itoa(n + 1))
	}
	b.WriteString("]\n")
	io.WriteString(w, b.String())
}

type LineParse struct {
	repolist     *RepositoryList
	line         string
	capabilities orderedStringSet
	stdin        io.ReadCloser
	stdout       io.WriteCloser
	infile       string
	outfile      string
	redirected   bool
	options      orderedStringSet
	closem       []io.Closer
}

func (rl *RepositoryList) newLineParse(line string, capabilities orderedStringSet) *LineParse {
	caps := make(map[string]bool)
	for _, cap := range capabilities {
		caps[cap] = true
	}
	lp := LineParse{
		line:         line,
		capabilities: capabilities,
		stdin:        os.Stdin,
		stdout:       control.baton,
		redirected:   false,
		options:      make([]string, 0),
		closem:       make([]io.Closer, 0),
	}

	var err error
	// Input redirection
	match := regexp.MustCompile("<[^ ]+").FindStringIndex(lp.line)
	if match != nil {
		if !caps["stdin"] {
			panic(throw("command", "no support for < redirection"))
		}
		lp.infile = lp.line[match[0]+1 : match[1]]
		if lp.infile != "" && lp.infile != "-" {
			lp.stdin, err = os.Open(lp.infile)
			if err != nil {
				panic(throw("command", "can't open %s for read", lp.infile))
			}
			lp.closem = append(lp.closem, lp.stdin)
		}
		lp.line = lp.line[:match[0]] + lp.line[match[1]:]
		lp.redirected = true
	}
	// Output redirection
	match = regexp.MustCompile("(>>?)([^ ]+)").FindStringSubmatchIndex(lp.line)
	if match != nil {
		if !caps["stdout"] {
			panic(throw("command", "no support for > redirection"))
		}
		lp.outfile = lp.line[match[2*2+0]:match[2*2+1]]
		if lp.outfile != "" && lp.outfile != "-" {
			info, err := os.Stat(lp.outfile)
			if err == nil {
				if info.Mode().IsDir() {
					panic(throw("command", "can't redirect output to %s, which is a directory", lp.outfile))
				}
			}
			// flush the outfile, if it happens to be a file
			// that Reposurgeon has already opened
			rl.writeNotify(lp.outfile)
			mode := os.O_WRONLY
			if match[2*1+1]-match[2*1+0] > 1 {
				mode |= os.O_CREATE | os.O_APPEND
			} else {
				mode |= os.O_CREATE | os.O_TRUNC
			}
			lp.stdout, err = os.OpenFile(lp.outfile, mode, userReadWriteMode)
			if err != nil {
				panic(throw("command", "can't open %s for writing", lp.outfile))
			}
			lp.closem = append(lp.closem, lp.stdout)
		}
		lp.line = lp.line[:match[2*0+0]] + lp.line[match[2*0+1]:]
		lp.redirected = true
	}
	// Options
	for true {
		match := regexp.MustCompile("--([^ ]+)").FindStringSubmatchIndex(lp.line)
		if match == nil {
			break
		} else {
			lp.options = append(lp.options, lp.line[match[2]-2:match[3]])
			lp.line = lp.line[:match[2]-2] + lp.line[match[3]:]
		}
	}
	// strip excess whitespace
	lp.line = strings.TrimSpace(lp.line)
	// Dash redirection
	if !lp.redirected && lp.line == "-" {
		if !caps["stdout"] && !caps["stdin"] {
			panic(throw("command", "no support for - redirection"))
		} else {
			lp.line = ""
			lp.redirected = true
		}
	}
	return &lp
}

// Return the argument token list after the parse for redirects.
func (lp *LineParse) Tokens() []string {
	return strings.Fields(lp.line)
}

func (lp *LineParse) OptVal(opt string) (val string, present bool) {
	for _, option := range lp.options {
		if strings.Contains(option, "=") {
			parts := strings.Split(option, "=")
			if len(parts) > 1 && parts[0] == opt {
				return parts[1], true
			}
			return "", true

		} else if option == opt {
			return "", true
		}
	}
	return "", false
}

func (lp *LineParse) RedirectInput(reader io.Closer) {
	if fp, ok := lp.stdin.(io.Closer); ok {
		for i, f := range lp.closem {
			if f == fp {
				lp.closem[i] = fp
				return
			}
		}
		lp.closem = append(lp.closem, reader)
	}
}

func (lp *LineParse) Closem() {
	for _, f := range lp.closem {
		if f != nil {
			f.Close()
		}
	}
}

type CmdControl struct {
	cmd          *kommandant.Kmdt
	definitions  map[string][]string
	inputIsStdin bool
}

func (md CmdControl) SetCore(k *kommandant.Kmdt) {
	md.cmd = k
}

// Reposurgeon tells Kommandant what our local commands are
type Reposurgeon struct {
	CmdControl
	RepositoryList
	SelectionParser
	callstack        [][]string
	selection        orderedIntSet
	history          []string
	preferred        *VCS
	extractor        Extractor
	startTime        time.Time
	promptFormat     string
	logHighwater     int
	ignorename       string
}

var unclean = regexp.MustCompile("^[^\n]*\n[^\n]")

func newReposurgeon() *Reposurgeon {
	rs := new(Reposurgeon)
	rs.SelectionParser.subclass = rs
	rs.startTime = time.Now()
	rs.definitions = make(map[string][]string)
	rs.inputIsStdin = true
	rs.promptFormat = "reposurgeon% "
	// These are globals and should probably be set in init().
	for _, option := range optionFlags {
		control.listOptions[option[0]] = newOrderedStringSet()
	}
	control.listOptions["svn_branchify"] = orderedStringSet{"trunk", "tags/*", "branches/*", "*"}
	return rs
}

// SetCore is a Kommandant housekeeping hook.
func (rs *Reposurgeon) SetCore(k *kommandant.Kmdt) {
	rs.cmd = k
	k.OneCmdHook = func(ctx context.Context, line string) (stop bool) {
		defer func(stop *bool) {
			if e := catch("command", recover()); e != nil {
				croak(e.message)
				*stop = false
			}
		}(&stop)
		stop = k.OneCmd_core(ctx, line)
		return
	}
}

// helpOutput handles Go multiline literals that may have a leading \n
// to make them more readable in source. It just clips off any leading \n.
func (rs *Reposurgeon) helpOutput(help string) {
	if help[0] == '\n' {
		help = help[1:]
	}
	fmt.Print(help)
}

func (rs *Reposurgeon) inScript() bool {
	return len(rs.callstack) > 0
}

//
// Command implementation begins here
//
func (rs *Reposurgeon) DoEOF(lineIn string) bool {
	if rs.inputIsStdin {
		respond("\n")
	}
	return true
}

func (rs *Reposurgeon) HelpQuit() {
	rs.helpOutput("Terminate reposurgeon cleanly.\n")
}
func (rs *Reposurgeon) DoQuit(lineIn string) bool {
	return true
}

//
// Housekeeping hooks.
//
var inlineCommentRE = regexp.MustCompile(`\s+#`)

func (rs *Reposurgeon) buildPrompt() {
	var chosenName string
	if rs.chosen() != nil {
		chosenName = rs.chosen().name
	}

	replacer := strings.NewReplacer("{chosen}", chosenName)
	rs.cmd.SetPrompt(replacer.Replace(rs.promptFormat))
}

func (rs *Reposurgeon) PreLoop() {
	rs.buildPrompt()
}

func (rs *Reposurgeon) PreCmd(line string) string {
	trimmed := strings.TrimRight(line, " \t\n")
	if len(trimmed) != 0 {
		rs.history = append(rs.history, trimmed)
	}
	if control.flagOptions["echo"] {
		control.baton.printLogString(trimmed + "\n")
	}
	if strings.HasPrefix(line, "#") {
		return ""
	}
	line = inlineCommentRE.Split(line, 2)[0]

	defer func(line *string) {
		if e := catch("command", recover()); e != nil {
			croak(e.message)
			*line = ""
		}
	}(&line)

	machine, rest := rs.parseSelectionSet(line)
	if rs.chosen() != nil {
		if machine != nil {
			rs.selection = rs.evalSelectionSet(machine, rs.chosen())
		} else {
			// nil means that the user specified no
			// specific selection set. each command has a
			// different notion of what to do in that
			// case; some bail out, others operate on the
			// whole repository, etc.
			rs.selection = nil
		}
	}

	rs.logHighwater = control.logcounter
	rs.buildPrompt()

	return rest
}

func (rs *Reposurgeon) PostCmd(stop bool, lineIn string) bool {
	if control.logcounter > rs.logHighwater {
		respond("%d new log message(s)", control.logcounter-rs.logHighwater)
	}
	return stop
}

func (rs *Reposurgeon) HelpShell() {
	rs.helpOutput(`
Run a shell command. Honors the $SHELL environment variable.
`)
}
func (rs *Reposurgeon) DoShell(line string) bool {
	shell := os.Getenv("SHELL")
	if shell == "" {
		shell = "/bin/sh"
	}
	logit(logCOMMANDS, "Spawning %s -c %#v...", shell, line)
	cmd := exec.Command(shell, "-c", line)
	cmd.Stdin = os.Stdin
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	err := cmd.Run()
	if err != nil {
		croak("spawn of %s returned error: %v", shell, err)
	}
	return false
}

// walkEvents walks a selection applying a hook function.to the events
// This metod needs to be ke[s in sync with the walkEvents function.
func (repo *Repository) walkEvents(selection orderedIntSet, hook func(i int, event Event)) {
	if control.flagOptions["serial"] {
		for i, e := range selection {
			hook(i, repo.events[e])
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
				hook(i, repo.events[selection[i]])
			}
			done <- true
		}()
	}

	// Populate the channel with the events
	for i := range selection {
		channel <- i
	}
	close(channel)

	// Wait for all workers to finish
	for n := 0; n < maxWorkers; n++ { <-done }
}

//
// The selection-language parsing code starts here.
//
func (rs *Reposurgeon) parseSelectionSet(line string) (machine selEvaluator, rest string) {
	s := strings.TrimLeft(line, " \t")
	i := strings.IndexAny(s, " \t")
	if i > 0 && rs.isNamed(s[:i]) {
		line = "<" + s[:i] + ">" + s[i:]
	}

	return rs.imp().compile(line)
}

func (rs *Reposurgeon) evalSelectionSet(machine selEvaluator, repo *Repository) []int {
	state := rs.evalState(len(repo.events))
	defer state.release()
	return rs.imp().evaluate(machine, state)
}

func (rs *Reposurgeon) setSelectionSet(line string) (rest string) {
	machine, rest := rs.parseSelectionSet(line)
	rs.selection = rs.evalSelectionSet(machine, rs.chosen())
	return rest
}

func (rs *Reposurgeon) isNamed(s string) (result bool) {
	defer func(result *bool) {
		if e := catch("command", recover()); e != nil {
			*result = false
		}
	}(&result)
	repo := rs.chosen()
	if repo != nil {
		result = repo.named(s) != nil
	}
	return
}

func (rs *Reposurgeon) parseExpression() selEvaluator {
	value := rs.SelectionParser.parseExpression()
	if value == nil {
		return nil
	}
	for {
		if rs.peek() != '?' {
			break
		}
		rs.pop()
		orig := value
		value = func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
			return rs.evalNeighborhood(x, s, orig)
		}
	}
	return value
}

func (rs *Reposurgeon) evalNeighborhood(state selEvalState,
	preselection *fastOrderedIntSet, subject selEvaluator) *fastOrderedIntSet {
	value := subject(state, preselection)
	addSet := newFastOrderedIntSet()
	removeSet := newFastOrderedIntSet()
	it := value.Iterator()
	for it.Next() {
		ei := it.Value()
		event := rs.chosen().events[ei]
		if c, ok := event.(*Commit); ok {
			for _, parent := range c.parents() {
				addSet.Add(rs.chosen().markToIndex(parent.getMark()))
			}
			for _, child := range c.children() {
				addSet.Add(rs.chosen().markToIndex(child.getMark()))
			}
		} else if _, ok := event.(*Blob); ok {
			removeSet.Add(ei) // Don't select the blob itself
			it2 := preselection.Iterator()
			for it2.Next() {
				i := it2.Value()
				event2 := rs.chosen().events[i]
				if c, ok := event2.(*Commit); ok {
					for _, fileop := range c.operations() {
						if fileop.op == opM &&
							fileop.ref == event.getMark() {
							addSet.Add(i)
						}
					}
				}
			}
		} else if t, ok := event.(*Tag); ok {
			if e := rs.repo.markToEvent(t.committish); e != nil {
				addSet.Add(rs.repo.eventToIndex(e))
			}
		} else if r, ok := event.(*Reset); ok {
			if e := rs.repo.markToEvent(r.committish); e != nil {
				addSet.Add(rs.repo.eventToIndex(e))
			}
		}
	}
	value = value.Union(addSet)
	value = value.Subtract(removeSet)
	value = value.Sort()
	return value
}

func (rs *Reposurgeon) parseTerm() selEvaluator {
	term := rs.SelectionParser.parseTerm()
	if term == nil {
		term = rs.parsePathset()
	}
	return term
}

// Parse a path name to evaluate the set of commits that refer to it.
func (rs *Reposurgeon) parsePathset() selEvaluator {
	rs.eatWS()
	if rs.peek() != '[' {
		return nil
	}
	rs.pop()
	var matcher string
	depth := 1
	for i, c := range rs.line {
		if c == '[' {
			depth++
		} else if c == ']' {
			depth--
		}
		if depth == 0 {
			matcher = rs.line[:i]
			rs.line = rs.line[i+1:]
			break
		}
	}
	if depth != 0 {
		panic(throw("command", "malformed path matcher; unbalanced [ and ]"))
	}
	if strings.HasPrefix(matcher, "/") {
		end := strings.LastIndexByte(matcher, '/')
		if end < 1 {
			panic(throw("command", "regexp matcher missing trailing /"))
		}
		pattern := matcher[1:end]
		flags := newOrderedStringSet()
		for _, c := range matcher[end+1:] {
			switch c {
			case 'a', 'c', opM, opD, opR, opC, opN:
				flags.Add(string(c))
			default:
				panic(throw("command", "unrecognized matcher flag '%c'", c))
			}
		}
		search, err := regexp.Compile(pattern)
		if err != nil {
			panic(throw("command", "invalid regular expression %s", matcher))
		}
		return func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
			return rs.evalPathsetRegex(x, s, search, flags)
		}
	}
	return func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
		return rs.evalPathset(x, s, matcher)
	}
}

// Resolve a path regex to the set of commits that refer to it.
func (rs *Reposurgeon) evalPathsetRegex(state selEvalState,
	preselection *fastOrderedIntSet, search *regexp.Regexp,
	flags orderedStringSet) *fastOrderedIntSet {
	if flags.Contains("c") {
		return rs.evalPathsetFull(state, preselection,
			search, flags.Contains("a"))
	}
	all := flags.Contains("a")
	flags.Remove("a")
	if len(flags) == 0 {
		flags = nil // paths(nil) means "all paths"
	}
	type vendPaths interface {
		paths(orderedStringSet) orderedStringSet
	}
	hits := newFastOrderedIntSet()
	events := rs.chosen().events
	it := preselection.Iterator()
	for it.Next() {
		if e, ok := events[it.Value()].(vendPaths); ok {
			matches := 0
			paths := e.paths(flags)
			for _, p := range paths {
				if search.MatchString(p) {
					matches++
					if !all {
						break
					}
				}
			}
			if (all && matches == len(paths)) || (!all && matches > 0) {
				hits.Add(it.Value())
			}
		}
	}
	return hits
}

// Resolve a path name to the set of commits that refer to it.
func (rs *Reposurgeon) evalPathset(state selEvalState,
	preselection *fastOrderedIntSet, matcher string) *fastOrderedIntSet {
	type vendPaths interface {
		paths(orderedStringSet) orderedStringSet
	}
	hits := newFastOrderedIntSet()
	events := rs.chosen().events
	it := preselection.Iterator()
	for it.Next() {
		if e, ok := events[it.Value()].(vendPaths); ok &&
			e.paths(nil).Contains(matcher) {
			hits.Add(it.Value())
		}
	}
	return hits
}

func (rs *Reposurgeon) evalPathsetFull(state selEvalState,
	preselection *fastOrderedIntSet, matchCond *regexp.Regexp,
	matchAll bool) *fastOrderedIntSet {
	// Try to match a regex in the trees. For each commit we remember
	// only the part of the tree that matches the regex. In most cases
	// it is a lot less memory and CPU hungry than running regexes on
	// the full commit manifests. In the matchAll case we instead
	// select commits that nowhere match the opposite condition.
	match := func(s string) bool { return matchCond.MatchString(s) }
	if matchAll {
		match = func(s string) bool { return !matchCond.MatchString(s) }
	}
	matchTrees := make(map[string]*PathMap)
	result := newFastOrderedIntSet()
	lastEvent := selMax(preselection)
	for i, event := range rs.chosen().events {
		c, ok := event.(*Commit)
		if !ok {
			continue
		}
		if i > lastEvent {
			break
		}
		var tree *PathMap
		parents := c.parents()
		if len(parents) == 0 {
			tree = newPathMap()
		} else {
			parentTree, ok := matchTrees[parents[0].getMark()]
			if !ok {
				panic(fmt.Sprintf("commit tree missing: %s",
					parents[0].getMark()))
			}
			tree = parentTree.snapshot()
		}
		for _, fileop := range c.operations() {
			if fileop.op == opM && match(fileop.Path) {
				tree.set(fileop.Path, true)
			} else if fileop.op == opC && match(fileop.Target) {
				tree.set(fileop.Target, true)
			} else if fileop.op == opR && match(fileop.Target) {
				tree.set(fileop.Target, true)
			} else if fileop.op == opD && match(fileop.Path) {
				tree.remove(fileop.Path)
			} else if fileop.op == opR && match(fileop.Source) {
				tree.remove(fileop.Source)
			} else if fileop.op == deleteall {
				tree = newPathMap()
			}
		}
		matchTrees[c.mark] = tree
		if tree.isEmpty() == matchAll {
			result.Add(i)
		}
	}
	return result
}

// Does an event contain something that looks like a legacy reference?
func (rs *Reposurgeon) hasReference(event Event) bool {
	repo := rs.chosen()
	repo.dollarOnce.Do(func() { repo.parseDollarCookies() })
	var text string
	type commentGetter interface{ getComment() string }
	if g, ok := event.(commentGetter); ok {
		text = g.getComment()
	} else {
		return false
	}
	if repo.vcs == nil {
		return false
	}
	result := repo.vcs.hasReference([]byte(text))
	return result
}

func (rs *Reposurgeon) visibilityTypeletters() map[rune]func(int) bool {
	type decodable interface {
		decodable() bool
	}
	type alldel interface {
		alldeletes(...rune) bool
	}
	e := func(i int) Event {
		return rs.chosen().events[i]
	}
	// Available: AEGJKQSVWXY
	return map[rune]func(int) bool{
		'B': func(i int) bool { _, ok := e(i).(*Blob); return ok },
		'C': func(i int) bool { _, ok := e(i).(*Commit); return ok },
		'T': func(i int) bool { _, ok := e(i).(*Tag); return ok },
		'R': func(i int) bool { _, ok := e(i).(*Reset); return ok },
		'P': func(i int) bool { _, ok := e(i).(*Passthrough); return ok },
		'H': func(i int) bool { c, ok := e(i).(*Commit); return ok && !c.hasChildren() },
		'O': func(i int) bool { c, ok := e(i).(*Commit); return ok && !c.hasParents() },
		'U': func(i int) bool { c, ok := e(i).(*Commit); return ok && c.hasCallouts() },
		'Z': func(i int) bool { c, ok := e(i).(*Commit); return ok && len(c.operations()) == 0 },
		'M': func(i int) bool { c, ok := e(i).(*Commit); return ok && len(c.parents()) > 1 },
		'F': func(i int) bool { c, ok := e(i).(*Commit); return ok && len(c.children()) > 1 },
		'L': func(i int) bool { c, ok := e(i).(*Commit); return ok && unclean.MatchString(c.Comment) },
		'I': func(i int) bool { p, ok := e(i).(decodable); return ok && !p.decodable() },
		'D': func(i int) bool { p, ok := e(i).(alldel); return ok && p.alldeletes() },
		'N': func(i int) bool { return rs.hasReference(e(i)) },
	}
}

func (rs *Reposurgeon) polyrangeInitials() string {
	return rs.SelectionParser.polyrangeInitials() + ":<"
}

// Does the input look like a possible polyrange?
func (rs *Reposurgeon) possiblePolyrange() bool {
	if !rs.SelectionParser.possiblePolyrange() {
		return false
	}
	// Avoid having an input redirect mistaken for the start of a literal.
	// This might break if a command can ever have both input and output
	// redirects.
	if rs.peek() == '<' && !strings.ContainsRune(rs.line, '>') {
		return false
	}
	return true
}

var markRE = regexp.MustCompile(`^:[0-9]+`)

func (rs *Reposurgeon) parseAtom() selEvaluator {
	selection := rs.SelectionParser.parseAtom()
	if selection == nil {
		// Mark references
		markref := markRE.FindString(rs.line)
		if len(markref) > 0 {
			rs.line = rs.line[len(markref):]
			selection = func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
				return rs.evalAtomMark(x, s, markref)
			}
		} else if rs.peek() == ':' {
			panic(throw("command", "malformed mark"))
		} else if rs.peek() == '<' {
			rs.pop()
			closer := strings.IndexRune(rs.line, '>')
			if closer == -1 {
				panic(throw("command", "reference improperly terminated. '%s'", rs.line))
			}
			ref := rs.line[:closer]
			rs.line = rs.line[closer+1:]
			selection = func(x selEvalState, s *fastOrderedIntSet) *fastOrderedIntSet {
				return rs.evalAtomRef(x, s, ref)
			}
		}
	}
	return selection
}

func (rs *Reposurgeon) evalAtomMark(state selEvalState,
	preselection *fastOrderedIntSet, markref string) *fastOrderedIntSet {
	events := rs.chosen().events
	for i := 0; i < state.nItems(); i++ {
		e := events[i]
		if val, ok := getAttr(e, "mark"); ok && val == markref {
			return newFastOrderedIntSet(i)
		} else if val, ok := getAttr(e, "committish"); ok && val == markref {
			return newFastOrderedIntSet(i)
		}
	}
	panic(throw("command", "mark %s not found.", markref))
}

func (rs *Reposurgeon) evalAtomRef(state selEvalState,
	preselection *fastOrderedIntSet, ref string) *fastOrderedIntSet {
	selection := newFastOrderedIntSet()
	lookup := rs.chosen().named(ref)
	if lookup != nil {
		// Choose to include *all* commits matching the date.
		// Alas, results in unfortunate behavior when a date
		// with multiple commits ends a span.
		selection = selection.Union(newFastOrderedIntSet(lookup...))
	} else {
		panic(throw("command", "couldn't match a name at <%s>", ref))
	}
	return selection
}

// Perform a text search of items.
func (rs *Reposurgeon) evalTextSearch(state selEvalState,
	preselection *fastOrderedIntSet,
	search *regexp.Regexp, modifiers string) *fastOrderedIntSet {
	matchers := newFastOrderedIntSet()
	// values ("author", "Branch", etc.) in 'searchableAttrs' and keys in
	// 'extractors' (below) must exactly match spelling and case of fields
	// in structures being interrogated since reflection is used both to
	// check that the structure has such a field and to retrieve the
	// field's value (the spelling and case requirement is true even for
	// extractors which pull field values directly, without going through
	// getAttr())
	searchableAttrs := map[rune]string{
		'a': "author",     // commit
		'b': "Branch",     // commit
		'c': "Comment",    // commit or tag
		'C': "committer",  // commit
		'r': "committish", // tag or reset
		'p': "text",       // passthrough
		't': "tagger",     // tag
		'n': "name",       // tag
	}
	var searchIn []string
	for _, v := range searchableAttrs {
		searchIn = append(searchIn, v)
	}
	exattr := func(e Event, k string) string {
		if s, ok := getAttr(e, k); ok {
			return s
		}
		panic(fmt.Sprintf("no %q in %T", k, e))
	}
	extractors := map[string]func(Event) string{
		"author": func(e Event) string {
			if c, ok := e.(*Commit); ok && len(c.authors) != 0 {
				return c.authors[0].who()
			}
			panic(fmt.Sprintf(`no "author" in %T`, e))
		},
		"Branch":  func(e Event) string { return exattr(e, "Branch") },
		"Comment": func(e Event) string { return exattr(e, "Comment") },
		"committer": func(e Event) string {
			if c, ok := e.(*Commit); ok {
				return c.committer.who()
			}
			panic(fmt.Sprintf(`no "committer" in %T`, e))
		},
		"committish": func(e Event) string { return exattr(e, "committish") },
		"text":       func(e Event) string { return exattr(e, "text") },
		"tagger": func(e Event) string {
			if t, ok := e.(*Tag); ok {
				return t.tagger.who()
			}
			panic(fmt.Sprintf(`no "tagger" in %T`, e))
		},
		"name": func(e Event) string { return exattr(e, "name") },
	}
	checkAuthors := false
	checkBlobs := false
	checkBranch := false
	if len(modifiers) != 0 {
		searchIn = []string{}
		for _, m := range modifiers {
			if m == 'a' {
				checkAuthors = true
			} else if m == 'B' {
				checkBlobs = true
			} else if _, ok := searchableAttrs[m]; ok {
				searchIn = append(searchIn, searchableAttrs[m])
				if m == 'b' {
					checkBranch = true
				}
			} else {
				panic(throw("command", "unknown textsearch flag"))
			}
		}
	}
	events := rs.chosen().events
	it := preselection.Iterator()
	for it.Next() {
		e := events[it.Value()]
		if checkBranch {
			if t, ok := e.(*Tag); ok {
				e = rs.repo.markToEvent(t.committish)
			} else if b, ok := e.(*Blob); ok {
				for ci := it.Value(); ci < len(events); ci++ {
					possible := events[ci]
					if c, ok := possible.(*Commit); ok &&
						c.references(b.mark) {
						// FIXME: Won't find multiple
						// references
						e = possible
						break
					}
				}
			}
		}
		for _, searchable := range searchIn {
			if _, ok := getAttr(e, searchable); ok {
				key := extractors[searchable](e)
				if len(key) != 0 && search.MatchString(key) {
					matchers.Add(it.Value())
				}
			}
		}
		if checkAuthors {
			if c, ok := e.(*Commit); ok {
				for _, a := range c.authors {
					if search.MatchString(a.String()) {
						matchers.Add(it.Value())
						break
					}
				}
			}
		}
		if checkBlobs {
			if b, ok := e.(*Blob); ok &&
				search.MatchString(string(b.getContent())) {
				matchers.Add(it.Value())
			}
		}
	}
	return matchers
}

func (rs *Reposurgeon) functions() map[string]selEvaluator {
	return map[string]selEvaluator{
		"chn": func(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
			return rs.chnHandler(state, subarg)
		},
		"dsc": func(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
			return rs.dscHandler(state, subarg)
		},
		"par": func(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
			return rs.parHandler(state, subarg)
		},
		"anc": func(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
			return rs.ancHandler(state, subarg)
		},
	}
}

// All children of commits in the selection set.
func (rs *Reposurgeon) chnHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	return rs.accumulateCommits(subarg,
		func(c *Commit) []CommitLike { return c.children() }, false)
}

// All descendants of a selection set, recursively.
func (rs *Reposurgeon) dscHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	return rs.accumulateCommits(subarg,
		func(c *Commit) []CommitLike { return c.children() }, true)
}

// All parents of a selection set.
func (rs *Reposurgeon) parHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	return rs.accumulateCommits(subarg,
		func(c *Commit) []CommitLike { return c.parents() }, false)
}

// All ancestors of a selection set, recursively.
func (rs *Reposurgeon) ancHandler(state selEvalState, subarg *fastOrderedIntSet) *fastOrderedIntSet {
	return rs.accumulateCommits(subarg,
		func(c *Commit) []CommitLike { return c.parents() }, true)
}

func (rs *Reposurgeon) accumulateCommits(subarg *fastOrderedIntSet,
	operation func(*Commit) []CommitLike, recurse bool) *fastOrderedIntSet {
	repo := rs.chosen()
	commits := repo.commits(newOrderedIntSet(subarg.Values()...))
	if !recurse {
		result := newFastOrderedIntSet()
		for _, commit := range commits {
			for _, x := range operation(commit) {
				result.Add(repo.eventToIndex(x))
			}
		}
		return result
	}
	result := newFastOrderedIntSet(subarg.Values()...)
	// Populate the queue with selected commits
	var queue []CommitLike
	for _, c := range commits {
		queue = append(queue, c)
	}
	// Breadth-first traversal of the graph
	for len(queue) != 0 {
		popped := queue[0].(*Commit)
		queue = queue[1:]
		for _, commit := range operation(popped) {
			ind := repo.eventToIndex(commit)
			if !result.Contains(ind) {
				result.Add(ind)
				queue = append(queue, commit)
			}
		}
	}
	return result
}

//
// Helpers
//

// Generate a repository report on all objects with a specified display method.
func (rs *Reposurgeon) reportSelect(parse *LineParse, display func(*LineParse, int, Event) string) {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return
	}
	repo := rs.chosen()
	selection := rs.selection
	if selection == nil {
		selection = repo.all()
	}
	for _, eventid := range selection {
		summary := display(parse, eventid, repo.events[eventid])
		if summary != "" {
			if strings.HasSuffix(summary, "\n") {
				fmt.Fprint(parse.stdout, summary)
			} else {
				fmt.Fprintln(parse.stdout, summary)
			}
		}
		if control.getAbort() {
			break
		}
	}
}

// Grab a whitespace-delimited token from the front of the line.
func popToken(line string) (string, string) {
	tok := ""
	line = strings.TrimLeft(line, " \n\t")
	for {
		if line == "" || line[0] == ' ' || line[0] == '\t' {
			break
		} else {
			tok += line[:1]
			line = line[1:]
		}
	}
	line = strings.TrimLeft(line, " \n\t")
	return tok, line
}

func (commit *Commit) findSuccessors(path string) []string {
	var here []string
	for _, child := range commit.children() {
		childCommit, ok := child.(*Commit)
		if !ok {
			continue
		}
		for _, fileop := range childCommit.operations() {
			if fileop.op == opM && fileop.Path == path {
				here = append(here, childCommit.mark)
			}
		}
		here = append(here, childCommit.findSuccessors(path)...)
	}
	return here
}

// edit mailboxizes and edits the non-blobs in the selection
// Assumes that rs.chosen() and selection are not None
func (rs *Reposurgeon) edit(selection orderedIntSet, line string) {
	parse := rs.newLineParse(line, orderedStringSet{"stdin", "stdout"})
	defer parse.Closem()
	editor := os.Getenv("EDITOR")
	if parse.line != "" {
		editor = parse.line
	}
	if editor == "" {
		croak("you have not specified an editor and $EDITOR is unset")
		// Fallback on /usr/bin/editor on Debian and
		// derivatives.  See
		// https://www.debian.org/doc/debian-policy/#editors-and-pagers
		editor = "/usr/bin/editor"
		realEditor, err := filepath.EvalSymlinks(editor)
		if err != nil {
			croak(err.Error())
			return
		}
		if islink(editor) && exists(realEditor) {
			respond("using %s -> %s instead", editor, realEditor)

		} else {
			return
		}
		control.setAbort(false)
	}
	// Special case: user selected a single blob
	if len(selection) == 1 {
		singleton := rs.chosen().events[selection[0]]
		if blob, ok := singleton.(*Blob); ok {
			for _, commit := range rs.chosen().commits(nil) {
				for _, fileop := range commit.operations() {
					if fileop.op == opM && fileop.ref == singleton.getMark() {
						if len(commit.findSuccessors(fileop.Path)) > 0 {
							croak("beware: not the last 'M %s' on its branch", fileop.Path)
						}
						break
					}
				}
			}
			runProcess(editor+" "+blob.materialize(), "editing")
			return
		}
		// Fall through

		file, err1 := ioutil.TempFile(".", "rse")
		if err1 != nil {
			croak("creating tempfile for edit: %v", err1)
			return
		}
		defer os.Remove(file.Name())
		for _, i := range selection {
			event := rs.chosen().events[i]
			switch event.(type) {
			case *Commit:
				file.WriteString(event.(*Commit).emailOut(nil, i, nil))
			case *Tag:
				file.WriteString(event.(*Tag).emailOut(nil, i, nil))
			}
		}
		file.Close()
		cmd := exec.Command(editor, file.Name())
		cmd.Stdin = parse.stdin
		cmd.Stdout = parse.stdout
		cmd.Stderr = os.Stderr
		err := cmd.Run()
		if err != nil {
			croak("running editor: %v", err)
			return
		}
		rs.DoMsgin("<" + file.Name())
	}
}

// Filter commit metadata (and possibly blobs) through a specified hook.
func (rs *Reposurgeon) dataTraverse(prompt string, hook func(string) string, attributes orderedStringSet, safety bool, quiet bool) {
	blobs := false
	nonblobs := false
	for _, ei := range rs.selection {
		event := rs.chosen().events[ei]
		switch event.(type) {
		case *Blob:
			blobs = true
		default:
			nonblobs = true
		}
		if blobs && nonblobs {
			break
		}
	}
	// Try to prevent user from shooting self in foot
	if safety && blobs && nonblobs {
		croak("cannot transform blobs and nonblobs in same command")
		return
	}
	// If user is transforming blobs, transform all inlines within the range.
	// This is an expensive step because of the sort; avoid doing it
	// when possible.
	if blobs && rs.chosen().inlines > 0 {
		for ei := rs.selection[0]; ei <= rs.selection[len(rs.selection)-1]; ei++ {
			event := rs.chosen().events[ei]
			if commit, ok := event.(*Commit); ok {
				for _, fileop := range commit.operations() {
					if len(fileop.inline) > 0 {
						rs.selection = append(rs.selection, ei)
					}
				}
			}
		}
		rs.selection.Sort()
	}
	if !quiet {
		control.baton.startProgress(prompt, uint64(len(rs.selection)))
	}
	var countlock sync.Mutex
	altered := 0
	safebump := func() {
		countlock.Lock()
		altered++
		countlock.Unlock()
	}
	rs.chosen().walkEvents(rs.selection, func(idx int, event Event) {
		if tag, ok := event.(*Tag); ok {
			if nonblobs {
				oldcomment := tag.Comment
				tag.Comment = hook(tag.Comment)
				anychanged := (oldcomment != tag.Comment)
				oldtagger := tag.tagger.who()
				newtagger := hook(oldtagger)
				if oldtagger != newtagger {
					newtagger += " " + tag.tagger.date.String()
					attrib, err := newAttribution(newtagger)
					if err != nil {
						panic(throw("command", "in data traverse of tag: %v", err))
					}
					tag.tagger = attrib
					anychanged = anychanged || true
				}
				if anychanged {
					safebump()
				}
			}
		} else if commit, ok := event.(*Commit); ok {
			if nonblobs {
				anychanged := false
				if attributes.Contains("c") {
					oldcomment := commit.Comment
					commit.Comment = hook(commit.Comment)
					if oldcomment != commit.Comment {
						anychanged = true
					}
				}
				if attributes.Contains("C") {
					oldcommitter := commit.committer.who()
					newcommitter := hook(oldcommitter)
					changed := (oldcommitter != newcommitter)
					if changed {
						newcommitter += " " + commit.committer.date.String()
						attrib, err := newAttribution(newcommitter)
						if err != nil {
							panic(throw("command", "in data traverse of commit: %v", err))
						}
						commit.committer = *attrib
						anychanged = true
					}
				}
				if attributes.Contains("a") {
					for i := range commit.authors {
						oldauthor := commit.authors[i].who()
						newauthor := hook(oldauthor)
						if oldauthor != newauthor {
							newauthor += " " + commit.authors[i].date.String()
							attrib, err := newAttribution(newauthor)
							if err != nil {
								panic(throw("command", "in data traverse of commit: %v", err))
							}
							commit.authors[i] = *attrib
							anychanged = true
						}
					}
				}
				if anychanged {
					safebump()
				}
			}
			if blobs {
				for _, fileop := range commit.operations() {
					if len(fileop.inline) > 0 {
						oldinline := fileop.inline
						fileop.inline = []byte(hook(string(fileop.inline)))
						if !bytes.Equal(fileop.inline, oldinline) {
							safebump()
						}
					}
				}
			}
		} else if blob, ok := event.(*Blob); ok {
			content := string(blob.getContent())
			modified := hook(content)
			if content != modified {
				blob.setContent([]byte(modified), noOffset)
				safebump()
			}
		}
		if !quiet {
			control.baton.percentProgress(uint64(idx))
		}
	})
	if !quiet {
		control.baton.endProgress()
	} else {
		respond("%d items modified by %s.", altered, strings.ToLower(prompt))
	}
}

//
// Command implementation begins here
//

func (rs *Reposurgeon) HelpNews() {
	rs.helpOutput(`
4.0 differences from the Python 3.x versions:

1. whoami() can get useful idenity data out of .muttrc files.
2. Regular expressions use Go syntax rather than Python, except that.
   group references are still Pythonically led with a backslash rather
   than Goishly with $; this is to avoid a collision with $ used as a
   leader for script arguments.
   Also, regexp substitutions are always 'g' (all copies).
3. We now interpret Subversion $Rev$ and $LastChangedRev$ cookies.
4. git hooks are preserved through surgery.
5. The set of structure fieldnames that can be used with setfield is smaller.
   However, all fieldnames for which support was documented will still work.
6. Subversion dump streams must now be a continuous span of revitions 
   starting from zero (restriction added for performance reasons).
7. The branchify_map command is now named branchmap.
`)
}

//
// On-line help and instrumentation
//
func (rs *Reposurgeon) HelpResolve() {
	rs.helpOutput(`
Does nothing but resolve a selection-set expression
and report the resulting event-number set to standard
output. The remainder of the line after the command is used
as a label for the output.

Implemented mainly for regression testing, but may be useful
for exploring the selection-set language.
`)
}

// Display the set of event numbers generated by a selection set.
func (rs *Reposurgeon) DoResolve(line string) bool {
	if rs.selection == nil {
		respond("No selection\n")
	} else {
		oneOrigin := newOrderedIntSet()
		for _, i := range rs.selection {
			oneOrigin.Add(i + 1)
		}
		if line != "" {
			control.baton.printLogString(fmt.Sprintf("%s: %v\n", line, oneOrigin))
		} else {
			control.baton.printLogString(fmt.Sprintf("%v\n", oneOrigin))
		}
	}
	return false
}

func (rs *Reposurgeon) HelpAssign() {
	rs.helpOutput(`
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
`)
}

func (rs *Reposurgeon) DoAssign(line string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen.")
		return false
	}
	if rs.selection == nil {
		if line != "" {
			croak("No selection")
			return false
		}
		for n, v := range repo.assignments {
			respond(fmt.Sprintf("%s = %v", n, v))
		}
		return false
	}
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	name := strings.TrimSpace(parse.line)
	for key := range repo.assignments {
		if key == name {
			croak("%s has already been set", name)
			return false
		}
	}
	//FIXME: Incorrect - could collide with an old assignment.
	//The logic of named needs to change.
	if repo.named(name) != nil {
		croak("%s conflicts with a branch, tag, legacy-ID, or date", name)
		return false
	} else if parse.options.Contains("--singleton") && len(rs.selection) != 1 {
		croak("a singleton selection was required here")
		return false
	} else {
		if repo.assignments == nil {
			repo.assignments = make(map[string]orderedIntSet)
		}
		repo.assignments[name] = rs.selection

	}
	return false
}

func (rs *Reposurgeon) HelpUnassign() {
	rs.helpOutput(`
Unassign a symbolic name.  Throws an error if the name is not assigned.
Tab-completes on the list of defined names.
`)
}

func (rs *Reposurgeon) CompleteUnassign(text string) []string {
	repo := rs.chosen()
	out := make([]string, 0)
	if repo != nil {
		for key := range repo.assignments {
			out = append(out, key)
		}
	}
	sort.Strings(out)
	return out
}

func (rs *Reposurgeon) DoUnassign(line string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen.")
		return false
	}
	if rs.selection != nil {
		croak("cannot take a selection")
		return false
	}
	name := strings.TrimSpace(line)
	if _, ok := repo.assignments[name]; ok {
		delete(repo.assignments, name)
	} else {
		croak("%s has not been set", name)
		return false
	}
	return false
}

func (rs *Reposurgeon) HelpNames() {
	rs.helpOutput(`
List all known symbolic names of branches and tags. Supports > redirection.
`)
}

func (rs *Reposurgeon) DoNames(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	branches := rs.chosen().branchset()
	//sortbranches.Sort()
	for _, branch := range branches {
		fmt.Fprintf(parse.stdout, "branch %s\n", branch)
	}
	for _, event := range rs.chosen().events {
		if tag, ok := event.(*Tag); ok {
			fmt.Fprintf(parse.stdout, "tag    %s\n", tag.name)

		}
	}
	return false
}

func (rs *Reposurgeon) HelpHistory() {
	rs.helpOutput(`
Dump your command list from this session so far.
`)
}

func (rs *Reposurgeon) DoHistory(_line string) bool {
	for _, line := range rs.history {
		fmt.Println(line)
	}
	return false
}

func (rs *Reposurgeon) HelpCoverage() {
	rs.helpOutput("Display the coverage-case set (developer instrumentation).")
}

// Display the coverage-case set (developer instrumentation).
func (rs *Reposurgeon) DoCoverage(lineIn string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen.")
		return false
	}
	parse := rs.newLineParse(lineIn, orderedStringSet{"stdout"})
	defer parse.Closem()
	for _, commit := range repo.commits(nil) {
		commit.fileopDump()
	}
	repo.caseCoverage.Sort()
	fmt.Fprintf(parse.stdout, "Case coverage: %v\n", repo.caseCoverage)
	return false
}

func (rs *Reposurgeon) HelpIndex() {
	rs.helpOutput(`
Display four columns of info on selected objects: their number, their
type, the associate mark (or '-' if no mark) and a summary field
varying by type.  For a branch or tag it's the reference; for a commit
it's the commit branch; for a blob it's the repository path of the
file in the blob.  Supports > redirection.
`)
}

// Generate a summary listing of objects.
func (rs *Reposurgeon) DoIndex(lineIn string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen.")
		return false
	}
	// We could do all this logic using reportSelect() and index() methods
	// in the objects, but that would have two disadvantages.  First, we'd
	// get a default-set computation we don't want.  Second, for this
	// function it's helpful to have the method strings close together so
	// we can maintain columnation.
	selection := rs.selection
	if rs.selection == nil {
		selection = make([]int, 0)
		for _, eventid := range repo.all() {
			event := repo.events[eventid]
			_, isblob := event.(*Blob)
			if !isblob {
				selection = append(selection, eventid)
			}
		}
	}
	parse := rs.newLineParse(lineIn, orderedStringSet{"stdout"})
	defer parse.Closem()
	for _, eventid := range selection {
		event := repo.events[eventid]
		switch e := event.(type) {
		case *Blob:
			fmt.Fprintf(parse.stdout, "%6d blob   %6s    %s\n", eventid+1, e.mark, strings.Join(e.paths(nil), " "))
		case *Commit:
			mark := e.mark
			if mark == "" {
				mark = "-"
			}
			fmt.Fprintf(parse.stdout, "%6d commit %6s    %s\n", eventid+1, mark, e.Branch)
		case *Tag:
			fmt.Fprintf(parse.stdout, "%6d tag    %6s    %4s\n", eventid+1, e.committish, e.name)
		case *Reset:
			committish := e.committish
			if committish == "" {
				committish = "-"
			}
			fmt.Fprintf(parse.stdout, "%6d branch %6s    %s\n", eventid+1, committish, e.ref)
		default:
			fmt.Fprintf(parse.stdout, "     ?             -    %s", e)
		}
	}
	return false
}

func saveAllProfiles(name string) {
	profiles := pprof.Profiles()
	for _, profile := range profiles {
		saveProfile(profile.Name(), name)
	}
}

func saveProfile(subject string, name string) {
	filename := fmt.Sprintf("%s.%s.prof", name, subject)
	f, err := os.Create(filename)
	if err != nil {
		croak("failed to create file %#v [%s]", filename, err)
	} else {
		pprof.Lookup(subject).WriteTo(f, 0)
		respond("%s profile saved to %#v", subject, filename)
	}
}

func startCPUProfiling(name string) {
	filename := name + ".cpu.prof"
	f, err := os.Create(filename)
	if err != nil {
		croak("failed to create file %#v [%s]", filename, err)
	} else {
		pprof.StartCPUProfile(f)
		respond("cpu profiling enabled.")
	}
}

func stopCPUProfiling() {
	pprof.StopCPUProfile()
}

func startTracing(name string) {
	filename := name + ".trace.prof"
	f, err := os.Create(filename)
	if err != nil {
		croak("failed to create file %#v [%s]", filename, err)
	} else {
		trace.Start(f)
		respond("tracing enabled.")
	}
}

func stopTracing() {
	trace.Stop()
}

func (rs *Reposurgeon) HelpProfile() {
	rs.helpOutput(`
DESCRIPTION
    Manages profiling.

SYNOPSIS
    profile [<verb>] [<subject>]

VERBS
    live
	profile live [<port>]
	    Starts an http server on the specified port which serves
	    the profiling data. If no port is specified, it defaults
	    to port 1234. Use in combination with pprof:
		go tool pprof -http=":8080" http://localhost:1234/debug/pprof/<profile>

    start
	profile start <profile> <filename>
	    Starts the named profiler, and tells it to save to the
	    named file, which will be overwritten. Currently only the
	    cpu profiler requires you to specifically start it; all
	    the others start automatically.

    save
	profile save <profile> <filename>
	    Saves the data from the named profiler to the named file,
	    which will be overwritten.
`)
}

func (rs *Reposurgeon) DoProfile(line string) bool {
	profiles := pprof.Profiles()
	names := newStringSet()
	for _, profile := range profiles {
		names.Add(profile.Name())
	}
	names.Add("cpu")
	names.Add("trace")
	names.Add("all")
	if line == "" {
		respond("The available profiles are %v", names)
	} else {
		verb, line := popToken(line)
		switch verb {
		case "live":
			port, _ := popToken(line)
			if port == "" {
				port = "1234"
			}
			go func() {
				http.ListenAndServe("localhost:"+port, nil)
			}()
			respond("pprof server started on http://localhost:%s/debug/pprof", port)
		case "start":
			subject, line := popToken(line)
			if !names.Contains(subject) {
				croak("I don't recognize %#v as a profile name. The names I do recognize are %v.", subject, names)
			} else if subject == "all" {
				control.profilename = line
				startCPUProfiling(line)
				startTracing(line)
			} else if subject == "cpu" {
				startCPUProfiling(line)
			} else if subject == "trace" {
				startTracing(line)
			} else {
				respond("The %s profile starts automatically when you start reposurgeon.", subject)
			}
		case "save":
			subject, line := popToken(line)
			filename, line := popToken(line)
			fmt.Fprintf(os.Stderr, "save; subject=%#v, filename=%#v\n", subject, filename)
			if !names.Contains(subject) {
				croak("I don't recognize %#v as a profile name. The names I do recognize are %v.", subject, names)
			} else if subject == "all" {
				runtime.GC()
				stopTracing()
				stopCPUProfiling()
				for subject := range names.Iterate() {
					if subject != "all" && subject != "cpu" {
						saveProfile(subject, filename)
					}
				}
				respond("all profiling stopped.")
			} else if subject == "cpu" {
				stopCPUProfiling()
				respond("cpu profiling stopped.")
			} else if subject == "trace" {
				stopTracing()
				respond("tracing stopped.")
			} else {
				saveProfile(subject, filename)
				respond("%s profiling stopped.", subject)
			}
		default:
			croak("I don't know how to %s. Possible verbs are [live, start, save].", verb)
		}
	}
	return false
}

func (rs *Reposurgeon) HelpTiming() {
	rs.helpOutput(`
Report phase-timing results from repository analysis.

If the command has following text, this creates a new, named time mark
that will be visible in a later report; this may be useful during 
long-running conversion recipes.
`)
}

// Report repo-analysis times
func (rs *Reposurgeon) DoTiming(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	if parse.line != "" {
		rs.chosen().timings = append(rs.chosen().timings, TimeMark{line, time.Now()})
	}
	rs.repo.dumptimes(parse.stdout)
	return false
}

func (rs *Reposurgeon) HelpMemory() {
	rs.helpOutput(`
Report memory usage.  Runs a garbage-collect before reporting so the figure will better relect
storage currently held in loaded repositories; this will not affect the reported high-water
mark.
`)
}

func (rs *Reposurgeon) DoMemory(line string) bool {
	var memStats runtime.MemStats
	debug.FreeOSMemory()
	runtime.ReadMemStats(&memStats)
	respond("     Total heap: %.2fMB  High water: %.2fMB\n",
		float64(memStats.HeapAlloc)/1e6, float64(memStats.TotalAlloc)/1e6)
	return false
}

//
// Information-gathering
//
func (rs *Reposurgeon) HelpStats() {
	rs.helpOutput(`
Report size statistics and import/export method information of the
currently chosen repository. Supports > redirection.
`)
}

// Report information on repositories.
func (rs *Reposurgeon) DoStats(line string) bool {
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	if parse.line == "" {
		if rs.chosen() == nil {
			croak("no repo has been chosen.")
			return false
		}
		parse.line = rs.chosen().name
	}
	for _, name := range parse.Tokens() {
		repo := rs.repoByName(name)
		if repo == nil {
			croak("no such repo as %s", name)
			return false
		}
		var blobs, commits, tags, resets, passthroughs int
		for _, event := range repo.events {
			switch event.(type) {
			case *Blob:
				blobs++
			case *Tag:
				tags++
			case *Reset:
				resets++
			case *Passthrough:
				passthroughs++
			case *Commit:
				commits++
			}
		}
		fmt.Fprintf(parse.stdout, "%s: %.0fK, %d events, %d blobs, %d commits, %d tags, %d resets, %s.\n",
			repo.name, float64(repo.size())/1000.0, len(repo.events),
			blobs, commits, tags, resets,
			rfc3339(repo.readtime))
		if repo.sourcedir != "" {
			fmt.Fprintf(parse.stdout, "  Loaded from %s\n", repo.sourcedir)
		}
		//if repo.vcs {
		//    parse.stdout.WriteString(polystr(repo.vcs) + "\n")
	}
	return false
}

func (rs *Reposurgeon) HelpCount() {
	rs.helpOutput(`
Report a count of items in the selection set. Default set is everything
in the currently-selected repo. Supports > redirection.
`)
}
func (rs *Reposurgeon) DoCount(lineIn string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	parse := rs.newLineParse(lineIn, orderedStringSet{"stdout"})
	defer parse.Closem()
	fmt.Fprintf(parse.stdout, "%d\n", len(selection))
	return false
}

func (rs *Reposurgeon) HelpList() {
	rs.helpOutput(`
Display commits in a human-friendly format; the first column is raw
event numbers, the second a timestamp in local time. If the repository
has legacy IDs, they will be displayed in the third column. The
leading portion of the comment follows. Supports > redirection.
`)
}

// Generate a human-friendly listing of objects.
func (rs *Reposurgeon) DoList(lineIn string) bool {
	parse := rs.newLineParse(lineIn, orderedStringSet{"stdout"})
	defer parse.Closem()
	w := screenwidth()
	modifiers := orderedStringSet{}
	f := func(p *LineParse, i int, e Event) string {
		c, ok := e.(*Commit)
		if ok {
			return c.lister(modifiers, i, w)
		}
		return ""
	}
	rs.reportSelect(parse, f)
	return false
}

func (rs *Reposurgeon) HelpTip() {
	rs.helpOutput(`
Display the branch tip names associated with commits in the selection
set.  These will not necessarily be the same as their branch fields
(which will often be tag names if the repo contains either annotated
or lightweight tags).

If a commit is at a branch tip, its tip is its branch name.  If it has
only one child, its tip is the child's tip.  If it has multiple children,
then if there is a child with a matching branch name its tip is the
child's tip.  Otherwise this function throws a recoverable error.

Supports > redirection.
`)
}

// Generate a human-friendly listing of objects.
func (rs *Reposurgeon) DoTip(lineIn string) bool {
	parse := rs.newLineParse(lineIn, orderedStringSet{"stdout"})
	defer parse.Closem()
	w := screenwidth()
	modifiers := orderedStringSet{}
	f := func(p *LineParse, i int, e Event) string {
		c, ok := e.(*Commit)
		if ok {
			return c.tip(modifiers, i, w)
		}
		return ""
	}
	rs.reportSelect(parse, f)
	return false
}

func (rs *Reposurgeon) HelpTags() {
	rs.helpOutput(`
Display tags and resets: three fields, an event number and a type and a name.
Branch tip commits associated with tags are also displayed with the type
field 'commit'. Supports > redirection.
`)
}

func (rs *Reposurgeon) DoTags(lineIn string) bool {
	parse := rs.newLineParse(lineIn, orderedStringSet{"stdout"})
	defer parse.Closem()
	w := screenwidth()
	modifiers := orderedStringSet{}
	f := func(p *LineParse, i int, e Event) string {
		// this is pretty stupid; pretend you didn't see it
		switch v := e.(type) {
		case *Commit:
			return v.tags(modifiers, i, w)
		case *Reset:
			return v.tags(modifiers, i, w)
		case *Tag:
			return v.tags(modifiers, i, w)
		default:
			return ""
		}
	}
	rs.reportSelect(parse, f)
	return false
}

func (rs *Reposurgeon) HelpStamp() {
	rs.helpOutput(`
Display full action stamps correponding to commits in a select.
The stamp is followed by the first line of the commit message.
Supports > redirection.
`)
}

func (rs *Reposurgeon) DoStamp(lineIn string) bool {
	parse := rs.newLineParse(lineIn, orderedStringSet{"stdout"})
	defer parse.Closem()
	w := screenwidth()
	modifiers := orderedStringSet{}
	f := func(p *LineParse, i int, e Event) string {
		// this is pretty stupid; pretend you didn't see it
		switch v := e.(type) {
		case *Commit:
			return v.stamp(modifiers, i, w)
		case *Tag:
			return v.stamp(modifiers, i, w)
		default:
			return ""
		}
	}
	rs.reportSelect(parse, f)
	return false
}

func (rs *Reposurgeon) HelpSizes() {
	rs.helpOutput(`
Print a report on data volume per branch; takes a selection set,
defaulting to all events. The numbers tally the size of uncompressed
blobs, commit and tag comments, and other metadata strings (a blob is
counted each time a commit points at it).  Not an exact measure of
storage size: intended mainly as a way to get information on how to
efficiently partition a repository that has become large enough to be
unwieldy. Supports > redirection.
`)
}

// Report branch relative sizes.
func (rs *Reposurgeon) DoSizes(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	sizes := make(map[string]int)
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	for _, i := range selection {
		if commit, ok := repo.events[i].(*Commit); ok {
			if _, ok := sizes[commit.Branch]; !ok {
				sizes[commit.Branch] = 0
			}
			sizes[commit.Branch] += len(commit.committer.String())
			for _, author := range commit.authors {
				sizes[commit.Branch] += len(author.String())
			}
			sizes[commit.Branch] += len(commit.Comment)
			for _, fileop := range commit.operations() {
				if fileop.op == opM {
					if !strings.HasPrefix(fileop.ref, ":") {
						// Skip submodule refs
						continue
					}
					ref := repo.markToEvent(fileop.ref)
					if ref == nil {
						croak("internal error: %s should be a blob reference", fileop.ref)
						continue
					}
					sizes[commit.Branch] += int(ref.(*Blob).size)
				}
			}
		} else if tag, ok := repo.events[i].(*Tag); ok {
			commit := repo.markToEvent(tag.committish).(*Commit)
			if commit == nil {
				croak("internal error: target of tag %s is nil", tag.name)
				continue
			}
			if _, ok := sizes[commit.Branch]; !ok {
				sizes[commit.Branch] = 0
			}
			sizes[commit.Branch] += len(tag.tagger.String())
			sizes[commit.Branch] += len(tag.Comment)
		}
	}
	total := 0
	for _, v := range sizes {
		total += v
	}
	sz := func(n int, s string) {
		fmt.Fprintf(parse.stdout, "%12d\t%2.2f%%\t%s\n",
			n, float64(n*100.0)/float64(total), s)
	}
	for key, val := range sizes {
		sz(val, key)
	}
	sz(total, "")
	return false
}

func (rs *Reposurgeon) HelpLint() {
	rs.helpOutput(`
Look for DAG and metadata configurations that may indicate a
problem. Presently can check for: (1) Mid-branch deletes, (2)
disconnected commits, (3) parentless commits, (4) the existance of
multiple roots, (5) committer and author IDs that don't look
well-formed as DVCS IDs, (6) multiple child links with identical
branch labels descending from the same commit, (7) time and
action-stamp collisions.

Give it the -? option for a list of available options.

Supports > redirection.
`)
}

// Look for lint in a repo.
func (rs *Reposurgeon) DoLint(line string) (StopOut bool) {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	var lintmutex sync.Mutex
	unmapped := regexp.MustCompile("^[^@]*$|^[^@]*@" + rs.chosen().uuid + "$")
	shortset := newOrderedStringSet()
	deletealls := newOrderedStringSet()
	disconnected := newOrderedStringSet()
	roots := newOrderedStringSet()
	emptyaddr := newOrderedStringSet()
	emptyname := newOrderedStringSet()
	badaddress := newOrderedStringSet()
	rs.chosen().walkEvents(selection, func(idx int, event Event) {
		commit, iscommit := event.(*Commit)
		if !iscommit {
			return
		}
		if len(commit.operations()) > 0 && commit.operations()[0].op == deleteall && commit.hasChildren() {
			lintmutex.Lock()
			deletealls.Add(fmt.Sprintf("on %s at %s", commit.Branch, commit.idMe()))
			lintmutex.Unlock()
		}
		if !commit.hasParents() && !commit.hasChildren() {
			lintmutex.Lock()
			disconnected.Add(commit.idMe())
			lintmutex.Unlock()
		} else if !commit.hasParents() {
			lintmutex.Lock()
			roots.Add(commit.idMe())
			lintmutex.Unlock()
		}
		if unmapped.MatchString(commit.committer.email) {
			lintmutex.Lock()
			shortset.Add(commit.committer.email)
			lintmutex.Unlock()
		}
		for _, person := range commit.authors {
			lintmutex.Lock()
			if unmapped.MatchString(person.email) {
				shortset.Add(person.email)
			}
			lintmutex.Unlock()
		}
		if commit.committer.email == "" {
			lintmutex.Lock()
			emptyaddr.Add(commit.idMe())
			lintmutex.Unlock()
		} else if !strings.Contains(commit.committer.email, "@") {
			lintmutex.Lock()
			badaddress.Add(commit.idMe())
			lintmutex.Unlock()
		}
		for _, author := range commit.authors {
			if author.email == "" {
				lintmutex.Lock()
				emptyaddr.Add(commit.idMe())
				lintmutex.Unlock()
			} else if !strings.Contains(author.email, "@") {
				lintmutex.Lock()
				badaddress.Add(commit.idMe())
				lintmutex.Unlock()
			}
		}
		if commit.committer.fullname == "" {
			lintmutex.Lock()
			emptyname.Add(commit.idMe())
		}
		for _, author := range commit.authors {
			if author.fullname == "" {
				lintmutex.Lock()
				emptyname.Add(commit.idMe())

			}
		}
	})
	// This check isn't done by default because these are common in Subverrsion repos
	// and do not necessarily indicate a problem.
	if parse.options.Contains("--deletealls") || parse.options.Contains("-d") {
		sort.Strings(deletealls)
		for _, item := range deletealls {
			fmt.Fprintf(parse.stdout, "mid-branch delete: %s\n", item)
		}
	}
	if parse.options.Empty() || parse.options.Contains("--connected") || parse.options.Contains("-c") {
		sort.Strings(disconnected)
		for _, item := range disconnected {
			fmt.Fprintf(parse.stdout, "disconnected commit: %s\n", item)
		}
	}
	if parse.options.Empty() || parse.options.Contains("--roots") || parse.options.Contains("-r") {
		if len(roots) > 1 {
			sort.Strings(roots)
			fmt.Fprintf(parse.stdout, "multiple root commits: %v\n", roots)
		}
	}
	if parse.options.Empty() || parse.options.Contains("--names") || parse.options.Contains("-n") {
		sort.Strings(shortset)
		for _, item := range shortset {
			fmt.Fprintf(parse.stdout, "unknown shortname: %s\n", item)
		}
		sort.Strings(emptyaddr)
		for _, item := range emptyaddr {
			fmt.Fprintf(parse.stdout, "empty committer address: %s\n", item)
		}
		sort.Strings(emptyname)
		for _, item := range emptyname {
			fmt.Fprintf(parse.stdout, "empty committer name: %s\n", item)
		}
		sort.Strings(badaddress)
		for _, item := range badaddress {
			fmt.Fprintf(parse.stdout, "email address missing @: %s\n", item)
		}
	}
	if parse.options.Empty() || parse.options.Contains("--uniqueness") || parse.options.Contains("-u") {
		rs.chosen().checkUniqueness(true, func(s string) {
			fmt.Fprint(parse.stdout, "reposurgeon: "+s+"\n")
		})
	}
	if parse.options.Contains("--options") || parse.options.Contains("-?") {
		fmt.Print(`\
--deletealls    -d     report mid-branch deletealls
--connected     -c     report disconnected commits
--roots         -r     report on multiple roots
--attributions  -a     report on anomalies in usernames and attributions
--uniqueness    -u     report on collisions among action stamps
--options       -?     list available options\
`)
	}
	return false
}

//
// Housekeeping
//
func (rs *Reposurgeon) HelpPrefer() {
	rs.helpOutput(`
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
`)
}

func (rs *Reposurgeon) CompletePrefer(text string) []string {
	out := make([]string, 0)
	for _, x := range vcstypes {
		if x.importer != "" && strings.HasPrefix(x.name, text) {
			out = append(out, x.name)
		}
	}
	sort.Strings(out)
	return out
}

// Report or select the preferred repository type.
func (rs *Reposurgeon) DoPrefer(line string) bool {
	if line == "" {
		for _, vcs := range vcstypes {
			control.baton.printLogString(vcs.String() + "\n")
		}
		for option := range fileFilters {
			control.baton.printLogString(fmt.Sprintf("read and write have a --format=%s option that supports %s files.\n", option, strings.ToTitle(option)))
		}
		extractable := make([]string, 0)
		for _, importer := range importers {
			if importer.visible && importer.basevcs != nil {
				extractable = append(extractable, importer.name)
			}
		}
		if len(extractable) > 0 {
			control.baton.printLogString(fmt.Sprintf("Other systems supported for read only: %s\n\n", strings.Join(extractable, " ")))
		}
	} else {
		known := ""
		rs.preferred = nil
		for _, repotype := range importers {
			if repotype.basevcs != nil && strings.ToLower(line) == repotype.name {
				rs.preferred = repotype.basevcs
				rs.extractor = repotype.engine
				break
			}
			if repotype.visible {
				known += " " + repotype.name
			}
		}
		if rs.preferred == nil {
			croak("known types are: %s\n", known)
		}
	}
	if control.isInteractive() {
		if rs.preferred == nil {
			control.baton.printLogString("No preferred type has been set.\n")
		} else {
			control.baton.printLogString(fmt.Sprintf("%s is the preferred type.\n", rs.preferred.name))
		}
	}
	return false
}

func (rs *Reposurgeon) HelpSourcetype() {
	rs.helpOutput(`
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
`)
}

func (rs *Reposurgeon) CompleteSourcetype(text string) []string {
	out := make([]string, 0)
	for _, x := range vcstypes {
		if x.exporter != "" && strings.HasPrefix(x.name, text) {
			out = append(out, x.name)
		}
	}
	sort.Strings(out)
	return out
}

// Report or select the current repository's source type.
func (rs *Reposurgeon) DoSourcetype(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	if line == "" {
		if rs.chosen().vcs != nil {
			fmt.Fprintf(control.baton, "%s: %s\n", repo.name, repo.vcs.name)
		} else {
			fmt.Fprintf(control.baton, "%s: no preferred type.\n", repo.name)
		}
	} else {
		known := ""
		for _, importer := range importers {
			if strings.ToLower(line) == importer.name {
				rs.chosen().vcs = importer.basevcs
				return false
			}
			if importer.visible {
				known += " " + importer.name
			}
		}
		croak("known types are %v.", known)
	}
	return false
}

func (rs *Reposurgeon) HelpChoose() {
	rs.helpOutput(`
Choose a named repo on which to operate.  The name of a repo is
normally the basename of the directory or file it was loaded from, but
repos loaded from standard input are 'unnamed'. The program will add
a disambiguating suffix if there have been multiple reads from the
same source.

With no argument, lists the names of the currently stored repositories
and their load times.  The second column is '*' for the currently selected
repository, '-' for others.

With an argument, the command tab-completes on the above list.
`)
}

func (rs *Reposurgeon) CompleteChoose(text string) []string {
	if rs.repolist == nil {
		return nil
	}
	out := make([]string, 0)
	for _, x := range rs.repolist {
		if strings.HasPrefix(x.name, text) {
			out = append(out, x.name)
		}
	}
	sort.Strings(out)
	return out
}

// Choose a named repo on which to operate.
func (rs *Reposurgeon) DoChoose(line string) bool {
	if rs.selection != nil {
		croak("choose does not take a selection set")
		return false
	}
	if len(rs.repolist) == 0 && len(line) > 0 {
		if control.isInteractive() {
			croak("no repositories are loaded, can't find %q.", line)
			return false
		}
	}
	if line == "" {
		for _, repo := range rs.repolist {
			status := "-"
			if rs.chosen() != nil && repo == rs.chosen() {
				status = "*"
			}
			if !control.flagOptions["quiet"] {
				fmt.Fprint(control.baton, rfc3339(repo.readtime)+" ")
			}
			fmt.Fprintf(control.baton, "%s %s\n", status, repo.name)
		}
	} else {
		if newOrderedStringSet(rs.reponames()...).Contains(line) {
			rs.choose(rs.repoByName(line))
			if control.isInteractive() {
				rs.DoStats(line)
			}
		} else {
			croak("no such repo as %s", line)
		}
	}
	return false
}

func (rs *Reposurgeon) HelpDrop() {
	rs.helpOutput(`
Drop a repo named by the argument from reposurgeon's list, freeing the memory
used for its metadata and deleting on-disk blobs. With no argument, drops the
currently chosen repo. Tab-completes on the list of loaded repositories.
`)
}
func (rs *Reposurgeon) CompleteDrop(text string) []string {
	return rs.CompleteChoose(text)
}

// Drop a repo from reposurgeon's list.
func (rs *Reposurgeon) DoDrop(line string) bool {
	if len(rs.reponames()) == 0 {
		if control.isInteractive() {
			croak("no repositories are loaded.")
			return false
		}
	}
	if rs.selection != nil {
		croak("drop does not take a selection set")
		return false
	}
	if line == "" {
		if rs.chosen() == nil {
			croak("no repo has been chosen.")
			return false
		}
		line = rs.chosen().name
	}
	if rs.reponames().Contains(line) {
		if rs.chosen() != nil && line == rs.chosen().name {
			rs.unchoose()
		}
		holdrepo := rs.repoByName(line)
		holdrepo.cleanup()
		rs.removeByName(line)
	} else {
		croak("no such repo as %s", line)
	}
	if control.isInteractive() && !control.flagOptions["quiet"] {
		// Emit listing of remaining repos
		rs.DoChoose("")
	}
	return false
}

func (rs *Reposurgeon) HelpRename() {
	rs.helpOutput(`
Rename the currently chosen repo; requires an argument.  Won't do it
if there is already one by the new name.
`)
}

// Rename a repository.
func (rs *Reposurgeon) DoRename(line string) bool {
	if rs.selection != nil {
		croak("rename does not take a selection set")
		return false
	}
	if rs.reponames().Contains(line) {
		croak("there is already a repo named %s.", line)
	} else if rs.chosen() == nil {
		croak("no repository is currently chosen.")
	} else {
		rs.chosen().rename(line)

	}
	return false
}

func (rs *Reposurgeon) HelpPreserve() {
	rs.helpOutput(`
Add (presumably untracked) files or directories to the repo's list of
paths to be restored from the backup directory after a rebuild. Each
argument, if any, is interpreted as a pathname.  The current preserve
list is displayed afterwards.
`)
}

// Add files and subdirectories to the preserve set.
func (rs *Reposurgeon) DoPreserve(line string) bool {
	if rs.selection != nil {
		croak("preserve does not take a selection set")
		return false
	}
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	for _, filename := range strings.Fields(line) {
		rs.chosen().preserve(filename)
	}
	respond("preserving %s.", rs.chosen().preservable())
	return false
}

func (rs *Reposurgeon) HelpUnpreserve() {
	rs.helpOutput(`
Remove (presumably untracked) files or directories to the repo's list
of paths to be restored from the backup directory after a
rebuild. Each argument, if any, is interpreted as a pathname.  The
current preserve list is displayed afterwards.
`)
}

// Remove files and subdirectories from the preserve set.
func (rs *Reposurgeon) DoUnpreserve(line string) bool {
	if rs.selection != nil {
		croak("unpreserve does not take a selection set")
		return false
	}
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	for _, filename := range strings.Fields(line) {
		rs.chosen().unpreserve(filename)
	}
	respond("preserving %s.", rs.chosen().preservable())
	return false
}

//
// Serialization and de-serialization.
//
func (rs *Reposurgeon) HelpRead() {
	rs.helpOutput(`
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
`)
}

// Read in a repository for surgery.
func (rs *Reposurgeon) DoRead(line string) bool {
	if rs.selection != nil {
		croak("read does not take a selection set")
		return false
	}
	parse := rs.newLineParse(line, []string{"stdin"})
	// Don't do parse.Closem() here - you'll nuke the seaakstream that
	// we use to get content out of dump streams.
	var repo *Repository
	if parse.redirected {
		repo = newRepository("")
		for _, option := range parse.options {
			if strings.HasPrefix(option, "--format=") {
				vcs := strings.Split(option, "=")[1]
				infilter, ok := fileFilters[vcs]
				if !ok {
					croak("unrecognized --format")
					return false
				}
				srcname := "unknown-in"
				if f, ok := parse.stdin.(*os.File); ok {
					srcname = f.Name()
				}
				// parse is redirected so this
				// must be something besides
				// os.Stdin, so we can close
				// it and substitute another
				// redirect
				parse.stdin.Close()
				command := fmt.Sprintf(infilter.importer, srcname)
				reader, _, err := readFromProcess(command)
				if err != nil {
					croak("can't open filter: %v", infilter)
					return false
				}
				parse.stdin = reader
				break
			}
		}
		repo.fastImport(context.TODO(), parse.stdin, parse.options.toStringSet(), "")
	} else if parse.line == "" || parse.line == "." {
		var err2 error
		// This is slightly asymmetrical with the write side, which
		// interprets an empty argument list as '-'
		cdir, err2 := os.Getwd()
		if err2 != nil {
			croak(err2.Error())
			return false
		}
		repo, err2 = readRepo(cdir, parse.options.toStringSet(), rs.preferred, rs.extractor, control.flagOptions["quiet"])
		if err2 != nil {
			croak(err2.Error())
			return false
		}
	} else if isdir(parse.line) {
		var err2 error
		repo, err2 = readRepo(parse.line, parse.options.toStringSet(), rs.preferred, rs.extractor, control.flagOptions["quiet"])
		if err2 != nil {
			croak(err2.Error())
			return false
		}
	} else {
		croak("read no longer takes a filename argument - use < redirection instead")
		return false
	}
	rs.repolist = append(rs.repolist, repo)
	rs.choose(repo)
	if rs.chosen() != nil {
		if rs.chosen().vcs != nil {
			rs.preferred = rs.chosen().vcs
		}
		name := rs.chosen().sourcedir
		if name == "" {
			name = parse.infile
			if name == "" {
				name = "unnamed"
			}
		}
		rs.chosen().rename(rs.uniquify(filepath.Base(name)))
	}
	if control.isInteractive() && !control.flagOptions["quiet"] {
		rs.DoChoose("")
	}
	return false
}

func (rs *Reposurgeon) HelpWrite() {
	rs.helpOutput(`
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
`)
}

// Stream out the results of repo surgery.
func (rs *Reposurgeon) DoWrite(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	// Python also handled prefix ~user
	if strings.HasPrefix(line, "~/") {
		usr, err := user.Current()
		if err == nil {
			line = usr.HomeDir + line[1:]
		}
	}
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	// This is slightly asymmetrical with the read side, which
	// interprets an empty argument list as '.'
	if parse.redirected || parse.line == "" {
		for _, option := range parse.options {
			if strings.HasPrefix(option, "--format=") {
				vcs := strings.Split(option, "=")[1]
				outfilter, ok := fileFilters[vcs]
				if !ok {
					croak("unrecognized --format")
					return false
				}
				srcname := "unknown-out"
				if f, ok := parse.stdout.(*os.File); ok {
					srcname = f.Name()
				}
				// parse is redirected so this
				// must be something besides
				// os.Stdout, so we can close
				// it and substitute another
				// redirect
				parse.stdout.Close()
				command := fmt.Sprintf(outfilter.exporter, srcname)
				writer, _, err := writeToProcess(command)
				if err != nil {
					croak("can't open output filter: %v", outfilter)
					return false
				}
				parse.stdout = writer
				break
			}
		}
		rs.chosen().fastExport(rs.selection, parse.stdout, parse.options.toStringSet(), rs.preferred)
	} else if isdir(parse.line) {
		err := rs.chosen().rebuildRepo(parse.line, parse.options.toStringSet(), rs.preferred)
		if err != nil {
			croak(err.Error())
		}
	} else {
		croak("write no longer takes a filename argument - use > redirection instead")
	}
	return false
}

func (rs *Reposurgeon) HelpInspect() {
	rs.helpOutput(`
Dump a fast-import stream representing selected events to standard
output or via > redirect to a file.  Just like a write, except (1) the
progress meter is disabled, and (2) there is an identifying header
before each event dump.
`)
}

// Dump raw events.
func (rs *Reposurgeon) DoInspect(lineIn string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen.")
		return false
	}

	parse := rs.newLineParse(lineIn, orderedStringSet{"stdout"})
	defer parse.Closem()

	selection := rs.selection
	if selection == nil {
		state := rs.evalState(len(repo.events))
		defer state.release()
		selection, parse.line = rs.parse(parse.line, state)
		if selection == nil {
			selection = repo.all()
		}
	}
	for _, eventid := range selection {
		event := repo.events[eventid]
		header := fmt.Sprintf("Event %d %s\n", eventid+1, strings.Repeat("=", 72))
		fmt.Fprintln(parse.stdout, header[:73])
		fmt.Fprint(parse.stdout, event.String())
	}

	return false
}

func (rs *Reposurgeon) HelpStrip() {
	rs.helpOutput(`
Replace the blobs in the selected repository with self-identifying stubs;
and/or strip out topologically uninteresting commits.  The modifiers for
this are 'blobs' and 'reduce' respectively; the default is 'blobs'.

A selection set is effective only with the 'blobs' option, defaulting to all
blobs. The 'reduce' mode always acts on the entire repository.

This is intended for producing reduced test cases from large repositories.
`)
}
func (rs *Reposurgeon) CompleteStrip(text string) []string {
	return []string{"blobs", "reduce"}
}

// Drop content to produce a reduced test case.
func (rs *Reposurgeon) DoStrip(line string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen.")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	var striptypes orderedStringSet
	var oldlen int
	if line == "" {
		striptypes = orderedStringSet{"blobs"}
	} else {
		striptypes = newOrderedStringSet(strings.Fields(line)...)
	}
	if striptypes.Contains("blobs") {
		for _, ei := range selection {
			if blob, ok := repo.events[ei].(*Blob); ok {
				blob.setContent([]byte(fmt.Sprintf("Blob at %s\n", blob.mark)), noOffset)
			}
		}
	}
	if striptypes.Contains("reduce") {
		interesting := newOrderedStringSet()
		for _, event := range repo.events {
			if tag, ok := event.(*Tag); ok {
				interesting.Add(tag.committish)
			} else if reset, ok := event.(*Reset); ok {
				interesting.Add(reset.ref)
			} else if commit, ok := event.(*Commit); ok {
				if len(commit.children()) != 1 || len(commit.parents()) != 1 {
					interesting.Add(commit.mark)
				} else {
					for _, op := range commit.operations() {
						direct := commit.parents()[0]
						var noAncestor bool
						if _, ok := direct.(*Callout); ok {
							noAncestor = true
						} else if commit, ok := direct.(*Commit); ok {
							noAncestor = commit.ancestorCount(op.Path) == 0
						}
						if op.op != opM || noAncestor {
							interesting.Add(commit.mark)
							break
						}
					}
				}
			}
		}
		neighbors := newOrderedStringSet()
		for _, event := range repo.events {
			if commit, ok := event.(*Commit); ok && interesting.Contains(commit.mark) {
				neighbors = neighbors.Union(newOrderedStringSet(commit.parentMarks()...))
				neighbors = neighbors.Union(newOrderedStringSet(commit.childMarks()...))
			}
		}
		interesting = interesting.Union(neighbors)
		oldlen = len(repo.events)
		deletia := newOrderedIntSet()
		for i, event := range repo.events {
			if commit, ok := event.(*Commit); ok && !interesting.Contains(commit.mark) {
				deletia.Add(i)
			}
		}
		repo.delete(deletia, nil)
		respond("From %d to %d events.", oldlen, len(repo.events))
	}
	return false
}

func (rs *Reposurgeon) HelpGraph() {
	rs.helpOutput(`
Dump a graph representing selected events to standard output in DOT markup
for graphviz. Supports > redirection.
`)
}

// Dump a commit graph.
func (rs *Reposurgeon) DoGraph(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	fmt.Fprint(parse.stdout, "digraph {\n")
	for _, ei := range selection {
		event := rs.chosen().events[ei]
		if commit, ok := event.(*Commit); ok {
			for _, parent := range commit.parentMarks() {
				if selection.Contains(rs.chosen().markToIndex(parent)) {
					fmt.Fprintf(parse.stdout, "\t%s -> %s;\n",
						parent[1:], commit.mark[1:])
				}
			}
		}
		if tag, ok := event.(*Tag); ok {
			fmt.Fprintf(parse.stdout, "\t\"%s\" -> \"%s\" [style=dotted];\n",
				tag.name, tag.committish[1:])
			fmt.Fprintf(parse.stdout, "\t{rank=same; \"%s\"; \"%s\"}\n",
				tag.name, tag.committish[1:])
		}
	}
	for _, ei := range selection {
		event := rs.chosen().events[ei]
		if commit, ok := event.(*Commit); ok {
			firstline := strings.Split(commit.Comment, "\n")[0]
			if len(firstline) > 42 {
				firstline = firstline[:42]
			}
			summary := html.EscapeString(firstline)
			cid := commit.mark
			if commit.legacyID != "" {
				cid = commit.showlegacy() + " &rarr; " + cid
			}
			fmt.Fprintf(parse.stdout, "\t%s [shape=box,width=5,label=<<table cellspacing=\"0\" border=\"0\" cellborder=\"0\"><tr><td><font color=\"blue\">%s</font></td><td>%s</td></tr></table>>];\n",
				commit.mark[1:], cid, summary)
			newbranch := true
			for _, cchild := range commit.children() {
				if child, ok := cchild.(*Commit); ok && commit.Branch == child.Branch {
					newbranch = false
				}
			}
			if newbranch {
				fmt.Fprintf(parse.stdout, "\t\"%s\" [shape=oval,width=2];\n", commit.Branch)
				fmt.Fprintf(parse.stdout, "\t\"%s\" -> \"%s\" [style=dotted];\n", commit.mark[1:], commit.Branch)
			}
		}
		if tag, ok := event.(*Tag); ok {
			summary := html.EscapeString(strings.Split(tag.Comment, "\n")[0][:32])
			fmt.Fprintf(parse.stdout, "\t\"%s\" [label=<<table cellspacing=\"0\" border=\"0\" cellborder=\"0\"><tr><td><font color=\"blue\">%s</font></td><td>%s</td></tr></table>>];\n", tag.name, tag.name, summary)
		}
	}
	fmt.Fprint(parse.stdout, "}\n")
	return false
}

func (rs *Reposurgeon) HelpRebuild() {
	rs.helpOutput(`
Rebuild a repository from the state held by reposurgeon.  The argument
specifies the target directory in which to do the rebuild; if the
repository read was from a repo directory (and not a git-import stream), it
defaults to that directory.  If the target directory is nonempty
its contents are backed up to a save directory.
`)
}

// Rebuild a repository from the edited state.
func (rs *Reposurgeon) DoRebuild(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	if len(rs.selection) != 0 {
		croak("rebuild does not take a selection set")
		return false
	}
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	err := rs.chosen().rebuildRepo(parse.line, parse.options.toStringSet(), rs.preferred)
	if err != nil {
		croak(err.Error())
	}
	return false
}

//
// Editing commands
//
func (rs *Reposurgeon) HelpMsgout() {
	rs.helpOutput(`
Emit a file of messages in RFC822 format representing the contents of
repository metadata. Takes a selection set; members of the set other
than commits, annotated tags, and passthroughs are ignored (that is,
presently, blobs and resets). Supports > redirection.

May have an option --filter, followed by = and a /-enclosed regular expression.
If this is given, only headers with names matching it are emitted.  In this
control the name of the header includes its trailing colon.
`)
}

// Generate a message-box file representing object metadata.
func (rs *Reposurgeon) DoMsgout(lineIn string) bool {
	parse := rs.newLineParse(lineIn, orderedStringSet{"stdout"})
	defer parse.Closem()

	var filterRegexp *regexp.Regexp
	s, present := parse.OptVal("--filter")
	if present {
		if len(s) >= 2 && strings.HasPrefix(s, "/") && strings.HasSuffix(s, "/") {
			var err error
			payload := s[1 : len(s)-1]
			filterRegexp, err = regexp.Compile(payload)
			if err != nil {
				croak("malformed filter option %q in msgout\n", payload)
				return false
			}
		} else {
			croak("malformed filter option %q in msgout\n", s)
			return false
		}
	}
	f := func(p *LineParse, i int, e Event) string {
		// this is pretty stupid; pretend you didn't see it
		switch v := e.(type) {
		case *Passthrough:
			return v.emailOut(orderedStringSet{}, i, filterRegexp)
		case *Commit:
			return v.emailOut(orderedStringSet{}, i, filterRegexp)
		case *Tag:
			return v.emailOut(orderedStringSet{}, i, filterRegexp)
		default:
			return ""
		}
	}
	rs.reportSelect(parse, f)
	return false
}

func (rs *Reposurgeon) HelpMsgin() {
	rs.helpOutput(`
Accept a file of messages in RFC822 format representing the
contents of the metadata in selected commits and annotated tags. Takes
no selection set. If there is an argument it will be taken as the name
of a message-box file to read from; if no argument, or one of '-', reads
from standard input. Supports < redirection.

Users should be aware that modifying an Event-Number or Event-Mark field
will change which event the update from that message is applied to.  This
is unlikely to have good results.

The header CheckText, if present, is examined to see if the comment
text of the associated event begins with it. If not, the item
modification is aborted. This helps ensure that you are landing
updates on the events you intend.

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
msgin logic will attempt to match the commit or tag first by Legacy-ID,
then by a unique committer ID and timestamp pair.

If output is redirected and the modifier '--changed' appears, a minimal
set of modifications actually made is written to the output file in a form
that can be fed back in. Supports > redirection.

If the option --empty-only is given, this command will throw a recoverable error
if it tries to alter a message body that is neither empty nor consists of the
CVS empty-comment marker.
`)
}

// Accept a message-box file representing object metadata and update from it.
func (rs *Reposurgeon) DoMsgin(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	parse := rs.newLineParse(line, orderedStringSet{"stdin", "stdout"})
	defer parse.Closem()
	updateList := make([]*MessageBlock, 0)
	r := bufio.NewReader(parse.stdin)
	if r == nil {
		croak("reader creation failed")
		return false
	}
	for {
		msg, err := newMessageBlock(r)
		if err == io.EOF {
			break
		} else if err != nil {
			croak("malformed message block: %v", err)
			return false
		}
		updateList = append(updateList, msg)
	}
	// First, a validation pass
	attributionByAuthor := make(map[string]Event)
	attributionByCommitter := make(map[string]Event)
	nameMap := make(map[string]*Tag)
	authorCounts := make(map[string]int)
	committerCounts := make(map[string]int)
	for _, commit := range repo.commits(nil) {
		stamp := commit.actionStamp()
		if found, ok := attributionByAuthor[stamp]; ok && found != commit {
			authorCounts[stamp]++
		}
		attributionByAuthor[stamp] = commit
		stamp = commit.committer.actionStamp()
		if found, ok := attributionByCommitter[stamp]; ok && found != commit {
			committerCounts[stamp]++
		}
		attributionByCommitter[stamp] = commit
	}
	for _, event := range repo.events {
		if tag, ok := event.(*Tag); ok {
			if tag.name != "" {
				nameMap[tag.name] = tag
			}
			if tag.tagger != nil {
				stamp := tag.tagger.actionStamp()
				if found, ok := attributionByAuthor[stamp]; ok && found != tag {
					authorCounts[stamp]++
				}
				attributionByAuthor[stamp] = tag
			}
		}
	}
	legacyMap := make(map[string]*Commit)
	for _, commit := range repo.commits(nil) {
		if commit.legacyID != "" {
			legacyMap[commit.legacyID] = commit
		}
	}
	// Special case - event creation
	if parse.options.Contains("--create") {
		for _, message := range updateList {
			if strings.Contains(message.String(), "Tag-Name") {
				blank := newTag(nil, "", "", nil, "")
				attrib, _ := newAttribution("")
				blank.tagger = attrib
				blank.emailIn(message, true)
				commits := repo.commits(nil)
				blank.remember(repo, commits[len(commits)-1].mark)
				repo.addEvent(blank)
			} else {
				blank := newCommit(repo)
				attrib, _ := newAttribution("")
				blank.committer = *attrib
				blank.emailIn(message, true)
				blank.mark = repo.newmark()
				if blank.Branch == "" {
					// Avoids crapping out on name lookup.
					blank.Branch = "generated-" + blank.mark[1:]
				}
				if rs.selection == nil || len(rs.selection) != 1 {
					repo.addEvent(blank)
				} else {
					commit, ok := repo.events[rs.selection[0]].(CommitLike)
					if ok {
						blank.setParents([]CommitLike{commit})
						repo.insertEvent(blank, rs.selection[0]+1, "event creation from message block")
					}
				}
			}
		}
		repo.declareSequenceMutation("event creation")
		return false
	}
	// Normal case - no --create
	events := make([]Event, 0)
	errorCount := 0
	var event Event
	for i, message := range updateList {
		event = nil
		if message.getHeader("Event-Number") != "" {
			eventnum, err := strconv.Atoi(message.getHeader("Event-Number"))
			if err != nil {
				croak("event number garbled in update %d: %v", i+1, err)
				errorCount++
			} else {
				if eventnum < 1 || eventnum > len(repo.events) {
					croak("event number %d out of range in update %d",
						eventnum, i+1)
					errorCount++
				} else {
					event = repo.events[eventnum - 1]
				}
			}
		} else if message.getHeader("Legacy-ID") != "" {
			event = legacyMap[message.getHeader("Legacy-ID")]
			if event == nil {
				croak("no commit matches legacy-ID %s",
					message.getHeader("Legacy-ID"))
				errorCount++
			}
		} else if message.getHeader("Event-Mark") != "" {
			event = repo.markToEvent(message.getHeader("Event-Mark"))
			if event == nil {
				croak("no commit matches mark %s",
					message.getHeader("Event-Mark"))
				errorCount++
			}
		} else if message.getHeader("Author") != "" && message.getHeader("Author-Date") != "" {
			blank := newCommit(repo)
			attrib, _ := newAttribution("")
			blank.authors = append(blank.authors, *attrib)
			blank.emailIn(message, false)
			stamp := blank.actionStamp()
			event = attributionByAuthor[stamp]
			if event == nil {
				croak("no commit matches stamp %s", stamp)
				errorCount++
			}
			if authorCounts[stamp] > 1 {
				croak("multiple events (%d) match %s", authorCounts[stamp], stamp)
				errorCount++
			}
		} else if message.getHeader("Committer") != "" && message.getHeader("Committer-Date") != "" {
			blank := newCommit(repo)
			attrib, _ := newAttribution("")
			blank.committer = *attrib
			blank.emailIn(message, false)
			stamp := blank.committer.actionStamp()
			event = attributionByCommitter[stamp]
			if event == nil {
				croak("no commit matches stamp %s", stamp)
				errorCount++
			}
			if committerCounts[stamp] > 1 {
				croak(fmt.Sprintf("multiple events (%d) match %s", committerCounts[stamp], stamp))
				errorCount++
			}
		} else if message.getHeader("Tagger") != "" && message.getHeader("Tagger-Date") != "" {
			blank := newTag(repo, "", "", nil, "")
			attrib, _ := newAttribution("")
			blank.tagger = attrib
			blank.emailIn(message, false)
			stamp := blank.tagger.actionStamp()
			event = attributionByAuthor[stamp]
			if event == nil {
				croak("no tag matches stamp %s", stamp)
				errorCount++
			}
			if authorCounts[stamp] > 1 {
				croak("multiple events match %s", stamp)
				errorCount++
			}
		} else if message.getHeader("Tag-Name") != "" {
			blank := newTag(repo, "", "", nil, "")
			attrib, _ := newAttribution("")
			blank.tagger = attrib
			blank.emailIn(message, false)
			event = nameMap[blank.name]
			if event == nil {
				croak("no tag matches name %s", blank.name)
				errorCount++
			}
		} else {
			croak("no commit matches update %d:\n%s", i+1, message.String())
			errorCount++
		}
		if event != nil {
			ei := repo.eventToIndex(event)
			if ei == -1 {
				croak("event at update %d can't be found in repository", i+1)
				errorCount++
				return false
			} else if _, ok := getAttr(event, "emailIn"); ok {
				croak("event %d cannot be modified", ei+1)
				errorCount++
				return false
			}
		}
		// Always append, even None, to stay in sync with updateList
		events = append(events, event)
	}
	if errorCount > 0 {
		croak("%d errors in metadata updates", errorCount)
		return false
	}
	// Now apply the updates
	changers := make([]*MessageBlock, 0)
	for i := range updateList {
		event := events[i]
		update := updateList[i]
		check := strings.TrimSpace(update.getHeader("Check-Text"))
		if check != "" && !strings.HasPrefix(strings.TrimSpace(event.getComment()), check) {
			croak("check text mismatch at %s (input %d of %d), expected %q saw %q, bailing out", event.(*Commit).actionStamp(), i+1, len(updateList), check, event.getComment())
			return false
		}
		if parse.options.Contains("--empty-only") {
			if event.getComment() != update.getPayload() && !emptyComment(event.getComment()) {
				croak("nonempty comment at %s (input %d of %d), bailing out", event.(*Commit).actionStamp(), i+1, len(updateList))
			}
		}

		switch event.(type) {
		case *Commit:
			commit := event.(*Commit)
			if commit.emailIn(update, false) {
				changers = append(changers, update)
			}
		case *Tag:
			tag := event.(*Tag)
			if tag.emailIn(update, false) {
				changers = append(changers, update)
			}
		}
	}
	if control.isInteractive() {
		if len(changers) == 0 {
			respond("no events modified by msgin.")
		} else {
			respond("%d events modified by msgin.", len(changers))
		}
	}
	if parse.stdout != os.Stdout {
		if parse.options.Contains("--changed") {
			for _, update := range changers {
				fmt.Fprint(parse.stdout, string(MessageBlockDivider)+"\n"+update.String())
			}
		}
	}
	return false
}

func (rs *Reposurgeon) HelpEdit() {
	rs.helpOutput(`
Report the selection set of events to a tempfile as msgout does,
call an editor on it, and update from the result as msgin does.
If you do not specify an editor name as second argument, it will be
taken from the $EDITOR variable in your environment.
If $EDITOR is not set, /usr/bin/editor will be used as a fallback
if it exists as a symlink to your default editor, as is the case on
Debian, Ubuntu and their derivatives.

Normally this command ignores blobs because msgout does.
However, if you specify a selection set consisting of a single
blob, your editor will be called on the blob file.

Supports < and > redirection.
`)
}

// Edit metadata interactively.
func (rs *Reposurgeon) DoEdit(line string) bool {
	if rs.chosen() == nil {
		croak("no repo is loaded")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	rs.edit(selection, line)
	return false
}

func (rs *Reposurgeon) HelpFilter() {
	rs.helpOutput(`
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

With --dedos, DOS/Windows-style \r\n line terminators are replaced with \n.
`)
}

type filterCommand struct {
	repo       *Repository
	filtercmd  string
	sub        func(string) string
	regexp     *regexp.Regexp
	attributes orderedStringSet
}

// GoReplacer bridges from Python-style back-references (\1) to Go-style ($1).
// This was originally a shim for testing during the Pythjon port.  It has
// been kept because Go's use of $n for group matches comflicys with the
// use of $n for script arguments in reposurgeon.
func GoReplacer(re *regexp.Regexp, fromString, toString string) string {
	for i := 0; i < 10; i++ {
		sdigit := fmt.Sprintf("%d", i)
		toString = strings.Replace(toString, `\`+sdigit, `${`+sdigit+`}`, -1)
	}
	out := re.ReplaceAllString(fromString, toString)
	return out
}

// newFilterCommand - Initialize a filter from the command line.
func newFilterCommand(repo *Repository, filtercmd string) *filterCommand {
	fc := new(filterCommand)
	fc.repo = repo
	fc.attributes = newOrderedStringSet()
	// Must not use LineParse here as it would try to strip options
	// in shell commands.
	flagRe := regexp.MustCompile(`[0-9]*g?`)
	if strings.HasPrefix(filtercmd, "--shell") {
		fc.filtercmd = strings.TrimSpace(filtercmd[7:])
		fc.attributes = newOrderedStringSet("c", "a", "C")
	} else if strings.HasPrefix(filtercmd, "--regex") || strings.HasPrefix(filtercmd, "--replace") {
		firstspace := strings.Index(filtercmd, " ")
		if firstspace == -1 {
			croak("missing filter specification")
			return nil
		}
		stripped := strings.TrimSpace(filtercmd[firstspace:])
		parts := strings.Split(stripped, stripped[0:1])
		subflags := parts[len(parts)-1]
		if len(parts) != 4 {
			croak("malformed filter specification")
			return nil
		} else if parts[0] != "" {
			croak("bad prefix %q on filter specification", parts[0])
			return nil
		} else if subflags != "" && !flagRe.MatchString(subflags) {
			croak("unrecognized filter flags")
			return nil
		} else if strings.Index(filtercmd, "%PATHS%") != -1 {
			croak("%s is not yet supported in regex filters", "%PATHS%")
			return nil
		} else {
			subcount := 1
			for subflags != "" {
				flag := subflags[0:1]
				subflags = subflags[:len(subflags)-1]
				if flag == "g" {
					subcount = -1
				} else if flag == "c" || flag == "a" || flag == "C" {
					fc.attributes.Add(flag)
				} else if i := strings.Index("0123456789", flag); i != -1 {
					subcount = i
				} else {
					croak("unknown filter flag")
					return nil
				}
			}
			if len(fc.attributes) == 0 {
				fc.attributes = newOrderedStringSet("c", "a", "C")
			}
			if strings.HasPrefix(filtercmd, "--regex") {
				pattern := parts[1]
				var err error
				fc.regexp, err = regexp.Compile(pattern)
				if err != nil {
					croak("filter compilation error: %v", err)
					return nil
				}
				fc.sub = func(s string) string {
					if subcount == -1 {
						return GoReplacer(fc.regexp, s, parts[2])
					}
					replacecount := subcount
					replacer := func(s string) string {
						replacecount--
						if replacecount > -1 {
							return parts[2]
						}
						return s
					}
					return fc.regexp.ReplaceAllStringFunc(s, replacer)
				}
			} else if strings.HasPrefix(filtercmd, "--replace") {
				fc.sub = func(s string) string {
					return strings.Replace(s, parts[1], parts[2], subcount)
				}
			}
		}
	} else if strings.HasPrefix(filtercmd, "--dedos") {
		if len(fc.attributes) == 0 {
			fc.attributes = newOrderedStringSet("c", "a", "C")
		}
		fc.sub = func(s string) string {
			out := strings.Replace(s, "\r\n", "\n", -1)
			return out
		}
	} else {
		croak("--shell or --regex or --dedos required")
		return nil
	}
	return fc
}

func (fc *filterCommand) do(content string) string {
	// Perform the filter on string content or a file.
	if fc.filtercmd != "" {
		//FIXME: %PATHS% looks like it never worked. Repair or remove.
		//var filtercmd string
		//if pathsubst != "" {
		//        filtercmd = strings.Replace(fc.filtercmd, "%PATHS%", pathsubst, -1)
		//} else {
		//        filtercmd = fc.filtercmd
		//}
		cmd := exec.Command("sh", "-c", fc.filtercmd)
		cmd.Stdin = strings.NewReader(content)
		content, err := cmd.CombinedOutput()
		if err != nil {
			logit(logWARN, "filter command failed")
		}
		return string(content)
	} else if fc.sub != nil {
		return fc.sub(content)
	} else {
		logit(logWARN, "unknown mode in filter command")
	}
	return content
}

func (rs *Reposurgeon) DoFilter(line string) (StopOut bool) {
	if rs.chosen() == nil {
		croak("no repo is loaded")
		return false
	}
	if line == "" {
		croak("no filter is specified")
		return false
	}
	if rs.selection == nil {
		croak("no selection")
		return false
	}
	// Mainline of do_filter() continues {
	filterhook := newFilterCommand(rs.chosen(), line)
	if filterhook != nil {
		rs.dataTraverse("Filtering",
			filterhook.do,
			filterhook.attributes,
			!strings.HasPrefix(line, "--dedos"),
			rs.inScript())
	}
	return false
}

func (rs *Reposurgeon) HelpTranscode() {
	rs.helpOutput(`
Transcode blobs, commit comments and committer/author names, or tag
comments and tag committer names in the selection set to UTF-8 from
the character encoding specified on the command line.

Attempting to specify a selection set including both blobs and
non-blobs (that is, commits or tags) throws an error. Inline content
in commits is filtered when the selection set contains (only) blobs
and the commit is within the range bounded by the earliest and latest
blob in the specification.

The encoding argument must name one of the codecs known to the Go
standard codecs library. In particular, 'latin-1' is a valid codec name.

Errors in this command force the repository to be dropped, because an
error may leave repository objects in a damaged state.

`)
}

func (rs *Reposurgeon) DoTranscode(line string) bool {
	if rs.chosen() == nil {
		croak("no repo is loaded")
		return false
	}

	enc, err := ianaindex.IANA.Encoding(line)
	if err != nil {
		croak("can's set up codec %s: error %v", line, err)
		return false
	}
	decoder := enc.NewDecoder()

	transcode := func(txt string) string {
		out, err := decoder.Bytes([]byte(txt))
		if err != nil {
			logit(logWARN, "decode error during transcoding: %v", err)
			rs.unchoose()
		}
		return string(out)
	}
	rs.dataTraverse("Transcoding",
		transcode,
		newOrderedStringSet("c", "a", "C"),
		true, !rs.inScript())
	return false
}

func (rs *Reposurgeon) HelpSetfield() {
	rs.helpOutput(`
In the selected objects (defaulting to none) set every instance of a
named field to a string value.  The string may be quoted to include
whitespace, and use backslash escapes interpreted by Go's C-like
string-escape codec, such as \s.

Attempts to set nonexistent attributes are ignored. Valid values for
the attribute are internal field names; in particular, for commits,
'comment' and 'branch' are legal.  Consult the source code for other
interesting values.

The special fieldnames 'author', 'commitdate' and 'authdate' apply
only to commits in the range.  The latter two sets attribution
dates. The former sets the author's name and email address (assuming
the value can be parsed for both), copying the committer
timestamp. The author's timezone may be deduced from the email
address.
`)
}

// Set an object field from a string.
func (rs *Reposurgeon) DoSetfield(line string) bool {
	if rs.chosen() == nil {
		croak("no repo is loaded")
		return false
	}
	repo := rs.chosen()
	if rs.selection == nil {
		croak("no selection")
		return false
	}
	fields, err := shlex.Split(line, true)
	if err != nil || len(fields) != 2 {
		croak("missing or malformed setfield line")
	}
	// Caling strings,Title so that Python-sytyle (uncapitalized)
	// fieldnsmes will still work.
	field := strings.Title(fields[0])
	value, err := stringEscape(fields[1])
	if err != nil {
		croak("while setting field: %v", err)
		return false
	}
	for _, ei := range rs.selection {
		event := repo.events[ei]
		if _, ok := getAttr(event, field); ok {
			setAttr(event, field, value)
		} else if commit, ok := event.(*Commit); ok {
			if field == "author" {
				attr := value
				attr += " " + commit.committer.date.String()
				newattr, _ := newAttribution("")
				commit.authors = append(commit.authors, *newattr)
			} else if field == "commitdate" {
				newdate, err := newDate(value)
				if err != nil {
					croak(err.Error())
					return false
				}
				commit.committer.date = newdate
			} else if field == "authdate" {
				newdate, err := newDate(value)
				if err != nil {
					croak(err.Error())
					return false
				}
				commit.authors[0].date = newdate
			}
		}
	}
	return false
}

func (rs *Reposurgeon) HelpSetperm() {
	rs.helpOutput(`
For the selected objects (defaulting to none) take the first argument as an
octal literal describing permissions.  All subsequent arguments are paths.
For each M fileop in the selection set and exactly matching one of the
paths, patch the permission field to the first argument value.
`)
}

// Set permissions on M fileops matching a path list.
func (rs *Reposurgeon) DoSetperm(line string) bool {
	if rs.chosen() == nil {
		croak("no repo is loaded")
		return false
	}
	if rs.selection == nil {
		croak("no selection")
		return false
	}
	fields, err := shlex.Split(line, true)
	if err != nil {
		croak("failurev in line pesing: %v", err)
		return false
	}
	if len(fields) < 2 {
		croak("missing or malformed setperm line")
		return false
	}
	perm := fields[0]
	paths := newOrderedStringSet(fields[1:]...)
	if !newOrderedStringSet("100644", "100755", "120000").Contains(perm) {
		croak("unexpected permission literal %s", perm)
		return false
	}
	baton := control.baton
	//baton.startProcess("patching modes", "")
	for _, ei := range rs.selection {
		if commit, ok := rs.chosen().events[ei].(*Commit); ok {
			for i, op := range commit.fileops {
				if op.op == opM && paths.Contains(op.Path) {
					commit.fileops[i].mode = perm
				}
			}
			baton.twirl()
		}
	}
	//baton.endProcess()
	return false
}

func (rs *Reposurgeon) HelpAppend() {
	rs.helpOutput(`
Append text to the comments of commits and tags in the specified
selection set. The text is the first token of the command and may
be a quoted string. C-style escape sequences in the string are
interpreted using Go's Quote/Unquote codec from the strconv library.

If the option --rstrip is given, the comment is right-stripped before
the new text is appended.
`)
}

// Append a line to comments in the specified selection set.
func (rs *Reposurgeon) DoAppend(line string) bool {
	if rs.chosen() == nil {
		croak("no repo is loaded")
		return false
	}
	if rs.selection == nil {
		croak("no selection")
		return false
	}
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	fields, err := shlex.Split(parse.line, true)
	if err != nil {
		croak(err.Error())
		return false
	}
	if len(fields) == 0 {
		croak("missing append line")
		return false
	}
	line, err = stringEscape(fields[0])
	if err != nil {
		croak(err.Error())
		return false
	}
	for _, ei := range rs.selection {
		event := rs.chosen().events[ei]
		switch event.(type) {
		case *Commit:
			commit := event.(*Commit)
			if parse.options.Contains("--rstrip") {
				commit.Comment = strings.TrimRight(commit.Comment, " \n\t")
			}
			commit.Comment += line
		case *Tag:
			tag := event.(*Tag)
			if parse.options.Contains("--rstrip") {
				tag.Comment = strings.TrimRight(tag.Comment, " \n\t")
			}
			tag.Comment += line
		}
	}
	return false
}

func (rs *Reposurgeon) HelpSquash() {
	rs.helpOutput(`
Combine a selection set of events; this may mean deleting them or
pushing their content forward or back onto a target commit just
outside the selection range, depending on policy flags.

The default selection set for this command is empty.  Blobs cannot be
directly affected by this command; they move or are deleted only when
removal of fileops associated with commits requires this.
`)
}

// Squash events in the specified selection set.
func (rs *Reposurgeon) DoSquash(line string) bool {
	if rs.chosen() == nil {
		croak("no repo is loaded")
		return false
	}
	if rs.selection == nil {
		rs.selection = nil
	}
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	rs.chosen().squash(rs.selection, parse.options)
	return false
}

func (rs *Reposurgeon) HelpDelete() {
	rs.helpOutput(`
Delete a selection set of events.  The default selection set for this
command is empty.  Tags, resets, and passthroughs are deleted with no
side effects.  Blobs cannot be directly deleted with this command; they
are removed only when removal of fileops associated with commits requires this.

When a commit is deleted, what becomes of tags and fileops attached to
it is controlled by policy flags.  A delete is equivalent to a
squash with the --delete flag.
`)
}

func (rs *Reposurgeon) DoDelete(line string) bool {
	if rs.chosen() == nil {
		croak("no repo is loaded")
		return false
	}
	if rs.selection == nil {
		rs.selection = nil
	}
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	parse.options.Add("--delete")
	rs.chosen().squash(rs.selection, parse.options)
	return false
}

func (rs *Reposurgeon) HelpCoalesce() {
	rs.helpOutput(`
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
`)
}

// Coalesce events in the specified selection set.
func (rs *Reposurgeon) DoCoalesce(line string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo is loaded")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	timefuzz := 90
	changelog := parse.options.Contains("--changelog")
	if parse.line != "" {
		var err error
		timefuzz, err = strconv.Atoi(parse.line)
		if err != nil {
			croak("time-fuzz value must be an integer")
			return false
		}
	}
	isChangelog := func(commit *Commit) bool {
		return strings.Contains(commit.Comment, "empty log message") && len(commit.operations()) == 1 && commit.operations()[0].op == opM && strings.HasSuffix(commit.operations()[0].Path, "ChangeLog")
	}
	coalesceMatch := func(cthis *Commit, cnext *Commit) bool {
		croakOnFail := logEnable(logDELETE) || parse.options.Contains("--debug")
		if cthis.committer.email != cnext.committer.email {
			if croakOnFail {
				croak("committer email mismatch at %s", cnext.idMe())
			}
			return false
		}
		if cthis.committer.date.delta(cnext.committer.date) >= time.Duration(timefuzz)*time.Second {
			if croakOnFail {
				croak("time fuzz exceeded at %s", cnext.idMe())
			}
			return false
		}
		if changelog && !isChangelog(cthis) && isChangelog(cnext) {
			return true
		}
		if cthis.Comment != cnext.Comment {
			if croakOnFail {
				croak("comment mismatch at %s", cnext.idMe())
			}
			return false
		}
		return true
	}
	eligible := make(map[string][]string)
	squashes := make([][]string, 0)
	for _, commit := range repo.commits(selection) {
		trial, ok := eligible[commit.Branch]
		if !ok {
			// No active commit span for this branch - start one
			// with the mark of this commit
			eligible[commit.Branch] = []string{commit.mark}
		} else if coalesceMatch(
			repo.markToEvent(trial[len(trial)-1]).(*Commit),
			commit) {
			// This commit matches the one at the
			// end of its branch span.  Append its
			// mark to the span.
			eligible[commit.Branch] = append(eligible[commit.Branch], commit.mark)
		} else {
			// This commit doesn't match the one
			// at the end of its span.  Coalesce
			// the span and start a new one with
			// this commit.
			if len(eligible[commit.Branch]) > 1 {
				squashes = append(squashes, eligible[commit.Branch])
			}
			eligible[commit.Branch] = []string{commit.mark}
		}
	}
	for _, endspan := range eligible {
		if len(endspan) > 1 {
			squashes = append(squashes, endspan)
		}
	}
	for _, span := range squashes {
		// Prevent lossage when last is a ChangeLog commit
		repo.markToEvent(span[len(span)-1]).(*Commit).Comment = repo.markToEvent(span[0]).(*Commit).Comment
		squashable := make([]int, 0)
		for _, mark := range span[:len(span)-1] {
			squashable = append(squashable, repo.markToIndex(mark))
		}
		repo.squash(squashable, orderedStringSet{"--coalesce"})
	}
	respond("%d spans coalesced.", len(squashes))
	return false
}

func (rs *Reposurgeon) HelpAdd() {
	rs.helpOutput(`
From a specified commit, add a specified fileop. The syntax is

     add {D path | M perm mark path | R source target | C source target}

For a D operation to be valid there must be an M operation for the path
in the commit's ancestry.  For an M operation to be valid, the 'perm'
part must be a token ending with 755 or 644 and the 'mark' must
refer to a blob that precedes the commit location.  For an R or C
operation to be valid, there must be an M operation for the source
in the commit's ancestry.

`)
}

// Add a fileop to a specified commit.
func (rs *Reposurgeon) DoAdd(line string) bool {
	if rs.chosen() == nil {
		croak("no repo is loaded")
		return false
	}
	repo := rs.chosen()
	fields, err := shlex.Split(line, true)
	if err != nil && len(fields) < 2 {
		croak("add requires an operation type and arguments")
		return false
	}
	optype := fields[0][0]
	var perms, argpath, mark, source, target string
	if optype == opD {
		argpath = fields[1]
		for _, event := range repo.commits(rs.selection) {
			if event.paths(nil).Contains(argpath) {
				croak("%s already has an op for %s",
					event.mark, argpath)
				return false
			}
			if event.ancestorCount(argpath) == 0 {
				croak("no previous M for %s", argpath)
				return false
			}
		}
	} else if optype == opM {
		if len(fields) != 4 {
			croak("wrong field count in add command")
			return false
		} else if strings.HasSuffix(fields[1], "644") {
			perms = "100644"
		} else if strings.HasSuffix(fields[1], "755") {
			perms = "100755"
		}
		mark = fields[2]
		if !strings.HasPrefix(mark, ":") {
			croak("garbled mark %s in add command", mark)
			return false
		}
		markval, err1 := strconv.Atoi(mark[1:])
		if err1 != nil {
			croak("non-numeric mark %s in add command", mark)
			return false
		}
		blob, ok := repo.markToEvent(mark).(*Blob)
		if !ok {
			croak("mark %s in add command does not refer to a blob", mark)
			return false
		} else if markval >= rs.selection.Min() {
			croak("mark %s in add command is after add location", mark)
			return false
		}
		argpath = fields[3]
		for _, event := range repo.commits(rs.selection) {
			if event.paths(nil).Contains(argpath) {
				croak("%s already has an op for %s",
					blob.mark, argpath)
				return false
			}
		}
	} else if optype == opR || optype == opC {
		if len(fields) < 3 {
			croak("too few arguments in add %c", optype)
			return false
		}
		source = fields[1]
		target = fields[2]
		for _, event := range repo.commits(rs.selection) {
			if event.paths(nil).Contains(source) || event.paths(nil).Contains(target) {
				croak("%s already has an op for %s or %s",
					event.mark, source, target)
				return false
			}
			if event.ancestorCount(source) == 0 {
				croak("no previous M for %s", source)
				return false
			}
		}
	} else {
		croak("unknown operation type %c in add command", optype)
		return false
	}
	for _, commit := range repo.commits(rs.selection) {
		fileop := newFileOp(rs.chosen())
		if optype == opD {
			fileop.construct(opD, argpath)
		} else if optype == opM {
			fileop.construct(opM, perms, mark, argpath)
		} else if optype == opR || optype == opC {
			fileop.construct(rune(optype), source, target)
		}
		commit.appendOperation(*fileop)
	}
	return false
}

func (rs *Reposurgeon) HelpBlob() {
	rs.helpOutput(`
Syntax:

     blob

Create a blob at mark :1 after renumbering other marks starting from
:2.  Data is taken from stdin, which may be a here-doc.  This can be
used with the add command to patch data into a repository.
`)
}

// Add a fileop to a specified commit.
func (rs *Reposurgeon) DoBlob(line string) bool {
	if rs.chosen() == nil {
		croak("no repo is loaded")
		return false
	}
	repo := rs.chosen()
	repo.renumber(2, nil)
	blob := newBlob(repo)
	blob.setMark(":1")
	repo.insertEvent(blob, len(repo.frontEvents()), "adding blob")
	parse := rs.newLineParse(line, orderedStringSet{"stdin"})
	defer parse.Closem()
	content, err := ioutil.ReadAll(parse.stdin)
	if err != nil {
		croak("while reading blob content: %v", err)
		return false
	}
	blob.setContent(content, noOffset)
	repo.declareSequenceMutation("adding blob")
	repo.invalidateNamecache()
	return false
}

func (rs *Reposurgeon) HelpRemove() {
	rs.helpOutput(`
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
`)
}

// Delete a fileop from a specified commit.
func (rs *Reposurgeon) DoRemove(line string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo is loaded")
		return false
	}
	if rs.selection == nil {
		rs.selection = newOrderedIntSet()
	}
	orig := line
	opindex, line := popToken(line)
	// FIXME: This needs more general parsing
	optypes := "DMRCN"
	regex := regexp.MustCompile("^[DMRCN]+$")
	match := regex.FindStringIndex(opindex)
	if match != nil {
		optypes = opindex[match[0]:match[1]]
		opindex, line = popToken(line)
	}
	for _, ie := range rs.selection {
		ev := repo.events[ie]
		event, ok := ev.(*Commit)
		if !ok {
			croak("Event %d is not a commit.", ie+1)
			return false
		}
		if opindex == "deletes" {
			ops := make([]FileOp, 0)
			for _, op := range event.operations() {
				if op.op != opD {
					ops = append(ops, op)
				}
			}
			event.setOperations(ops)
			return false
		}
		ind := -1
		// first, see if opindex matches the filenames of any
		// of this event's operations
		for i, op := range event.operations() {
			if !strings.Contains(optypes, string(op.op)) {
				continue
			}
			if op.Path == opindex || op.Source == opindex || op.Target == opindex {
				ind = i
				break
			}
		}
		// otherwise, perhaps it's an integer
		if ind == -1 {
			var err error
			ind, err = strconv.Atoi(opindex)
			ind--
			if err != nil {
				croak("invalid or missing fileop specification '%s' on %s", opindex, orig)
				return false
			}
		}
		target := -1
		if line != "" {
			verb, line := popToken(line)
			if verb == "to" {
				rs.setSelectionSet(line)
				if len(rs.selection) != 1 {
					croak("remove to requires a singleton selection")
					return false
				}
				target = rs.selection[0]
			}
		}
		ops := event.operations()
		present := ind >= 0 && ind < len(ops)
		if !present {
			croak("out-of-range fileop index %d", ind)
			return false
		}
		removed := ops[ind]
		event.fileops = append(ops[:ind], ops[ind+1:]...)
		if target != -1 {
			present := target >= 0 && target < len(repo.events)
			if !present {
				croak("out-of-range target event %d", target+1)
				return false
			}
			commit, ok := repo.events[target].(*Commit)
			if !ok {
				croak("event %d is not a commit", target+1)
				return false
			}
			commit.appendOperation(removed)
			// Blob might have to move, too - we need to keep the
			// relocated op from having an unresolvable forward
			// mark reference.
			if removed.ref != "" && target < ie {
				i := repo.markToIndex(removed.ref)
				blob := repo.events[i]
				repo.events = append(repo.events[:i], repo.events[i+1:]...)
				repo.insertEvent(blob, target, "blob move")
			}
			// FIXME: Scavenge blobs left with no references
		}
	}
	return false
}

func (rs *Reposurgeon) HelpRenumber() {
	rs.helpOutput(`
Renumber the marks in a repository, from :1 up to <n> where <n> is the
count of the last mark. Just in case an importer ever cares about mark
ordering or gaps in the sequence.
`)
}

func (rs *Reposurgeon) DoRenumber(line string) bool {
	// Renumber the marks in the selected repo.
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	rs.repo.renumber(1, nil)
	return false
}

func (rs *Reposurgeon) HelpDedup() {
	rs.helpOutput(`
Deduplicate blobs in the selection set.  If multiple blobs in the selection
set have the same SHA1, throw away all but the first, and change fileops
referencing them to instead reference the (kept) first blob.
`)
}

// Deduplicate identical (up to SHA1) blobs within the selection set
func (rs *Reposurgeon) DoDedup(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	blobMap := make(map[string]string) // hash -> mark
	dupMap := make(map[string]string)  // duplicate mark -> canonical mark
	for _, ei := range selection {
		event := rs.chosen().events[ei]
		if blob, ok := event.(*Blob); ok {
			sha := blob.sha()
			if blobMap[sha] != "" {
				dupMap[blob.mark] = blobMap[sha]
			} else {
				blobMap[sha] = blob.mark
			}
		}
	}
	rs.chosen().dedup(dupMap)
	return false
}

func (rs *Reposurgeon) HelpTimeoffset() {
	rs.helpOutput(`
Apply a time offset to all time/date stamps in the selected set.  An offset
argument is required; it may be in the form [+-]ss, [+-]mm:ss or [+-]hh:mm:ss.
The leading sign is required to distingush it from a selection expression.

Optionally you may also specify another argument in the form [+-]hhmm, a
timeone literal to apply.  To apply a timezone without an offset, use
an offset literal of +0 or -0.
`)
}

// Apply a time offset to all dates in selected events.
func (rs *Reposurgeon) DoTimeoffset(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	if line == "" {
		croak("a signed time offset argument is required.")
		return false
	} else if line[0] != '-' && line[0] != '+' {
		croak("time offset argument must begin with + or -.")
		return false
	}
	offsetOf := func(hhmmss string) (int, error) {
		h := "0"
		m := "0"
		s := "0"
		if strings.Count(hhmmss, ":") == 0 {
			s = hhmmss
		} else if strings.Count(hhmmss, ":") == 1 {
			fields := strings.Split(hhmmss, ":")
			m = fields[0]
			s = fields[1]
		} else if strings.Count(hhmmss, ":") == 2 {
			fields := strings.Split(hhmmss, ":")
			h = fields[0]
			m = fields[1]
			s = fields[2]
		} else {
			croak("too many colons")
			return 0, errors.New("too many colons")
		}
		hn, err := strconv.Atoi(h)
		if err != nil {
			croak("bad literal in hour field")
			return 0, err
		}
		mn, err1 := strconv.Atoi(m)
		if err1 != nil {
			croak("bad literal in minute field")
			return 0, err1
		}
		sn, err2 := strconv.Atoi(s)
		if err2 != nil {
			croak("bad literal in seconds field")
			return 0, err2
		}
		return hn*360 + mn*60 + sn, nil
	}
	args := strings.Fields(line)
	var loc *time.Location
	noffset, err := offsetOf(args[0])
	if err != nil {
		return false
	}
	offset := time.Duration(noffset) * time.Second
	if len(args) > 1 {
		tr := regexp.MustCompile(`[+-][0-9][0-9][0-9][0-9]`)
		if !tr.MatchString(args[1]) {
			croak("expected timezone literal to be [+-]hhmm")
			return false
		}
		zoffset, err1 := offsetOf(args[1])
		if err1 != nil {
			return false
		}
		loc = time.FixedZone(args[1], zoffset)
	}
	for _, ei := range selection {
		event := rs.chosen().events[ei]
		if tag, ok := event.(*Tag); ok {
			if tag.tagger != nil {
				tag.tagger.date.timestamp.Add(offset)
				if len(args) > 1 {
					tag.tagger.date.timestamp = tag.tagger.date.timestamp.In(loc)
				}
			}
		} else if commit, ok := event.(*Commit); ok {
			commit.committer.date.timestamp.Add(offset)
			if len(args) > 1 {
				commit.committer.date.timestamp = commit.committer.date.timestamp.In(loc)
			}
			for _, author := range commit.authors {
				author.date.timestamp.Add(offset)
				if len(args) > 1 {
					author.date.timestamp = author.date.timestamp.In(loc)
				}
			}
		}
	}
	return false
}

func (rs *Reposurgeon) HelpWhen() {
	rs.helpOutput(`
Interconvert between git timestamps (integer Unix time plus TZ) and
RFC3339 format.  Takes one argument, autodetects the format.  Useful
when eyeballing export streams.  Also accepts any other supported
date format and converts to RFC3339.
`)
}
func (rs *Reposurgeon) DoWhen(LineIn string) (StopOut bool) {
	if LineIn == "" {
		croak("a timestamp in either integer or RFC3339 form is required.")
		return false
	}
	d, err := newDate(LineIn)
	if err != nil {
		croak("unrecognized date format")
	} else if strings.Contains(LineIn, "Z") {
		fmt.Println(d.String())
	} else {
		fmt.Println(d.rfc3339())
	}
	return false
}

func (rs *Reposurgeon) HelpDivide() {
	rs.helpOutput(`
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
`)
}

func (rs *Reposurgeon) DoDivide(_line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	if len(rs.selection) == 0 {
		croak("one or possibly two arguments specifying a link are required")
		return false
	}
	earlyEvent := rs.chosen().events[rs.selection[0]]
	earlyCommit, ok := earlyEvent.(*Commit)
	if !ok {
		croak("first element of selection is not a commit")
		return false
	}
	possibles := earlyCommit.children()
	var late Event
	var lateCommit *Commit
	if len(rs.selection) == 1 {
		if len(possibles) > 1 {
			croak("commit has multiple children, one must be specified")
			return false
		} else if len(possibles) == 1 {
			late = possibles[0]
			lateCommit, ok = late.(*Commit)
			if !ok {
				croak("only child of selected commit is not a commit")
				return false
			}
		} else {
			croak("parent has no children")
			return false
		}
	} else if len(rs.selection) == 2 {
		late = rs.chosen().events[rs.selection[1]]
		lateCommit, ok = late.(*Commit)
		if !ok {
			croak("last element of selection is not a commit")
			return false
		}
		if !orderedStringSet(lateCommit.parentMarks()).Contains(earlyCommit.mark) {
			croak("not a parent-child pair")
			return false
		}
	} else if len(rs.selection) > 2 {
		croak("too many arguments")
	}
	//assert(early && late)
	rs.selection = nil
	// Try the topological cut first
	if rs.cut(earlyCommit, lateCommit) {
		respond("topological cut succeeded")
	} else {
		// If that failed, cut anyway and rename the branch segments
		lateCommit.removeParent(earlyCommit)
		if earlyCommit.Branch != lateCommit.Branch {
			respond("no branch renames were required")
		} else {
			basename := earlyCommit.Branch
			respond("%s has been split into %s-early and %s-late",
				basename, basename, basename)
			for i, event := range rs.chosen().events {
				if commit, ok := event.(*Commit); ok && commit.Branch == basename {
					if i <= rs.selection[0] {
						commit.Branch += "-early"
					} else {
						commit.Branch += "-late"
					}
				}
			}
		}
	}
	if control.isInteractive() && !control.flagOptions["quiet"] {
		rs.DoChoose("")
	}
	return false
}

func (rs *Reposurgeon) HelpExpunge() {
	rs.helpOutput(`
Expunge files from the selected portion of the repo history; the
default is the entire history.  The arguments to this command may be
paths or regular expressions matching paths (regexps must
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
`)
}

// Expunge files from the chosen repository.
func (rs *Reposurgeon) DoExpunge(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()

	}
	rs.expunge(selection, strings.Fields(line))
	return false
}

func (rs *Reposurgeon) HelpSplit() {
	rs.helpOutput(`
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
`)
}

// Split a commit.
func (rs *Reposurgeon) DoSplit(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	if len(rs.selection) != 1 {
		croak("selection of a single commit required for this command")
		return false
	}
	where := rs.selection[0]
	event := rs.chosen().events[where]
	commit, ok := event.(*Commit)
	if !ok {
		croak("selection doesn't point at a commit")
		return false
	}
	fields := strings.Fields(line)
	prep := fields[0]
	obj := fields[1]
	if len(fields) != 2 {
		croak("ill-formed split command")
		return false
	}
	if prep == "at" {
		splitpoint, err := strconv.Atoi(obj)
		if err != nil {
			croak("expected integer fileop index (1-origin)")
			return false
		}
		splitpoint--
		if splitpoint > len(commit.operations()) {
			croak("fileop index %d out of range", splitpoint)
			return false
		}
		err = rs.chosen().splitCommitByIndex(where, splitpoint)
		if err != nil {
			croak(err.Error())
			return false
		}
	} else if prep == "by" {
		err := rs.chosen().splitCommitByPrefix(where, obj)
		if err != nil {
			croak(err.Error())
			return false
		}
	} else {
		croak("don't know what to do for preposition %s", prep)
		return false
	}
	respond("new commits are events %d and %d.", where+1, where+2)
	return false
}

func (rs *Reposurgeon) HelpUnite() {
	rs.helpOutput(`
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
`)
}

// Unite repos together.
func (rs *Reposurgeon) DoUnite(line string) bool {
	rs.unchoose()
	factors := make([]*Repository, 0)
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	for _, name := range strings.Fields(parse.line) {
		repo := rs.repoByName(name)
		if repo == nil {
			croak("no such repo as %s", name)
			return false
		}
		factors = append(factors, repo)
	}
	if len(factors) < 2 {
		croak("unite requires two or more repo name arguments")
		return false
	}
	rs.unite(factors, parse.options.toStringSet())
	if control.isInteractive() && !control.flagOptions["quiet"] {
		rs.DoChoose("")
	}
	return false
}

func (rs *Reposurgeon) HelpGraft() {
	rs.helpOutput(`
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
resolved in the control of the currently chosen one. Finally, the
named repo is removed from the load list.

With the option --prune, prepend a deleteall operation into the root
of the grafted repository.
`)
}

// Graft a named repo onto the selected one.
func (rs *Reposurgeon) DoGraft(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	if len(rs.repolist) == 0 {
		croak("no repositories are loaded.")
		return false
	}
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	graftRepo := rs.repoByName(parse.line)
	requireGraftPoint := true
	var graftPoint int
	if rs.selection != nil && len(rs.selection) == 1 {
		graftPoint = rs.selection[0]
	} else {
		for _, commit := range graftRepo.commits(nil) {
			for _, parent := range commit.parents() {
				if isCallout(parent.getMark()) {
					requireGraftPoint = false
				}
			}
		}
		if !requireGraftPoint {
			graftPoint = invalidGraftIndex
		} else {
			croak("a singleton selection set is required.")
			return false
		}
	}
	// OK, we've got the two repos and the graft point.  Do it.
	rs.chosen().graft(graftRepo, graftPoint, parse.options.toStringSet())
	rs.removeByName(graftRepo.name)
	return false
}

func (rs *Reposurgeon) HelpDebranch() {
	rs.helpOutput(`
Takes one or two arguments which must be the names of source and target
branches; if the second (target) argument is omitted it defaults to 'master'.
The history of the source branch is merged into the history of the target
branch, becoming the history of a subdirectory with the name of the source
branch. Any trailing segment of a branch name is accepted as a synonym for
it; thus 'master' is the same as 'refs/heads/master'.  Any resets of the
source branch are removed.
`)
}

// Turn a branch into a subdirectory.
func (rs *Reposurgeon) DoDebranch(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	args := strings.Fields(line)
	if len(args) == 0 {
		croak("debranch command requires at least one argument")
		return false
	}
	target := "refs/heads/master"
	source := args[0]
	if len(args) == 2 {
		target = args[1]
	}
	repo := rs.chosen()
	branches := repo.branchmap()
	if branches[source] == "" {
		for candidate := range branches {
			if strings.HasSuffix(candidate, string(os.PathSeparator)+source) {
				source = candidate
				goto found1
			}
		}
		croak("no branch matches source %s", source)
		return false
	found1:
	}
	if branches[target] == "" {
		for candidate := range branches {
			if strings.HasSuffix(candidate, string(os.PathSeparator)+target) {
				target = candidate
				goto found2
			}
		}
		croak("no branch matches %s", target)
		return false
	found2:
	}
	// Now that the arguments are in proper form, implement
	stip := repo.markToIndex(branches[source])
	scommits := append(repo.ancestors(stip), stip)
	sort.Ints(scommits)
	ttip := repo.markToIndex(branches[target])
	tcommits := append(repo.ancestors(ttip), ttip)
	sort.Ints(tcommits)
	// Don't touch commits up to the branch join.
	lastParent := make([]string, 0)
	for len(scommits) > 0 && len(tcommits) > 0 && scommits[0] == tcommits[0] {
		lastParent = []string{repo.events[scommits[0]].getMark()}
		scommits = scommits[1:]
		tcommits = tcommits[1:]
	}
	pref := filepath.Base(source)
	for _, ci := range scommits {
		for idx := range repo.events[ci].(*Commit).operations() {
			fileop := &(repo.events[ci].(*Commit).fileops[idx])
			if fileop.op == opD || fileop.op == opM {
				fileop.Path = filepath.Join(pref, fileop.Path)
			} else if fileop.op == opR || fileop.op == opC {
				fileop.Source = filepath.Join(pref, fileop.Source)
				fileop.Target = filepath.Join(pref, fileop.Target)
			}
		}
	}
	merged := append(scommits, tcommits...)
	sort.Ints(merged)
	sourceReset := -1
	for _, i := range merged {
		commit := repo.events[i].(*Commit)
		if len(lastParent) > 0 {
			trailingMarks := commit.parentMarks()
			if len(trailingMarks) > 0 {
				trailingMarks = trailingMarks[1:]
			}
			commit.setParentMarks(append(lastParent, trailingMarks...))
		}
		commit.setBranch(target)
		lastParent = []string{commit.mark}
	}
	for i, event := range rs.repo.events {
		if reset, ok := event.(*Reset); ok && reset.ref == source {
			sourceReset = i
		}
	}
	if sourceReset != -1 {
		repo.delete([]int{sourceReset}, nil)
	}
	repo.declareSequenceMutation("debranch operation")
	return false
}

func (rs *Reposurgeon) HelpPath() {
	rs.helpOutput(`
Rename a path in every fileop of every selected commit.  The
default selection set is all commits. The first argument is interpreted as a
Go regular expression to match against paths; the second may contain Go
back-reference syntax.

Ordinarily, if the target path already exists in the fileops, or is visible
in the ancestry of the commit, this command throws an error.  With the
--force option, these checks are skipped.
`)
}

type pathAction struct {
	fileop  *FileOp
	commit  *Commit // Only used for debug dump
	attr    string
	newpath string
}

func (pa pathAction) String() string {
	var i int
	var op FileOp
	for i, op = range pa.commit.fileops {
		if op.Equals(pa.fileop) {
			break
		}
	}

	return fmt.Sprintf("[%s(%d) %s=%s]", pa.commit.idMe(), i, pa.attr, pa.newpath)
}

// Rename paths in the history.
func (rs *Reposurgeon) DoPath(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	selection := rs.selection
	if selection == nil {
		selection = repo.all()
	}
	var sourcePattern string
	sourcePattern, line = popToken(line)
	sourceRE, err1 := regexp.Compile(sourcePattern)
	if err1 != nil {
		logit(logWARN, "source path regexp compilation failed: %v", err1)
		return false
	}
	var verb string
	verb, line = popToken(line)
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	if verb == "rename" {
		force := parse.options.Contains("--force")
		targetPattern, _ := popToken(parse.line)
		if targetPattern == "" {
			logit(logWARN, "no target specified in rename")
			return false
		}
		actions := make([]pathAction, 0)
		for _, commit := range repo.commits(selection) {
			for idx := range commit.fileops {
				for _, attr := range []string{"Path", "Source", "Target"} {
					fileop := &commit.fileops[idx]
					if oldpath, ok := getAttr(*fileop, attr); ok {
						if ok && oldpath != "" && sourceRE.MatchString(oldpath) {
							newpath := GoReplacer(sourceRE, oldpath, targetPattern)
							if !force && commit.visible(newpath) != nil {
								logit(logWARN, "rename of %s at %s failed, %s visible in ancestry", oldpath, commit.idMe(), newpath)
								return false
							} else if !force && commit.paths(nil).Contains(newpath) {
								logit(logWARN, "rename of %s at %s failed, %s exists there", oldpath, commit.idMe(), newpath)
								return false
							} else {
								actions = append(actions, pathAction{fileop, commit, attr, newpath})
							}
						}
					}
				}
			}
		}
		// All checks must pass before any renames
		for _, action := range actions {
			setAttr(action.fileop, action.attr, action.newpath)
		}
	} else {
		logit(logWARN, "unknown verb '%s' in path command.", verb)
	}
	return false
}

func (rs *Reposurgeon) HelpPaths() {
	rs.helpOutput(`
Without a modifier, list all paths touched by fileops in
the selection set (which defaults to the entire repo). This
variant does > redirection.

With the 'sub' modifier, take a second argument that is a directory
name and prepend it to every path. With the 'sup' modifier, strip
any directory argument from the start of the path if it appears there;
with no argument, strip the first directory component from every path.
`)
}

func (rs *Reposurgeon) DoPaths(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	if !strings.HasPrefix(line, "sub") && !strings.HasPrefix(line, "sup") {
		allpaths := newOrderedStringSet()
		for _, commit := range rs.chosen().commits(rs.selection) {
			allpaths = allpaths.Union(commit.paths(nil))
		}
		sort.Strings(allpaths)
		fmt.Fprint(parse.stdout, strings.Join(allpaths, "\n")+"\n")
		return false
	}
	fields := strings.Fields(line)
	if fields[0] == "sub" {
		if len(fields) < 2 {
			croak("Error paths sub needs a directory name argument")
			return false
		}
		prefix := fields[1]
		modified := rs.chosen().pathWalk(selection,
			func(f string) string { return prefix + string(os.PathSeparator) + f })
		fmt.Fprint(parse.stdout, strings.Join(modified, "\n")+"\n")
	} else if fields[0] == "sup" {
		if len(fields) == 1 {
			modified := rs.chosen().pathWalk(selection,
				func(f string) string {
					slash := strings.Index(f, "/")
					if slash == -1 {
						return f
					}
					return f[slash+1:]
				})
			sort.Strings(modified)
			fmt.Fprint(parse.stdout, strings.Join(modified, "\n")+"\n")
		} else {
			prefix := fields[1]
			if !strings.HasSuffix(prefix, "/") {
				prefix += "/"
			}
			modified := rs.chosen().pathWalk(selection,
				func(f string) string {
					if strings.HasPrefix(f, prefix) {
						return f[len(prefix):]
					}
					return f
				})
			sort.Strings(modified)
			fmt.Fprint(parse.stdout, strings.Join(modified, "\n")+"\n")
			return false
		}
	}
	//rs.chosen().invalidateManifests()
	return false
}

func (rs *Reposurgeon) HelpManifest() {
	rs.helpOutput(`
Print commit path lists. Takes an optional selection set argument
defaulting to all commits, and an optional Go regular expression.
For each commit in the selection set, print the mapping of all paths in
that commit tree to the corresponding blob marks, mirroring what files
would be created in a checkout of the commit. If a regular expression
is given, only print "path -> mark" lines for paths matching it.
This command supports > redirection.
`)
}

// Print all files (matching the regex) in the selected commits trees.
func (rs *Reposurgeon) DoManifest(line string) bool {
	if rs.chosen() == nil {
		logit(logWARN, "no repo has been chosen")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	var filterFunc = func(s string) bool { return true }
	line = strings.TrimSpace(parse.line)
	if line != "" {
		filterRE, err := regexp.Compile(line)
		if err != nil {
			logit(logWARN, "invalid regular expression: %v", err)
			return false
		}
		filterFunc = func(s string) bool {
			return filterRE.MatchString(s)
		}
	}
	events := rs.chosen().events
	for _, ei := range selection {
		commit, ok := events[ei].(*Commit)
		if !ok {
			continue
		}
		header := fmt.Sprintf("Event %d, ", ei+1)
		header = header[:len(header)-2]
		header += " " + strings.Repeat("=", 72-len(header)) + "\n"
		fmt.Fprint(parse.stdout, header)
		if commit.legacyID != "" {
			fmt.Fprintf(parse.stdout, "# Legacy-ID: %s\n", commit.legacyID)
		}
		fmt.Fprintf(parse.stdout, "commit %s\n", commit.Branch)
		if commit.mark != "" {
			fmt.Fprintf(parse.stdout, "mark %s\n", commit.mark)
		}
		fmt.Fprint(parse.stdout, "\n")
		type ManifestItem struct {
			path  string
			entry *ManifestEntry
		}
		manifestItems := make([]ManifestItem, 0)
		for _, elt := range commit.manifest().items() {
			path, entry := elt.name, elt.value.(*ManifestEntry)
			if filterFunc(path) {
				manifestItems = append(manifestItems, ManifestItem{path, entry})
			}
		}
		sort.Slice(manifestItems, func(i, j int) bool { return manifestItems[i].path < manifestItems[j].path })
		for _, item := range manifestItems {
			fmt.Fprintf(parse.stdout, "%s -> %s\n", item.path, item.entry.ref)
		}
	}
	return false
}

func (rs *Reposurgeon) HelpTagify() {
	rs.helpOutput(`
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
`)
}

// Search for empty commits and turn them into tags.
func (rs *Reposurgeon) DoTagify(line string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = repo.all()
	}
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	if parse.line != "" {
		croak("too many arguments for tagify.")
		return false
	}
	before := len(repo.commits(nil))
	repo.tagifyEmpty(
		selection,
		parse.options.Contains("--tipdeletes"),
		parse.options.Contains("--tagify-merges"),
		parse.options.Contains("--canonicalize"),
		nil,
		nil,
		true,
		func(msg string) { fmt.Print(msg) })
	after := len(repo.commits(nil))
	respond("%d commits tagified.", before-after)
	return false
}

func (rs *Reposurgeon) HelpMerge() {
	rs.helpOutput(`
Create a merge link. Takes a selection set argument, ignoring all but
the lowest (source) and highest (target) members.  Creates a merge link
from the highest member (child) to the lowest (parent).
`)
}
func (rs *Reposurgeon) DoMerge(_line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	commits := rs.chosen().commits(rs.selection)
	if len(commits) < 2 {
		croak("merge requires a selection set with at least two commits.")
		return false
	}
	early := commits[0]
	late := commits[len(commits)-1]
	if late.mark < early.mark {
		late, early = early, late
	}
	late.addParentCommit(early)
	//earlyID = fmt.Sprintf("%s (%s)", early.mark, early.Branch)
	//lateID = fmt.Sprintf("%s (%s)", late.mark, late.Branch)
	//respond("%s added as a parent of %s", earlyID, lateID)
	return false
}

func (rs *Reposurgeon) HelpUnmerge() {
	rs.helpOutput(`
Linearizes a commit. Takes a selection set argument, which must resolve to a
single commit, and removes all its parents except for the first. It is
equivalent to reparent --rebase {first parent},{commit}, where {commit} is the
selection set given to unmerge and {first parent} is a set resolving to that
commit's first parent, but doesn't need you to find the first parent yourself.
`)
}

func (rs *Reposurgeon) DoUnmerge(_line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	if len(rs.selection) != 1 {
		croak("unmerge requires a single commit.")
		return false
	}
	event := rs.chosen().events[rs.selection[0]]
	if commit, ok := event.(*Commit); !ok {
		croak("unmerge target is not a commit.")
	} else {
		commit.setParents(commit.parents()[:1])
	}
	return false

}

func (rs *Reposurgeon) HelpReparent() {
	rs.helpOutput(`
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
`)
}

func (rs *Reposurgeon) DoReparent(line string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen.")
		return false
	}
	// FIXME: Prevents infinite loop, but shouldn't be necessary.
	for _, commit := range repo.commits(nil) {
		commit.invalidateManifests()
	}
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	useOrder := parse.options.Contains("--use-order")
	// Determine whether an event resort might be needed.  it is
	// assumed that ancestor commits already have a lower event
	// index before this function is called, which should be true
	// as long as every function that modifies the DAG calls
	// Repository.resort() when needed.  thus, a call to resort()
	// should only be necessary if --use-order is passed and a
	// parent will have an index higher than the modified commit.
	var doResort bool
	if useOrder {
		for _, idx := range rs.selection[:len(rs.selection)-1] {
			if idx > rs.selection[len(rs.selection)-1] {
				doResort = true
			}
		}
	} else {
		sort.Ints(rs.selection)
	}
	selected := repo.commits(rs.selection)
	if len(selected) == 0 || len(rs.selection) != len(selected) {
		logit(logWARN, "reparent requires one or more selected commits")
	}
	child := selected[len(selected)-1]
	parents := make([]CommitLike, len(rs.selection)-1)
	for i, c := range selected[:len(selected)-1] {
		parents[i] = c
	}
	if doResort {
		for _, p := range parents {
			if p.(*Commit).descendedFrom(child) {
				logit(logWARN, "reparenting a commit to its own descendant would introduce a cycle")
				return false
			}
		}
	}
	if !parse.options.Contains("--rebase") {
		// Recreate the state of the tree
		f := *newFileOp(repo)
		f.construct(deleteall)
		newops := []FileOp{f}
		for _, elt := range child.manifest().items() {
			path, entry := elt.name, elt.value.(*ManifestEntry)
			f = *newFileOp(repo)
			f.construct(opM, entry.mode, entry.ref, path)
			if entry.ref == "inline" {
				f.inline = entry.inline
			}
			newops = append(newops, f)
		}
		newops = append(newops, child.operations()...)
		child.setOperations(newops)
		child.sortOperations()
	}
	child.setParents(parents)
	// Restore this when we have toposort working identically in Go and Python.
	if doResort {
		repo.resort()
	}
	return false
}

func (rs *Reposurgeon) HelpReorder() {
	rs.helpOutput(`
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
`)
}

// Re-order a contiguous range of commits.
func (rs *Reposurgeon) DoReorder(lineIn string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen.")
		return false
	}
	sel := rs.selection
	if sel == nil {
		croak("no selection")
		return false
	}
	parse := rs.newLineParse(lineIn, nil)
	defer parse.Closem()
	if parse.line != "" {
		croak("'reorder' takes no arguments")
		return false
	}
	commits := repo.commits(sel)
	if len(commits) == 0 {
		croak("no commits in selection")
		return false
	} else if len(commits) == 1 {
		croak("only 1 commit selected; nothing to re-order")
		return false
	} else if len(commits) != len(sel) {
		croak("selection set must be all commits")
		return false
	}
	_, quiet := parse.OptVal("--quiet")

	repo.reorderCommits(sel, quiet)
	return false
}

func (rs *Reposurgeon) HelpBranch() {
	rs.helpOutput(`
Rename or delete a branch (and any associated resets).  First argument
must be an existing branch name; second argument must one of the verbs
'rename' or 'delete'. The branchname may use backslash escapes
interpreted by the Python string-escape codec, such as \\s.

For a 'rename', the third argument may be any token that is a syntactically
valid branch name (but not the name of an existing branch). For a 'delete',
no third argument is required.

For either name, if it does not contain a '/' the prefix 'heads/'
is prepended. If it does not begin with 'refs/', 'refs/' is prepended.
`)
}

// Rename a branch or delete it.
func (rs *Reposurgeon) DoBranch(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	branchname, line := popToken(line)
	var err error
	branchname, err = stringEscape(branchname)
	if err != nil {
		croak("while selecting branch: %v", err)
		return false
	}
	if !strings.Contains(branchname, "/") {
		branchname = "refs/heads/" + branchname
	}
	if !repo.branchset().Contains(branchname) {
		croak("no such branch as %s", branchname)
		return false
	}
	var verb string
	verb, line = popToken(line)
	if verb == "rename" {
		var newname string
		newname, line = popToken(line)
		if newname == "" {
			croak("new branch name must be nonempty.")
			return false
		}
		if !strings.Contains(newname, "/") {
			newname = "refs/heads/" + newname
		}
		if repo.branchset().Contains(newname) {
			croak("there is already a branch named '%s'.", newname)
			return false
		}
		for _, event := range repo.events {
			if commit, ok := event.(*Commit); ok {
				if commit.Branch == branchname {
					commit.setBranch(newname)
				}
			} else if reset, ok := event.(*Reset); ok {
				if reset.ref == branchname {
					reset.ref = newname
				}
			}
		}
	} else if verb == "delete" {
		deletia := make([]int, 0)
		for ei := range repo.events {
			event := repo.events[ei]
			if commit, ok := event.(*Commit); ok {
				if commit.Branch == branchname {
					deletia = append(deletia, ei)
				}
			} else if reset, ok := event.(*Reset); ok {
				if reset.ref == branchname {
					deletia = append(deletia, ei)
				}
			}
		}
		repo.delete(orderedIntSet(deletia), nil)
	} else {
		croak("unknown verb '%s' in branch command.", verb)
		return false
	}
	return false
}

func (rs *Reposurgeon) HelpTag() {
	rs.helpOutput(`
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
Such deletions can be restricted by a selection set in the normal way.

Tag names may use backslash escapes interpreted by the Python
string-escape codec, such as \s.

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
`)
}

// Move a tag to point to a specified commit, or rename it, or delete it.
func (rs *Reposurgeon) DoTag(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	// A tag name can refer to one of the following things {
	// (1) A tag object, by name
	// (2) A reset object having a name in the tags/ namespace
	// (3) The tip commit of a branch with branch fields
	// These things often occur in combination. Notably, git-fast-export
	// generates for each tag object corresponding branch labels on
	// some ancestor commits - the rule for where this stops is unclear.
	var tagname string
	tagname, line = popToken(line)
	if len(tagname) == 0 {
		croak("missing tag name")
		return false
	}
	var err error
	tagname, err = stringEscape(tagname)
	if err != nil {
		croak("in tag command: %v", err)
		return false
	}
	var verb string
	verb, line = popToken(line)
	if verb == "create" {
		var ok bool
		var target *Commit
		if repo.named(tagname) != nil {
			croak("something is already named %s", tagname)
			return false
		}
		rs.setSelectionSet(line)
		if rs.selection == nil {
			croak("usage: tag <name> create <singleton-selection>")
			return false
		} else if len(rs.selection) != 1 {
			croak("tag create requires a singleton commit set.")
			return false
		} else if target, ok = repo.events[rs.selection[0]].(*Commit); !ok {
			croak("create target is not a commit.")
			return false
		}
		tag := newTag(repo, tagname, target.mark,
			target.committer.clone(),
			target.Comment)
		tag.tagger.date.timestamp = tag.tagger.date.timestamp.Add(time.Second) // So it is unique
		var lasttag int
		var lastcommit int
		for i, event := range repo.events {
			if _, ok := event.(*Tag); ok {
				lasttag = i
			} else if _, ok := event.(*Commit); ok {
				lastcommit = i
			}
			control.baton.twirl()
		}
		if lasttag == 0 {
			lasttag = lastcommit
		}
		repo.insertEvent(tag, lasttag+1, "tag creation")
		control.baton.twirl()
		return false
	}
	tags := make([]*Tag, 0)
	resets := make([]*Reset, 0)
	commits := make([]*Commit, 0)
	if tagname[0] == '/' && tagname[len(tagname)-1] == '/' {
		// Regexp - can refer to a list of tags matched
		tagre := regexp.MustCompile(tagname[1 : len(tagname)-1])
		selection := rs.selection
		if selection == nil {
			selection = repo.all()
		}
		for _, idx := range selection {
			event := repo.events[idx]
			if tag, ok := event.(*Tag); ok && tagre.MatchString(tag.name) {
				tags = append(tags, tag)
			} else if reset, ok := event.(*Reset); ok && tagre.MatchString(reset.ref[11:]) {
				// len("refs/heads/") = 11
				resets = append(resets, reset)
			} else if commit, ok := event.(*Commit); ok && tagre.MatchString(commit.Branch[10:]) {
				// len("refs/tags/") = 10
				commits = append(commits, commit)
			}
			control.baton.twirl()
		}
	} else {
		// Non-regexp - can only refer to a single tag
		fulltagname := branchname(tagname)
		for _, event := range repo.events {
			if tag, ok := event.(*Tag); ok && tag.name == tagname {
				tags = append(tags, tag)
			} else if reset, ok := event.(*Reset); ok && reset.ref == fulltagname {
				resets = append(resets, reset)
			} else if commit, ok := event.(*Commit); ok && commit.Branch == fulltagname {
				commits = append(commits, commit)
			}
			control.baton.twirl()
		}
	}
	if len(tags) == 0 && len(resets) == 0 && len(commits) == 0 {
		croak("no tags matching %s", tagname)
		return false
	}
	if verb == "move" {
		var target *Commit
		var ok bool
		rs.setSelectionSet(line)
		if len(rs.selection) != 1 {
			croak("tag move requires a singleton commit set.")
			return false
		} else if target, ok = repo.events[rs.selection[0]].(*Commit); !ok {
			croak("move target is not a commit.")
			return false
		}
		if len(tags) > 0 {
			for _, tag := range tags {
				tag.forget()
				tag.remember(repo, target.mark)
				control.baton.twirl()
			}
		}
		if len(resets) > 0 {
			if len(resets) == 1 {
				resets[0].committish = target.mark
			} else {
				croak("cannot move multiple tags.")
			}
			control.baton.twirl()
		}
		if len(commits) > 0 {
			logit(logWARN, "warning - tag move does not modify branch fields")
		}
	} else if verb == "rename" {
		if len(tags) > 1 {
			croak("exactly one tag is required for rename")
			return false
		}
		var newname string
		newname, line = popToken(line)
		if newname == "" {
			croak("new tag name must be nonempty.")
			return false
		}
		if len(tags) == 1 {
			for _, event := range repo.events {
				if tag, ok := event.(*Tag); ok && tag != tags[0] && tag.name == tags[0].name {
					croak("tag name collision, not renaming.")
					return false
				}
			}
			tags[0].name = newname
			control.baton.twirl()
		}
		fullnewname := branchname(newname)
		for _, reset := range resets {
			reset.ref = fullnewname
		}
		for _, event := range commits {
			event.Branch = fullnewname
		}
	} else if verb == "delete" {
		for _, tag := range tags {
			// the order here in important
			repo.delete([]int{tag.index()}, nil)
			tag.forget()
			control.baton.twirl()
		}
		if len(tags) > 0 {
			repo.declareSequenceMutation("tag deletion")
		}
		for _, reset := range resets {
			reset.forget()
			repo.delete([]int{repo.eventToIndex(reset)}, nil)
		}
		if len(resets) > 0 {
			repo.declareSequenceMutation("reset deletion")
		}
		// Strictly speak it doesn't matter what new tag identifier we patch in to
		// replace the deleted one(s), because when thev repos is imported only the
		// names of the resets will matter.  The goal here is to produce something
		// similar enough to what git-fast-export would dump that it would coincide
		// in most cases, because that eases regression testing.
		if len(commits) > 0 {
			successors := make([]string, 0)
			for _, child := range commits[len(commits)-1].children() {
				childCommit, ok := child.(*Commit)
				if !ok {
					continue
				}
				childFather, ok := childCommit.parents()[0].(*Commit)
				if !ok {
					continue
				}
				if childFather == commits[len(commits)-1] {
					successors = append(successors, childCommit.Branch)
				}
			}

			//successors := {child.Branch for child in commits[-1].children() if child.parents()[0] == commits[-1]}
			if len(successors) >= 1 {
				for _, event := range commits {
					event.Branch = successors[0]
				}
			} else {
				for _, event := range commits {
					if event.hasParents() && event.isCommit() && event.parents()[0].isCommit() {
						event.Branch = event.parents()[0].(*Commit).Branch
					} else {
						// Must be a root commit. This should
						// work unless rgee repo is multiroot
						// and probably eon't foo up even then.
						event.Branch = "refs/heads/master"
					}
				}
			}
			control.baton.twirl()
		}
	} else {
		croak("unknown verb '%s' in tag command.", verb)
		return false
	}
	return false
}

func (rs *Reposurgeon) HelpReset() {
	rs.helpOutput(`
Create, move, rename, or delete a reset. Create is a special case; it
requires a singleton selection which is the associated commit for the
reset, takes as a first argument the name of the reset (which must not
exist), and ends with the keyword create.

In the other modes, the first argument must match an existing reset
name with the selection; second argument must be one of the verbs
'move', 'rename', or 'delete'. The default selection is all events.

For a 'move', a third argument must be a singleton selection set. For
a 'rename', the third argument may be any token that can be interpreted
as a valid reset name (but not the name of an existing
reset). For a 'delete', no third argument is required.

Reset names may use backslash escapes interpreted by the Go
string-escape codec, such as \s.

An argument matches a reset's name if it is either the entire
reference (refs/heads/FOO or refs/tags/FOO for some some value of FOO)
or the basename (e.g. FOO), or a suffix of the form heads/FOO or tags/FOO.
An unqualified basename is assumed to refer to a head.

When a reset is renamed, commit branch fields matching the tag are
renamed with it to match.  When a reset is deleted, matching branch
fields are changed to match the branch of the unique descendent of the
tip commit of the associated branch, if there is one.  When a reset is
moved, no branch fields are changed.
`)
}

// Move a reset to point to a specified commit, or rename it, or delete it.
func (rs *Reposurgeon) DoReset(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	var resetname string
	var err error
	resetname, line = popToken(line)
	resetname, err = stringEscape(resetname)
	if err != nil {
		croak("in reset command: %v", err)
		return false
	}
	if !strings.Contains(resetname, "/") {
		resetname = "heads/" + resetname
	}
	if !strings.HasPrefix(resetname, "refs/") {
		resetname = "refs/" + resetname
	}
	resets := make([]*Reset, 0)
	selection := rs.selection
	if selection == nil {
		selection = rs.repo.all()
	}
	for _, ei := range selection {
		reset, ok := repo.events[ei].(*Reset)
		if ok && reset.ref == resetname {
			resets = append(resets, reset)
		}
	}
	var verb string
	verb, line = popToken(line)
	if verb == "create" {
		var target *Commit
		var ok bool
		if len(resets) > 0 {
			croak("one or more resets match %s", resetname)
			return false
		}
		if len(rs.selection) != 1 {
			croak("reset create requires a singleton commit set.")
			return false
		} else if target, ok = repo.events[rs.selection[0]].(*Commit); !ok {
			croak("create target is not a commit.")
			return false
		}
		reset := newReset(repo, resetname, target.mark)
		repo.addEvent(reset)
		repo.declareSequenceMutation("reset create")
	} else if verb == "move" {
		var reset *Reset
		var target *Commit
		var ok bool
		if len(resets) == 0 {
			croak("no such reset as %s", resetname)
		}
		if len(resets) == 1 {
			reset = resets[0]
		} else {
			croak("can't move multiple resets")
			return false
		}
		rs.setSelectionSet(line)
		if len(rs.selection) != 1 {
			croak("reset move requires a singleton commit set.")
			return false
		} else if target, ok = repo.events[rs.selection[0]].(*Commit); !ok {
			croak("move target is not a commit.")
			return false
		}
		reset.forget()
		reset.remember(repo, target.mark)
		repo.declareSequenceMutation("reset move")
	} else if verb == "rename" {
		var newname string
		if len(resets) == 0 {
			croak("no such reset as %s", resetname)
			return false
		}
		newname, line = popToken(line)
		if newname == "" {
			croak("new reset name must be nonempty.")
			return false
		}
		if strings.Count(newname, "/") == 0 {
			newname = "heads/" + newname
		}
		if !strings.HasPrefix(newname, "refs/") {
			newname = "refs/" + newname
		}
		selection := rs.selection
		if selection == nil {
			selection = repo.all()
		}
		for _, ei := range selection {
			reset, ok := repo.events[ei].(*Reset)
			if ok && reset.ref == newname {
				croak("reset reference collision, not renaming.")
				return false
			}
		}
		for _, commit := range repo.commits(nil) {
			if commit.Branch == newname {
				croak("commit branch collision, not renaming.")
				return false
			}
		}

		for _, reset := range resets {
			reset.ref = newname
		}
		for _, commit := range repo.commits(nil) {
			if commit.Branch == resetname {
				commit.Branch = newname
			}
		}
	} else if verb == "delete" {
		if len(resets) == 0 {
			croak("no such reset as %s", resetname)
			return false
		}
		var tip *Commit
		for _, commit := range repo.commits(nil) {
			if commit.Branch == resetname {
				tip = commit
			}
		}
		if tip != nil && len(tip.children()) == 1 {
			successor := tip.children()[0]
			if cSuccessor, ok := successor.(*Commit); ok {
				for _, commit := range repo.commits(nil) {
					if commit.Branch == resetname {
						commit.Branch = cSuccessor.Branch
					}
				}
			}
		}
		for _, reset := range resets {
			reset.forget()
			repo.delete([]int{repo.eventToIndex(reset)}, nil)
		}
		repo.declareSequenceMutation("reset delete")
	} else {
		croak("unknown verb '%s' in reset command.", verb)
	}
	return false
}

func (rs *Reposurgeon) HelpIgnores() {
	rs.helpOutput(`
Intelligent handling of ignore-pattern files.

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
`)
}

// Manipulate ignore patterns in the repo.
func (rs *Reposurgeon) DoIgnores(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	if rs.preferred != nil && rs.ignorename == "" {
		rs.ignorename = rs.preferred.ignorename
	}
	if rs.preferred == nil {
		croak("preferred repository type has not been set")
		return false
	}
	if rs.ignorename == "" {
		croak("preferred repository type has no declared ignorename")
		return false
	}
	isIgnore := func(blob *Blob) bool {
		if len(blob.pathlist) == 0 {
			return false
		}
		for _, fpath := range blob.pathlist {
			if !strings.HasSuffix(fpath, rs.ignorename) {
				return false
			}
		}
		return true
	}
	for _, verb := range strings.Fields(line) {
		if verb == "defaults" {
			if rs.preferred.styleflags.Contains("import-defaults") {
				croak("importer already set default ignores")
				return false
			} else if len(rs.preferred.dfltignores) == 0 {
				croak("no default ignores in %s", rs.preferred.name)
				return false
			} else {
				changecount := 0
				// Modify existing ignore files
				for _, event := range repo.events {
					if blob, ok := event.(*Blob); ok && isIgnore(blob) {
						blob.setContent([]byte(rs.preferred.dfltignores+string(blob.getContent())), -1)
						changecount++
					}
				}
				// Create an early ignore file if required.
				// Do not move this before the modification pass!
				earliest := repo.earliestCommit()
				hasIgnoreBlob := false
				for _, fileop := range earliest.operations() {
					if fileop.op == opM && strings.HasSuffix(fileop.Path, rs.ignorename) {
						hasIgnoreBlob = true
					}
				}
				if !hasIgnoreBlob {
					blob := newBlob(repo)
					blob.addalias(rs.ignorename)
					blob.setContent([]byte(rs.preferred.dfltignores), noOffset)
					blob.mark = ":insert"
					repo.insertEvent(blob, repo.eventToIndex(earliest), "ignore-blob creation")
					repo.declareSequenceMutation("ignore creation")
					newop := newFileOp(rs.chosen())
					newop.construct(opM, "100644", ":insert", rs.ignorename)
					earliest.appendOperation(*newop)
					repo.renumber(1, nil)
					respond(fmt.Sprintf("initial %s created.", rs.ignorename))
				}
				respond(fmt.Sprintf("%d %s blobs modified.", changecount, rs.ignorename))
			}
		} else if verb == "rename" {
			changecount := 0
			for _, commit := range repo.commits(nil) {
				for idx, fileop := range commit.operations() {
					for _, attr := range []string{"Path", "Source", "Target"} {
						oldpath, ok := getAttr(fileop, attr)
						if ok {
							if ok && strings.HasSuffix(oldpath, rs.ignorename) {
								newpath := filepath.Join(filepath.Dir(oldpath),
									rs.preferred.ignorename)
								setAttr(&commit.fileops[idx], attr, newpath)
								changecount++
								if fileop.op == opM {
									blob := repo.markToEvent(fileop.ref).(*Blob)
									if blob.pathlist[0] == oldpath {
										blob.replacealias(0, newpath)
									}
								}
							}
						}
					}
				}
			}
			respond("%d ignore files renamed (%s -> %s).",
				changecount, rs.ignorename, rs.preferred.ignorename)
			rs.ignorename = rs.preferred.ignorename
		} else if verb == "translate" {
			changecount := 0
			for _, event := range repo.events {
				if blob, ok := event.(*Blob); ok && isIgnore(blob) {
					if rs.preferred.name == "hg" {
						if !bytes.HasPrefix(blob.getContent(), []byte("syntax: glob\n")) {
							blob.setContent([]byte("syntax: glob\n"+string(blob.getContent())), noOffset)
							changecount++
						}
					}
				}
			}
			respond(fmt.Sprintf("%d %s blobs modified.", changecount, rs.ignorename))
		} else {
			croak("unknown verb %s in ignores line", verb)
			return false
		}
	}
	return false
}

func (rs *Reposurgeon) HelpAttribution() {
	rs.helpOutput(`
Inspect, modify, add, and remove commit and tag attributions.

Attributions upon which to operate are selected in much the same way as events
are selected. The <selection> argument of each action is an expression
composed of 1-origin attribution-sequence numbers, '$' for last attribution,
'..' ranges, comma-separated items, '(...)' grouping, set operations '|'
union, '&' intersection, and '~' negation, and function calls @min(), @max(),
@amp(), @pre(), @suc(), @srt().

Attributions can also be selected by visibility set '=C' for committers, '=A'
for authors, and '=T' for taggers.

Finally, /regex/ will attempt to match the Go regular expression regex
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
`)
}

// Inspect, modify, add, and remove commit and tag attributions.
func (rs *Reposurgeon) DoAttribution(line string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen")
		return false
	}
	selparser := newAttrEditSelParser()
	machine, rest := selparser.compile(line)
	parse := rs.newLineParse(rest, orderedStringSet{"stdout"})
	defer parse.Closem()
	fields, err := shlex.Split(parse.line, true)
	if err != nil {
		croak("attribution parse failed: %v", err)
		return false
	}
	var action string
	args := []string{}
	if len(fields) == 0 {
		action = "show"
	} else {
		action = fields[0]
		args = fields[1:]
	}
	selection := rs.selection
	if rs.selection == nil {
		if action == "show" {
			selection = repo.all()
		} else {
			croak("no selection")
			return false
		}
	}
	var sel []int
	for _, i := range selection {
		switch repo.events[i].(type) {
		case *Commit, *Tag:
			sel = append(sel, i)
		}
	}
	if len(sel) == 0 {
		croak("no commits or tags in selection")
		return false
	}
	ed := newAttributionEditor(sel, repo.events, func(attrs []attrEditAttr) []int {
		state := selparser.evalState(attrs)
		defer state.release()
		return selparser.evaluate(machine, state)
	})
	if action == "show" {
		if len(args) > 0 {
			croak("'show' takes no arguments")
			return false
		}
		ed.inspect(parse.stdout)
	} else if action == "delete" {
		if len(args) > 0 {
			croak("'delete' takes no arguments")
			return false
		}
		ed.remove()
	} else if action == "set" {
		if len(args) < 1 || len(args) > 3 {
			croak("'set' requires at least one of: name, email, date")
			return false
		}
		ed.assign(args)
	} else if action == "prepend" || action == "append" {
		if len(args) < 1 || len(args) > 3 {
			croak("'%s' requires at least one of: name, email; date is optional", action)
			return false
		}
		if action == "prepend" {
			ed.insert(args, false)
		} else if action == "append" {
			ed.insert(args, true)
		}
	} else if action == "resolve" {
		ed.resolve(parse.stdout, strings.Join(args, " "))
	} else {
		croak("unrecognized action: %s", action)
		return false
	}
	return false
}

//
// Artifact removal
//
func (rs *Reposurgeon) HelpAuthors() {
	rs.helpOutput(`
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
`)
}

// Apply or dump author-mapping file.
func (rs *Reposurgeon) DoAuthors(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	if strings.HasPrefix(line, "write") {
		line = strings.TrimSpace(line[5:])
		parse := rs.newLineParse(line, orderedStringSet{"stdout"})
		defer parse.Closem()
		if len(parse.Tokens()) > 0 {
			croak("authors write no longer takes a filename argument - use > redirection instead")
			return false
		}
		rs.chosen().writeAuthorMap(selection, parse.stdout)
	} else {
		if strings.HasPrefix(line, "read") {
			line = strings.TrimSpace(line[4:])
		}
		parse := rs.newLineParse(line, orderedStringSet{"stdin"})
		defer parse.Closem()
		if len(parse.Tokens()) > 0 {
			croak("authors read no longer takes a filename argument - use < redirection instead")
			return false
		}
		rs.chosen().readAuthorMap(selection, parse.stdin)
	}
	return false
}

//
// Reference lifting
//
func (rs *Reposurgeon) HelpLegacy() {
	rs.helpOutput(`
Apply or list legacy-reference information. Does not take a
selection set. The 'read' variant reads from standard input or a
<-redirected filename; the 'write' variant writes to standard
output or a >-redirected filename.
`)
}

// Apply a reference-mapping file.
func (rs *Reposurgeon) DoLegacy(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	if strings.HasPrefix(line, "write") {
		line = strings.TrimSpace(line[5:])
		parse := rs.newLineParse(line, orderedStringSet{"stdout"})
		defer parse.Closem()
		if len(parse.Tokens()) > 0 {
			croak("legacy write does not take a filename argument - use > redirection instead")
			return false
		}
		rs.chosen().writeLegacyMap(parse.stdout)
	} else {
		if strings.HasPrefix(line, "read") {
			line = strings.TrimSpace(line[4:])
		}
		parse := rs.newLineParse(line, []string{"stdin"})
		defer parse.Closem()
		if len(parse.Tokens()) > 0 {
			croak("legacy read does not take a filename argument - use < redirection instead")
			return false
		}
		rs.chosen().readLegacyMap(parse.stdin)
	}
	return false
}

func (rs *Reposurgeon) HelpReferences() {
	rs.helpOutput(`
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
`)
}

// Look for things that might be CVS or Subversion revision references.
func (rs *Reposurgeon) DoReferences(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	if strings.Contains(line, "lift") {
		rs.chosen().parseDollarCookies()
		hits := 0
		substitute := func(getter func(string) *Commit, legend string) string {
			// legend was matchobj.group(0) in Python
			commit := getter(legend)
			if commit == nil {
				logit(logWARN, "no commit matches %q", legend)
				return legend // no replacement
			}
			text := commit.actionStamp()
			hits++
			return text
		}
		type getterPair struct {
			pattern string
			getter  func(string) *Commit
		}
		getterPairs := []getterPair{
			{`\[\[CVS:[^:\]]+:[0-9.]+\]\]`,
				func(p string) *Commit {
					p = p[2 : len(p)-2]
					if c := repo.legacyMap[p]; c != nil {
						return c
					}
					c, ok := repo.dollarMap.Load(p)
					if ok {
						return c.(*Commit)
					}
					return nil
				}},
			{`\[\[SVN:[0-9]+\]\]`,
				func(p string) *Commit {
					p = p[2 : len(p)-2]
					if c := repo.legacyMap[p]; c != nil {
						return c
					}
					c, ok := repo.dollarMap.Load(p)
					if ok {
						return c.(*Commit)
					}
					return nil
				}},
			{`\[\[HG:[0-9a-f]+\]\]`,
				func(p string) *Commit {
					p = p[2 : len(p)-2]
					return repo.legacyMap[p]
				}},
			{`\[\[:[0-9]+\]\]`,
				func(p string) *Commit {
					p = p[2 : len(p)-2]
					event := repo.markToEvent(p)
					commit, ok := event.(*Commit)
					if ok {
						return commit
					}
					return nil
				}},
		}
		for _, item := range getterPairs {
			matchRE := regexp.MustCompile(item.pattern)
			for _, commit := range rs.chosen().commits(selection) {
				commit.Comment = matchRE.ReplaceAllStringFunc(
					commit.Comment,
					func(m string) string {
						return substitute(item.getter, m)
					})
			}
		}
		respond("%d references resolved.", hits)
		repo.writeLegacy = true
	} else {
		//FIXME: Maybe this should filter rather than making a new set?
		selection = make([]int, 0)
		for idx, commit := range repo.commits(nil) {
			if rs.hasReference(commit) {
				selection = append(selection, idx)
			}
		}
		if len(selection) > 0 {
			if strings.HasPrefix(line, "edit") {
				rs.edit(selection, strings.TrimSpace(line[4:]))
			} else {
				parse := rs.newLineParse(line, orderedStringSet{"stdout"})
				defer parse.Closem()
				w := screenwidth()
				for _, ei := range selection {
					event := repo.events[ei]
					summary := ""
					switch event.(type) {
					case *Commit:
						commit := event.(*Commit)
						summary = commit.lister(nil, ei, w)
						break
						//case *Tag:
						//	tag := event.(*Tag)
						//	summary = tag.lister(nil, ei, w)
					}
					if summary != "" {
						fmt.Fprint(parse.stdout, summary+"\n")
					}
				}
			}
		}
	}
	return false
}

func (rs *Reposurgeon) HelpGitify() {
	rs.helpOutput(`
Attempt to massage comments into a git-friendly form with a blank
separator line after a summary line.  This code assumes it can insert
a blank line if the first line of the comment ends with '.', ',', ':',
';', '?', or '!'.  If the separator line is already present, the comment
won't be touched.

Takes a selection set, defaulting to all commits and tags.
`)
}

// Gitify comments.
func (rs *Reposurgeon) DoGitify(_line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	lineEnders := orderedStringSet{".", ",", ";", ":", "?", "!"}
	control.baton.startProgress("gitifying comments", uint64(len(selection)))
	rs.chosen().walkEvents(selection, func(idx int, event Event) {
		if commit, ok := event.(*Commit); ok {
			commit.Comment = strings.TrimSpace(commit.Comment) + "\n"
			if strings.Count(commit.Comment, "\n") < 2 {
				return
			}
			firsteol := strings.Index(commit.Comment, "\n")
			if commit.Comment[firsteol+1] == byte('\n') {
				return
			}
			if lineEnders.Contains(string(commit.Comment[firsteol-1])) {
				commit.Comment = commit.Comment[:firsteol] +
					"\n" +
					commit.Comment[firsteol:]
			}
		} else if tag, ok := event.(*Tag); ok {
			tag.Comment = strings.TrimSpace(tag.Comment) + "\n"
			if strings.Count(tag.Comment, "\n") < 2 {
				return
			}
			firsteol := strings.Index(tag.Comment, "\n")
			if tag.Comment[firsteol+1] == byte('\n') {
				return
			}
			if lineEnders.Contains(string(tag.Comment[firsteol-1])) {
				tag.Comment = tag.Comment[:firsteol] +
					"\n" +
					tag.Comment[firsteol:]
			}
		}
		control.baton.percentProgress(uint64(idx))
	})
	control.baton.endProgress()
	return false
}

//
// Examining tree states
//
func (rs *Reposurgeon) HelpCheckout() {
	rs.helpOutput(`
Check out files for a specified commit into a directory.  The selection
set must resolve to a singleton commit.
`)
}

// Check out files for a specified commit into a directory.
func (rs *Reposurgeon) DoCheckout(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	if line == "" {
		croak("no target directory specified.")
	} else if len(selection) == 1 {
		event := repo.events[selection[0]]
		if commit, ok := event.(*Commit); ok {
			commit.checkout(line)
		} else {
			croak("not a commit.")
		}
	} else {
		croak("a singleton selection set is required.")
	}
	return false
}

func (rs *Reposurgeon) HelpDiff() {
	rs.helpOutput(`
Display the difference between commits. Takes a selection-set argument which
must resolve to exactly two commits. Supports > redirection.
`)
}

// Display a diff between versions.
func (rs *Reposurgeon) DoDiff(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	if len(rs.selection) != 2 {
		logit(logWARN, "a pair of commits is required.")
		return false
	}
	lower, ok1 := repo.events[rs.selection[0]].(*Commit)
	upper, ok2 := repo.events[rs.selection[1]].(*Commit)
	if !ok1 || !ok2 {
		logit(logWARN, "a pair of commits is required.")
		return false
	}
	dir1 := newOrderedStringSet()
	for _, elt := range lower.manifest().items() {
		dir1.Add(elt.name)
	}
	dir2 := newOrderedStringSet()
	for _, elt := range upper.manifest().items() {
		dir2.Add(elt.name)
	}
	allpaths := dir1.Union(dir2)
	sort.Strings(allpaths)
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	for _, path := range allpaths {
		if dir1.Contains(path) && dir2.Contains(path) {
			// FIXME: Can we detect binary files and do something
			// more useful here?
			fromtext, _ := lower.blobByName(path)
			totext, _ := upper.blobByName(path)
			// Don't list identical files
			if !bytes.Equal(fromtext, totext) {
				lines0 := difflib.SplitLines(string(fromtext))
				lines1 := difflib.SplitLines(string(totext))
				file0 := path + " (" + lower.mark + ")"
				file1 := path + " (" + upper.mark + ")"
				diff := difflib.UnifiedDiff{
					A:        lines0,
					B:        lines1,
					FromFile: file0,
					ToFile:   file1,
					Context:  3,
				}
				text, _ := difflib.GetUnifiedDiffString(diff)
				fmt.Fprint(parse.stdout, text)
			}
		} else if dir1.Contains(path) {
			fmt.Fprintf(parse.stdout, "%s: removed\n", path)
		} else if dir2.Contains(path) {
			fmt.Fprintf(parse.stdout, "%s: added\n", path)
		} else {
			logit(logWARN, "internal error - missing path in diff")
			return false
		}
	}
	return false
}

//
// Setting paths to branchify
//
func (rs *Reposurgeon) HelpBranchify() {
	rs.helpOutput(`
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
`)
}

func (rs *Reposurgeon) DoBranchify(line string) bool {
	if rs.selection != nil {
		croak("branchify does not take a selection set")
		return false
	}
	if strings.TrimSpace(line) != "" {
		control.listOptions["svn_branchify"] = strings.Fields(strings.TrimSpace(line))
	}
	respond("branchify " + strings.Join(control.listOptions["svn_branchify"], " "))
	return false
}

//
// Setting branch name rewriting
//
func (rs *Reposurgeon) HelpBranchmap() {
	rs.helpOutput(`
Specify the list of regular expressions used for mapping the svn branches that
are detected by branchify. If none of the expressions match, the default behavior
applies. This maps a branch to the name of the last directory, except for trunk
and '*' which are mapped to master and root.

With no arguments the current regex replacement pairs are shown. Passing 'reset'
will clear the mapping.

Syntax: branchmap /regex1/branch1/ /regex2/branch2/ ...

Will match each branch name against regex1 and if it matches rewrite its branch
name to branch1. If not it will try regex2 and so forth until it either found a
matching regex or there are no regexs left. The regular expressions should be in
python's format (see http://docs.python.org/2/library/re.html). The branch name
can use backreferences (see the sub function in the python documentation).

Note that the regular expressions are appended to 'refs/' without either the
needed 'heads/' or 'tags/'. This allows for choosing the right kind of branch
type.

While the syntax template above uses slashes, any first character will
be used as a delimiter (and you will need to use a different one in the
common case that the paths contain slashes).

You must give this command *before* the Subversion repository read it
is supposed to affect!

Note that the branchmap set is a property of the reposurgeon interpreter,
not of any individual repository, and will persist across Subversion
dumpfile reads. This may lead to unexpected results if you forget
to re-set it.
`)
}

func (rs *Reposurgeon) DoBranchmap(line string) bool {
	if rs.selection != nil {
		croak("branchmap does not take a selection set")
		return false
	}

	line = strings.TrimSpace(line)
	if line == "reset" {
		control.branchMappings = nil
	} else if line != "" {
		control.branchMappings = make([]branchMapping, 0)
		for _, regex := range strings.Fields(line) {
			separator := regex[0]
			if separator != regex[len(regex)-1] {
				croak("Regex '%s' did not end with separator character", regex)
				return false
			}
			stuff := strings.SplitN(regex[1:len(regex)-1], string(separator), 2)
			match, replace := stuff[0], stuff[1]
			if replace == "" || match == "" {
				croak("Regex '%s' has an empty search or replace part", regex)
				return false
			}
			re, err := regexp.Compile(match)
			if err != nil {
				croak("Regex '%s' is ill-formed", regex)
				return false
			}
			control.branchMappings = append(control.branchMappings, branchMapping{re, replace})
		}
	}
	if len(control.branchMappings) != 0 {
		respond("branchmap, regex -> branch name:")
		for _, pair := range control.branchMappings {
			respond("\t" + pair.match.String() + " -> " + pair.replace)
		}
	} else {
		croak("branchmap is empty.")
	}
	return false
}

//
// Setting options
//
func (rs *Reposurgeon) HelpSet() {
	rs.helpOutput(`
Set a (tab-completed) boolean option to control reposurgeon's
behavior.  With no arguments, displays the state of all flags and
options. The following flags and options are defined:

`)
	for _, opt := range optionFlags {
		fmt.Print(opt[0] + ":\n" + opt[1] + "\n")
	}
}

func (rs *Reposurgeon) CompleteSet(text string) []string {
	out := make([]string, 0)
	for _, x := range optionFlags {
		if strings.HasPrefix(x[0], text) && !control.flagOptions[x[0]] {
			out = append(out, x[0])
		}
	}
	sort.Strings(out)
	return out
}

func performOptionSideEffect(opt string, val bool) {
	if opt == "tighten" {
		enableIntern(val)
	} else if opt == "progress" {
		control.baton.setInteractivity(val)
	}
}

func tweakFlagOptions(line string, val bool) {
	if strings.TrimSpace(line) == "" {
		for _, opt := range optionFlags {
			respond("\t%s = %v\n", opt[0], control.flagOptions[opt[0]])
		}
	} else {
		line = strings.Replace(line, ",", " ", -1)
		for _, name := range strings.Fields(line) {
			for _, opt := range optionFlags {
				if name == opt[0] {
					control.flagOptions[opt[0]] = val
					performOptionSideEffect(opt[0], val)
					goto good
				}
			}
			croak("no such option flag as '%s'", name)
		good:
		}
	}
}

func (rs *Reposurgeon) DoSet(line string) bool {
	tweakFlagOptions(line, true)
	return false
}

func (rs *Reposurgeon) HelpClear() {
	rs.helpOutput(`
Clear a (tab-completed) boolean option to control reposurgeon's
behavior.  With no arguments, displays the state of all flags. The
following flags and options are defined:

`)
	for _, opt := range optionFlags {
		fmt.Print(opt[0] + ":\n" + opt[1] + "\n")
	}
}

func (rs *Reposurgeon) CompleteClear(text string) []string {
	out := make([]string, 0)
	for _, x := range optionFlags {
		if strings.HasPrefix(x[0], text) && control.flagOptions[x[0]] {
			out = append(out, x[0])
		}
	}
	sort.Strings(out)
	return out
}

func (rs *Reposurgeon) DoClear(line string) bool {
	tweakFlagOptions(line, false)
	return false
}

func (rs *Reposurgeon) HelpReadLimit() {
	rs.helpOutput(`
Set a maximum number of commits to read from a stream.  If the limit
is reached before EOF it will be logged. Mainly useful for benchmarking.
Without arguments, report the read limit; 0 means there is none.
`)
}

func (rs *Reposurgeon) DoReadlimit(line string) bool {
	if line == "" {
		respond("readlimit %d\n", control.readLimit)
		return false
	}
	lim, err := strconv.ParseUint(line, 10, 64)
	if err != nil {
		logit(logWARN, "ill-formed readlimit argument %q: %v.", line, err)
	}
	control.readLimit = lim
	return false
}

//
// Macros and custom extensions
//
func (rs *Reposurgeon) HelpDefine() {
	rs.helpOutput(`
Define a macro.  The first whitespace-separated token is the name; the
remainder of the line is the body, unless it is '{', which begins a
multi-line macro terminated by a line beginning with '}'.

A later 'do' call can invoke this macro.

'define' by itself without a name or body produces a macro list.
`)
}

// Define a macro
func (rs *Reposurgeon) DoDefine(lineIn string) bool {
	words := strings.SplitN(lineIn, " ", 2)
	name := words[0]
	if len(words) > 1 {
		body := words[1]
		if body[0] == '{' {
			subbody := make([]string, 0)
			depth := 0
			existingPrompt := rs.cmd.GetPrompt()
			if rs.inputIsStdin {
				rs.cmd.SetPrompt("> ")
			} else {
				rs.cmd.SetPrompt("")
			}
			defer rs.cmd.SetPrompt(existingPrompt)
			for true {
				line, err := rs.cmd.Readline()
				line = strings.TrimSpace(line)
				if err == io.EOF {
					line = "EOF"
				} else if err != nil {
					break
				}
				if depth == 0 && (line[0] == '}' || line == "EOF") {
					// done, exit loop
					break
				} else if strings.HasPrefix(line, "define") &&
					strings.HasSuffix(line, "{") {
					depth++
				} else if line[0] == '}' || line == "EOF" {
					if depth > 0 {
						depth--
					}
				}
				subbody = append(subbody, line)
			}
			rs.definitions[name] = subbody
		} else {
			rs.definitions[name] = []string{body}
		}
	} else {
		for name, body := range rs.definitions {
			if len(body) == 1 {
				respond("define %s %s\n", name, body[0])
			} else {
				respond("define %s {\n", name)
				for _, line := range body {
					respond("\t%s", line)
				}
				respond("}")
			}
		}
	}
	return false
}

func (rs *Reposurgeon) HelpDo() {
	rs.helpOutput(`
Expand and perform a macro.  The first whitespace-separated token is
the name of the macro to be called; remaining tokens replace {0}, 
{1}... in the macro definition. Tokens may contain whitespace if they
are string-quoted; string quotes are stripped. Macros can call macros.
If the macro expansion does not itself begin with a selection set,
whatever set was specified before the 'do' keyword is available to
the command generated by the expansion.
`)
}

// Do a macro
func (rs *Reposurgeon) DoDo(ctx context.Context, line string) bool {
	parse := rs.newLineParse(line, orderedStringSet{"stdout"})
	defer parse.Closem()
	words, err := shlex.Split(parse.line, true)
	if len(words) == 0 {
		croak("no macro name was given.")
		return false
	}
	if err != nil {
		croak("macro parse failed, %s", err)
		return false
	}
	name := words[0]
	macro, present := rs.definitions[name]
	if !present {
		croak("'%s' is not a defined macro", name)
		return false
	}
	args := words[1:]
	replacements := make([]string, 2*len(args))
	for i, arg := range args {
		replacements = append(replacements, fmt.Sprintf("{%d}", i), arg)
	}
	body := strings.NewReplacer(replacements...).Replace(strings.Join(macro, "\n"))
	doSelection := rs.selection

	for _, defline := range strings.Split(body, "\n") {
		// If a leading portion of the expansion body is a selection
		// expression, use it.  Otherwise we'll restore whatever
		// selection set came before the do keyword.
		expansion := rs.cmd.PreCmd(ctx, defline)
		if rs.selection == nil {
			rs.selection = doSelection
		}
		// Call the base method so RecoverableExceptions
		// won't be caught; we want them to abort macros.
		rs.cmd.OneCmd(ctx, expansion)
	}

	return false
}

func (rs *Reposurgeon) HelpUndefine() {
	rs.helpOutput(`
Undefine the macro named in this command's first argument.
`)
}

func (rs *Reposurgeon) CompleteUndefine(text string) []string {
	repo := rs.chosen()
	out := make([]string, 0)
	if repo != nil {
		for key := range rs.definitions {
			out = append(out, key)
		}
	}
	sort.Strings(out)
	return out
}

func (rs *Reposurgeon) DoUndefine(line string) bool {
	words := strings.SplitN(line, " ", 1)
	name := words[0]
	if name == "" {
		croak("no macro name was given.")
		return false
	}
	_, present := rs.definitions[name]
	if !present {
		croak("'%s' is not a defined macro", name)
		return false
	}
	delete(rs.definitions, name)
	return false
}

//
// Timequakes and bumping
//
func (rs *Reposurgeon) HelpTimequake() {
	rs.helpOutput(`
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
`)
}

func (rs *Reposurgeon) DoTimequake(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}
	baton := control.baton
	//baton.startProcess("reposurgeon: disambiguating", "")
	modified := 0
	for _, event := range repo.commits(selection) {
		parents := event.parents()
		if len(parents) == 1 {
			if parent, ok := parents[0].(*Commit); ok {
				if event.committer.date.timestamp.Equal(parent.committer.date.timestamp) {
					event.bump(1)
					modified++
				}
			}
		}
		baton.twirl()
	}
	//baton.endProcess()
	respond("%d events modified", modified)
	repo.invalidateNamecache()
	return false
}

func (rs *Reposurgeon) HelpTimebump() {
	rs.helpOutput(`
Bump the committer and author timestamps of commits in the selection
set (defaulting to empty) by one second.  With following integer argument,
that many seconds.  Argument may be negative.

The normal use case for this command is early in converting CVS or Subversion
repositories, cleaning up after 'timequake', to ensure that the surgical
language can count on having a unique action-stamp ID for each commit.
`)
}

func (rs *Reposurgeon) DoTimebump(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	if rs.selection == nil {
		croak("reposurgeon: no default select set for bump.")
		return false
	}
	var offset int
	var err error
	if line == "" {
		offset = 1
	} else {
		offset, err = strconv.Atoi(line)
		if err != nil {
			croak("in timebump: %v", err)
			return false
		}
	}
	for _, event := range rs.chosen().commits(rs.selection) {
		event.bump(offset)
	}
	return false
}

//
// Changelog processing
//
func (rs *Reposurgeon) HelpChangelogs() {
	rs.helpOutput(`
Mine ChangeLog files for authorship data.

Takes a selection set.  If no set is specified, proces all changelogs.

Assume such files have basename 'ChangeLog', and that they are in the
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
However, if the name is an author-map alias with an associated timezone,
that zone is used.
`)
}

var ymdRE = regexp.MustCompile("[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]")
var addressRE = regexp.MustCompile(`([^<@>]+\S)\s+<([^<@>\s]+@[^<@>\s]+)>`)

// stringCopy forces crearion of a copy o f the input strimg.  This is
// useful because the Go runtime tries not to do more allcations tn
// necessary, making string-valued references instead, Thus,
// sectioning a small string out of a very large one may cause
// the large string to be held in memory even thouggh the rest of the
// contnt is no longer referenced.
func stringCopy(a string) string {
	return (a + " ")[:len(a)]
}

// Mine repository changelogs for authorship data.
func (rs *Reposurgeon) DoChangelogs(line string) bool {
	if rs.chosen() == nil {
		croak("no repo has been chosen.")
		return false
	}
	repo := rs.chosen()
	selection := rs.selection
	if selection == nil {
		selection = rs.chosen().all()
	}

	cc, cl, cm, cd := 0, 0, 0, 0

	parseAttributionLine := func(line string) string {
		// Parse an attribution line in a ChangeLog entry, get an email address
		if len(line) <= 10 || unicode.IsSpace(rune(line[0])) {
			return ""
		}
		// Massage old-style addresses into newstyle
		line = strings.Replace(line, "(", "<", -1)
		line = strings.Replace(line, ")", ">", -1)
		// Deal with some address masking that can interfere with next stages
		line = strings.Replace(line, " <at> ", "@", -1)
		// Line must contain an email address. Find it.
		addrStart := strings.LastIndex(line, "<")
		addrEnd := strings.Index(line[addrStart+1:], ">") + addrStart + 1
		if addrStart < 0 || addrEnd < 0 {
			return ""
		}
		// Remove all other < and > delimiters to avoid malformed attributions
		// After the address, they can be dropped, but before they might come
		// legit parenthesis that was converted above.
		pre := strings.Replace(
		           strings.Replace(line[:addrStart], "<", "(", -1),
		           ">", ")", -1)
		post := strings.Replace(line[addrEnd+1:], ">", "", -1)
		email := line[addrStart:addrEnd+1]
		// Detect more types of address masking
		email = strings.Replace(email, " at ", "@", 1)
		// Regenerate cleaned up attribution
		line = pre + email + post
		if unicode.IsDigit(rune(line[0])) && unicode.IsDigit(rune(line[0])) {
			space := strings.Index(line, " ")
			if space < 0 {
				return ""
			}
			date := line[:space]
			if !ymdRE.MatchString(date) {
				return ""
			}
			addr := strings.TrimSpace(line[space+1:])
			return stringCopy(addr)
		}
		// Scan for old-style date like "Tue Dec  9 01:16:06 1997"
		// This corresponds to Go ANSIC format.
		fields := strings.Fields(line)
		if len(fields) >= 5 {
			possibleDate := strings.Join(fields[:5], " ")
			// Doesn't matter that TZ is wrong here, we're only going
			// to use the day part at most.
			_, err := time.Parse(time.ANSIC, possibleDate)
			if err != nil {
				return ""
			}
			skipre := regexp.MustCompile(strings.Join(strings.Fields(line)[:5], `\s+`))
			m := skipre.FindStringIndex(line)
			if m == nil {
				return ""
			}
			addr := strings.TrimSpace(line[m[1]:])
			return stringCopy(addr)
		}
		return ""
	}
	control.baton.startProgress("processing changelogs", uint64(len(repo.events)))
	attributions := make([][]string, len(repo.events))
	blobRefs := make([][]string, len(repo.events))
	evts := 0 // shared between threads, for progression only
	repo.walkEvents(selection, func(event_id int, event Event) {
		commit, iscommit := event.(*Commit)
		evts++
		if !iscommit {
			return
		}
		cc++
		// If a changeset is *all* ChangeLog mods, it is probably either
		// a log rotation or a maintainer fixing a typo. In either case,
		// best not to re-attribute this.
		notChangelog := false
		for _, op := range commit.operations() {
			if op.op != opM || !strings.HasPrefix(filepath.Base(op.Path), "ChangeLog") {
				notChangelog = true
			}
		}
		if !notChangelog {
			return
		}
		for _, op := range commit.operations() {
			if op.op == opM && filepath.Base(op.Path) == "ChangeLog" {
				cl++
				// Figure out where we should look for changes in
				// this blob by comparing it to its nearest ancestor.
				then := make([]string, 0)
				if ob := repo.blobAncestor(commit, op.Path); ob != nil {
					then = strings.Split(string(ob.getContent()), "\n")
				}
				newcontent := repo.markToEvent(op.ref).(*Blob).getContent()
				now := strings.Split(string(newcontent), "\n")
				var attribution string
				var commonCount int
				//print("Analyzing Changelog at %s." % commit.mark)
				differ := difflib.NewMatcherWithJunk(then, now, true, nil)
				comparison := differ.GetOpCodes()
				for _, difflines := range comparison {
					if difflines.Tag == 'i' || difflines.Tag == 'r' {
						for _, diffline := range now[difflines.J1:difflines.J2] {
							attribution = parseAttributionLine(diffline)
							if attribution != "" {
								goto attributionFound
							}
						}
					}
				}
				// This is the tricky part.  We want the
				// last attribution from before the change
				// band to stick because there is none *in*
				// the change band. If there's more than one,
				// assume the most recent is the latest and
				// correct. First count the lines before the
				// first change...
				for _, difflines := range comparison {
					if difflines.Tag == 'e' {
						commonCount = difflines.I2
					} else {
						break
					}
				}
				// Then parse the attributions in reverse order to
				// avoid parsing and tossing away a lot of them.
				for i := commonCount - 1; i >= 0; i-- {
					attribution = parseAttributionLine(now[i])
					if attribution != "" {
						goto attributionFound
					}
				}
				continue
			attributionFound:
				attributions[event_id] = append(attributions[event_id], attribution)
				blobRefs[event_id] = append(blobRefs[event_id], op.ref)
			}
		}
		control.baton.percentProgress(uint64(evts))
	})
	control.baton.endProgress()
	for _, eventID := range selection {
		commit, iscommit := repo.events[eventID].(*Commit)
		if !iscommit {
			continue
		}
		for i, attribution := range attributions[eventID] {
			// Invalid addresses will cause fatal errors if they get into a
			// fast-import stream. Filter out bogons...
			matches := addressRE.FindAllStringSubmatch(strings.TrimSpace(attribution), -1)
			if matches == nil {
				logit(logSHOUT, "invalid attribution %q in blob %s", attribution, blobRefs[eventID][i])
				continue
			}
			cm++
			newattr := commit.committer.clone()
			newattr.email = matches[0][2]
			newattr.fullname = matches[0][1]
			// This assumes email addreses of contributors are unique.
			// We could get wacky results if two people with different
			// human names but identicall email addresses were run through
			// this code, but that outcome seems wildly unlikely.
			if newattr.fullname == "" {
				for _, mapentry := range repo.authormap {
					if newattr.email == mapentry.email {
						newattr.fullname = mapentry.fullname
						break
					}
				}
			}
			if tz, ok := repo.tzmap[newattr.email]; ok { //&& unicode.IsLetter(rune(tz.String()[0])) {
				newattr.date.timestamp = newattr.date.timestamp.In(tz)
			} else if zone := zoneFromEmail(newattr.email); zone != "" {
				newattr.date.setTZ(zone)
			}
			if val, ok := repo.aliases[ContributorID{fullname: newattr.fullname, email: newattr.email}]; ok {
				newattr.fullname, newattr.email = val.fullname, val.email
			}
			if len(commit.authors) == 0 {
				commit.authors = append(commit.authors, *newattr)
			} else {
				// Required because git sometimes fills in the
				// author field from the committer.
				if commit.authors[len(commit.authors)-1].email == commit.committer.email {
					commit.authors = commit.authors[:len(commit.authors)-1]
				}
				if len(commit.authors) == 0 {
					matched := false
					for _, author := range commit.authors {
						if author.email == newattr.email {
							matched = true
						}
					}
					if !matched {
						commit.authors = append(commit.authors, *newattr)
						cd++
					}
				}
			}
		}
	}
	repo.invalidateNamecache()
	respond("fills %d of %d authorships, changing %d, from %d ChangeLogs.", cm, cc, cd, cl)
	return false
}

//
// Tarball incorporation
//
func extractTar(dst string, r io.Reader) ([]tar.Header, error) {
	files := make([]tar.Header, 0)
	tr := tar.NewReader(r)
	for {
		header, err := tr.Next()
		if err == io.EOF {
			return files, nil
		} else if err != nil {
			return nil, err
		} else if header == nil {
			continue
		}

		target := filepath.Join(dst, header.Name)
		if header.Typeflag == tar.TypeDir {
			if _, err := os.Stat(target); err != nil {
				if err := os.MkdirAll(target, 0755); err != nil {
					return nil, err
				}
			}
		} else if header.Typeflag == tar.TypeReg {
			files = append(files, *header)
			f, err := os.OpenFile(target, os.O_CREATE|os.O_TRUNC|os.O_RDWR, os.FileMode(header.Mode))
			if err != nil {
				return nil, err
			}
			defer f.Close()
			if _, err := io.Copy(f, tr); err != nil {
				return nil, err
			}
		}
	}
}

func (rs *Reposurgeon) HelpIncorporate() {
	rs.helpOutput(`
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
`)
}

// Create a new commit from a tarball.
func (rs *Reposurgeon) DoIncorporate(line string) bool {
	repo := rs.chosen()
	if repo == nil {
		croak("no repo has been chosen.")
		return false
	}
	if rs.selection == nil {
		rs.selection = []int{repo.markToIndex(repo.earliestCommit().mark)}
	}
	var commit *Commit
	if len(rs.selection) == 1 {
		event := repo.events[rs.selection[0]]
		var ok bool
		if commit, ok = event.(*Commit); !ok {
			croak("selection is not a commit.")
			return false
		}
	} else {
		croak("a singleton selection set is required.")
		return false
	}
	parse := rs.newLineParse(line, nil)
	defer parse.Closem()
	if parse.line == "" {
		croak("no tarball specified.")
		return false
	}

	// Create new commit to carry the new content
	blank := newCommit(repo)
	attr, _ := newAttribution("")
	blank.committer = *attr
	blank.mark = repo.newmark()
	blank.repo = repo
	blank.committer.fullname, blank.committer.email = whoami()
	blank.Branch = commit.Branch
	blank.Comment = fmt.Sprintf("Content from %s\n", parse.line)
	var err error
	blank.committer.date, err = newDate("1970-01-01T00:00:00Z")
	stripstr, present := parse.OptVal("--strip")
	var strip int
	if !present {
		strip = 1
	} else {
		var err error
		strip, err = strconv.Atoi(stripstr)
		if err != nil {
			croak("strip option must be an integer")
			return false
		}
	}

	_, insertAfter := parse.OptVal("--after")
	var loc int
	if insertAfter {
		loc = repo.markToIndex(commit.mark) + 1
	} else {
		loc = repo.markToIndex(commit.mark)
		for loc > 0 {
			_, ok := repo.events[loc-1].(*Blob)
			if ok {
				loc--
			} else {
				break
			}
		}
	}

	// Incorporate the tarball content
	tarfile, err := os.Open(parse.line)
	if err != nil {
		croak("open or read failed on %s", parse.line)
		return false
	}
	defer tarfile.Close()

	logit(logSHUFFLE, "extracting %s into %s", parse.line, repo.subdir(""))
	repo.makedir()
	headers, err := extractTar(repo.subdir(""), tarfile)
	if err != nil {
		croak("error while extracting tarball %s: %s", parse.line, err.Error())
	}
	// Pre-sorting avoids an indeterminacy bug in tarfile
	// order traversal.
	sort.SliceStable(headers, func(i, j int) bool { return headers[i].Name < headers[j].Name })

	var newest time.Time
	for _, header := range headers {
		if header.ModTime.Before(newest) {
			newest = header.ModTime
		}
		b := newBlob(repo)
		repo.insertEvent(b, loc, "")
		loc++
		repo.declareSequenceMutation("")
		repo.invalidateObjectMap()
		b.setMark(repo.newmark())
		//b.size = header.size
		b.setBlobfile(filepath.Join(repo.subdir(""), header.Name))
		op := newFileOp(repo)
		fn := path.Join(strings.Split(header.Name, string(os.PathSeparator))[strip:]...)
		mode := 0100644
		if header.Mode&0111 != 0 {
			mode = 0100755
		}
		op.construct(opM, strconv.FormatInt(int64(mode), 8), b.mark, fn)
		blank.appendOperation(*op)
	}

	repo.declareSequenceMutation("")
	repo.invalidateObjectMap()
	if !control.flagOptions["testmode"] {
		blank.committer.date = Date{timestamp: newest}
	}

	// Link it into the repository
	if !insertAfter {
		repo.insertEvent(blank, loc, "")
		blank.setParents(commit.parents())
		commit.setParents([]CommitLike{blank})
	} else {
		blank._parentNodes = []CommitLike{commit}
		for _, offspring := range commit.children() {
			c, ok := offspring.(*Commit)
			if ok {
				c.replaceParent(commit, blank)
			}
		}
		repo.insertEvent(blank, loc, "")
	}

	// We get here if incorporation worked OK.
	date, present := parse.OptVal("--date")
	if present {
		blank.committer.date, err = newDate(date)
		if err != nil {
			croak("invalid date: %s", date)
			return false
		}
	}

	// Generate deletes into the next commit(s) so files won't
	// leak forward. Also prevent files leaking forward from any
	// previous commit.  We have to force deterministic path list
	// order here, otherwise regressio tests will fail in flaky
	// ways.
	blankPathList := blank.paths(nil)
	sort.Slice(blankPathList, func(i, j int) bool { return blankPathList[i] < blankPathList[j] })
	for _, path := range blankPathList {
		for _, child := range blank.children() {
			c, ok := child.(*Commit)
			if ok {
				if !c.paths(nil).Contains(path) {
					op := newFileOp(repo)
					op.construct(opD, path)
					c.appendOperation(*op)
				}
			}
		}
	}
	for _, parent := range blank.parents() {
		c, ok := parent.(*Commit)
		if ok {
			for _, leaker := range c.paths(nil) {
				if !blankPathList.Contains(leaker) {
					op := newFileOp(repo)
					op.construct(opD, leaker)
					blank.appendOperation(*op)
				}
			}
		}
	}

	return false
}

//
// Version binding
//
func (rs *Reposurgeon) HelpVersion() {
	rs.helpOutput(`
With no argument, display the reposurgeon version and supported VCSes.
With argument, declare the major version (single digit) or full
version (major.minor) under which the enclosing script was developed.
The program will error out if the major version has changed (which
means the surgical language is not backwards compatible).
`)
}

func (rs *Reposurgeon) DoVersion(line string) bool {
	if line == "" {
		supported := make([]string, 0)
		for _, v := range vcstypes {
			supported = append(supported, v.name)
		}
		for _, x := range importers {
			if x.visible {
				supported = append(supported, x.name)
			}
		}
		respond("reposurgeon " + version + " supporting " + strings.Join(supported, " "))
	} else {
		fields := strings.Split(version, ".")
		vmajor := fields[0]
		var major string
		if strings.Contains(line, ".") {
			fields = strings.Split(strings.TrimSpace(line), ".")
			if len(fields) != 2 {
				croak("invalid version.")
				return false
			}
		} else {
			major = strings.TrimSpace(line)
		}
		if major != vmajor {
			panic("major version mismatch, aborting.")
		} else if control.isInteractive() {
			respond("version check passed.")

		}
	}
	return false
}

//
// Exiting (in case EOT has been rebound)
//
func (rs *Reposurgeon) HelpElapsed() {
	rs.helpOutput(`
Desplay elapsed time since start.
`)
}

func (rs *Reposurgeon) DoElapsed(_line string) bool {
	respond("elapsed time %v.", time.Now().Sub(rs.startTime))
	return false
}

func (rs *Reposurgeon) HelpExit() {
	rs.helpOutput(`
Exit the program cleanly, emitting a goodbye message.

Typing EOT (usually Ctrl-D) will exit quietly.
`)
}

func (rs *Reposurgeon) DoExit(_line string) bool {
	respond("exiting, elapsed time %v.", time.Now().Sub(rs.startTime))
	return true
}

//
// Prompt customization
//
func (rs *Reposurgeon) HelpPrompt() {
	rs.helpOutput(`
Set the command prompt format to the value of the command line; with
an empty command line, display it. The prompt format is evaluated
after each command with the following substitutions:

{chosen}: The name of the selected repository, or the empty string if
          no repository is currently selected.

Thus, one useful format might be 'rs[{chosen}]% '.

More format items may be added in the future.  The default prompt
corresponds to the format 'reposurgeon% '. The format line is
evaluated with shell quoting of tokens, so that spaces can be
included.
`)
}

func (rs *Reposurgeon) DoPrompt(lineIn string) bool {
	if lineIn != "" {
		words, err := shlex.Split(lineIn, true)
		if err != nil {
			croak("failed to parse your prompt string: %s", err.Error())
			return false
		}
		rs.promptFormat = strings.Join(words, " ")
	}
	return false
}

//
// On-line help and instrumentation
//
func (rs *Reposurgeon) HelpHelp() {
	rs.helpOutput("Show help for a command. Follow with space and the command name.\n")
}

func (rs *Reposurgeon) HelpSelection() {
	rs.helpOutput(`
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
`)
}

func (rs *Reposurgeon) HelpSyntax() {
	rs.helpOutput(`
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
`)
}

func (rs *Reposurgeon) HelpLog() {
	rs.helpOutput(`
Without an argument, list all log message classes, prepending a + if
that class is enabled and a - if not.

Otherwise, it expects a space-separated list of "<+ or -><log message
class>" entries, and enables (with +) or disables (with -) the
corresponding log message class. The special keyword "all" can be used
to affect all the classes at the same time.

For instance, "log -all +shout +warn" will disable all classes except
"shout" and "warn", which is the default setting. "log +all -svnparse"
would enable logging everything but messages from the svn parser.

A list of available message classes follows; most above "warn"
level or above are only of interest to developers, consult the source
code to learn more.

`)
	for _, item := range verbosityLevelList() {
		fmt.Println(item.k)
	}
	fmt.Println("")
}

type assoc struct {
	k string
	v uint
}

func verbosityLevelList() []assoc {
	items := make([]assoc, 0)
	for k, v := range logtags {
		items = append(items, assoc{k, v})
	}
	sort.Slice(items, func(i, j int) bool {
		return items[i].v < items[j].v
	})
	return items
}

func (rs *Reposurgeon) DoLog(lineIn string) bool {
	lineIn = strings.Replace(lineIn, ",", " ", -1)
	for _, tok := range strings.Fields(lineIn) {
		enable := tok[0] == '+'
		if !(enable || tok[0] == '-') {
			croak("an entry should start with a + or a -")
			goto breakout
		}
		tok = tok[1:]
		mask, ok := logtags[tok]
		if !ok {
			if tok == "all" {
				mask = ^uint(0)
			} else {
				croak("no such log class as %s", tok)
				goto breakout
			}
		}
		if enable {
			control.logmask |= mask
		} else {
			control.logmask &= ^mask
		}
	}
breakout:
	if len(lineIn) == 0 || control.isInteractive() {
		// We make the capabilities display in ascending value order
		out := "log"
		for i, item := range verbosityLevelList() {
			if logEnable(item.v) {
				out += " +"
			} else {
				out += " -"
			}
			out += item.k
			if (i+1)%4 == 0 {
				out += "\n\t\t"
			}
		}
		respond(out)
	}
	return false
}

func (rs *Reposurgeon) HelpLogfile() {
	rs.helpOutput(`
Set the name of the file to which output will be redirected.
Without an argument, this command reports what logfile is set.
`)
}

func (rs *Reposurgeon) DoLogfile(lineIn string) bool {
	if len(lineIn) != 0 {
		fp, err := os.OpenFile(lineIn, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, userReadWriteMode)
		if err != nil {
			respond("log file open failed: %v", err)
		} else {
			var i interface{} = fp
			control.logfp = i.(io.Writer)
		}
	}
	if len(lineIn) == 0 || control.isInteractive() {
		switch v := control.logfp.(type) {
		case *os.File:
			respond("logfile %s", v.Name())
		case *Baton:
			respond("logfile stdout")
		}
	}
	return false
}

func (rs *Reposurgeon) HelpPrint() {
	rs.helpOutput("Print a literal string.\n")
}

func (rs *Reposurgeon) DoPrint(lineIn string) bool {
	parse := rs.newLineParse(lineIn, []string{"stdout"})
	defer parse.Closem()
	fmt.Fprintf(parse.stdout, "%s\n", parse.line)
	return false
}

func (rs *Reposurgeon) HelpScript() {
	rs.helpOutput("Read and execute commands from a named file.\n")
}

func (rs *Reposurgeon) DoScript(ctx context.Context, lineIn string) bool {
	interpreter := rs.cmd
	if len(lineIn) == 0 {
		fmt.Print("script requires a file argument\n")
		return false
	}
	if len(rs.callstack) == 0 {
		control.setAbort(false)
	}
	words := strings.Split(lineIn, " ")
	rs.callstack = append(rs.callstack, words)
	fname := words[0]
	scriptfp, err := os.Open(fname)
	if err != nil {
		croak("script failure on '%s': %s", fname, err)
		return false
	}
	defer scriptfp.Close()
	script := bufio.NewReader(scriptfp)

	existingInputIsStdin := rs.inputIsStdin
	rs.inputIsStdin = false

	interpreter.PreLoop(ctx)
	lineno := 0
	for {
		scriptline, err := script.ReadString('\n')
		lineno++
		if err == io.EOF && scriptline == "" {
			break
		}
		// Handle multiline commands
		for strings.HasSuffix(scriptline, "\\\n") {
			nexterline, err := script.ReadString('\n')
			if err == io.EOF && nexterline == "" {
				break
			}
			lineno++
			scriptline = scriptline[:len(scriptline)-2] + nexterline
		}

		scriptline = strings.TrimSpace(scriptline)

		// Simulate shell here-document processing
		if strings.Contains(scriptline, "<<") {
			heredoc, err := ioutil.TempFile("", "reposurgeon-")
			if err != nil {
				croak("script failure on '%s': %s", fname, err)
				return false
			}
			defer os.Remove(heredoc.Name())

			stuff := strings.Split(scriptline, "<<")
			scriptline = stuff[0]
			terminator := stuff[1] + "\n"
			for true {
				nextline, err := script.ReadString('\n')
				if err == io.EOF && nextline == "" {
					break
				} else if nextline == terminator {
					break
				} else {
					_, err := fmt.Fprint(heredoc, nextline)
					if err != nil {
						croak("script failure on '%s': %s", fname, err)
						return false
					}
				}
				lineno++
			}

			heredoc.Close()
			// Note: the command must accept < redirection!
			scriptline += "<" + heredoc.Name()
		}
		// End of heredoc simulation

		// Positional variables
		for i, v := range rs.callstack[len(rs.callstack)-1] {
			ref := "$" + strconv.FormatInt(int64(i), 10)
			scriptline = strings.Replace(scriptline, ref, v, -1)
		}
		scriptline = strings.Replace(scriptline, "$$", strconv.FormatInt(int64(os.Getpid()), 10), -1)

		// if the script wants to define a macro, the input
		// for the macro has to come from the script file
		existingStdin := rs.cmd.GetStdin()
		if strings.HasPrefix(scriptline, "define") && strings.HasSuffix(scriptline, "{") {
			rs.cmd.SetStdin(ioutil.NopCloser(script))
		}

		// finally we execute the command, plus the before/after steps
		originalline := scriptline
		scriptline = interpreter.PreCmd(ctx, scriptline)
		stop := interpreter.OneCmd(ctx, scriptline)
		stop = interpreter.PostCmd(ctx, stop, scriptline)

		// and then we have to put the stdin back where it
		// was, in case we changed it
		rs.cmd.SetStdin(existingStdin)

		// Abort flag is set by croak() and signals.
		// When it is set, we abort out of every nested
		// script call.
		if control.getAbort() {
			if originalline != "" {
				logit(logSHOUT, "script abort on line %d %q", lineno, originalline)
			} else {
				logit(logSHOUT, "script abort on line %d", lineno)
			}
			break
		}
		if stop {
			break
		}
	}
	interpreter.PostLoop(ctx)

	rs.inputIsStdin = existingInputIsStdin

	rs.callstack = rs.callstack[:len(rs.callstack)-1]
	return false
}

// DoSizes is for developer use when optimizing structure packing to reduce memory use
// const MaxUint = ^uint(0)
// const MinUint = 0
// const MaxInt = int(MaxUint >> 1)
// const MinInt = -MaxInt - 1
func (rs *Reposurgeon) DoSizeof(lineIn string) bool {
	const wordLengthInBytes = 8
	roundUp := func(n, m uintptr) uintptr {
		return ((n + m - 1) / m) * m
	}
	explain := func(size uintptr) string {
		out := fmt.Sprintf("%3d", size)
		if size%wordLengthInBytes > 0 {
			paddedSize := roundUp(size, wordLengthInBytes)
			out += fmt.Sprintf(" (padded to %d, step down %d)", paddedSize, size%wordLengthInBytes)
		}
		return out
	}
	// Don't use respond() here, we wabt to be abke to do "reposurgeon sizeof"
	// and get a result.
	fmt.Printf("NodeAction:        %s\n", explain(unsafe.Sizeof(*new(NodeAction))))
	fmt.Printf("RevisionRecord:    %s\n", explain(unsafe.Sizeof(*new(RevisionRecord))))
	fmt.Printf("Commit:            %s\n", explain(unsafe.Sizeof(*new(Commit))))
	fmt.Printf("Callout:           %s\n", explain(unsafe.Sizeof(*new(Callout))))
	fmt.Printf("FileOp:            %s\n", explain(unsafe.Sizeof(*new(FileOp))))
	fmt.Printf("Blob:              %s\n", explain(unsafe.Sizeof(*new(Blob))))
	fmt.Printf("Tag:               %s\n", explain(unsafe.Sizeof(*new(Tag))))
	fmt.Printf("Reset:             %s\n", explain(unsafe.Sizeof(*new(Reset))))
	fmt.Printf("Attribution:       %s\n", explain(unsafe.Sizeof(*new(Attribution))))
	fmt.Printf("blobidx:           %3d\n", unsafe.Sizeof(blobidx(0)))
	fmt.Printf("markidx:           %3d\n", unsafe.Sizeof(markidx(0)))
	fmt.Printf("revidx:            %3d\n", unsafe.Sizeof(revidx(0)))
	fmt.Printf("nodeidx:           %3d\n", unsafe.Sizeof(nodeidx(0)))
	fmt.Printf("string:            %3d\n", unsafe.Sizeof("foo"))
	fmt.Printf("pointer:           %3d\n", unsafe.Sizeof(new(Attribution)))
	fmt.Printf("int:               %3d\n", unsafe.Sizeof(0))
	fmt.Printf("map[string]string: %3d\n", unsafe.Sizeof(make(map[string]string)))
	fmt.Printf("[]string:          %3d\n", unsafe.Sizeof(make([]string, 0)))
	return false
}

func main() {
	ctx := context.Background()
	// need to have at least one task for the trace viewer to show any logs/regions
	ctx, task := trace.NewTask(ctx, "awesomeTask")
	defer task.End()
	defer trace.StartRegion(ctx, "main").End()
	control.init()
	rs := newReposurgeon()
	interpreter := kommandant.NewKommandant(rs)
	interpreter.EnableReadline(true)

	defer func() {
		maybePanic := recover()
		control.baton.Sync()
		//fmt.Print("\n")
		stopCPUProfiling()
		stopTracing()
		if len(control.profilename) > 0 {
			saveAllProfiles(control.profilename)
		}
		files, err := ioutil.ReadDir("./")
		if err == nil {
			for _, f := range files {
				if strings.HasPrefix(f.Name(), ".rs") && f.IsDir() {
					os.RemoveAll(f.Name())
				}
			}
		}
		if maybePanic != nil {
			panic(maybePanic)
		}
	}()

	if len(os.Args[1:]) == 0 {
		os.Args = append(os.Args, "-")
	}

	r := trace.StartRegion(ctx, "process-args")
	interpreter.PreLoop(ctx)
	stop := false
	for _, arg := range os.Args[1:] {
		for _, acmd := range strings.Split(arg, ";") {
			if acmd == "-" {
				control.flagOptions["interactive"] = terminal.IsTerminal(0)
				control.flagOptions["progress"] = terminal.IsTerminal(1)
				control.baton.setInteractivity(control.flagOptions["interactive"])
				r := trace.StartRegion(ctx, "repl")
				interpreter.CmdLoop(ctx, "")
				r.End()
			} else {
				// A minor concession to people used
				// to GNU conventions.  Makes
				// "reposurgeon --help" and
				// "reposurgeon --version" work as
				// expected.
				if strings.HasPrefix(acmd, "--") {
					acmd = acmd[2:]
				}
				acmd = interpreter.PreCmd(ctx, acmd)
				stop = interpreter.OneCmd(ctx, acmd)
				stop = interpreter.PostCmd(ctx, stop, acmd)
				if stop {
					break
				}
			}
		}
	}
	interpreter.PostLoop(ctx)
	r.End()
}

// end
