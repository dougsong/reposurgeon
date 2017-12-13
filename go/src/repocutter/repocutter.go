package main

// SPDX-License-Identifier: BSD-2-Clause

import (
	"bufio"
	"bytes"
	"flag"
	"fmt"
	"io"
	"isatty"
	"math"
	"os"
	"regexp"
	//"runtime"
	"strconv"
	"strings"
	"time"
)

const linesep = "\n"

var doc []byte = []byte(`repocutter - stream surgery on SVN dump files
general usage: repocutter [-q] [-r SELECTION] SUBCOMMAND

In all commands, the -r (or --range) option limits the selection of revisions
over which an operation will be performed. A selection consists of
one or more comma-separated ranges. A range may consist of an integer
revision number or the special name HEAD for the head revision. Or it
may be a colon-separated pair of integers, or an integer followed by a
colon followed by HEAD.

Normally, each subcommand produces a progress spinner on standard
error; each turn means another revision has been filtered. The -q (or
--quiet) option suppresses this.

Type 'repocutter help <subcommand>' for help on a specific subcommand.

Available subcommands:
   expunge
   log
   pathrename
   propdel
   proprename
   propset
   reduce
   renumber
   see
   select
   setlog
   sift
   strip
   swaps

Translated from the 2017-12-13 version of repocutter,
which began life as 'svncutter' in 2009.  The obsolete 
'squash' command has been omitted.
`)

var debug bool = false

var oneliners = map[string]string {
	//"squash":     "Squashing revisions",
	"select":     "Selecting revisions",
	"propdel":    "Deleting revision properties",
	"propset":    "Setting revision properties",
	"proprename": "Renaming revision properties",
	"log":        "Extracting log entries",
	"setlog":     "Mutating log entries",
	"strip":      "Replace content with unique cookies, preserving structure",
	"expunge":    "Expunge operations by Node-path header",
	"sift":       "Sift for operations by Node-path header",
	"pathrename": "Transform path headers with a regexp replace",
	"renumber":   "Renumber revisions so they're contiguous",
	"reduce":     "Topologically reduce a dump.",
	"see":        "Report only essential topological information",
	"swap":       "Swap first two compenents of pathnames",
}

var helpdict = map[string]string{
	"select": `select: usage: repocutter [-q] [-r SELECTION] select

The 'select' subcommand selects a range and permits only revisions in
that range to pass to standard output.  A range beginning with 0
includes the dumpfile header.
`,
	"propdel": `propdel: usage: repocutter [-r SELECTION] propdel PROPNAME...

Delete the property PROPNAME. May be restricted by a revision
selection. You may specify multiple properties to be deleted.

`,
	"propset": `propset: usage: repocutter [-r SELECTION] propset PROPNAME=PROPVAL...

Set the property PROPNAME to PROPVAL. May be restricted by a revision
selection. You may specify multiple property settings.
`,
	"proprename": `proprename: usage: repocutter [-r SELECTION] proprename OLDNAME->NEWNAME...

Rename the property OLDNAME to NEWNAME. May be restricted by a
revision selection. You may specify multiple properties to be renamed.
`,
	"log": `log: usage: repocutter [-r SELECTION] log

Generate a log report, same format as the output of svn log on a
repository, to standard output.
`,
	"setlog": `setlog: usage: repocutter [-r SELECTION] --logentries=LOGFILE setlog

Replace the log entries in the input dumpfile with the corresponding entries
in the LOGFILE, which should be in the format of an svn log output.
Replacements may be restricted to a specified range.
`,
	"strip": `strip: usage: repocutter [-r SELECTION] strip PATTERN...

Replace content with unique generated cookies on all node paths
matching the specified regular expressions; if no expressions are
given, match all paths.  Useful when you need to examine a
particularly complex node structure.
`,
	"expunge": `expunge: usage: repocutter [-r SELECTION ] expunge PATTERN...

Delete all operations with Node-path headers matching specified
Python regular expressions (opposite of 'sift').  Any revision
left with no Node records after this filtering has its Revision
record removed as well.
`,
	"sift": `sift: usage: repocutter [-r SELECTION ] sift PATTERN...

Delete all operations with Node-path headers *not* matching specified
Python regular expressions (opposite of 'expunge').  Any revision left
ith no Node records after this filtering has its Revision record
removed as well.
`,
	"pathrename": `pathrename: usage: repocutter [-r SELECTION ] pathrename FROM TO

Modify Node-path headers, Node-copyfrom-path headers, and
svn:mergeinfo properies matching the specified Python regular
expression FROM; replace with TO.  TO may contain Pyton backreferences
to parenthesized portions of FROM.
`,
	"renumber": `renumber: usage: repocutter renumber

Renumber all revisions, patching Node-copyfrom headers as required.
Any selection option is ignored. Takes no arguments.
`,
	"reduce": `reduce: usage: repocutter reduce INPUT-FILE

Strip revisions out of a dump so the only parts left those likely to
be relevant to a conversion problem. A revision is interesting if it
either (a) contains any operation that is not a plain file
modification - any directory operation, or any add, or any delete, or
any copy, or any operation on properties - or (b) it is referenced by
a later copy operation. Any commit that is neither interesting nor
has interesting neighbors is dropped.

Because the 'interesting' status of a commit is not known for sure
until all future commits have been checked for copy operations, this
command requires an input file.  It cannot operate on standard input.
The reduced dump is emitted to standard output.
`,
	"see": `see: usage: repocutter [-r SELECTION] see

Render a very condensed report on the repository node structure, mainly
useful for examining strange and pathological repositories.  File content
is ignored.  You get one line per repository operation, reporting the
revision, operation type, file path, and the copy source (if any).
Directory paths are distinguished by a trailing slash.  The 'copy'
operation is really an 'add' with a directory source and target;
the display name is changed to make them easier to see.
`,
}

// Baton - ship progress indications to stderr
type Baton struct {
	stream  *os.File
	count int
	endmsg string
	time time.Time
}	

func NewBaton(prompt string, endmsg string) *Baton {
	var baton Baton
	baton.stream  = os.Stderr
        baton.stream.Write([]byte(prompt + "..."))
        if isatty.IsTerminal(baton.stream.Fd()){
		baton.stream.Write([]byte(" \010"))
	}
        //baton.stream.Flush()
        baton.endmsg = endmsg
        baton.time = time.Now()
	return &baton
}

func (baton *Baton) Twirl(ch string) {
	if baton.stream == nil {
		return
	}
        if isatty.IsTerminal(baton.stream.Fd()) {
		if ch != "" {
			baton.stream.Write([]byte(ch))
		} else {
			baton.stream.Write([]byte{"-/|\\"[baton.count % 4]})
			baton.stream.Write([]byte("\010"))
		}
	}
        baton.count++
}

func (baton *Baton) End(msg string) {
	if msg == "" {
		msg = baton.endmsg
	}
	fmt.Fprintf(baton.stream, "...(%s) %s.\n", time.Since(baton.time), msg)
}
	
// LineBufferedSource - Generic class for line-buffered input with pushback.
type LineBufferedSource struct {
        Linebuffer []byte
	source io.Reader
        reader *bufio.Reader
	stream *os.File
        linenumber int
}

func NewLineBufferedSource(source io.Reader) LineBufferedSource {
	if debug {
		fmt.Fprintf(os.Stderr, "<setting up NewLineBufferedSource>\n")
	}
	var lbs LineBufferedSource
	lbs.Linebuffer = []byte("")
	lbs.source = source
	lbs.reader = bufio.NewReader(lbs.source)
	fd, ok := lbs.source.(*os.File)
	if ok {
		lbs.stream = fd
	}
	return lbs
}

func (lbs *LineBufferedSource) Rewind() {
	lbs.reader.Reset(lbs.reader)
	if lbs.stream != nil {
		if debug {
			fmt.Fprintf(os.Stderr, "<Rewind>\n")
		}
		lbs.stream.Seek(0, 0)
	}
}

func vis(line []byte) string {
	return strconv.Quote(string(line))
}

// Line-buffered readline.  Return "" on EOF.
func (lbs *LineBufferedSource) Readline() []byte {
	var line []byte
	var err error
	if len(lbs.Linebuffer) != 0 {
		line = lbs.Linebuffer
		if debug {
			fmt.Fprintf(os.Stderr, "<Readline: popping %s>\n", vis(line))
		}
		lbs.Linebuffer = []byte("")
	} else {
		line, err = lbs.reader.ReadBytes('\n')
		lbs.linenumber++
		if debug {
			fmt.Fprintf(os.Stderr, "<Readline %d: read %s>\n", lbs.linenumber, vis(line))
		}
		if err == io.EOF {
			return []byte("")
		} else if err != nil {
			panic("repocutter: I/O error in Readline of LineBufferedSource")
		}
	}
	return line
}
	
// Read a line, require it to have a specified prefix.
func (lbs *LineBufferedSource) Require(prefix string) []byte {
	line := lbs.Readline()
	if !strings.HasPrefix(string(line), prefix) {
		fmt.Printf("repocutter: required prefix '%s' not seen after line %d\n", prefix, lbs.linenumber)
		os.Exit(1)
	}
	//if debug {
	//	fmt.Fprintf(os.Stderr, "<Require %s -> %s>\n", strconv.Quote(prefix), vis(line))
	//}
	return line
}
	
// Straight read from underlying file, no buffering.
func (lbs *LineBufferedSource) Read(rlen int) []byte {
	if len(lbs.Linebuffer) != 0 {
		panic(fmt.Sprintf("repocutter: line buffer unexpectedly nonempty after line %d", lbs.linenumber))
	}
	text := make([]byte, rlen)
	n, err := lbs.reader.Read(text)
	if err != nil && err != io.EOF {
		panic("repocutter: I/O error in Read of LineBufferedSource")
	}
	if n < rlen {
		panic(fmt.Sprintf("repocutter: short %d of %d in Read of LineBufferedSource", n, rlen))
	}
	lbs.linenumber += strings.Count(string(text), "\n")
	return text
}

// Peek at the next line in the source.
func (lbs *LineBufferedSource) Peek() []byte {
	//assert(lbs.Linebuffer is None)
	nxtline, err := lbs.reader.ReadBytes('\n')
	lbs.linenumber++
	if err != nil && err != io.EOF {
		panic(fmt.Sprintf("repocutter: I/O error in Peek of LineBufferedSource: %s", err))
	}
	if debug {
		fmt.Fprintf(os.Stderr, "<Peek: buffer=%s + next=%s>\n", vis(lbs.Linebuffer), vis(nxtline))
	}
	lbs.Linebuffer = nxtline
	return lbs.Linebuffer
}

// Get the contents of the line buffer, clearing it.
func (lbs *LineBufferedSource) Flush() []byte {
	//assert(lbs.Linebuffer is not None)
	line := lbs.Linebuffer
	lbs.Linebuffer = []byte("")
	return line
}

// Push a line back to the line buffer.
func (lbs *LineBufferedSource) Push(line []byte) {
	//assert(lbs.linebuffer is None)
	if debug {
		fmt.Fprintf(os.Stderr, "<Push: pushing %s>\n", vis(line))
	}
	lbs.Linebuffer = []byte(line)
}
	
func (lbs *LineBufferedSource) HasLineBuffered() bool { 
	return len(lbs.Linebuffer) != 0
}

// Properties -- represent revision or node properties
type Properties struct {
        properties map[string]string
        propkeys []string
}

func NewProperties(source DumpfileSource) Properties {
	var props Properties
	newprops := make(map[string]string)
	props.properties = newprops
	for {
		if bytes.HasPrefix(source.Lbs.Peek(), []byte("PROPS-END")) {
			break
		}
		source.Lbs.Require("K")
		keyhd := string(source.Lbs.Readline())
		key := strings.TrimRight(keyhd, linesep)
		valhd := source.Lbs.Require("V")
		vlen, _ := strconv.Atoi(string(bytes.Fields(valhd)[1]))
		value := string(source.Lbs.Read(vlen))
		source.Lbs.Require(linesep)
		props.properties[key] = value
		props.propkeys = append(props.propkeys, key)
	}
        source.Lbs.Flush()
	return props
}

func (props *Properties) Stringer() string {
        st := ""
        for i := range props.propkeys {
		key := props.propkeys[i]
		if props.properties[key] != "" {
			st += fmt.Sprintf("K %d%s", len(key), linesep)
			st += fmt.Sprintf("%s%s", key, linesep)
			st += fmt.Sprintf("V %d%s", len(props.properties[key]), linesep)
			st += fmt.Sprintf("%s%s", props.properties[key], linesep)
		}
	}
	st += "PROPS-END\n"
        return st
}

func (props *Properties) Contains(key string) bool {
	_, ok := props.properties[key]
	return ok
}

// Dumpfile parsing machinery goes here

var NodeLeader *regexp.Regexp
var RevisionLine *regexp.Regexp
var TextContentLength *regexp.Regexp
var NodeCopyfrom *regexp.Regexp

func init() {
	NodeLeader = regexp.MustCompile("Node-")
	RevisionLine = regexp.MustCompile("Revision-number: ([0-9])")
	TextContentLength = regexp.MustCompile("Text-content-length: ([1-9][0-9]*)")
	NodeCopyfrom = regexp.MustCompile("Node-copyfrom-rev: ([1-9][0-9]*)")
}

// DumpfileSource - This class knows about Subversion dumpfile format.
type DumpfileSource struct {
	Lbs LineBufferedSource
	Baton *Baton
	Revision int
	EmittedRevisions map[string]bool
}

func NewDumpfileSource(rd io.Reader, baton *Baton) DumpfileSource {
	var ds DumpfileSource
	ds.Lbs = NewLineBufferedSource(rd)
	ds.Baton = baton
        ds.Revision = 0
        ds.EmittedRevisions = make(map[string]bool)
	//runtime.SetFinalizer(&ds, func (s DumpfileSource) {s.Baton.End("")}) 
	return ds
}

func SetLength(header string, data []byte, val int) []byte {
	re := regexp.MustCompile("(" + header + "-length:) ([0-9]+)")
	return re.ReplaceAll(data, []byte("$1 " + strconv.Itoa(val)))
}

// Read a revision header, parsing its properties.
func (ds *DumpfileSource) ReadRevisionHeader(PropertyHook func(*Properties)) ([]byte, map[string]string) {
        stash := ds.Lbs.Require("Revision-number:")
	rev := string(bytes.Fields(stash)[1])
        rval, err := strconv.Atoi(rev)
	if err != nil {
		fmt.Printf("repocutter: invalid revision number %s at line %d\n", rev, ds.Lbs.linenumber)
		os.Exit(1)
	}
	ds.Revision = rval
        stash = append(stash, ds.Lbs.Require("Prop-content-length:")...)
        stash = append(stash, ds.Lbs.Require("Content-length:")...)
        stash = append(stash, ds.Lbs.Require(linesep)...)
        props := NewProperties(*ds)
        if PropertyHook != nil {
		PropertyHook(&props)
		stash = SetLength("Prop-content", stash, len(props.Stringer()))
		stash = SetLength("Content", stash, len(props.Stringer()))
	}
        stash = append(stash, []byte(props.Stringer())...)
	for {
		if string(ds.Lbs.Peek()) == linesep {
			stash = append(stash, ds.Lbs.Readline()...)
		} else {
			break
		}
	}
	if ds.Baton != nil {
		ds.Baton.Twirl("")
	}
	if debug {
		fmt.Fprintf(os.Stderr, "<ReadRevisionHeader: returns stash=%s>\n",
			vis(stash))
	}
        return stash, props.properties
}

// Read a node header and body.
func (ds DumpfileSource) ReadNode(PropertyHook func(*Properties)) ([]byte, []byte, []byte) {
	if debug {
		fmt.Fprintf(os.Stderr, "<READ NODE BEGINS>\n")
	}
        header := ds.Lbs.Require("Node-")
        for {
		line := ds.Lbs.Readline()
		if len(line) == 0 {
			fmt.Fprintf(os.Stderr, "repocutter: unexpected EOF in node header\n")
			os.Exit(1)
		}
		m := NodeCopyfrom.Find(line)
		if len(m) > 0 {
			r := string(m[1])
			if !ds.EmittedRevisions[r] {
				header = append(header, line...)
				header = append(header, ds.Lbs.Require("Node-copyfrom-path")...)
				continue
			}
		}
		header = append(header, line...)
		if string(line) == linesep {
			break
		}
	}
	properties := ""
	if bytes.Contains(header, []byte("Prop-content-length")) {
		props := NewProperties(ds)
		if PropertyHook != nil {
			PropertyHook(&props)
		}
		properties = props.Stringer()
	}
        // Using a read() here allows us to handle binary content
        content := []byte("")
        cl := TextContentLength.FindSubmatch(header)
        if len(cl) > 1 {
		n, _ := strconv.Atoi(string(cl[1]))
		content = append(content, ds.Lbs.Read(n)...)
	}
	if debug {
		fmt.Fprintf(os.Stderr, "<READ NODE ENDS>\n")
	}
        if PropertyHook != nil {
		header = SetLength("Prop-content", header, len(properties))
		header = SetLength("Content", header, len(properties) + len(content))
	}
	return header, []byte(properties), content
}

// Accumulate lines until the next matches a specified prefix.
func (ds *DumpfileSource) ReadUntilNext(prefix string, revmap map[int]int) []byte {
	if debug {
		fmt.Fprintf(os.Stderr, "<ReadUntilNext: until %s>\n", prefix)
	}
        stash := []byte("")
        for {
		line := ds.Lbs.Readline()
		if debug {
			fmt.Fprintf(os.Stderr, "<ReadUntilNext: sees %s>\n", vis(line))
		}

		if len(line) == 0 {
			return stash
		} else if strings.HasPrefix(string(line), prefix) {
			ds.Lbs.Push(line)
			if debug {
				fmt.Fprintf(os.Stderr, "<ReadUntilNext pushes: %s>\n", vis(line))
			}
			return stash
		} else {
			// Hack the revision levels in copy-from headers.
			// We're actually modifying the dumpfile contents
			// (rather than selectively omitting parts of it).
			// Note: this will break on a dumpfile that has dumpfiles
			// in its nodes!
			if revmap != nil && strings.HasPrefix(string(line), "Node-copyfrom-rev:") {
				old := bytes.Fields(line)[1]
				oldi, err := strconv.Atoi(string(old))
				if err != nil {
					newrev := []byte(strconv.Itoa(revmap[oldi]))
					line = bytes.Replace(line, old, newrev, 1)
				}
			}
			stash = append(stash, line...)
			if debug {
				fmt.Fprintf(os.Stderr, "<ReadUntilNext: appends %s>\n", vis(line))
			}
		}
	}
}

func (ds *DumpfileSource) say(text []byte) {
	matches := RevisionLine.FindSubmatch(text)
        if len(matches) > 1 {
		ds.EmittedRevisions[string(matches[1])] = true
	}
        os.Stdout.Write(text)
}

type SubversionRange struct {
	intervals [][2]int
}

func NewSubversionRange(txt string) SubversionRange {
	var s SubversionRange 
	s.intervals = make([][2]int, 0)
	for _, item := range strings.Split(txt, ",") {
		var parts [2]int
		var upperbound int = 0
		if strings.Index(item, ":") != -1 {
			fields := strings.Split(item, ":")
			if fields[0] == "HEAD" {
				panic("repocutter: can't accept HEAD as lower bound of a range.")
			}
		    	parts[0], _ = strconv.Atoi(fields[0])
			if fields[1] == "HEAD" {
				// Be on safe side - could be a 32-bit machine
				parts[1] = math.MaxInt32
			} else {
				parts[1], _ = strconv.Atoi(fields[1])
			}
		} else {
		    	parts[0], _ = strconv.Atoi(item)
		    	parts[1], _ = strconv.Atoi(item)
		}
		if parts[0] >= upperbound {
			upperbound = parts[0]
		} else {
			panic("ill-formed range specification")
		}
		s.intervals = append(s.intervals, parts)
	}
	return s
}

func (s *SubversionRange) Contains(rev int) bool {
	for _, interval := range s.intervals {
		if rev >= interval[0] && rev <= interval[1] {
			return true
		}
	}
        return false
}

// What is the uppermost revision in the spec?
func (s *SubversionRange) Upperbound() int {
	return s.intervals[len(s.intervals)-1][1]
}

// Report a filtered portion of content.
func (ds *DumpfileSource) Report(selection SubversionRange,
		nodehook func(header []byte, properties []byte, content []byte) []byte,
		prophook func(properties *Properties),
		passthrough bool, passempty bool) {
	emit := passthrough && selection.intervals[0][0] == 0
	stash := ds.ReadUntilNext("Revision-number:", nil)
	if emit {
		if debug {
			fmt.Fprintf(os.Stderr, "<early stash dump: %s>\n", vis(stash))
		}
		os.Stdout.Write(stash)
	}
	if !ds.Lbs.HasLineBuffered() {
		return
	}
	var nodecount int
	var line []byte
	for {
		nodecount = 0
		stash, _ := ds.ReadRevisionHeader(prophook)
		if selection.Contains(ds.Revision) {
			// pass
		} else if ds.Revision == selection.Upperbound()+1 {
			return
		} else {
			ds.ReadUntilNext("Revision-number:", nil)
			continue
		}
		for {
			line = ds.Lbs.Readline()
			if len(line) == 0 {
				return
			} else if string(line) == "\n" {
				if passthrough && emit {
					if debug {
						fmt.Fprintf(os.Stderr, "<passthrough dump: %s>\n", vis(line))
					}
					os.Stdout.Write(line)
					continue
				}
			} else if strings.HasPrefix(string(line), "Revision-number:") {
				ds.Lbs.Push(line)
				if len(stash) != 0 && nodecount == 0 && passempty {
					if passthrough {
						if debug {
							fmt.Fprintf(os.Stderr, "<revision stash dump: %s>\n", vis(stash))
						}
						ds.say(stash)
					}
				}
				nodecount = 0
				break
			} else if strings.HasPrefix(string(line), "Node-") {
				nodecount += 1
				ds.Lbs.Push(line)
				header, properties, content := ds.ReadNode(prophook)
				if debug {
					fmt.Fprintf(os.Stderr, "<header: %s>\n", vis(header))
					fmt.Fprintf(os.Stderr, "<properties: %s>\n", vis(properties))
					fmt.Fprintf(os.Stderr, "<content: %s>\n", vis(content))
				}
				nodetxt := nodehook(header, properties, content)
				if debug {
					fmt.Fprintf(os.Stderr, "<nodetxt: %s>\n", vis(nodetxt))
				}
				emit = len(nodetxt) > 0
				if emit && len(stash) > 0 {
					if debug {
						fmt.Fprintf(os.Stderr, "<appending to: %s>\n", vis(stash))
					}
					nodetxt = append(stash, nodetxt...)
					stash = []byte("")
				}
				if passthrough && len(nodetxt) > 0 {
					if debug {
						fmt.Fprintf(os.Stderr, "<node dump: %s>\n", vis(nodetxt))
					}
					ds.say(nodetxt)
				}
				continue
			} else {
				fmt.Fprintf(os.Stderr, "repocutter: parse at %s doesn't look right (%s), aborting!\n", ds.Revision, line)
				os.Exit(1)
			}
		}
	}
}

type Logentry struct {
	author []byte
	date []byte
	text []byte
}

// Logfile represents the state of a logfile
type Logfile struct {
        comments map[int]Logentry
        source LineBufferedSource
}

// Contains - Does the logfile contain an entry for a specified revision
func (lf *Logfile) Contains(revision int) bool {
	_, ok := lf.comments[revision]
	return ok
}

const delim = "------------------------------------------------------------------------"

func NewLogfile(readable io.Reader, restrict *SubversionRange) *Logfile {
	var lf Logfile
	lf.comments = make(map[int]Logentry, 0)
	lf.source = NewLineBufferedSource(readable)
	state := "awaiting_header"
        author := []byte("")
	date := []byte("")
        logentry := []byte("")
        lineno := 0
        rev := -1
	re := regexp.MustCompile("^r[0-9]+")
	var line []byte
	for {
		lineno += 1
		line = lf.source.Readline()
		if state == "in_logentry" {
			if len(line) == 0 || bytes.HasPrefix(line, []byte(delim)) {
				if rev > -1 {
					logentry = bytes.TrimSpace(logentry)
					if restrict == nil || restrict.Contains(rev) {
						lf.comments[rev] = Logentry{author, date, logentry}
					}
					rev = -1
					logentry = []byte("")
				}
				if len(line) != 0 {
					state = "awaiting_header"
				} else {
					break
				}
			} else {
				logentry = append(logentry, line...)
			}
		} else if state == "awaiting_header" {
			if len(line) == 0 {
				break
			} else if bytes.HasPrefix(line, []byte("-----------")) {
				continue
			} else {
				if re.Find(line) == nil {
					fmt.Fprintf(os.Stderr, "line %d: repocutter did not see a comment header where one was expected\n", lineno)
					os.Exit(1)
				} else {
					fields := bytes.Split(line, []byte("|"))
					revstr := bytes.TrimSpace(fields[0])
					author = bytes.TrimSpace(fields[1])
					date = bytes.TrimSpace(fields[2])
					//lc := bytes.TrimSpace(fields[3])
					revstr = revstr[1:]	// strip off leaing 'r'
					rev, _ = strconv.Atoi(string(revstr))
					state = "in_logentry"
				}
			}
		}
	}
	return &lf
}

// Extract content of  a specified header
func payload(hd string, header []byte) []byte {
	offs := bytes.Index(header, []byte(hd + ": "))
	if offs == -1 {
		return nil
	} else {
		offs += len(hd) + 2
		end := bytes.Index(header[offs:], []byte("\n"))
		return header[offs:offs+end]
	}
}
	

// Select a portion of the dump file defined by a revision selection.
func sselect(source DumpfileSource, selection SubversionRange) {
	if debug {
		fmt.Fprintf(os.Stderr, "<entering sselect>")
	}
	emit := selection.Contains(0)
	for {
		stash := source.ReadUntilNext("Revision-number:", nil)
		if debug {
			fmt.Fprintf(os.Stderr, "<stash: %s>\n", vis(stash))
		}
		if emit {
			os.Stdout.Write(stash)
		}
		if !source.Lbs.HasLineBuffered() {
			return
		} else {
			fields := bytes.Fields(source.Lbs.Linebuffer)
			// Error already checked during source parsing
			revision, _ := strconv.Atoi(string(fields[1]))
			emit = selection.Contains(revision)
			if debug {
				fmt.Fprintf(os.Stderr, "<%s:%b>\n", revision, emit)
			}
			if emit {
				os.Stdout.Write(source.Lbs.Flush())
			} else if revision == selection.Upperbound()+1 {
				return
			} else {
				source.Lbs.Flush()
			}
		}
	}
}

func dumpall(header []byte, properties []byte, content []byte) []byte {
	var all []byte = make([]byte, 0)
	all = append(all, header...)
	all = append(all, properties...)
	all = append(all, content...)
        return all
}

// propdel - Delete properties
func propdel(source DumpfileSource, propnames []string, selection SubversionRange) {
	revhook := func(props *Properties) {
		for _, propname := range propnames {
			if _, ok := props.properties[propname]; ok {
				props.properties[propname] = ""
			}
			var delindex = -1
			var item string
			for delindex, item = range props.propkeys {
				if item == propname {
					break
				}
			}
			if delindex != -1 {
				props.propkeys = append(props.propkeys[:delindex], props.propkeys[delindex+1:]...)
			}
		}
	}
	source.Report(selection, dumpall, revhook, true, true)
}

// Set properties.
func propset(source DumpfileSource, propnames []string, selection SubversionRange) {
	revhook := func(props *Properties) {
		for _, propname := range propnames {
			fields := strings.Split(propname, "=")
			if _, present := props.properties[fields[0]]; !present {
				props.propkeys = append(props.propkeys, fields[0])
			}
			props.properties[fields[0]] = fields[1]
		}
	}
	source.Report(selection, dumpall, revhook, true, true)
}

// Rename properties.
func proprename(source DumpfileSource, propnames []string, selection SubversionRange) {
	revhook := func(props *Properties) {
		for _, propname := range propnames {
			fields := strings.Split(propname, "->")
			if _, present := props.properties[fields[0]]; present {
				props.properties[fields[1]] = props.properties[fields[0]]
				props.properties[fields[0]] = ""
				for i, item := range props.propkeys {
					if item == fields[0] {
						props.propkeys[i] = fields[1]
					}
				}
			}
		}
	}
	source.Report(selection, dumpall, revhook, true, true)
}

func getAuthor(props map[string]string) string {
	author := props["svn:author"]
	if author == "" {
		author = "(no author)"
	}
	return author
}

// Extract a given field from a header string
func get_header(txt []byte, hdr string) []byte {
        for _, line := range bytes.Split(txt, []byte("\n")) {
		if bytes.HasPrefix(line, []byte(hdr + ": ")){
		    return line[len(hdr)+2:]
	    }
	}
        return nil
}

func SVNTimeParse(rdate string) time.Time {
	// An example date in SVN format is '2011-11-30T16:40:02.180831Z'
	date, ok := time.Parse(time.RFC3339Nano, rdate)
	if ok != nil {
		fmt.Fprintf(os.Stderr, "ill-formed date '%s': %v\n", rdate, ok)
		os.Exit(1)
	}
	return date
}

// Extract log entries
func log(source DumpfileSource, _selection SubversionRange) {
	for {
		source.ReadUntilNext("Revision-number:", nil)
		if !source.Lbs.HasLineBuffered() {
			return
		} else {
			_, props := source.ReadRevisionHeader(nil)
			logentry := props["svn:log"]
			if logentry != ""{
				os.Stdout.Write([]byte(delim + "\n"))
			}
			author := getAuthor(props)
			date := SVNTimeParse(props["svn:date"])
			drep := date.Format("2006-01-02 15:04:05 +0000 (Mon, 02 Jan 2006)")
			fmt.Printf("r%d | %s | %s | %d lines\n",
				source.Revision,
				author,
				drep,
				strings.Count(logentry, "\n"))
			os.Stdout.Write([]byte("\n" + logentry + "\n"))
		}
	}
}

// Mutate log entries.
func setlog(source DumpfileSource, logpath string, selection SubversionRange) {
	fd, ok := os.Open(logpath)
	if ok != nil {
		panic("couldn't open " + logpath)
	}
	logpatch := NewLogfile(fd, &selection)
	loghook := func(prop *Properties) {
		_, haslog := prop.properties["svn:log"]
		if haslog && logpatch.Contains(source.Revision) {
			logentry := logpatch.comments[source.Revision]
			if string(logentry.author) != getAuthor(prop.properties) {
				fmt.Fprintf(os.Stderr, "repocutter: author of revision %s doesn't look right, aborting!\n", source.Revision)
				os.Exit(1)
			}
			prop.properties["svn:log"] = string(logentry.text)
		}
	}
	source.Report(selection, dumpall, loghook, true, true)
}

// Strip a portion of the dump file defined by a revision selection.
func strip(source DumpfileSource, selection SubversionRange, patterns []string) {
	innerstrip := func(header []byte, properties []byte, content []byte) []byte {
		set_length := func(hd []byte, name string, val int) []byte {
			r := regexp.MustCompile(name + ": ([0-9]*)")
			m := r.FindSubmatchIndex([]byte(hd))
			if len(m) != 4 {
				panic(fmt.Sprintf("While setting length of %s", name))
			}
			var res []byte
			res = hd[0:m[2]]
			res = append(res, []byte(fmt.Sprintf("%d", val))...)
			res = append(res, hd[m[3]:len(hd)]...)
			return res
		}

		// first check against the patterns, if any are given
		ok := true
		offs := bytes.Index(header, []byte("Node-path: "))
		if offs > -1 {
			offs += 11
			filepath := header[offs:bytes.Index(header[offs:], []byte("\n"))]
			for _, pattern := range patterns {
				re := regexp.MustCompile(pattern)
				if re.Find(filepath) == nil {
					//os.Stderr.Write("strip skipping: %s\n", filepath)
					ok = false
					break
				}
			}
		}
		if ok {
			if content != nil && len(content) > 0  {
				tell := fmt.Sprintf("Revision is %s, file path is %s.\n\n\n",
					source.Revision, get_header(header, "Node-path"))
				// Avoid replacing symlinks, a reposurgeon sanity check barfs.
				if bytes.HasPrefix(content, []byte("link ")) {
					content = append(content, []byte(tell)...)
				} else {
					content = []byte(tell)
				}
				header = set_length(header,
					"Text-content-length", len(content)-2)
				header = set_length(header,
					"Content-length", len(properties)+len(content)-2)
			}
			r1 := regexp.MustCompile("Text-content-md5:.*\n")
			header = r1.ReplaceAll(header, []byte(""))
			r2 := regexp.MustCompile("Text-content-sha1:.*\n")
			header = r2.ReplaceAll(header, []byte(""))
			r3 := regexp.MustCompile("Text-copy-source-md5:.*\n")
			header = r3.ReplaceAll(header, []byte(""))
			r4 := regexp.MustCompile("Text-copy-source-sha1:.*\n")
			header = r4.ReplaceAll(header, []byte(""))
		}

		var all []byte = make([]byte, 0)
		all = append(all, header...)
		all = append(all, properties...)
		all = append(all, content...)
		return all
	}
	source.Report(selection, innerstrip, nil, true, true)
}

// Topologically reduce a dump, removing spans of plain file modifications.
func doreduce(source DumpfileSource) {
	interesting := make([]int, 0)
	__reduce := func(header []byte, properties []byte, _content []byte) []byte {
		if !(string(get_header(header, "Node-kind")) == "file" && string(get_header(header, "Node-action")) == "change") || (properties != nil && len(properties) > 0) {
			interesting = append(interesting, source.Revision)
		}
		copysource := get_header(header, "Node-copyfrom-rev")
		if copysource != nil {
			n, err := strconv.Atoi(string(copysource))
			if err == nil {
				interesting = append(interesting, n)
			}
		}
		return nil
	}
	source.Report(NewSubversionRange("0:HEAD"), __reduce, nil, false, true)
	var selection string
	integerIn := func(n int, v []int) bool {
		for _, i := range v {
			if n == v[i] {
				return true
			}
		}
		return false
	}
	for _, item := range interesting {
		if integerIn(item-1, interesting) || integerIn(item, interesting) ||integerIn(item+1, interesting) {
		selection += fmt.Sprintf("%d,", item) 
		}
	}	
	source.Lbs.Rewind()
	// -2 is to trim off trailing comma
	sselect(source, NewSubversionRange(selection[0:len(selection)-2]))
}

// Strip out ops defined by a revision selection and a path regexp.
func expunge(source DumpfileSource, selection SubversionRange, patterns []string) {
	__expunge := func(header []byte, properties []byte, content []byte) []byte {
		matched := false
		offs := bytes.Index(header, []byte("Node-path: "))
		var filepath []byte
		if offs > -1 {
			offs += 11
			filepath = header[offs:offs+bytes.Index(header[offs:], []byte("\n"))]
			for _, pattern := range patterns {
				r := regexp.MustCompile(pattern)
				if r.Find(filepath) != nil {
					//log.Write("expunge skipping: " + filepath +"\n")
					matched = true
					break
				}
			}
		}
		if !matched {
			var all []byte = make([]byte, 0)
			all = append(all, header...)
			all = append(all, properties...)
			all = append(all, content...)
			return all
		} else {
			return []byte("")
		}
	}
	source.Report(selection, __expunge, nil, true, true)
}
	
// Sift for ops defined by a revision selection and a path regexp.
func sift(source DumpfileSource, selection SubversionRange, patterns []string) {
	__sift := func(header []byte, properties []byte, content []byte) []byte {
		matched := false
		offs := bytes.Index(header, []byte("Node-path: "))
		if offs > -1 {
			offs += 11
			filepath := header[offs:offs+bytes.Index(header[offs:], []byte("\n"))]
			for _, pattern := range patterns {
				r := regexp.MustCompile(pattern)
				if r.Find(filepath) != nil {
					//log.Write("sift skipping: " + filepath +"\n")
					matched = true
					break
				}
			}
		}
		if matched {
			var all []byte = make([]byte, 0)
			all = append(all, header...)
			all = append(all, properties...)
			all = append(all, content...)
			return all
		} else {
			return []byte("")
		}
	}
	source.Report(selection, __sift, nil, false, true)
}
	
// Hack paths by applying a regexp transformation.
func pathrename(source DumpfileSource, selection SubversionRange, patterns []string) {
	revhook := func(props *Properties) {
		if _, present := props.properties["svn:mergeinfo"]; present {
			r := regexp.MustCompile(patterns[0])
			props.properties["svn:mergeinfo"] = r.ReplaceAllString(
				props.properties["svn:mergeinfo"],
				patterns[1])
		}
	}
	nodehook := func(header []byte, properties []byte, content []byte) []byte {
		for _, htype := range []string{"Node-path: ", "Node-copyfrom-path: "} {
			offs := bytes.Index(header, []byte(htype))
			if offs > -1 {
				offs += len(htype)
				endoffs := offs + bytes.Index(header[offs:], []byte("\n"))
				before := header[:offs]
				pathline := header[offs:endoffs]
				after := header[endoffs:]
				//sys.stderr.write("Patterns: %s %s\n" % (patterns[0], patterns[1]))
				r := regexp.MustCompile(patterns[0])
				pathline = r.ReplaceAll(pathline, []byte(patterns[1]))
				header = before
				header = append(header, pathline...)
				header = append(header, after...)
			}
		}
		var all []byte = make([]byte, 0)
		all = append(all, header...)
		all = append(all, properties...)
		all = append(all, content...)
		return all
	}
	source.Report(selection, nodehook, revhook, true, true)
}
	
// Renumber all revisions.
func renumber(source DumpfileSource) {
	renumbering := make(map[string]int, 0)
	counter := 0
	var p []byte
	for {
		line := source.Lbs.Readline()
		if len(line) == 0 {
			break
		} else if p = payload("Revision-number", line); p != nil {
			fmt.Printf("Revision-number: %d\n", counter)
			renumbering[string(p)] = counter
			counter += 1
		} else if p = payload("Node-copyfrom-rev:", line); p != nil {
			fmt.Printf("Node-copyfrom-rev: %s\n", p)
		} else {
			os.Stdout.Write(line)
		}
	}
}

// Strip out ops defined by a revision selection and a path regexp.
func see(source DumpfileSource, selection SubversionRange) {
	__seenode := func(header []byte, _properties []byte, _content []byte) []byte {
		if debug {
			fmt.Fprintf(os.Stderr, "<header: %s>\n", vis(header))
		}
		path := payload("Node-path", header)
		kind := payload("Node-kind", header)
		if string(kind) == "dir" {
			path = append(path, os.PathSeparator)
		}
		frompath := payload("Node-copyfrom-path", header)
		fromrev := payload("Node-copyfrom-rev", header)
		action := payload("Node-action", header)
		if frompath != nil && fromrev != nil {
			if string(kind) == "dir" {
				frompath = append(frompath, os.PathSeparator)
			}
			path = append(path, []byte(fmt.Sprintf(" from %s:%s", fromrev, frompath))...)
			action = []byte("copy")
		}
		fmt.Printf("%-5d %-8s %s\n", source.Revision, action, path)
		return nil
	}
	source.Report(selection, __seenode, nil, false, true)
}

var swaplatch = false	// Ugh...

// Hack paths by swapping the top two components.
func swap(source DumpfileSource, selection SubversionRange) {
	mutator := func(path []byte) []byte {
		parts := bytes.Split(path, []byte("/"))
		if len(parts) < 2 {
			// Single-component directory creations should be
			// skipped; each such operation for directory 'foo' is
			// replaced by the creation of the swapped directory
			// trunk/foo.  Works because both reposurgeon and
			// Subversion's stream dump reader don't mind if no
			// explicit trunk/ directory creation is ever done as
			// long as some trunk subdirectory *is* created.
			return nil
		} else {
			tp := parts[0]
			parts[0] = parts[1]
			parts[1] = tp
			return bytes.Join(parts, []byte("/"))
		}
	}
	revhook := func(props *Properties) {
		var mergepath []byte
		if m, ok := props.properties["svn:mergeinfo"]; ok {
			mergepath = mutator([]byte(m))
		}
		if mergepath != nil {
			props.properties["svn:mergeinfo"] = string(mergepath)
		}
		if source.Revision == 1 && props.Contains("svn:log") {
			props.properties["svn:log"] = "Synthetic branch-structure creation.\n"
		}
		// We leave author and date alone.  This will get
		// dropped in the git version; it's only being
		// generated so reposurgeon doesn't get confused about
		// the branch structure.
	}
	nodehook := func(header []byte, properties []byte, content []byte) []byte {
		// This is dodgy.  The assumption here is that the first node
		// of r1 is the directory creation for the first project.
		// Replace it with synthetic nodes that create normal directory
		// structure.
		var swap_header = `Node-path: branches
Node-kind: dir
Node-action: add
Prop-content-length: 10
Content-length: 10

PROPS-END


Node-path: tags
Node-kind: dir
Node-action: add
Prop-content-length: 10
Content-length: 10

PROPS-END


Node-path: trunk
Node-kind: dir
Node-action: add
Prop-content-length: 10
Content-length: 10

PROPS-END

`
		if source.Revision == 1 && !swaplatch {
			swaplatch = true
			return []byte(swap_header)
		}
		for _, htype := range []string{"Node-path: ", "Node-copyfrom-path: "} {
			offs := bytes.Index(header, []byte(htype))
			if offs > -1 {
				offs += len(htype)
				endoffs := offs + bytes.Index(header[offs:], []byte("\n"))
				before := header[:offs]
				pathline := header[offs:endoffs]
				after := header[endoffs:]
				pathline = mutator(pathline)
				if pathline == nil {
					return nil
				}
				header = []byte(string(before) + string(pathline) + string(after))
			}
		}
		var all []byte = make([]byte, 0)
		all = append(all, header...)
		all = append(all, properties...)
		all = append(all, content...)
		return all
	}
	source.Report(selection, nodehook, revhook, true, true)
}

func main () {
        selection := NewSubversionRange("0:HEAD")
        var quiet bool
        var logpatch string
	var rangestr string
	flag.BoolVar(&debug,      "d", false, "enable debug messages")
	flag.BoolVar(&debug,      "debug", false, "enable debug messages")
	flag.StringVar(&logpatch, "l", "", "pass in log patch")
	flag.StringVar(&logpatch, "logpatch", "", "pass in log patch")
	flag.BoolVar(&quiet,      "q", false, "disable progress messages")
	flag.BoolVar(&quiet,      "quiet", false, "disable progress messages")
	flag.StringVar(&rangestr, "r", "", "set selection range")
	flag.StringVar(&rangestr, "range", "", "set selection range")
	flag.Parse()
	if rangestr != "" {
		selection = NewSubversionRange(rangestr)
	}
	if debug {
		fmt.Fprintf(os.Stderr, "<selection: %v>\n", selection)
	}
	
        if flag.NArg() == 0 {
		fmt.Fprint(os.Stderr, "Type 'repocutter help' for usage.\n")
		os.Exit(1)
	} else if debug {
		fmt.Fprintf(os.Stderr, "<command=%s>\n", flag.Arg(0))
	}
        var baton *Baton
        if flag.Arg(0) != "help" {
		if !quiet {
			baton = NewBaton(oneliners[flag.Arg(0)], "done")
		} else {
			baton = nil
		}
        }
	if flag.Arg(0) == "propdel" {
		propdel(NewDumpfileSource(os.Stdin, baton), flag.Args()[1:], selection)
        } else if flag.Arg(0) == "propset" {
		propset(NewDumpfileSource(os.Stdin, baton), flag.Args()[1:], selection)
        } else if flag.Arg(0) == "proprename" {
		proprename(NewDumpfileSource(os.Stdin, baton), flag.Args()[1:], selection)
        } else if flag.Arg(0) == "select" {
		sselect(NewDumpfileSource(os.Stdin, baton), selection)
        } else if flag.Arg(0) == "log" {
		log(NewDumpfileSource(os.Stdin, baton), selection)
        } else if flag.Arg(0) == "setlog" {
		if logpatch == "" {
			fmt.Fprintf(os.Stderr, "repocutter: setlog requires a log entries file.\n")
			os.Exit(1)
		}
		setlog(NewDumpfileSource(os.Stdin, baton), logpatch, selection)
        } else if flag.Arg(0) == "strip" {
		strip(NewDumpfileSource(os.Stdin, baton), selection, flag.Args()[1:])
        } else if flag.Arg(0) == "pathrename" {
		pathrename(NewDumpfileSource(os.Stdin, baton), selection, flag.Args()[1:])
        } else if flag.Arg(0) == "expunge" {
		expunge(NewDumpfileSource(os.Stdin, baton), selection, flag.Args()[1:])
        } else if flag.Arg(0) == "sift" {
		sift(NewDumpfileSource(os.Stdin, baton), selection, flag.Args()[1:])
        } else if flag.Arg(0) == "renumber" {
		renumber(NewDumpfileSource(os.Stdin, baton))
        } else if flag.Arg(0) == "reduce" {
		f, err := os.Open(flag.Args()[1])
		if err != nil {
			fmt.Fprintf(os.Stderr, "repocutter: can't open stream ro reduce\n")
			os.Exit(1)
		}
		doreduce(NewDumpfileSource(f, baton))
        } else if flag.Arg(0) == "see" {
		see(NewDumpfileSource(os.Stdin, baton), selection)
        } else if flag.Arg(0) == "swap" {
		swap(NewDumpfileSource(os.Stdin, baton), selection)
        } else if flag.Arg(0) == "help" {
		if len(flag.Args()) == 1 {
			os.Stdout.Write(doc)
		} else {
			fmt.Fprintf(os.Stderr, "repocutter: no such command\n")
			os.Exit(1)
		}
        } else {
		fmt.Fprintf(os.Stderr, "repocutter: \"%s\": unknown subcommand\n", flag.Arg(0))
		os.Exit(1)
	}
        if baton != nil {
		baton.End("")
	}
}
