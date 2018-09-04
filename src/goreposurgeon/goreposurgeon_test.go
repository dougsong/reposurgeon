package main

import (
	"bufio"
	"fmt"
	"log"
	"os"
	"strconv"
	"strings"
	"testing"
)

var ts stringSet

func init() {
	ts = newStringSet("a", "b", "c")
}

func TestContains(t *testing.T) {
	if ts.Contains("d") {
		t.Error("Contain check failed on \"d\", expected false.")
	}
	if !ts.Contains("a") {
		t.Error("Contain check failed on \"a\", expected true.")
	}
}

func TestEqual(t *testing.T) {
	ts2 := newStringSet("c", "b", "a")
	if !ts.Equal(ts2) {
		t.Error("Equality check failed when pass expected.")
	}
	ts3 := newStringSet("c", "b", "d")
	if ts.Equal(ts3) {
		t.Error("Equality check suceeded when fail expected.")
	}
}

func TestString(t *testing.T) {
	expect := `{"a", "b", "c"}`
	get := ts.String()
	if expect != get {
		t.Errorf("Stringer check failed, expected %s got %s.",
			expect, get)
	}
}

func TestAdd(t *testing.T) {
	ts.Add("d")
	if !ts.Contains("d") {
		t.Error("string set add failed.")
	}
}

func GetVCS(name string) VCS {
	for _, vcs := range vcstypes {
		if vcs.name == name {
			return vcs
		}
	}
	panic("Unknown VCS name: " + name)
}

func TestHasReferences(t *testing.T) {
	type vcsTestEntry struct {
		vcs      string
		expected bool
		comment  string
	}
	var vcsTestTable = []vcsTestEntry{
		{"git", false, "abracadabra"},
		{"git", true, "commit 56ab29."},
		{"svn", true, " r2336 "},
		{"svn", false, " 3.14159 "},
		{"cvs", true, " 1.15 "},
		{"cvs", false, " 42 "},
	}
	for _, tst := range vcsTestTable {
		vcs := GetVCS(tst.vcs)
		match := vcs.hasReference([]byte(tst.comment))
		if match != tst.expected {
			t.Errorf("%s ID in '%s' unexpectedly %v (%v).",
				tst.vcs, tst.comment, match, tst)
		}
	}
}

func TestZoneFromEmail(t *testing.T) {
	var ezTestTable = []struct {
		addr string
		tz   string
	}{
		{"pistol.cz", "Europe/Prague"},
		{"foo.com", ""},
	}
	for _, tst := range ezTestTable {
		tz := zoneFromEmail(tst.addr)
		if tz != tst.tz {
			t.Errorf("For %s, expected %s saw %s.",
				tst.addr, tst.tz, tz)
		}
	}
}

func TestEmptyComment(t *testing.T) {
	var TestTable = []struct {
		comment string
		empty   bool
	}{
		{"nonempty", false},
		{"", true},
		{"\t\n", true},
		{"*** empty log message ***", true},
	}
	for _, tst := range TestTable {
		empty := emptyComment(tst.comment)
		if empty != tst.empty {
			t.Errorf("For %s, expected %v saw %v.",
				strconv.Quote(tst.comment), tst.empty, empty)
		}
	}
}

func TestReadMessage(t *testing.T) {
	rawmsg := `------------------------------------------------------------------------------
Event-Number: 2
Event-Mark: :2
Branch: refs/heads/master
Parents: 
Committer: Ralf Schlatterbeck <rsc@runtux.com>
Committer-Date: 1970-01-01T00:00:00Z
Check-Text: First commit.

First commit.
------------------------------------------------------------------------------
Event-Number: 4
Event-Mark: :4
Branch: refs/heads/master
Parents: :2
Committer: Ralf Schlatterbeck <rsc@runtux.com>
Committer-Date: 1970-01-01T00:00:10Z
Check-Text: Second commit.

Second commit. This one tests byte stuffing.

.------------------------------------------------------------------------------

Magic cookie.

------------------------------------------------------------------------------
`

	r := bufio.NewReader(strings.NewReader(rawmsg))
	msg, err := newMessageBlock(r)
	if err != nil {
		log.Fatalf("On first read: %v", err)
	}

	saw := msg.getHeader("Event-Mark")
	expected := ":2"
	if saw != expected {
		t.Errorf("While parsing first message saw %q when expecting %q",
			saw, expected)
	}
	expected = "First commit.\n"
	saw = string(msg.body)
	if saw != expected {
		t.Errorf("Unexpected body content %q while expecting %q",
			saw, expected)
	}

	msg, err = newMessageBlock(r)
	if err != nil {
		log.Fatalf("On second read: %v", err)
	}

	saw = msg.getHeader("Event-Mark")
	expected = ":4"
	if saw != expected {
		t.Errorf("While parsing second message saw %q when expecting %q",
			saw, expected)
	}
	expected = "Second commit."
	saw = string(msg.body)
	if !strings.HasPrefix(saw, expected) {
		t.Errorf("Unexpected body content %q while expecting %q",
			saw, expected)
	}

	// Test the byte stuffing
	if strings.Index(saw, "\n----------------------------------") == -1 {
		t.Error("Failure to remove byte-stuffing prefix")
	}
	if strings.Index(saw, "Magic cookie") == -1 {
		t.Error("False match on bye-stuffed delimiter")
	}

	saw = msg.String()
	expected = "Event-Number"
	if strings.Index(saw, expected) == -1 {
		t.Errorf("Unexpected stringer content %s, expecting %s",
			strconv.Quote(saw), strconv.Quote(expected))
	}

}

func TestDateFormats(t *testing.T) {
	toGitdump := func(from string) string {
		d, err := newDate(from)
		if err != nil {
			t.Errorf("ill-formed date %v error %v", from, err)
		}
		return d.String()
	}
	toRFC3339 := func(from string) string {
		d, err := newDate(from)
		if err != nil {
			t.Errorf("ill-formed date %v error %v", from, err)
		}
		return d.rfc3339()
	}
	toGitlog := func(from string) string {
		d, err := newDate(from)
		if err != nil {
			t.Errorf("ill-formed date %v error %v", from, err)
		}
		return d.gitlog()
	}

	type harness struct {
		from      string
		converter func(string) string
		expected  string
	}
	const DumpSample = "1288205012 +0000"
	const RFC3339Sample = "2010-10-27T18:43:32Z"
	const LogSample = "Wed Oct 27 18:43:32 +0000 2010" // Bogus
	testTable := []harness{
		{DumpSample, toGitdump, DumpSample},
		{DumpSample, toRFC3339, RFC3339Sample},
		{DumpSample, toGitlog, LogSample},
		{RFC3339Sample, toGitdump, DumpSample},
		{RFC3339Sample, toRFC3339, RFC3339Sample},
		{RFC3339Sample, toGitlog, LogSample},
		{LogSample, toGitdump, DumpSample},
		{LogSample, toRFC3339, RFC3339Sample},
		{LogSample, toGitlog, LogSample},
	}
	for _, item := range testTable {
		conversion := item.converter(item.from)
		if conversion != item.expected {
			t.Errorf("date conversion from %s: expected %s saw %s",
				item.from, item.expected, conversion)
		}
	}
}

func TestDateComparison(t *testing.T) {
	assertBool := func(see bool, expect bool) {
		if see != expect {
			t.Errorf("assertBool: expected %v saw %v", expect, see)
		}
	}
	d1, _ := newDate("2010-10-27T18:43:32Z")
	d2, _ := newDate("1288205012 +0000")
	assertBool(d1.timestamp.Equal(d2.timestamp), true)
	d1, _ = newDate("2010-10-27T18:43:32Z")
	d2, _ = newDate("2010-10-27T18:43:33Z")
	assertBool(d1.timestamp.Equal(d2.timestamp), false)
	assertBool(d1.timestamp.Before(d2.timestamp), true)
	assertBool(d2.timestamp.After(d1.timestamp), true)
	d1, _ = newDate("1288205012 +0000")
	d2, _ = newDate("1288205013 +0000")
	assertBool(d1.timestamp.Equal(d2.timestamp), false)
	assertBool(d1.timestamp.Before(d2.timestamp), true)
	assertBool(d2.timestamp.After(d1.timestamp), true)
}

func assertEqual (t *testing.T, a string, b string) {
	if a != b {
		t.Errorf("assertEqual: expected %q = %q", a, b)
	}
}

func TestParseAttributionLine(t *testing.T) {
	sample := []byte("J. Random Hacker <jrh@foobar.com> 1456976347 -0500")
	name, addr, date := parseAttributionLine(sample)
	assertEqual(t, name, "J. Random Hacker")
	assertEqual(t, addr, "jrh@foobar.com")
	assertEqual(t, date, "1456976347 -0500")

	attr := newAttribution(sample)
	n, a := attr.address()
	assertEqual(t, n, "J. Random Hacker")
	assertEqual(t, a, "jrh@foobar.com")

	assertEqual(t, attr.String(), string(sample))
}

func TestRemapAttribution(t *testing.T) {
	authormap := map[string]authorEntry{
		"jrh": {name: "J. Random Hacker", email: "jrh@foobar.com"},
		"esr": {name: "Eric S. Raymond", email: "esr@thyrsus.com", timezone: "America/New_York"},
	}

	// Verify name remapping
	attr1 := newAttribution([]byte("jrh <jrh> 1456976347 -0500"))
	assertEqual(t, attr1.email, "jrh")
	attr1.remap(authormap)
	assertEqual(t, attr1.email, "jrh@foobar.com")

	attr2 := newAttribution([]byte("esr <esr> 1456976347 +0000"))
	zone, offset := attr2.date.timestamp.Zone()
	if offset != 0 {
		t.Errorf("Zone was +0000 but computed offset is %d", offset)
	}

	// Verify offset correction by timezone. Note, this test is
	// fragile, it will fail if the IANA zone database is not
	// available
	attr2.remap(authormap)
	zone, offset = attr2.date.timestamp.Zone()
	if zone != "EST" {
		t.Errorf("Zone was %s (%d) after remapping.", zone, offset)
	}
}

func TestBlobfile(t *testing.T) {
	repo := newRepository("fubar")
	repo.basedir = "foo"
	expectdir := fmt.Sprintf("foo/.rs%d-fubar/blobs/", os.Getpid())

	blob1 := newBlob(repo)
	assertEqual(t, blob1.getBlobfile(false), expectdir + "000/000/000")
	blob2 := newBlob(repo)
	assertEqual(t, blob2.getBlobfile(false), expectdir + "000/000/001")

	nuke("foo", "")	// In case last unit test didn't execute cleanly
	const sampleContent = "Abracadabra!"
	blob1.setContent(sampleContent, 0)
	saw := blob1.getContent()
	assertEqual(t, sampleContent, saw)
	repo.cleanup()
}

func TestUndecodable(t *testing.T) {
	var TestTable = []struct {
		text string
		codec string
		expected bool
	}{
		{"Potrzebie", "US-ASCII", true},
		{"Potr\x8fzebie", "US-ASCII", false},
	}
	for _, item := range TestTable {
		_, ok, err := ianaDecode(item.text, item.codec)
		if ok != item.expected {
			t.Errorf("decodability of %q: expected %v saw %v: %v",
				item.text, item.expected, ok, err)
		}
	}
}

func TestTag(t *testing.T) {
	repo := newRepository("fubar")
	repo.basedir = "foo"
	attr1 := newAttribution([]byte("jrh <jrh> 1456976347 -0500"))
	t1 := newTag(repo, "sample1", ":2", nil, attr1, "Sample tag #1\n")
	repo.events = append(repo.events, t1)
	if strings.Index(t1.comment, "Sample") == -1 {
		t.Error("expected string not found in tag comment")
	}
	u1 := repo.markToEvent(t1.getMark())
	if u1 == nil {
		t.Error("test lookup of event by mark failed")
	}
	assertEqual(t, t1.getMark(), u1.getMark())
	// verify that events are passed by reference,
	// so the one in the map is an alias of the one in the event list
	t1.comment = "modified\n"
	assertEqual(t, t1.comment, u1.(*Tag).comment)

	assertEqual(t, t1.actionStamp(), "2016-03-03T03:39:07Z!jrh")
	assertEqual(t, t1.emailOut(nil, 42, nil),
		"Event-Number: 43\nTag-Name: sample1\nTarget-Mark: :2\nTagger: jrh <jrh>\nTagger-Date: 2016-03-03T03:39:07Z\nCheck-Text: modified\n\nmodified")
	assertEqual(t, t1.String(),
		"tag sample1\nfrom :2\ntagger jrh <jrh> 1456976347 -0500\ndata 9\nmodified\n\n")

	inboxTag := `Event-Number: 45
Tag-Name: sample2
Target-Mark: :2317
Tagger: J. Random Hacker <jrh@foobar.com>
Tagger-Date: 2018-06-05T05:37:00Z
Check-Text: Test to be sure

Test to be sure we can read in a tag in inbox format.
`
	r := bufio.NewReader(strings.NewReader(inboxTag))
	msg, err := newMessageBlock(r)
	if err != nil {
		log.Fatalf("On first read: %v", err)
	}
	var t2 Tag
	t2.tagger = newAttribution(nil)
	t2.emailIn(*msg, false)

	assertEqual(t, "sample2", t2.name, )
	assertEqual(t, ":2317", t2.committish)
	
	if t1.undecodable("US-ASCII") {
		t.Errorf("%q was expected to be decodable, is not", t1.String())
		
	}
}

func TestBranchname(t *testing.T) {
	assertEqual(t, branchname("dubious"), "refs/tags/dubious")
}

func (s stringSet) Equal(other stringSet) bool {
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


func TestFileOp(t *testing.T) {
	fileop1 := newFileOp(nil).construct("M", "100644", ":1", "README")
	assertEqual(t, "M", fileop1.op)
	assertEqual(t, "100644", fileop1.mode)
	assertEqual(t, ":1", fileop1.ref)
	assertEqual(t, "README", fileop1.path)
	if !fileop1.paths(nil).Equal(stringSet{"README"}) {
		t.Error("fileop1 path extraction failed equality check")
	}
	
	fileop2 := newFileOp(nil).construct("M", "100755", ":2", "DRINKME")
	assertEqual(t, "M", fileop2.op)
	assertEqual(t, "100755", fileop2.mode)
	assertEqual(t, ":2", fileop2.ref)
	assertEqual(t, "DRINKME", fileop2.path)
	if !fileop2.paths(nil).Equal(stringSet{"DRINKME"}) {
		t.Error("fileop2 path extraction failed equality check")
	}

	fileop3 := newFileOp(nil).construct("D", "DRINKME")
	assertEqual(t, "D", fileop3.op)
	assertEqual(t, "DRINKME", fileop3.path)
	if !fileop3.paths(nil).Equal(stringSet{"DRINKME"}) {
		t.Error("fileop3 path extraction failed equality check")
	}

	fileop4 := newFileOp(nil).construct("R", "DRINKME", "EATME")
	assertEqual(t, "R", fileop4.op)
	assertEqual(t, "DRINKME", fileop4.source)
	assertEqual(t, "EATME", fileop4.target)
	if !fileop4.paths(nil).Equal(stringSet{"EATME", "DRINKME"}) {
		t.Error("fileop4 path extraction failed equality check")
	}

	fileop5 := newFileOp(nil).construct("C", "DRINKME", "EATME")
	assertEqual(t, "C", fileop5.op)
	assertEqual(t, "DRINKME", fileop5.source)
	assertEqual(t, "EATME", fileop5.target)
	if !fileop5.paths(nil).Equal(stringSet{"EATME", "DRINKME"}) {
		t.Error("fileop5 path extraction failed equality check")
	}

	fileop6 := newFileOp(nil).construct("N", ":3", "EATME")
	assertEqual(t, "N", fileop6.op)
	assertEqual(t, ":3", fileop6.ref)
	assertEqual(t, "EATME", fileop6.path)
	if !fileop6.paths(nil).Equal(stringSet{"EATME"}) {
		t.Error("fileop6 path extraction failed equality check")
	}

	fileop7 := newFileOp(nil).construct("deleteall")
	assertEqual(t, "deleteall", fileop7.op)
	if !fileop7.paths(nil).Equal(stringSet{}) {
		t.Error("fileop7 path extraction failed equality check")
	}

	fileop8 := newFileOp(nil).parse("M 100644 :4 COPYING")
	assertEqual(t, "M", fileop8.op)
	assertEqual(t, "100644", fileop8.mode)
	assertEqual(t, ":4", fileop8.ref)
	assertEqual(t, "COPYING", fileop8.path)

	fileop9 := newFileOp(nil).parse("M 100755 :5 runme.sh")
	assertEqual(t, "M", fileop9.op)
	assertEqual(t, "100755", fileop9.mode)
	assertEqual(t, ":5", fileop9.ref)
	assertEqual(t, "runme.sh", fileop9.path)

	fileop10 := newFileOp(nil).parse("D deleteme")
	assertEqual(t, "D", fileop10.op)
	assertEqual(t, "deleteme", fileop10.path)

	fileop11 := newFileOp(nil).parse("R DRINKME EATME")
	assertEqual(t, "R", fileop11.op)
	assertEqual(t, "DRINKME", fileop11.source)
	assertEqual(t, "EATME", fileop11.target)

	fileop12 := newFileOp(nil).parse("C DRINKME EATME")
	assertEqual(t, "C", fileop12.op)
	assertEqual(t, "DRINKME", fileop12.source)
	assertEqual(t, "EATME", fileop12.target)

	fileop13 := newFileOp(nil).parse("N :6 EATME")
	assertEqual(t, "N", fileop13.op)
	assertEqual(t, ":6", fileop13.ref)
	assertEqual(t, "EATME", fileop13.path)

	fileop14 := newFileOp(nil).parse("deleteall")
	assertEqual(t, "deleteall", fileop14.op)

}

// end
