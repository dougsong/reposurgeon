package main

import (
	"bufio"
	"fmt"
	"log"
	"os"
	"reflect"
	"strconv"
	"strings"
	"testing"
)

func assertBool(t *testing.T, see bool, expect bool) {
	if see != expect {
		t.Errorf("assertBool: expected %v saw %v", expect, see)
	}
}

func assertEqual(t *testing.T, a string, b string) {
	if a != b {
		t.Errorf("assertEqual: expected %q == %q", a, b)
	}
}

func TestStringSet(t *testing.T) {
	ts := newStringSet("a", "b", "c")

	if ts.Contains("d") {
		t.Error("Contain check failed on \"d\", expected false.")
	}
	if !ts.Contains("a") {
		t.Error("Contain check failed on \"a\", expected true.")
	}

	ts2 := newStringSet("c", "b", "a")
	if !ts.Equal(ts2) {
		t.Error("Equality check failed when pass expected.")
	}

	ts3 := newStringSet("c", "b", "d")
	if ts.Equal(ts3) {
		t.Error("Equality check succeeded when fail expected.")
	}

	ts4 := newStringSet("c", "b", "a")
	if !ts.Equal(ts.Intersection(ts4)) {
		t.Error("Intersection computation failed. (1)")
	}

	ts5 := newStringSet("c", "b", "d")
	expected5 := stringSet{"c", "b"}
	saw5 := ts.Intersection(ts5)
	if !saw5.Equal(expected5) {
		t.Error("Intersection computation failed. (2)")
	}

	ts6 := newStringSet("x", "y", "z")
	expected4 := stringSet{}
	saw6 := ts.Intersection(ts6)
	if !saw6.Equal(expected4) {
		t.Error("Intersection computation failed. (3)")
	}

	ts7 := newStringSet("c", "b", "a")
	ts7.Remove("b")
	expected7 := stringSet{"c", "a"}
	if !ts7.Equal(expected7) {
		t.Error("Remove computation failed.")
	}

	expect := `{"a", "b", "c"}`
	get := ts.String()
	if expect != get {
		t.Errorf("Stringer check failed, expected %s got %s.",
			expect, get)
	}

	ts.Add("d")
	if !ts.Contains("d") {
		t.Error("string set add failed.")
	}
}

func TestOrderedMap(t *testing.T) {
	m := newOrderedMap()

	m.set("foo", "bar")
	expect1 := "bar"
	get1 := m.get("foo")
	if expect1 != get1 {
		t.Errorf("OrderedMap retrieval failed, expected %s got %s.",
			expect1, get1)
	}

	m.set("hugger", "mugger")
	expect2 := "mugger"
	get2 := m.get("hugger")
	if expect2 != get2 {
		t.Errorf("OrderedMap retrieval failed, expected %s got %s.",
			expect2, get2)
	}

	if !reflect.DeepEqual(m.keys, []string{"foo", "hugger"}) {
		t.Errorf("keys value ot as expected")
	}

	// Should be false as key is not present
	assertBool(t, m.delete("bargle"), false)

	// Should be true as key is present
	assertBool(t, m.delete("foo"), true)

	expect3 := ""
	get3 := m.get("foo")
	if expect3 != get3 {
		t.Errorf("OrderedMap retrieval failed, expected %s got %s.",
			expect3, get3)
	}

	if !reflect.DeepEqual(m.keys, []string{"hugger"}) {
		t.Errorf("keys value not as expected after deletion")
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
	d1, _ := newDate("2010-10-27T18:43:32Z")
	d2, _ := newDate("1288205012 +0000")
	assertBool(t, d1.timestamp.Equal(d2.timestamp), true)
	d1, _ = newDate("2010-10-27T18:43:32Z")
	d2, _ = newDate("2010-10-27T18:43:33Z")
	assertBool(t, d1.timestamp.Equal(d2.timestamp), false)
	assertBool(t, d1.timestamp.Before(d2.timestamp), true)
	assertBool(t, d2.timestamp.After(d1.timestamp), true)
	d1, _ = newDate("1288205012 +0000")
	d2, _ = newDate("1288205013 +0000")
	assertBool(t, d1.timestamp.Equal(d2.timestamp), false)
	assertBool(t, d1.timestamp.Before(d2.timestamp), true)
	assertBool(t, d2.timestamp.After(d1.timestamp), true)
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

	// Verify that tag index works - would be -1 on failure
	if t1.index() != 0 {
		t.Error("test index of tag failed")
	}

	assertEqual(t, t1.actionStamp(), "2016-03-03T03:39:07Z!jrh")
	assertEqual(t, t1.emailOut(nil, 42, nil),
		"Event-Number: 43\nTag-Name: sample1\nTarget-Mark: :2\nTagger: jrh <jrh>\nTagger-Date: 2016-03-03T03:39:07Z\nCheck-Text: Sample tag #1\n\nSample tag #1\n")
	assertEqual(t, t1.String(),
		"tag sample1\nfrom :2\ntagger jrh <jrh> 1456976347 -0500\ndata 14\nSample tag #1\n\n")

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
		t.Fatalf("On first read: %v", err)
	}
	var t2 Tag
	t2.tagger = newAttribution(nil)
	t2.emailIn(msg, false)

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

	line8 := "M 100644 :4 COPYING"
	fileop8 := newFileOp(nil).parse(line8)
	assertEqual(t, "M", fileop8.op)
	assertEqual(t, "100644", fileop8.mode)
	assertEqual(t, ":4", fileop8.ref)
	assertEqual(t, "COPYING", fileop8.path)
	assertEqual(t, line8 + "\n", fileop8.String())

	line9 := "M 100755 :5 runme.sh"
	fileop9 := newFileOp(nil).parse(line9)
	assertEqual(t, "M", fileop9.op)
	assertEqual(t, "100755", fileop9.mode)
	assertEqual(t, ":5", fileop9.ref)
	assertEqual(t, "runme.sh", fileop9.path)
	assertEqual(t, line9 + "\n", fileop9.String())

	line10 := "D deleteme"
	fileop10 := newFileOp(nil).parse(line10)
	assertEqual(t, "D", fileop10.op)
	assertEqual(t, "deleteme", fileop10.path)
	assertEqual(t, line10 + "\n", fileop10.String())

	line11 := `R DRINKME EATME`
	fileop11 := newFileOp(nil).parse(line11)
	assertEqual(t, "R", fileop11.op)
	assertEqual(t, "DRINKME", fileop11.source)
	assertEqual(t, "EATME", fileop11.target)
	assertEqual(t, line11 + "\n", fileop11.String())

	line12 := `C DRINKME EATME`
	fileop12 := newFileOp(nil).parse(line12)
	assertEqual(t, "C", fileop12.op)
	assertEqual(t, "DRINKME", fileop12.source)
	assertEqual(t, "EATME", fileop12.target)
	assertEqual(t, line12 + "\n", fileop12.String())

	line13 := "N :6 EATME"
	fileop13 := newFileOp(nil).parse(line13)
	assertEqual(t, "N", fileop13.op)
	assertEqual(t, ":6", fileop13.ref)
	assertEqual(t, "EATME", fileop13.path)
	assertEqual(t, line13 + "\n", fileop13.String())

	line14 := "deleteall"
	fileop14 := newFileOp(nil).parse(line14)
	assertEqual(t, "deleteall", fileop14.op)
	assertEqual(t, line14 + "\n", fileop14.String())

	if fileop1.relevant(fileop2) {
		t.Error("relevance check succeed where failure expected")
	}
	if !fileop2.relevant(fileop3) {
		t.Error("relevance check failed where success expected")
	}

	repo := newRepository("fubar")
	commit := newCommit(repo)
	// Appending these in opposite order from how they should sort
	commit.appendOperation(*fileop1)	// README
	commit.appendOperation(*fileop2)	// DRINKME
	commit.sortOperations()
	assertEqual(t, commit.fileops[0].path, "DRINKME")
	assertEqual(t, commit.fileops[1].path, "README")
}

func TestCommitMethods(t *testing.T) {
	repo := newRepository("fubar")
	commit := newCommit(repo)
	committer := []byte("J. Random Hacker <jrh@foobar.com> 1456976347 -0500")
	commit.committer = *newAttribution(committer)
	author := newAttribution([]byte("esr <esr@thyrsus.com> 1457998347 +0000"))
	commit.authors = append(commit.authors, *author)
	commit.comment = "Example commit for unit testing\n"

	// Check for actual cloning. rather than just copying a reference 
	copied := commit.clone(repo)
	copied.committer.name = "J. Fred Muggs"
	if commit.committer.name == copied.committer.name {
		t.Fatal("unexpected pass by reference of committer attribution")
	}
	copied.authors[0].name = "I am legion"
	if commit.authors[0].name == copied.authors[0].name {
		t.Fatal("unexpected pass by reference of authot attribution")
	}

	// Check that various reports look sane, at least matching each other
	assertEqual(t, commit.lister(nil, 42, 0),
		"    43 2016-03-14T23:32:27Z        Example commit for unit testing")
	assertEqual(t, commit.actionStamp(),
		"2016-03-14T23:32:27Z!esr@thyrsus.com")
	assertEqual(t, commit.showlegacy(), "")
	assertEqual(t, commit.stamp(nil, 42, 0),
		"<2016-03-14T23:32:27Z!esr@thyrsus.com> Example commit for unit testing")
	expectout := `Event-Number: 43
Author: esr <esr@thyrsus.com>
Author-Date: 2016-03-14T23:32:27Z
Committer: J. Random Hacker <jrh@foobar.com>
Committer-Date: 2016-03-03T03:39:07Z
Check-Text: Example commit for unit testing

Example commit for unit testing
`
	assertEqual(t, commit.emailOut(nil, 42, nil), expectout)
	hackheader := `Event-Number: 43
Author: Tim the Enchanter <esr@thyrsus.com>

Example commit for unit testing, modified.
`
	r := bufio.NewReader(strings.NewReader(hackheader))
	msg, err := newMessageBlock(r)
	if err != nil {
		log.Fatalf("On first read: %v", err)
	}
	commit.emailIn(msg, false)
	hackcheck := `Event-Number: 43
Author: Tim the Enchanter <esr@thyrsus.com>
Author-Date: 2016-03-14T23:32:27Z
Committer: J. Random Hacker <jrh@foobar.com>
Committer-Date: 2016-03-03T03:39:07Z
Check-Text: Example commit for unit testing, modified.

Example commit for unit testing, modified.
`
	assertEqual(t, commit.emailOut(nil, 42, nil), hackcheck)

	attr1 := newAttribution([]byte("jrh <jrh> 1456976347 -0500"))
	newTag(repo, "sample1", ":2", commit, attr1, "Sample tag #1\n")

	if len(commit.attachments) != 1 {
		t.Errorf("tag attachment failed: %d", len(commit.attachments))
	}
}

func TestParentChildMethods(t *testing.T) {
	repo := newRepository("fubar")
	commit1 := newCommit(repo)
	committer1 := []byte("J. Random Hacker <jrh@foobar.com> 1456976347 -0500")
	commit1.committer = *newAttribution(committer1)
	author1 := newAttribution([]byte("esr <esr@thyrsus.com> 1457998347 +0000"))
	commit1.authors = append(commit1.authors, *author1)
	commit1.comment = "Example commit for unit testing\n"
	commit1.setMark(":1")

	commit2 := newCommit(repo)
	committer2 := []byte("J. Random Hacker <jrh@foobar.com> 1456976347 -0500")
	commit2.committer = *newAttribution(committer2)
	author2 := newAttribution([]byte("esr <esr@thyrsus.com> 1457998347 +0000"))
	commit2.authors = append(commit2.authors, *author2)
	commit2.comment = "Second example commit for unit testing\n"
	commit2.setMark(":2")

	commit2.addParentByMark(":1")
}

// end
