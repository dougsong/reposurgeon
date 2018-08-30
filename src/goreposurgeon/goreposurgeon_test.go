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
Committer-Date: Thu 01 Jan 1970 00:00:00 +0000
Check-Text: First commit.

First commit.
------------------------------------------------------------------------------
Event-Number: 4
Event-Mark: :4
Branch: refs/heads/master
Parents: :2
Committer: Ralf Schlatterbeck <rsc@runtux.com>
Committer-Date: Thu 01 Jan 1970 00:00:10 +0000
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

	saw := msg.header.Get("Event-Mark")
	expected := ":2"
	if saw != expected {
		t.Errorf("While parsing first message saw %s when expecting %s",
			saw, expected)
	}
	expected = "First commit.\n"
	saw = string(msg.body)
	if saw != expected {
		t.Errorf("Unexpected body content %s while expecting %s",
			strconv.Quote(saw), strconv.Quote(expected))
	}

	msg, err = newMessageBlock(r)
	if err != nil {
		log.Fatalf("On second read: %v", err)
	}

	saw = msg.header.Get("Event-mark")
	expected = ":4"
	if saw != expected {
		t.Errorf("While parsing second message saw %s when expecting %s",
			saw, expected)
	}
	expected = "Second commit."
	saw = string(msg.body)
	if !strings.HasPrefix(saw, expected) {
		t.Errorf("Unexpected body content %s while expecting %s",
			strconv.Quote(saw), strconv.Quote(expected))
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

func TestParseAttributionLine(t *testing.T) {
	assertEqual := func(a string, b string) {
		if a != b {
			t.Errorf("assertEqual: expected %v = %v",
				strconv.Quote(a), strconv.Quote(b))
		}
	}

	sample := []byte("J. Random Hacker <jrh@foobar.com> 1456976347 -0500")
	name, addr, date := parseAttributionLine(sample)
	assertEqual(name, "J. Random Hacker")
	assertEqual(addr, "jrh@foobar.com")
	assertEqual(date, "1456976347 -0500")

	attr := newAttribution(sample)
	n, a := attr.address()
	assertEqual(n, "J. Random Hacker")
	assertEqual(a, "jrh@foobar.com")

	assertEqual(attr.String(), string(sample))
}

func TestRemapAttribution(t *testing.T) {
	assertEqual := func(a string, b string) {
		if a != b {
			t.Errorf("assertEqual: expected %v = %v",
				strconv.Quote(a), strconv.Quote(b))
		}
	}

	authormap := map[string]authorEntry{
		"jrh": {name: "J. Random Hacker", email: "jrh@foobar.com"},
		"esr": {name: "Eric S. Raymond", email: "esr@thyrsus.com", timezone: "America/New_York"},
	}

	// Verify name remapping
	attr1 := newAttribution([]byte("jrh <jrh> 1456976347 -0500"))
	assertEqual(attr1.email, "jrh")
	attr1.remap(authormap)
	assertEqual(attr1.email, "jrh@foobar.com")

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
	assertEqual := func(a string, b string) {
		if a != b {
			t.Errorf("assertEqual: expected %v = %v",
				strconv.Quote(a), strconv.Quote(b))
		}
	}
	repo := newRepository("fubar")
	repo.basedir = "foo"
	expectdir := fmt.Sprintf("foo/.rs%d-fubar/blobs/", os.Getpid())

	blob1 := newBlob(repo)
	assertEqual(blob1.getBlobfile(false), expectdir + "000/000/000")
	blob2 := newBlob(repo)
	assertEqual(blob2.getBlobfile(false), expectdir + "000/000/001")

	nuke("foo", "")	// In case last unit test didn't execute cleanly
	const sampleContent = "Abracadabra!"
	blob1.setContent(sampleContent, 0)
	saw := blob1.getContent()
	assertEqual(sampleContent, saw)
	repo.cleanup()
}

// end
