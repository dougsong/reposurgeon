package main

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"log"
	"os"
	"reflect"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"testing"
)

func assertBool(t *testing.T, see bool, expect bool) {
	t.Helper()
	if see != expect {
		t.Errorf("assertBool: expected %v saw %v", expect, see)
	}
}

func assertTrue(t *testing.T, see bool) {
	t.Helper()
	assertBool(t, see, true)
}

func assertEqual(t *testing.T, a string, b string) {
	t.Helper()
	if a != b {
		t.Fatalf("assertEqual: expected %q == %q", a, b)
	}
}

func assertRuneEqual(t *testing.T, a rune, b rune) {
	t.Helper()
	if a != b {
		t.Fatalf("assertEqual: expected %q == %q", a, b)
	}
}

func assertIntEqual(t *testing.T, a int, b int) {
	t.Helper()
	if a != b {
		t.Errorf("assertIntEqual: expected %d == %d", a, b)
	}
}

func TestBackreferences(t *testing.T) {
	from := []byte("aaabxbcccc")
	pattern := "b(.)b"
	replacement := []byte("dd${1}d")
	expected := "aaaddxdcccc"

	pre := regexp.MustCompile(pattern)
	result := pre.ReplaceAll(from, replacement)
	assertEqual(t, string(result), expected)
}

func TestOrderedStringSet(t *testing.T) {
	ts := newOrderedStringSet("a", "b", "c")

	if ts.Contains("d") {
		t.Error("Contain check failed on \"d\", expected false.")
	}
	if !ts.Contains("a") {
		t.Error("Contain check failed on \"a\", expected true.")
	}

	ts2 := newOrderedStringSet("c", "b", "a")
	if !ts.Equal(ts2) {
		t.Error("Equality check failed when pass expected.")
	}

	ts3 := newOrderedStringSet("c", "b", "d")
	if ts.Equal(ts3) {
		t.Error("Equality check succeeded when fail expected.")
	}

	ts4 := newOrderedStringSet("c", "b", "a")
	if !ts.Equal(ts.Intersection(ts4)) {
		t.Error("Intersection computation failed. (1)")
	}

	ts5 := newOrderedStringSet("c", "b", "d")
	expected5 := newOrderedStringSet("c", "b")
	saw5 := ts.Intersection(ts5)
	if !saw5.Equal(expected5) {
		t.Error("Intersection computation failed. (2)")
	}

	ts6 := newOrderedStringSet("x", "y", "z")
	expected4 := orderedStringSet{}
	saw6 := ts.Intersection(ts6)
	if !saw6.Equal(expected4) {
		t.Error("Intersection computation failed. (3)")
	}

	ts7 := newOrderedStringSet("c", "b", "a")
	ts7.Remove("b")
	expected7 := newOrderedStringSet("c", "a")
	if !ts7.Equal(expected7) {
		t.Error("Remove computation failed.")
	}

	expect := `["a", "b", "c"]`
	get := ts.String()
	if expect != get {
		t.Errorf("Stringer check failed, expected %s got %s.",
			expect, get)
	}

	ts.Add("d")
	if !ts.Contains("d") {
		t.Error("string set add failed.")
	}

	ts8 := newOrderedStringSet("a", "b", "c", "d")
	ts9 := newOrderedStringSet("b", "e")
	diff := ts8.Subtract(ts9)
	if diff[0] != "a" || diff[1] != "c" || diff[2] != "d" || len(diff) != 3 {
		t.Errorf("unexpected result of set difference: %v", diff)
	}

	sum := ts8.Union(ts9)
	if sum[0] != "a" || sum[1] != "b" || sum[2] != "c" || sum[4] != "e" || len(sum) != 5 {
		t.Errorf("unexpected result of set union: %v", sum)
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
	expected5 := newStringSet("c", "b")
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
	expected7 := newStringSet("c", "a")
	if !ts7.Equal(expected7) {
		t.Error("Remove computation failed.")
	}

	expect := `["a", "b", "c"]`
	get := ts.String()
	if expect != get {
		t.Errorf("Stringer check failed, expected %s got %s.",
			expect, get)
	}

	ts.Add("d")
	if !ts.Contains("d") {
		t.Error("string set add failed.")
	}

	ts8 := newStringSet("a", "b", "c", "d")
	ts9 := newStringSet("b", "e")
	diff := ts8.Subtract(ts9)
	if !(diff.Contains("a") && diff.Contains("c") && diff.Contains("d") && diff.Len() == 3) {
		t.Errorf("unexpected result of set difference: %v", diff)
	}

	sum := ts8.Union(ts9)
	if !(sum.Contains("a") && sum.Contains("b") && sum.Contains("c") && sum.Contains("e") && sum.Len() == 5) {
		t.Errorf("unexpected result of set union: %v", sum)
	}
}

func TestOrderedIntSet(t *testing.T) {
	ts := newOrderedIntSet(1, 2, 3)
	if ts.Contains(4) {
		t.Error("Contain check failed on \"d\", expected false.")
	}
	if !ts.Contains(1) {
		t.Error("Contain check failed on \"a\", expected true.")
	}

	ts2 := newOrderedIntSet(3, 2, 1)
	if !ts.Equal(ts2) {
		t.Error("Equality check failed when pass expected.")
	}

	ts3 := newOrderedIntSet(3, 2, 4)
	if ts.Equal(ts3) {
		t.Error("Equality check succeeded when fail expected.")
	}

	ts4 := newOrderedIntSet(3, 2, 1)
	if !ts.Equal(ts.Intersection(ts4)) {
		t.Error("Intersection computation failed. (1)")
	}

	ts5 := newOrderedIntSet(3, 2, 4)
	expected5 := orderedIntSet{3, 2}
	saw5 := ts.Intersection(ts5)
	if !saw5.Equal(expected5) {
		t.Error("Intersection computation failed. (2)")
	}

	ts6 := newOrderedIntSet(24, 25, 26)
	expected4 := orderedIntSet{}
	saw6 := ts.Intersection(ts6)
	if !saw6.Equal(expected4) {
		t.Error("Intersection computation failed. (3)")
	}

	ts7 := newOrderedIntSet(3, 2, 1)
	ts7.Remove(2)
	expected7 := orderedIntSet{3, 1}
	if !ts7.Equal(expected7) {
		t.Error("Remove computation failed.")
	}

	expect := `[1, 2, 3]`
	get := ts.String()
	if expect != get {
		t.Errorf("Stringer check failed, expected %s got %s.",
			expect, get)
	}

	ts.Add(4)
	if !ts.Contains(4) {
		t.Error("string set add failed.")
	}

	ts8 := newOrderedIntSet(1, 2, 3, 4)
	ts9 := newOrderedIntSet(2, 5)
	diff := ts8.Subtract(ts9)
	if diff[0] != 1 || diff[1] != 3 || diff[2] != 4 || len(diff) != 3 {
		t.Errorf("unexpected result of set difference: %v", diff)
	}

	sum := ts8.Union(ts9)
	if sum[0] != 1 || sum[1] != 2 || sum[2] != 3 || sum[4] != 5 || len(sum) != 5 {
		t.Errorf("unexpected result of set union: %v", sum)
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

	assertBool(t, m.delete("hugger"), true)

	m.set("a", "z")
	m.set("b", "y")
	m.set("c", "x")
	assertBool(t, m.Len() == 3, true)
	m.valueLess = func(s1, s2 string) bool {
		return s1 < s2
	}
	sort.Sort(m)
	assertEqual(t, m.keys[0], "c")
	assertEqual(t, m.keys[1], "b")
	assertEqual(t, m.keys[2], "a")

	expected := "{'c': 'x', 'b': 'y', 'a': 'z'}"
	saw := m.String()
	if expected != saw {
		t.Errorf("in OrderedMap String() test, expected %s saw %s",
			expected, saw)
	}
}

func TestHasReferences(t *testing.T) {
	type vcsTestEntry struct {
		vcs      string
		expected bool
		Comment  string
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
		vcs := findVCS(tst.vcs)
		match := vcs.hasReference([]byte(tst.Comment))
		if match != tst.expected {
			t.Errorf("%s ID in '%s' unexpectedly %v (%v).",
				tst.vcs, tst.Comment, match, tst)
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
		Comment string
		empty   bool
	}{
		{"nonempty", false},
		{"", true},
		{"\t\n", true},
		{"*** empty log message ***", true},
	}
	for _, tst := range TestTable {
		empty := emptyComment(tst.Comment)
		if empty != tst.empty {
			t.Errorf("For %s, expected %v saw %v.",
				strconv.Quote(tst.Comment), tst.empty, empty)
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
	if !strings.Contains(saw, "\n----------------------------------") {
		t.Error("Failure to remove byte-stuffing prefix")
	}
	if !strings.Contains(saw, "Magic cookie") {
		t.Error("False match on bye-stuffed delimiter")
	}

	saw = msg.String()
	expected = "Event-Number"
	if !strings.Contains(saw, expected) {
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
	toRFC3339Z := func(from string) string {
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
	const LogSample = "Wed Oct 27 18:43:32 2010 +0000"
	testTable := []harness{
		{DumpSample, toGitdump, DumpSample},
		{DumpSample, toRFC3339Z, RFC3339Sample},
		{DumpSample, toGitlog, LogSample},
		{RFC3339Sample, toGitdump, DumpSample},
		{RFC3339Sample, toRFC3339Z, RFC3339Sample},
		{RFC3339Sample, toGitlog, LogSample},
		{LogSample, toGitdump, DumpSample},
		{LogSample, toRFC3339Z, RFC3339Sample},
		{LogSample, toGitlog, LogSample},
	}
	for _, item := range testTable {
		conversion := item.converter(item.from)
		if conversion != item.expected {
			t.Errorf("date conversion from %s: expected %s saw %s",
				item.from, item.expected, conversion)
		}
	}
	testTable2 := []harness{
		{"2016-03-13T14:55:50-04:00", toRFC3339Z, "2016-03-13T18:55:50Z"},
		{"2016-03-13T14:55:29-04:00", toRFC3339Z, "2016-03-13T18:55:29Z"},
		{"2016-03-02T22:46:38-05:00", toRFC3339Z, "2016-03-03T03:46:38Z"},
		{"2016-03-02T22:45:15-05:00", toRFC3339Z, "2016-03-03T03:45:15Z"},
		{"2016-03-02T22:43:26-05:00", toRFC3339Z, "2016-03-03T03:43:26Z"},
		{"2018-03-02T22:41:15-05:00", toRFC3339Z, "2018-03-03T03:41:15Z"},
		{"2018-05-02T22:40:08-05:00", toRFC3339Z, "2018-05-03T03:40:08Z"},
		{"2018-06-02T22:39:07-05:00", toRFC3339Z, "2018-06-03T03:39:07Z"},
	}
	for _, item := range testTable2 {
		conversion := item.converter(item.from)
		if conversion != item.expected {
			t.Errorf("date conversion from %s: expected %s saw %s",
				item.from, item.expected, conversion)
		}
	}
}

func TestDateRoundtrip(t *testing.T) {
	// Test round-tripping of git-style dates
	type harness struct {
		from     int64
		expected string
	}
	testTable := []string{
		"1288205012 +0000",
		"1287754582 -0400",
		"1288996926 -0400",
	}
	for _, item := range testTable {
		tobj, _ := newDate(item)
		through := tobj.String()
		if through != item {
			t.Errorf("date roundtrip from %s: saw %s",
				item, through)
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
	sample := "J. Random Hacker <jrh@foobar.com> 1456976347 -0500"
	name, addr, date, err := parseAttributionLine(sample)
	assertEqual(t, name, "J. Random Hacker")
	assertEqual(t, addr, "jrh@foobar.com")
	assertEqual(t, date, "1456976347 -0500")
	if err != nil {
		t.Errorf("Parse error on %q where none expected: %v", sample, err)
	}

	attr, _ := newAttribution(sample)
	n, a := attr.address()
	assertEqual(t, n, "J. Random Hacker")
	assertEqual(t, a, "jrh@foobar.com")

	assertEqual(t, attr.String(), string(sample))
}

func TestParseAttribution(t *testing.T) {
	// Eric Sunshine's tests, minus the date formats we don't care about.
	tests := []struct{ s, name, email, date, err string }{
		{" ", "", "", "", "malformed attribution on ' '"},
		{"name", "", "", "", "malformed attribution on 'name'"},
		{"name<email>1262347994 +0000", "name", "email", "1262347994 +0000", ""},
		{"name <email> 1262347994 +0000", "name", "email", "1262347994 +0000", ""},
		{"(no-author) <> 1262347994 +0000", "(no-author)", "", "1262347994 +0000", ""},
	}
	for _, x := range tests {
		fullname, email, date, err := parseAttributionLine(x.s)
		if err != nil {
			if len(x.err) == 0 {
				t.Errorf("unexpected error: %v", err)
			} else if !strings.Contains(err.Error(), x.err) {
				t.Errorf("expected error %q but got %v",
					x.err, err)
			}
			continue
		}
		v := []string{x.name, x.email, x.date}
		for i, q := range []string{fullname, email, date} {
			if q != v[i] {
				t.Errorf("expected %q but got %q", v[i], q)
			}
		}
	}
}

func TestChangelogParseAttribution(t *testing.T) {
	// Wacky cases from ChangeLog files that we have to be able to handle
	tests := []struct{ attribution, name, email string }{
		{"Andreas Jaeger  <aj@suse.de>, rkl@connect.org.uk", "Andreas Jaeger", "aj@suse.de"},
	}
	for _, x := range tests {
		matches := addressRE.FindAllStringSubmatch(strings.TrimSpace(x.attribution), -1)
		assertEqual(t, matches[0][1], x.name)
		assertEqual(t, matches[0][2], x.email)
	}
}

func TestRemapAttribution(t *testing.T) {
	authormap := map[string]Contributor{
		"jrh": {fullname: "J. Random Hacker", email: "jrh@foobar.com"},
		"esr": {fullname: "Eric S. Raymond", email: "esr@thyrsus.com", timezone: "America/New_York"},
	}

	// Verify name remapping
	attr1, _ := newAttribution("jrh <jrh> 1456976347 -0500")
	assertEqual(t, attr1.email, "jrh")
	attr1.remap(authormap)
	assertEqual(t, attr1.email, "jrh@foobar.com")

	attr2, _ := newAttribution("esr <esr> 1456976347 +0000")
	_, offset := attr2.date.timestamp.Zone()
	if offset != 0 {
		t.Errorf("Zone was +0000 but computed offset is %d", offset)
	}

	// Verify offset correction by timezone. Note, this test is
	// fragile, it will fail if the IANA zone database is not
	// available
	attr2.remap(authormap)
	zone, offset := attr2.date.timestamp.Zone()
	if zone != "EST" {
		t.Errorf("Zone was %s (%d) after remapping.", zone, offset)
	}
}

func TestBlobfile(t *testing.T) {
	repo := newRepository("fubar")
	defer repo.cleanup()
	repo.basedir = "foo"
	expectdir := fmt.Sprintf("foo/.rs%d-fubar/blobs/", os.Getpid())

	blob1 := newBlob(repo)
	assertEqual(t, blob1.getBlobfile(false), expectdir+"000/000/000")
	blob2 := newBlob(repo)
	assertEqual(t, blob2.getBlobfile(false), expectdir+"000/000/001")

	nuke("foo", "") // In case last unit test didn't execute cleanly
	const sampleContent = "Abracadabra!"
	blob1.setContent([]byte(sampleContent), 0)
	saw := blob1.getContent()
	assertEqual(t, string(sampleContent), string(saw))
	nuke("foo", "")
}

func TestBlobColor(t *testing.T) {
	repo := newRepository("fubar")
	defer repo.cleanup()
	blob := newBlob(repo)
	assertTrue(t, blob.colors == 0)
	assertTrue(t, !blob.colors.Contains(colorEARLY))
	assertTrue(t, !blob.colors.Contains(colorDELETE))
	blob.colors.Add(colorEARLY)
	assertTrue(t, blob.colors.Contains(colorEARLY))
	assertTrue(t, !blob.colors.Contains(colorDELETE))
	blob.colors.Add(colorDELETE)
	assertTrue(t, blob.colors.Contains(colorEARLY))
	assertTrue(t, blob.colors.Contains(colorDELETE))
	blob.colors.Remove(colorEARLY)
	assertTrue(t, !blob.colors.Contains(colorEARLY))
	assertTrue(t, blob.colors.Contains(colorDELETE))
	blob.colors.Remove(colorDELETE)
	assertTrue(t, !blob.colors.Contains(colorEARLY))
	assertTrue(t, !blob.colors.Contains(colorDELETE))
	assertTrue(t, blob.colors == 0)
}

func TestUndecodable(t *testing.T) {
	var TestTable = []struct {
		text     string
		codec    string
		expected bool
	}{
		{"Potrzebie", "US-ASCII", true},
		{"Potr\x8fzebie", "US-ASCII", false},
	}
	for _, item := range TestTable {
		_ = item
		// XXX(mem): what's "ianaDecode"?
		// _, ok, err := ianaDecode(item.text, item.codec)
		// if ok != item.expected {
		// 	t.Errorf("decodability of %q: expected %v saw %v: %v",
		// 		item.text, item.expected, ok, err)
		// }
	}
}

func TestTag(t *testing.T) {
	repo := newRepository("fubar")
	defer repo.cleanup()
	attr1, _ := newAttribution("jrh <jrh> 1456976347 -0500")
	t1 := newTag(repo, "sample1", ":2", attr1, "Sample tag #1\n")
	repo.events = append(repo.events, t1)
	if !strings.Contains(t1.Comment, "Sample") {
		t.Error("expected string not found in tag Comment")
	}

	// Verify that tag index works - would be -1 on failure
	if t1.index() != 0 {
		t.Error("test index of tag failed")
	}

	assertEqual(t, t1.actionStamp(), "2016-03-03T03:39:07Z!jrh")
	assertEqual(t, t1.emailOut(nullOrderedStringSet, 42, nil),
		"------------------------------------------------------------------------------\nEvent-Number: 43\nTag-Name: sample1\nTarget-Mark: :2\nTagger: jrh <jrh>\nTagger-Date: Wed, 02 Mar 2016 22:39:07 -0500\nCheck-Text: Sample tag #1\n\nSample tag #1\n")
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
	t2.tagger, _ = newAttribution("")
	t2.emailIn(msg, false)

	assertEqual(t, "sample2", t2.getHumanName())
	assertEqual(t, ":2317", t2.committish)

	// XXX(mem): what's undecodable?
	// if t1.undecodable("US-ASCII") {
	// 	t.Errorf("%q was expected to be decodable, is not", t1.String())
	// }
}

func TestBranchname(t *testing.T) {
	assertEqual(t, branchname("dubious"), "refs/tags/dubious")
}

func TestStringScan(t *testing.T) {
	type testEntry struct {
		input  string
		tokens []string
	}
	var testTable = []testEntry{
		{"abab cdecde", []string{"abab", "cdecde"}},
		{"\"xy zzy\" zorkmid", []string{"xy zzy", "zorkmid"}},
		{"xyzzy \"zorkmid\"", []string{"xyzzy", "zorkmid"}},
		{"\"bubble\" \"squeak\"", []string{"bubble", "squeak"}},
	}

	for _, item := range testTable {
		trial := stringScan(item.input, 99)
		if !stringSliceEqual(trial, item.tokens) {
			t.Errorf("%q -> %v (expected %v)\n", item.input, trial, item.tokens)
		}
	}
}

func TestFileOp(t *testing.T) {
	fileop1 := newFileOp(nil).construct('M', "100644", ":1", "README")
	assertRuneEqual(t, 'M', fileop1.op)
	assertEqual(t, "100644", fileop1.mode)
	assertEqual(t, ":1", fileop1.ref)
	assertEqual(t, "README", fileop1.Source)
	if !fileop1.paths(nil).Equal(orderedStringSet{"README"}) {
		t.Error("fileop1 path extraction failed equality check")
	}

	fileop2 := newFileOp(nil).construct('M', "100755", ":2", "DRINKME")
	assertRuneEqual(t, 'M', fileop2.op)
	assertEqual(t, "100755", fileop2.mode)
	assertEqual(t, ":2", fileop2.ref)
	assertEqual(t, "DRINKME", fileop2.Source)
	if !fileop2.paths(nil).Equal(orderedStringSet{"DRINKME"}) {
		t.Error("fileop2 path extraction failed equality check")
	}

	fileop3 := newFileOp(nil).construct('D', "DRINKME")
	assertRuneEqual(t, 'D', fileop3.op)
	assertEqual(t, "DRINKME", fileop3.Source)
	if !fileop3.paths(nil).Equal(orderedStringSet{"DRINKME"}) {
		t.Error("fileop3 path extraction failed equality check")
	}

	fileop4 := newFileOp(nil).construct('R', "DRINKME", "EATME")
	assertRuneEqual(t, 'R', fileop4.op)
	assertEqual(t, "DRINKME", fileop4.Source)
	assertEqual(t, "EATME", fileop4.Target)
	if !fileop4.paths(nil).Equal(orderedStringSet{"EATME", "DRINKME"}) {
		t.Error("fileop4 path extraction failed equality check")
	}

	fileop5 := newFileOp(nil).construct('C', "DRINKME", "EATME")
	assertRuneEqual(t, 'C', fileop5.op)
	assertEqual(t, "DRINKME", fileop5.Source)
	assertEqual(t, "EATME", fileop5.Target)
	if !fileop5.paths(nil).Equal(orderedStringSet{"EATME", "DRINKME"}) {
		t.Error("fileop5 path extraction failed equality check")
	}

	fileop6 := newFileOp(nil).construct('N', ":3", "EATME")
	assertRuneEqual(t, 'N', fileop6.op)
	assertEqual(t, ":3", fileop6.ref)
	assertEqual(t, "EATME", fileop6.Source)
	if !fileop6.paths(nil).Equal(orderedStringSet{"EATME"}) {
		t.Error("fileop6 path extraction failed equality check")
	}

	fileop7 := newFileOp(nil).construct('d')
	assertRuneEqual(t, 'd', fileop7.op)
	if !fileop7.paths(nil).Equal(orderedStringSet{}) {
		t.Error("fileop7 path extraction failed equality check")
	}

	line8 := "M 100644 :4 COPYING"
	fileop8 := newFileOp(nil).parse(line8)
	assertRuneEqual(t, 'M', fileop8.op)
	assertEqual(t, "100644", fileop8.mode)
	assertEqual(t, ":4", fileop8.ref)
	assertEqual(t, "COPYING", fileop8.Source)
	assertEqual(t, line8+"\n", fileop8.String())

	line9 := "M 100755 :5 runme.sh"
	fileop9 := newFileOp(nil).parse(line9)
	assertRuneEqual(t, 'M', fileop9.op)
	assertEqual(t, "100755", fileop9.mode)
	assertEqual(t, ":5", fileop9.ref)
	assertEqual(t, "runme.sh", fileop9.Source)
	assertEqual(t, line9+"\n", fileop9.String())

	line10 := "D deleteme"
	fileop10 := newFileOp(nil).parse(line10)
	assertRuneEqual(t, 'D', fileop10.op)
	assertEqual(t, "deleteme", fileop10.Source)
	assertEqual(t, line10+"\n", fileop10.String())

	line11 := `R "DRINKME" "EATME"`
	fileop11 := newFileOp(nil).parse(line11)
	assertRuneEqual(t, 'R', fileop11.op)
	assertEqual(t, "DRINKME", fileop11.Source)
	assertEqual(t, "EATME", fileop11.Target)
	assertEqual(t, line11+"\n", fileop11.String())

	line12 := `C "DRINKME" "EATME"`
	fileop12 := newFileOp(nil).parse(line12)
	assertRuneEqual(t, 'C', fileop12.op)
	assertEqual(t, "DRINKME", fileop12.Source)
	assertEqual(t, "EATME", fileop12.Target)
	assertEqual(t, line12+"\n", fileop12.String())

	line13 := "N :6 EATME"
	fileop13 := newFileOp(nil).parse(line13)
	assertRuneEqual(t, 'N', fileop13.op)
	assertEqual(t, ":6", fileop13.ref)
	assertEqual(t, "EATME", fileop13.Source)
	assertEqual(t, line13+"\n", fileop13.String())

	line14 := "deleteall"
	fileop14 := newFileOp(nil).parse(line14)
	assertRuneEqual(t, 'd', fileop14.op)
	assertEqual(t, line14+"\n", fileop14.String())

	if fileop1.relevant(fileop2) {
		t.Error("relevance check succeed where failure expected")
	}
	if !fileop2.relevant(fileop3) {
		t.Error("relevance check failed where success expected")
	}
}

func TestSimplify(t *testing.T) {
	test := func(as []string, bs []string) {
		if len(as) != len(bs) {
			t.Fatalf("sort test must have two slices of the same length")
		}
		repo := newRepository("fubar")
		defer repo.cleanup()
		commit := newCommit(repo)
		repo.addEvent(commit)
		for _, a := range as {
			fileop := newFileOp(nil).construct('M', "100644", ":1", a)
			commit.appendOperation(fileop)
		}
		commit.simplify()
		sorted := make([]string, len(as))
		for i := range as {
			sorted[i] = commit.fileops[i].Source
		}
		if !reflect.DeepEqual(sorted, bs) {
			t.Fatalf("fileops didn't get sorted correctly; expected %#v == %#v", sorted, bs)
		}
	}

	test([]string{"README", "DRINKME"},
		[]string{"DRINKME", "README"})
	test([]string{"a", "a/b", "a/b/c"},
		[]string{"a/b/c", "a/b", "a"})
	test([]string{"b/a", "b/b", "a"},
		[]string{"a", "b/a", "b/b"})
	test([]string{"z/t/u/v", "a/b/c", "a/b"},
		[]string{"a/b/c", "a/b", "z/t/u/v"})
	test([]string{"abc/def", "abcdef/", "a/b", "a/b/c"},
		[]string{"a/b/c", "a/b", "abc/def", "abcdef/"})
	test([]string{"clients/upslog.c", "clients/upsmon.c", "CHANGES"},
		[]string{"CHANGES", "clients/upslog.c", "clients/upsmon.c"})
	test([]string{"clients/upslog.c", "clients/upsmon.c", "CHANGES", "clients/.gitignore"},
		[]string{"CHANGES", "clients/.gitignore", "clients/upslog.c", "clients/upsmon.c"})

	test2 := func(as []*FileOp, bs []*FileOp) {
		repo := newRepository("fubar")
		defer repo.cleanup()
		commit := newCommit(repo)
		repo.addEvent(commit)
		for _, a := range as {
			commit.appendOperation(a)
		}
		commit.simplify()
		quasiEquals := func(a *FileOp, b *FileOp) bool {
			return a.op == b.op && a.Source == b.Source
		}
		if len(commit.fileops) != len(bs) {
			t.Fatalf("sort test did not result in two slices of the same length")
		}
		compare := make([]string, len(bs))
		for i := range bs {
			compare[i] = bs[i].String()
		}
		sorted := make([]string, len(commit.fileops))
		for i := range commit.fileops {
			sorted[i] = commit.fileops[i].String()
		}
		for idx, b := range bs {
			if !quasiEquals(commit.fileops[idx], b) {
				t.Fatalf("fileops didn't get sorted correctly; expected %#v == %#v", sorted, compare)
				break
			}
		}
	}

	// These are not super readable; perhaps there's a better way?

	// b, a → a, b (in spite of the differing ops)
	test2([]*FileOp{newFileOp(nil).construct(opD, "b"), newFileOp(nil).construct(opM, "100644", ":1", "a")},
		[]*FileOp{newFileOp(nil).construct(opM, "100644", ":1", "a"), newFileOp(nil).construct(opD, "b")})

	// modify, deleteall → deleteall (to keep the manifest unchanged)
	test2([]*FileOp{newFileOp(nil).construct(opM, "100644", ":1", "foo/bar"), newFileOp(nil).construct(deleteall)},
		[]*FileOp{newFileOp(nil).construct(deleteall)})
	// deleteall, modify → deleteall, modify
	test2([]*FileOp{newFileOp(nil).construct(deleteall), newFileOp(nil).construct(opM, "100644", ":1", "foo/bar")},
		[]*FileOp{newFileOp(nil).construct(deleteall), newFileOp(nil).construct(opM, "100644", ":1", "foo/bar")})
	// deleteall, deleteall → deleteall (shouldn't
	// actually occur in real commits, but shouldn't break
	// anything either)
	test2([]*FileOp{newFileOp(nil).construct(deleteall), newFileOp(nil).construct(deleteall)},
		[]*FileOp{newFileOp(nil).construct(deleteall)})

	// modify, rename → rename, modify
	test2([]*FileOp{newFileOp(nil).construct(opM, "100644", ":1", "z"), newFileOp(nil).construct(opR, "a", "aa")},
		[]*FileOp{newFileOp(nil).construct(opR, "a", "aa"), newFileOp(nil).construct(opM, "100644", ":1", "z")})
}

func TestCommitMethods(t *testing.T) {
	repo := newRepository("fubar")
	defer repo.cleanup()
	commit := newCommit(repo)
	committer := "J. Random Hacker <jrh@foobar.com> 1456976347 -0500"
	attrib, _ := newAttribution(committer)
	commit.committer = *attrib
	author, _ := newAttribution("esr <esr@thyrsus.com> 1457998347 +0000")
	commit.authors = append(commit.authors, *author)
	commit.Comment = "Example commit for unit testing\n"
	commit.mark = ":2"
	repo.addEvent(commit)

	// Check for actual cloning. rather than just copying a reference
	copied := commit.clone(repo)
	copied.committer.fullname = "J. Fred Muggs"
	if commit.committer.fullname == copied.committer.fullname {
		t.Fatal("unexpected pass by reference of committer attribution")
	}
	copied.authors[0].fullname = "I am legion"
	if commit.authors[0].fullname == copied.authors[0].fullname {
		t.Fatal("unexpected pass by reference of author attribution")
	}

	// Check that various reports look sane, at least matching each other
	assertEqual(t, commit.lister(nullOrderedStringSet, 42, 0),
		"    43 2016-03-14T23:32:27Z     :2 621be4 Example commit for unit testing")
	assertEqual(t, commit.actionStamp(),
		"2016-03-14T23:32:27Z!esr@thyrsus.com")
	assertEqual(t, commit.showlegacy(), "")
	assertEqual(t, commit.stamp(nullOrderedStringSet, 42, 0),
		"<2016-03-14T23:32:27Z!esr@thyrsus.com> Example commit for unit testing")
	expectout := "------------------------------------------------------------------------------\nEvent-Number: 43\nEvent-Mark: :2\nCommitter: J. Random Hacker <jrh@foobar.com>\nCommitter-Date: Wed, 02 Mar 2016 22:39:07 -0500\nAuthor: esr <esr@thyrsus.com>\nAuthor-Date: Mon, 14 Mar 2016 23:32:27 +0000\nCheck-Text: Example commit for unit testing\n\nExample commit for unit testing\n"
	assertEqual(t, commit.emailOut(nullOrderedStringSet, 42, nil), expectout)
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
	hackcheck := "------------------------------------------------------------------------------\nEvent-Number: 43\nEvent-Mark: :2\nCommitter: J. Random Hacker <jrh@foobar.com>\nCommitter-Date: Wed, 02 Mar 2016 22:39:07 -0500\nAuthor: Tim the Enchanter <esr@thyrsus.com>\nAuthor-Date: Mon, 14 Mar 2016 23:32:27 +0000\nCheck-Text: Example commit for unit testing, modified.\n\nExample commit for unit testing, modified.\n"
	assertEqual(t, commit.emailOut(nullOrderedStringSet, 42, nil), hackcheck)

	attr1, _ := newAttribution("jrh <jrh> 1456976347 -0500")
	newTag(repo, "sample1", ":2", attr1, "Sample tag #1\n")

	if len(commit.attachments) != 1 {
		t.Errorf("tag attachment failed: %d", len(commit.attachments))
	}
}

func TestParentChildMethods(t *testing.T) {
	repo := newRepository("fubar")
	defer repo.cleanup()
	commit1 := newCommit(repo)
	repo.addEvent(commit1)
	committer1 := "J. Random Hacker <jrh@foobar.com> 1456976347 -0500"
	attrib, _ := newAttribution(committer1)
	commit1.committer = *attrib
	author1, _ := newAttribution("esr <esr@thyrsus.com> 1457998347 +0000")
	commit1.authors = append(commit1.authors, *author1)
	commit1.Comment = "Example commit for unit testing\n"
	commit1.setMark(":1")

	commit2 := newCommit(repo)
	repo.addEvent(commit2)
	committer2 := "J. Random Hacker <jrh@foobar.com> 1456976347 -0500"
	attrib, _ = newAttribution(committer2)
	commit2.committer = *attrib
	author2, _ := newAttribution("esr <esr@thyrsus.com> 1457998347 +0000")
	commit2.authors = append(commit2.authors, *author2)
	commit2.Comment = "Second example commit for unit testing\n"
	commit2.setMark(":2")

	commit2.addParentByMark(":1")
	if len(commit1.children()) != 1 || commit1.children()[0].getMark() != ":2" {
		t.Errorf("parent addition failed")
	}

	// should complain but not crash; complaint won't be visible
	// unless some other unit test fails.
	commit2.insertParent(0, ":0")

	commit3 := newCommit(repo)
	repo.addEvent(commit3)
	committer3 := "J. Random Hacker <jrh@foobar.com> 1456976447 -0500"
	attrib, _ = newAttribution(committer3)
	commit3.committer = *attrib
	author3, _ := newAttribution("esr <esr@thyrsus.com> 1457998447 +0000")
	commit3.authors = append(commit3.authors, *author3)
	commit3.Comment = "Third example commit for unit testing\n"
	commit3.setMark(":3")

	commit3.addParentByMark(":2")
	commit3.insertParent(0, ":1")
	if len(commit3.parents()) != 2 || commit3.parents()[0].getMark() != ":1" {
		t.Errorf("parent insertion :1 before :2 in :3 failed")
	}

	commit3.removeParent(commit1)
	if len(commit3.parents()) != 1 || commit3.parents()[0].getMark() != ":2" {
		t.Errorf("parent deletion of :1 in :3 failed")
	}

	assertBool(t, commit1.descendedFrom(commit3), false)
	assertBool(t, commit2.descendedFrom(commit1), true)
	assertBool(t, commit3.descendedFrom(commit2), true)
	assertBool(t, commit3.descendedFrom(commit1), true)

	// Set up some fileops so we can test things like manifests
	addop := func(commit *Commit, line string) {
		commit.appendOperation(newFileOp(repo).parse(line))
	}
	assertPathsAre := func(commit *Commit, expected []string) {
		saw := commit.paths(nil)
		if !stringSliceEqual(saw, expected) {
			t.Errorf("pathset equality check failed, expected %v saw %v",
				expected, saw)
		}
	}

	addop(commit1, "M 100644 :4 README")
	assertPathsAre(commit1, []string{"README"})
	addop(commit1, "M 100644 :5 COPYING")
	assertPathsAre(commit1, []string{"README", "COPYING"})
	assertBool(t, commit3.visible("README") != nil, true)
	assertBool(t, commit3.visible("nosuchfile") != nil, false)
	addop(commit2, "D README")
	assertBool(t, commit3.visible("README") != nil, false)
	addop(commit2, "M 100644 :6 randomness")
	m := commit3.manifest()
	if m.size() != 2 {
		t.Errorf("expected manifest length 2 at :3, saw %d", m.size())
	}
	ce, ok := m.get("COPYING")
	if !ok {
		t.Errorf("expected COPYING in manifest at :3.")
	}
	if ce.(*FileOp).ref != ":5" {
		t.Errorf("expected COPYING in manifest at :3 to trace to :5, saw %q", ce.(*FileOp).ref)
	}
	commit1.canonicalize()
	p1 := commit1.paths(nil)
	if len(p1) != 2 || p1[0] != "COPYING" || p1[1] != "README" {
		t.Errorf("unexpected content at :1 after canonicalization: %v",
			p1)
	}
	addop(commit3, "M 100644 :6 vat")
	addop(commit3, "M 100644 :7 rat")
	addop(commit3, "M 100644 :8 cat")
	commit3.canonicalize()
	p3 := commit3.paths(nil)
	if len(p3) != 3 || p3[0] != "cat" || p3[1] != "rat" {
		t.Errorf("unexpected content at :3 after 1st canonicalization: %v",
			p3)
	}

	addop(commit3, "M 100644 :9 rat")
	commit3.canonicalize()
	p4 := commit3.paths(nil)
	if len(p4) != 3 || p4[0] != "cat" || p4[1] != "rat" {
		t.Errorf("unexpected content at :3 after 2nd canonicalization: %v",
			p4)

	}

	commit3.setBranch("refs/heads/master")
	assertEqual(t, commit3.head(), "refs/heads/master")

	assertBool(t, commit1.references(":6"), false)
	assertBool(t, commit3.references(":6"), true)

	saw := commit3.String()
	expected := "commit refs/heads/master\nmark :3\nauthor esr <esr@thyrsus.com> 1457998447 +0000\ncommitter J. Random Hacker <jrh@foobar.com> 1456976447 -0500\ndata 38\nThird example commit for unit testing\nfrom :2\nM 100644 :8 cat\nM 100644 :9 rat\nM 100644 :6 vat\n\n"
	assertEqual(t, saw, expected)
}

func TestAlldeletes(t *testing.T) {
	repo := newRepository("fubar")
	defer repo.cleanup()
	commit1 := newCommit(repo)
	repo.addEvent(commit1)
	committer1 := "J. Random Hacker <jrh@foobar.com> 1456976347 -0500"
	attrib, _ := newAttribution(committer1)
	commit1.committer = *attrib
	author1, _ := newAttribution("esr <esr@thyrsus.com> 1457998347 +0000")
	commit1.authors = append(commit1.authors, *author1)
	commit1.Comment = "Example commit for unit testing\n"
	commit1.setMark(":1")

	// Set up some fileops so we can test things like manifests
	addop := func(commit *Commit, line string) {
		commit.appendOperation(newFileOp(repo).parse(line))
	}

	addop(commit1, "deleteall")
	assertBool(t, commit1.alldeletes(), true)
	addop(commit1, "D README")
	assertBool(t, commit1.alldeletes(), true)
	addop(commit1, "M 100644 :2 COPYING")
	assertBool(t, commit1.alldeletes(), false)
}

func TestBranchbase(t *testing.T) {
	assertEqual(t, branchbase("refs/heads/gronk"), "gronk")
	assertEqual(t, branchbase("refs/heads/grink"), "grink")
	assertEqual(t, branchbase("refs/random"), "random")
}

func TestCapture(t *testing.T) {
	data, err0 := captureFromProcess("echo stdout; echo 1>&2 stderr")
	if err0 != nil {
		t.Fatalf("error while spawning process: %v", err0)
	}
	assertEqual(t, data, "stdout\nstderr\n")

	r, cmd, err1 := readFromProcess("echo arglebargle")
	if err1 != nil {
		t.Fatalf("error while spawning process: %v", err1)
	}
	b := bufio.NewReader(r)
	ln, err2 := b.ReadString(byte('\n'))
	assertEqual(t, ln, "arglebargle\n")
	if err2 != nil {
		t.Fatalf("error while reading from process: %v", err2)
	}
	_, errend := b.ReadString(byte('\n'))
	if errend != io.EOF {
		t.Fatalf("EOF not seen when expected: %v", errend)
	}
	cmd.Wait()

}

func TestSVNParse(t *testing.T) {
	saw := sdBody([]byte("Content-Length: 23\n"))
	expected := "23"
	assertEqual(t, string(saw), string(expected))

	rawmsg := `K 7
svn:log
V 79
A vanilla repository - standard layout, linear history, no tags, no branches. 

K 10
svn:author
V 3
esr
K 8
svn:date
V 27
2011-11-30T16:41:55.154754Z
PROPS-END
`
	sp := newStreamParser(nil)
	sp.fp = bufio.NewReader(strings.NewReader(rawmsg))
	om := sp.sdReadProps("test", len(rawmsg))
	expected = "{'svn:log': 'A vanilla repository - standard layout, linear history, no tags, no branches. \n', 'svn:author': 'esr', 'svn:date': '2011-11-30T16:41:55.154754Z'}"
	saw2 := om.String()
	assertEqual(t, saw2, string(expected))
}

func TestFastImportParse1(t *testing.T) {
	rawdump := `blob
mark :1
data 20
1234567890123456789

commit refs/heads/master
mark :2
committer Ralf Schlatterbeck <rsc@runtux.com> 0 +0000
data 14
First commit.
M 100644 :1 README

blob
mark :3
data 20
0123456789012345678

commit refs/heads/master
mark :4
committer Ralf Schlatterbeck <rsc@runtux.com> 10 +0000
data 262
From https://unicodebook.readthedocs.io/encodings.html

When a byte string is decoded, the decoder may fail to decode a
specific byte sequence. For example, 'bacx' (0x61 0x62 0x63 0xE9) is not
decodable from ASCII nor UTF-8, but it is decodable from ISO 8859-1.
from :2
M 100644 :3 README

`
	repo := newRepository("test")
	defer repo.cleanup()
	sp := newStreamParser(repo)
	r := strings.NewReader(rawdump)
	sp.fastImport(context.TODO(), r, nullStringSet, "synthetic test load")

	assertBool(t, len(repo.events) == 4, true)
	assertBool(t, repo.events[3].getMark() == ":4", true)
	assertEqual(t, string(repo.markToEvent(":3").(*Blob).getContent()), "0123456789012345678\n")
	assertEqual(t, repo.markToEvent(":2").(*Commit).Comment, "First commit.\n")
	commit2 := repo.events[3].(*Commit)
	assertEqual(t, commit2.String(), rawdump[len(rawdump)-len(commit2.String()):])
	d, _ := commit2.blobByName("README")
	assertEqual(t, string(d), "0123456789012345678\n")
	assertIntEqual(t, repo.size(), len(rawdump))
	saw2 := repo.branchset()
	exp2 := []string{"refs/heads/master"}
	if !stringSliceEqual(saw2, exp2) {
		t.Errorf("saw branchset %v, expected %v", saw2, exp2)
	}
	saw3 := repo.branchmap()
	exp3 := map[string]string{"refs/heads/master": ":4"}
	if !reflect.DeepEqual(saw3, exp3) {
		t.Errorf("saw branchmap %v, expected %v", saw3, exp3)
	}

	// Hack in illegal UTF-8 sequence - can't do this in Go source text,
	// the compiler doesn't like it.
	// XXX(mem): what's undecodable?
	// assertBool(t, commit2.undecodable("ASCII"), false)
	// assertIntEqual(t, int(commit2.Comment[161]), 120)
	// commit2.Comment = strings.Replace(commit2.Comment, "bacx", "bac\xe9", 1)
	// assertIntEqual(t, int(commit2.Comment[161]), 0xe9)
	// assertBool(t, commit2.undecodable("ASCII"), true)
	// assertBool(t, commit2.undecodable("ISO-8859-1"), false)
	// assertBool(t, commit2.undecodable("UTF-8"), false)
}

func TestReadAuthorMap(t *testing.T) {
	input := `
# comment
foo=foobar <smorp@zoop> EST
COW= boofar <proms@pooz> -0500

woc = wocwoc <woc@cow>
+ bozo <b@clown.com> +0100
`
	people := []struct{ local, fullname, email, tz string }{
		{"foo", "foobar", "smorp@zoop", "-0500"},
		{"cow", "boofar", "proms@pooz", "-0500"},
		{"woc", "wocwoc", "woc@cow", ""},
	}
	aliases := []struct{ aliasFullname, aliasEmail, fullname, email, tz string }{
		{"bozo", "b@clown.com", "wocwoc", "woc@cow", "+0100"},
	}

	repo := newRepository("test")
	defer repo.cleanup()

	err := repo.readAuthorMap(newOrderedIntSet(), strings.NewReader(input))
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}

	if len(repo.authormap) != len(people) {
		t.Fatalf("expected %d people but got %d",
			len(people), len(repo.authormap))
	}
	for _, x := range people {
		if a, ok := repo.authormap[x.local]; !ok {
			t.Errorf("authormap[%s] lookup failed", x.local)
			continue
		} else {
			if a.fullname != x.fullname || a.email != x.email {
				t.Errorf("authormap[%s] entry contents unexpected: %v", x.local, a)
				continue
			}
		}
	}

	if len(repo.aliases) != len(aliases) {
		t.Errorf("expected %d aliases but got %d",
			len(aliases), len(repo.aliases))
	}
	for _, x := range aliases {
		k := ContributorID{x.aliasFullname, x.aliasEmail}
		if a, ok := repo.aliases[k]; !ok {
			t.Errorf("aliases[%v] lookup failed", k)
			continue
		} else if a.fullname != x.fullname {
			t.Errorf("alias[%v] entry contents unexpected: %v", x, a)
		}
	}
}

// Sample small repository used for multiple tests
const rawdump = `blob
mark :1
data 23
This is a sample file.

reset refs/heads/master
commit refs/heads/master
mark :2
committer esr <esr> 1322671432 +0000
data 16
First revision.
M 100644 :1 README

blob
mark :3
data 68
This is a sample file.

This is our first line of modified content.

commit refs/heads/master
mark :4
committer esr <esr> 1322671521 +0000
data 17
Second revision.
from :2
M 100644 :3 README

blob
mark :5
data 114
This is a sample file.

This is our first line of modified content.

This is our second line of modified content.

commit refs/heads/master
mark :6
committer esr <esr> 1322671565 +0000
data 16
Third revision.
from :4
M 100644 :5 README

tag root
from :2
tagger esr <esr> 1322671315 +0000
data 122
A vanilla repository - standard layout, linear history, no tags, no branches. 

[[Tag from root commit at Subversion r1]]

tag emptycommit-5
from :6
tagger esr <esr> 1323084440 +0000
data 151
Adding a property setting.

[[Tag from zero-fileop commit at Subversion r5:
<NodeAction: r5 change file 'trunk/README' properties=[('foo', 'bar')]>
]]

tag no-comment
from :4
tagger esr <esr> 1322671316 +0000
data 0

tag with-comment
from :6
tagger esr <esr> 1322671317 +0000
data 19
this is a test tag

`

func TestFastImportParse2(t *testing.T) {
	repo := newRepository("test")
	defer repo.cleanup()
	sp := newStreamParser(repo)
	r := strings.NewReader(rawdump)
	sp.fastImport(context.TODO(), r, nullStringSet, "synthetic test load")

	testTag1, ok1 := repo.events[len(repo.events)-1].(*Tag)
	assertBool(t, ok1, true)
	assertEqual(t, "refs/tags/with-comment", testTag1.name)

	testTag2, ok2 := repo.events[len(repo.events)-2].(*Tag)
	assertBool(t, ok2, true)
	assertEqual(t, "refs/tags/no-comment", testTag2.name)

	testReset, ok2 := repo.events[1].(*Reset)
	assertBool(t, ok2, true)
	assertEqual(t, "refs/heads/master", testReset.ref)

	// Check roundtripping via fastExport
	var a strings.Builder
	if err := repo.fastExport(repo.all(), &a, nullStringSet, nil); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	assertEqual(t, rawdump, a.String())

	onecommit := `blob
mark :3
data 68
This is a sample file.

This is our first line of modified content.

reset refs/heads/master
from refs/heads/master^0

commit refs/heads/master
mark :4
committer esr <esr> 1322671521 +0000
data 17
Second revision.
M 100644 :3 README

tag no-comment
from :4
tagger esr <esr> 1322671316 +0000
data 0

`
	a.Reset()
	// Check partial export - Event 4 is the second commit
	if err := repo.fastExport(newOrderedIntSet(4), &a, nullStringSet, nil); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	assertEqual(t, onecommit, a.String())

	repo.checkUniqueness(false, nil)
	assertEqual(t, repo.uniqueness, "committer_date")

	// Check for no false positives on front events */
	assertIntEqual(t, len(repo.frontEvents()), 0)

	authordump := "esr = Eric S. Raymond <esr@thyrsus.com>"
	err := repo.readAuthorMap(newOrderedIntSet(), strings.NewReader(authordump))
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	commit1 := repo.events[2].(*Commit)
	assertEqual(t, commit1.committer.fullname, "esr")
	commit1.committer.remap(repo.authormap)
	assertEqual(t, commit1.committer.fullname, "Eric S. Raymond")

	var b strings.Builder
	mapped := orderedIntSet{repo.eventToIndex(commit1)}
	if err = repo.writeAuthorMap(mapped, &b); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	expect := "esr = Eric S. Raymond <esr@thyrsus.com>\n"
	assertEqual(t, expect, b.String())
	if err = repo.writeAuthorMap(repo.all(), &b); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	expect = "esr = Eric S. Raymond <esr@thyrsus.com>\nesr = esr <esr>\n"
	assertEqual(t, expect, b.String())

	// Test appending a done marker
	assertIntEqual(t, len(repo.events), 11)
	repo.addEvent(newPassthrough(repo, "done"))
	assertIntEqual(t, len(repo.events), 12)

	// Test appending passthrough to make sure it's inserted before "done"
	repo.addEvent(newPassthrough(repo, "boogabooga"))
	assertIntEqual(t, len(repo.events), 13)
	isPassthrough := func(event Event, payload string) bool {
		passthrough, ok := event.(*Passthrough)
		return ok && passthrough.text == payload
	}
	assertBool(t, isPassthrough(repo.events[12], "done"), true)
	assertBool(t, isPassthrough(repo.events[11], "boogabooga"), true)

	assertEqual(t, repo.earliestCommit().Comment, "First revision.\n")
	allcommits := repo.commits(nil)
	lastcommit := repo.eventToIndex(allcommits[len(allcommits)-1])
	ancestors := repo.ancestors(lastcommit)
	assertBool(t, ancestors.Equal(orderedIntSet{4, 2}), true)
}

func TestDelete(t *testing.T) {
	repo := newRepository("test")
	defer repo.cleanup()
	sp := newStreamParser(repo)
	r := strings.NewReader(rawdump)
	sp.fastImport(context.TODO(), r, nullStringSet, "synthetic test load")

	thirdcommit := repo.markToIndex(":6")
	repo.delete(orderedIntSet{thirdcommit}, nil)
	var a strings.Builder
	if err := repo.fastExport(repo.all(), &a, nullStringSet, nil); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}

	dtrimmed := `blob
mark :1
data 23
This is a sample file.

reset refs/heads/master
commit refs/heads/master
mark :2
committer esr <esr> 1322671432 +0000
data 16
First revision.
M 100644 :1 README

blob
mark :3
data 68
This is a sample file.

This is our first line of modified content.

commit refs/heads/master
mark :4
committer esr <esr> 1322671521 +0000
data 17
Second revision.
from :2
M 100644 :3 README

tag root
from :2
tagger esr <esr> 1322671315 +0000
data 122
A vanilla repository - standard layout, linear history, no tags, no branches. 

[[Tag from root commit at Subversion r1]]

tag no-comment
from :4
tagger esr <esr> 1322671316 +0000
data 0

`
	assertEqual(t, a.String(), dtrimmed)
}

func TestResort(t *testing.T) {
	repo := newRepository("test")
	defer repo.cleanup()
	sp := newStreamParser(repo)
	r := strings.NewReader(rawdump)
	sp.fastImport(context.TODO(), r, nullStringSet, "synthetic test load")

	// Reverse the event array, trick from SliceTricks
	for i := len(repo.events)/2 - 1; i >= 0; i-- {
		opp := len(repo.events) - 1 - i
		repo.events[i], repo.events[opp] = repo.events[opp], repo.events[i]
	}

	// This should reorder it.
	//repo.resort()

	var a strings.Builder
	if err := repo.fastExport(repo.all(), &a, nullStringSet, nil); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	//assertEqual(t, "", a.String())
}

func TestRenumber(t *testing.T) {
	// doubled is a version of rawdump with all blob numbers doubled
	doubled := `blob
mark :2
data 23
This is a sample file.

reset refs/heads/master
commit refs/heads/master
mark :4
committer esr <esr> 1322671432 +0000
data 16
First revision.
M 100644 :2 README

blob
mark :6
data 68
This is a sample file.

This is our first line of modified content.

commit refs/heads/master
mark :8
committer esr <esr> 1322671521 +0000
data 17
Second revision.
from :4
M 100644 :6 README

blob
mark :10
data 114
This is a sample file.

This is our first line of modified content.

This is our second line of modified content.

commit refs/heads/master
mark :12
committer esr <esr> 1322671565 +0000
data 16
Third revision.
from :8
M 100644 :10 README

tag root
from :4
tagger esr <esr> 1322671315 +0000
data 122
A vanilla repository - standard layout, linear history, no tags, no branches. 

[[Tag from root commit at Subversion r1]]

tag emptycommit-5
from :12
tagger esr <esr> 1323084440 +0000
data 151
Adding a property setting.

[[Tag from zero-fileop commit at Subversion r5:
<NodeAction: r5 change file 'trunk/README' properties=[('foo', 'bar')]>
]]

tag no-comment
from :8
tagger esr <esr> 1322671316 +0000
data 0

tag with-comment
from :12
tagger esr <esr> 1322671317 +0000
data 19
this is a test tag

`
	repo := newRepository("test")
	defer repo.cleanup()
	sp := newStreamParser(repo)
	r := strings.NewReader(doubled)
	sp.fastImport(context.TODO(), r, nullStringSet, "synthetic test load")

	//verbose = debugUNITE
	repo.renumber(1, nil)

	var a strings.Builder
	if err := repo.fastExport(repo.all(), &a, nullStringSet, nil); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}

	assertEqual(t, a.String(), rawdump)
}

func TestGetSetAttr(t *testing.T) {
	// Test data swiped from TestReferences
	type vcsTestEntry struct {
		Vcs      string
		Expected bool
		Comment  string
	}
	var vcsTestTable = []vcsTestEntry{
		{"git", false, "abracadabra"},
		{"git", true, "commit 56ab29."},
		{"svn", true, " r2336 "},
		{"svn", false, " 3.14159 "},
		{"cvs", true, " 1.15 "},
		{"cvs", false, " 42 "},
	}
	extractor := func(v vcsTestEntry, s string) string {
		val, ok := getAttr(v, s)
		if !ok {
			t.Fatalf("value has no field %s", s)
		}
		return val
	}
	pextractor := func(v *vcsTestEntry, s string) string {
		val, ok := getAttr(v, s)
		if !ok {
			t.Fatalf("value has no field %s", s)
		}
		return val
	}
	assertEqual(t, vcsTestTable[0].Vcs, extractor(vcsTestTable[0], "Vcs"))
	assertEqual(t, vcsTestTable[4].Comment, extractor(vcsTestTable[4], "Comment"))
	assertEqual(t, vcsTestTable[0].Vcs, pextractor(&vcsTestTable[0], "Vcs"))
	assertEqual(t, vcsTestTable[4].Comment, pextractor(&vcsTestTable[4], "Comment"))
	err := setAttr(&vcsTestTable[0], "Vcs", "foozle")
	if err != nil {
		t.Fatalf("during setattr test: %v", err)
	}
	assertEqual(t, vcsTestTable[0].Vcs, "foozle")
}

func TestPathMap(t *testing.T) {
	p := newPathMap()
	assertTrue(t, p.isEmpty())
	p.set("foo/bar", 42)
	value, contains := p.get("foo/bar")
	assertTrue(t, contains)
	assertIntEqual(t, value.(int), 42)
	// Deleting a directory should delete subcomponents, too
	p.remove("foo/bar")
	_, contains = p.get("foo/bar")
	assertTrue(t, !contains)
	assertEqual(t, p.String(), "{}")
	p.set("baz/qux", 23)
	_, contains = p.get("baz/qux")
	assertTrue(t, contains)
	p.remove("baz")
	assertEqual(t, p.String(), "{}")
	_, contains = p.get("baz/qux")
	assertTrue(t, !contains)
	p.set("gronk/baz/qux", 23)
	_, contains = p.get("gronk/baz/qux")
	assertTrue(t, contains)
	p.remove("gronk")
	_, contains = p.get("gronk/baz/qux")
	assertTrue(t, !contains)
	assertEqual(t, p.String(), "{}")
	// Test copyFrom
	p.set("foo/bar", 42)
	p.copyFrom("baz/qux", p, "foo")
	_, contains = p.get("baz/qux/bar")
	assertTrue(t, contains)
	p.set("gronk", 0)
	p.copyFrom("bat", p, "")
	_, contains = p.get("bat/baz/qux/bar")
	assertTrue(t, contains)
	_, contains = p.get("bat/gronk")
	assertTrue(t, contains)
	p.copyFrom("", p, "foo")
	_, contains = p.get("bat/gronk")
	p.copyFrom("", p, "")
	assertTrue(t, !contains)
	_, contains = p.get("bat/baz/qux/bar")
	assertTrue(t, !contains)
	_, contains = p.get("bar")
	assertTrue(t, contains)
	p.remove("bar")
	assertEqual(t, p.String(), "{}")
}

func TestDeclaredBranch(t *testing.T) {
	type testcase struct {
		path             string
		isDeclaredBranch bool
	}
	var branchsets = []orderedStringSet{
		orderedStringSet{"trunk", "tags/*", "branches/*"},
		orderedStringSet{"trunk", "tags/*", "branches/*", "*"},
		orderedStringSet{"trunk", "tags/*/*", "branches/*"},
	}
	var testcases = [][]testcase{
		{
			{"trunk", true},
			{"foobar", false},
			{"branches/foobar", true},
			{"branches/foobar/test", false},
			{"tags/foobar", true},
			{"tags/foobar/cetc", false},
			{"tag/foobar", false},
			{"tags", false},
			{"branches", false},
			{"/", false},
			{"", false},
		},
		{
			{"trunk", true},
			{"foobar", true},
			{"branches/foobar", true},
			{"branches/foobar/test", false},
			{"tags/foobar", true},
			{"tags/foobar/cetc", false},
			{"tag/foobar", false},
			{"tags", false},
			{"branches", false},
			{"/", false},
			{"", false},
		},
		{
			{"trunk", true},
			{"foobar", false},
			{"branches/foobar", true},
			{"branches/foobar/test", false},
			{"tags/foobar", false},
			{"tags/foobar/cetc", true},
			{"tag/foobar", false},
			{"tags", false},
			{"branches", false},
			{"/", false},
			{"", false},
		},
	}
	control.listOptions = make(map[string]orderedStringSet)
	for idx, branchset := range branchsets {
		branchset := branchset
		t.Run(fmt.Sprint(idx), func(t *testing.T) {
			for idx, test := range testcases[idx] {
				test := test
				t.Run(fmt.Sprint(idx), func(t *testing.T) {
					control.listOptions["svn_branchify"] = branchset
					sp := new(StreamParser)
					sp.initBranchify()
					assertBool(t, sp.isDeclaredBranch(test.path), test.isDeclaredBranch)
				})
			}
		})
	}
}

func TestBranchSplit(t *testing.T) {
	control.listOptions = make(map[string]orderedStringSet)
	control.listOptions["svn_branchify"] = orderedStringSet{"trunk", "tags/*", "branches/*", "*"}
	sp := new(StreamParser)
	sp.initBranchify()
	type splitTestEntry struct {
		raw    string
		branch string
		path   string
	}
	var splitTestTable = []splitTestEntry{
		{"trunk/README", "trunk", "README"},
		{"foobar/README", "foobar", "README"},
		{"trunk/", "trunk", ""},
		{"trunk", "", "trunk"},
		{"README", "", "README"},
		{"branches/foo/bar", "branches/foo", "bar"},
		{"branches/foo/bar/baz", "branches/foo", "bar/baz"},
	}
	for _, tst := range splitTestTable {
		b, p := sp.splitSVNBranchPath(tst.raw)
		assertEqual(t, b, tst.branch)
		assertEqual(t, p, tst.path)
	}
}

func TestContainingDir(t *testing.T) {
	type testcase struct {
		path string
		dir  string
	}
	var testcases = []testcase{
		{"/foo/bar/baz.js", "/foo/bar"},
		{"/foo/bar/baz", "/foo/bar"},
		{"/foo/bar/baz/", "/foo/bar/baz"},
		{"dev.txt", ""},
		{"/", ""},
		{"", ""},
	}
	for idx, test := range testcases {
		test := test
		t.Run(fmt.Sprint(idx), func(t *testing.T) {
			t.Parallel()
			assertEqual(t, containingDir(test.path), test.dir)
		})
	}
}

func TestChangelogParse(t *testing.T) {
	type testcase struct {
		line  string
		pre   string
		email string
	}
	var testcases = []testcase{
		{"2020-01-02 Eric S. Raymond <esr@thyrsus.com>", "2020-01-02 Eric S. Raymond", "<esr@thyrsus.com>"},
		{"2001-04-29  Toomas Rosin <toomas@ns dot tklabor dot ee>", "2001-04-29  Toomas Rosin", "<toomas@ns.tklabor.ee>"},
		{"2001-04-29 Ian Bolton\t<ian.bolton@arm.com>", "2001-04-29 Ian Bolton", "<ian.bolton@arm.com>"},
		{"2004-04-16  Kazuhiro Inaoka <inaoka dot kazuhiro at renesas dot com>", "2004-04-16  Kazuhiro Inaoka", "<inaoka.kazuhiro@renesas.com>"},
		{"Torsten Hilbrich <torsten <dot> hilbrich <at> gmx.net>", "Torsten Hilbrich", "<torsten.hilbrich@gmx.net>"},
	}
	for idx, test := range testcases {
		test := test
		t.Run(fmt.Sprint(idx), func(t *testing.T) {
			t.Parallel()
			ok, pre, email, _ := canonicalizeInlineAddress(test.line)
			assertTrue(t, ok)
			assertEqual(t, test.pre, strings.TrimSpace(pre))
			assertEqual(t, test.email, email)
		})
	}
}

func TestWalkManifests(t *testing.T) {
	rs := newReposurgeon()
	rs.DoRead("<../test/implicit.fi")
	maxnum := 0
	rs.chosen().walkManifests(func(i int, _ *Commit, _ int, _ *Commit) {
		num := 0
		for _, e := range rs.chosen().events {
			if c, ok := e.(*Commit); ok {
				if c._manifest != nil {
					num++
				}
			}
		}
		if maxnum < num {
			maxnum = num
		}
	})
	assertTrue(t, maxnum == 6)
	num := 0
	for _, e := range rs.chosen().events {
		if c, ok := e.(*Commit); ok {
			if c._manifest != nil {
				num++
			}
		}
	}
	assertTrue(t, num == 0)
}
