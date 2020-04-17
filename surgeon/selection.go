package main

// The event selector. Exports one class, which is used
// to compile and evaluate selection expressions.
//
// SPDX-License-Identifier: BSD-2-Clause

import (
	"fmt"
	"io"
	"math"
	"reflect"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"
)

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
			if matches > 0 && (!all || matches == len(paths)) {
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
			} else if fileop.op == opC && match(fileop.Path) {
				tree.set(fileop.Path, true)
			} else if fileop.op == opR && match(fileop.Path) {
				tree.set(fileop.Path, true)
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
	if op == nil {
		panic(throw("command", "inner expression to be negated is invalid"))
	}
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

// end
