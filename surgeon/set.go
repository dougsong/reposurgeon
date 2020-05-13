/*
 * set is a simple string-set class.
 *
// Copyright by Eric S. Raymond
 * SPDX-License-Identifier: BSD-2-Clause
*/

package main

import (
	"fmt"
	"sort"
	"strings"
)

type stringSet struct {
	store map[string]bool
}

var nullStringSet stringSet
var nullOrderedStringSet orderedStringSet

func setInit() {
	nullStringSet = newStringSet()
	nullOrderedStringSet = newOrderedStringSet()
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

// This representation optimizes for small memory footprint at the expense
// of speed.  To make the opposite trade we would do the obvious thing with
// map[string] bool.
type orderedStringSet []string

func newOrderedStringSet(elements ...string) orderedStringSet {
	set := make([]string, 0)
	for _, el := range elements {
		found := false
		for _, already := range set {
			if already == el {
				found = true
			}
		}
		if !found {
			set = append(set, el)
		}
	}
	return set
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
	var rep strings.Builder
	rep.WriteByte('[')
	lastIdx := len(s) - 1
	for idx, el := range s {
		fmt.Fprintf(&rep, "\"%s\"", el)
		if idx != lastIdx {
			rep.WriteString(", ")
		}
	}
	rep.WriteByte(']')
	return rep.String()
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

func (s stringSet) Ordered() orderedStringSet {
	oset := newOrderedStringSet()
	for item := range s.store {
		oset.Add(item)
	}
	return oset
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
	return s.toOrderedStringSet().String()
}

// end
