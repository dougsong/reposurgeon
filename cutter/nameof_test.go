package main

import (
	"fmt"
	"os"
	"testing"
)

func assertEqual(t *testing.T, a string, b string) {
	t.Helper()
	if a != b {
		t.Fatalf("assertEqual: expected %q == %q", a, b)
	}
}

func TestNameSequenceLength(t *testing.T) {
	// first cut down the sequence so that it will have a much smaller ring
	seq := NewNameSequence()
	seq.color = seq.color[0:3]
	seq.item = seq.item[0:3]
	// then test that the name sequence loops after 3*3=9 names, and gains a suffix when it starts looping
	input := []string{"a", "b", "c", "d", "e", "f", "g", "h", "i", "j"}
	expected := []string{
		"AmberAngel", "AmethystAxe", "ArgentAngel",
		"AmberBear", "AmethystAngel", "ArgentBear",
		"AmberAxe", "AmethystBear", "ArgentAxe",
		"AmberAngel1"}
	names := make([]string, 0, 10)
	for _, s := range input {
		names = append(names, seq.obscureString(s))
	}
	fmt.Fprintf(os.Stderr, "names = %#v\n", names)
	for i := range expected {
		assertEqual(t, names[i], expected[i])
	}
}
