// Package repomapper - update and manipulate contributor maps
package main

// SPDX-License-Identifier: BSD-2-Clause

import (
	"bufio"
	"flag"
	"fmt"
	"log"
	"os"
	"regexp"
	"sort"
	"strings"
)

// Contributor - ssociate a username with a DVCS-style ID
type Contributor struct {
	name     string
	fullname string
	email    string
	tz       string
}

// Does this entry need completion?
func (cb *Contributor) incomplete() bool {
	return cb.name == cb.fullname || !strings.Contains(cb.email, "@")
}

// Stringer - render a Contributor in rereadable form
func (cb *Contributor) Stringer() string {
	out := fmt.Sprintf("%s = %s <%s>", cb.name, cb.fullname, cb.email)
	if cb.tz != "" {
		out += " " + cb.tz
	}
	out += "\n"
	return out
}

// ContribMap - a map of contributors.
type ContribMap map[string]Contributor

/* apply a specified function to each line of a file */
func bylines(fn string, hook func(string)) {
	file, err := os.Open(fn)
	if err != nil {
		log.Fatal(err)
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		hook(scanner.Text())
	}

	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

// NewContribMap - initialize a new contributor map from a file */
func NewContribMap(fn string) ContribMap {
	re := regexp.MustCompile("([^ ]+) *= ([^<]+)*<([^<]+)> *(.*)")
	cm := make(map[string]Contributor)

	digest := func(line string) {
		groups := re.FindAllStringSubmatch(line, -1)
		if groups == nil {
			log.Fatal("repomapper: ill-formed map line.\n")
		}
		v := *new(Contributor)
		firstmatch := groups[0]
		v.name = firstmatch[1]
		v.fullname = strings.Trim(firstmatch[2], " \t")
		v.email = firstmatch[3]
		v.tz = firstmatch[4]
		cm[v.name] = v
	}
	bylines(fn, digest)
	return cm
}

// Suffix - add an address suffix to entries lacking one.
func (cm *ContribMap) Suffix(addr string) {
	for k, obj := range *cm {
		if !strings.Contains(obj.email, "@") {
			obj.email += "@" + addr
			(*cm)[k] = obj
		}
	}
}

/* Write the current state of this contrib map. */
func (cm *ContribMap) Write(fp *os.File, incomplete bool) {
	keys := make([]string, 0)
	for k := range *cm {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, name := range keys {
		item := (*cm)[name]
		if incomplete && !item.incomplete() {
			continue
		}
		fmt.Print(item.Stringer())
	}
}

// Manifest constants describning the Unix password DSV format
const pwdFLDSEP = ":" // field separator
const pwdNAME = 0     // field index of username
const pwdGECOS = 4    // field index of fullname
const pwdFLDCOUNT = 7 // required number of fields

func main() {
	var host string
	var passwdfile string
	var updatefile string
	var incomplete bool

	flag.StringVar(&host, "h", "", "set host for suffixing")
	flag.StringVar(&passwdfile, "p", "", "specify password file")
	flag.StringVar(&updatefile, "u", "", "specify update file")
	flag.BoolVar(&incomplete, "i", false, "dump incomplete entries")
	flag.Parse()

	if flag.NArg() == 0 {
		fmt.Fprintf(os.Stderr,
			"repomapper: requires a contrib-map file argument.\n")
		os.Exit(1)
	}

	// Read in an ordered dictionary of existing attributions.
	contribmap := NewContribMap(flag.Arg(0))

	// Apply the -h option
	if host != "" {
		contribmap.Suffix(host)
	}

	// With -p, read the password data
	if passwdfile != "" {
		passwd := make(map[string]string)
		eatline := func(line string) {
			fields := strings.Split(line, pwdFLDSEP)
			if len(fields) != pwdFLDCOUNT {
				fmt.Fprintf(os.Stderr,
					"repomapper: ill-formed passwd line\n")
				os.Exit(1)
			}
			name := fields[pwdNAME]
			gecos := fields[pwdGECOS]
			if strings.Index(gecos, ",") != 1 {
				gecos = strings.Split(gecos, ",")[0]
			}
			passwd[name] = gecos
		}
		bylines(passwdfile, eatline)

		// Attempt to fill in the contribmap
		for name, obj := range contribmap {
			_, ok := passwd[name]
			if !ok {
				fmt.Fprintf(os.Stderr,
					"repomapper: %s not in password file.\n", name)
			} else if obj.fullname == name {
				item := contribmap[name]
				item.fullname = passwd[name]
				contribmap[name] = item
			} else {
				fmt.Fprintf(os.Stderr,
					"repomapper: %s -> %s should be %s.\n",
					name, obj.fullname, passwd[name])
			}
		}

		// Now dump the result
		contribmap.Write(os.Stdout, false)
		os.Exit(0)
	}

	// With -u, copy in all complete entries in the update file
	if updatefile != "" {
		updatemap := NewContribMap(updatefile)
		for name, obj := range updatemap {
			_, ok := contribmap[name]
			if !ok {
				contribmap[name] = obj
			}
		}
		// Now dump the result
		contribmap.Write(os.Stdout, false)
		os.Exit(0)
	}

	// By default, report on incomplete entries
	contribmap.Write(os.Stdout, incomplete)
}

// end
