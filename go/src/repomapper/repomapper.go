/* repomapper - update and manipulate contributor maps */
package main

// SPDX-License-Identifier: BSD-2-Clause

import (
	"bufio"
	"flag"
	"fmt"
	"log"
	"os"
	"regexp"
	"strings"
	"sort"
)

/* Associate a username with a DVCS-style ID. */
type Contributor struct {
        name string
        fullname string
        email string
        tz string
}

/* Does this entry need completion? */
func (cb *Contributor) incomplete() bool {
        return cb.name == cb.fullname || strings.Index(cb.email, "@") == -1
}

func (cb *Contributor) Stringer() string {
        out := fmt.Sprintf("%s = %s <%s>", cb.name, cb.fullname, cb.email)
	if cb.tz != "" {
		out += " " + cb.tz
	}
        out += "\n"
	return out
}

/* A map of contributors. */
type ContribMap map[string]Contributor

/* apply a soecified function to each line of a file */
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
		v.name = string(firstmatch[1])
		v.fullname = string(firstmatch[2])
		v.email = string(firstmatch[3])
		v.tz = string(firstmatch[4])
		cm[string(v.name)] = v 
	}
	bylines(fn, digest)
	return cm
}

/* Add an address suffix to entries lacking one.*/
func (cm *ContribMap) Suffix(addr string) {
        for _, obj := range *cm {
		if strings.Index(obj.email, "@") == -1 {
			obj.email += "@" + addr
		}
	}
}

/* Write the current state of this contrib map. */
func (cm *ContribMap) Write(fp *os.File, incomplete bool) {
        keys := make([]string, 0)
	for k, _ := range *cm {
		keys = append(keys, k)
	}
	sort.Strings(keys)	
        for _, name := range keys {
		if incomplete && !cm[name].incomplete() {
			continue
		}
		fmt.Print(cm[name].Stringer())
	}
}

// Manifest constants describning the Unix password DSV format
const FLDSEP   =	":"	// field separator
const NAME     =	0	// field index of username
const GECOS    =	4	// field index of fullname
const FLDCOUNT =	7	// required number of fields

func main() {
	var host string
	var passwdfile string
	var updatefile string
	var incomplete bool

	flag.StringVar(&host,       "h", "", "set host for suffixing")
	flag.StringVar(&passwdfile, "p", "", "specify password file")
	flag.StringVar(&updatefile, "u", "", "specify update file")
	flag.BoolVar(&incomplete,   "i", false, "dump incomplete entries")
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
			fields := strings.Split(line, FLDSEP)
			if len(fields) != FLDCOUNT {
				fmt.Fprintf(os.Stderr,
					"repomapper: ill-formed passwd line\n")
				os.Exit(1)
			}		
			name := fields[NAME]
			gecos := fields[GECOS]
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
				contribmap[name].fullname = passwd[name]
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

