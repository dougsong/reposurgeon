/*
 * Baton machinery
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

package main

import (
	"bytes"
	"fmt"
	"io"
	"math"
	"os"
	"strings"
	"sync"
	"time"
)

// Baton is the overall state of the output
type Baton struct {
	progressEnabled bool
	stream          *os.File
	channel         chan Message
	start           time.Time
	twirly          Twirly
	counter         Counter
	progress        Progress
	process         Process
}

// Twirly is the state of a twirly indefinite progess meter that ships indications to stdout.
type Twirly struct {
	sync.RWMutex
	lastupdate time.Time
	count      uint8
}

// Counter is usually used for "N of M" type progress, but the caller can supply any format string they want
type Counter struct {
	sync.RWMutex
	lastupdate time.Time
	format     string
	count      uint64
}

// Progress is the evolved form of the counter which shows the percentage of completion and the rate of progress in addition to the count
type Progress struct {
	sync.RWMutex
	start      time.Time
	lastupdate time.Time
	tag        []byte
	count      uint64
	lastcount  uint64
	expected   uint64
}

// Process prints a message before and after the other status messages
type Process struct {
	sync.RWMutex
	lastupdate time.Time
	startmsg   []byte
	endmsg     []byte
	start      time.Time
}

type msgType uint8

const (
	// NONE is the abscence of a message
	NONE msgType = iota
	// LOG represents a message that should be printed once, as if
	// to a logfile
	LOG
	// PROGRESS messages are printed to the status line,
	// overwriting whatever was already there
	PROGRESS
	// SYNC allows for synchronization between the goroutine and
	// the calling code; the goroutine replies but takes no other
	// action
	SYNC
)

type Message struct {
	ty  msgType
	str []byte
}

const twirlInterval = 100 * time.Millisecond // Rate-limit baton twirls
const progressInterval = 1 * time.Second     // Rate-limit progress messages

func newBaton(interactive bool) *Baton {
	me := new(Baton)
	me.start = time.Now()
	tiColZero := getTerminfoString("hpa", "0")
	tiClrEol := getTerminfoString("el")
	tiScrollForward := getTerminfoString("ind")
	me.channel = make(chan Message)
	me.progressEnabled = interactive
	go func() {
		lastProgress := &[]byte{}
		for {
			msg := <-me.channel
			if msg.ty == SYNC {
				me.channel <- msg
			} else if me.stream != nil {
				if msg.ty == LOG {
					if me.progressEnabled {
						me.stream.Write(tiColZero)
						me.stream.Write(tiClrEol)
						me.stream.Write(msg.str)
						if !bytes.HasSuffix(msg.str, tiScrollForward) {
							me.stream.Write(tiScrollForward)
						}
						me.stream.Write(tiColZero)
						me.stream.Write(*lastProgress)
					} else {
						if len(msg.str) != 0 {
							me.stream.Write(msg.str)
						}
						if !bytes.HasSuffix(msg.str, []byte{'\n'}) {
							me.stream.Write([]byte{'\n'})
						}
					}
				} else if msg.ty == PROGRESS {
					me.stream.Write(tiColZero)
					me.stream.Write(tiClrEol)
					me.stream.Write(msg.str)
					lastProgress = &msg.str
				}
			}
		}
	}()
	me.stream = os.Stdout

	return me
}

func (baton *Baton) setInteractivity(enabled bool) {
	if baton != nil {
		baton.channel <- Message{SYNC, nil}
		baton.progressEnabled = enabled
		<-baton.channel
	}
}

// log prints out a simple log message
func (baton *Baton) printLog(str []byte) {
	if baton != nil {
		if baton.progressEnabled {
			baton.channel <- Message{LOG, _copyb(str)}
		} else {
			baton.stream.Write(str)
		}
	}
}

func (baton *Baton) printLogString(str string) {
	if baton != nil {
		if baton.progressEnabled {
			baton.channel <- Message{LOG, _copystr(str)}
		} else {
			baton.stream.WriteString(str)
		}
	}
}

// progress prints out a progress message in the status line
func (baton *Baton) printProgress() {
	if baton != nil && baton.progressEnabled {
		var buf bytes.Buffer
		baton.render(&buf)
		baton.channel <- Message{PROGRESS, _copyb(buf.Bytes())}
	}
}

// twirl spins the baton
func (baton *Baton) twirl() {
	if baton != nil && baton.progressEnabled {
		baton.twirly.Lock()
		if time.Since(baton.twirly.lastupdate) > twirlInterval {
			baton.twirly.count = (baton.twirly.count + 1) % 4
			baton.twirly.lastupdate = time.Now()
			baton.twirly.Unlock()
			baton.printProgress()
		} else {
			baton.twirly.Unlock()
		}
	}
}

func (baton *Baton) startProcess(startmsg string, endmsg string) {
	if baton != nil && baton.progressEnabled {
		baton.progress.Lock()
		defer baton.progress.Unlock()
		baton.process.startmsg = []byte(startmsg)
		baton.process.endmsg = []byte(endmsg)
		baton.process.start = time.Now()
	}
}

func (baton *Baton) endProcess(endmsg ...string) {
	if baton != nil && baton.progressEnabled {
		baton.progress.Lock()
		defer baton.progress.Unlock()
		if endmsg != nil {
			baton.process.endmsg = []byte(strings.Join(endmsg, " "))
		}
		fmt.Fprintf(baton, "%s ...(%s) %s.",
			baton.process.startmsg,
			time.Since(baton.process.start).Round(time.Millisecond*10),
			baton.process.endmsg)
		baton.process.startmsg = nil
		baton.process.endmsg = nil
		baton.channel <- Message{PROGRESS, nil}
	}
}

func (baton *Baton) startcounter(countfmt string, initial uint64) {
	if baton != nil && baton.progressEnabled {
		baton.counter.Lock()
		defer baton.counter.Unlock()
		baton.counter.format = countfmt
		baton.counter.count = initial
	}
}

func (baton *Baton) bumpcounter() {
	if baton != nil && baton.progressEnabled {
		baton.counter.Lock()
		if baton.counter.format != "" {
			baton.counter.count++
			baton.counter.Unlock()
			baton.printProgress()
		} else {
			baton.counter.Unlock()
			baton.twirl()
		}
	}
}

func (baton *Baton) endcounter() {
	if baton != nil && baton.progressEnabled {
		baton.counter.render(baton)
		baton.counter.Lock()
		defer baton.counter.Unlock()
		baton.counter.format = ""
		baton.counter.count = 0
		baton.channel <- Message{PROGRESS, nil}
	}
}

func (baton *Baton) startProgress(tag string, expected uint64) {
	if baton != nil && baton.progressEnabled {
		baton.progress.Lock()
		defer baton.progress.Unlock()
		baton.progress.start = time.Now()
		baton.progress.lastupdate = baton.progress.start
		baton.progress.tag = []byte(tag)
		baton.progress.count = 0
		baton.progress.expected = expected
	}
}

func (baton *Baton) percentProgress(ccount uint64) {
	if baton != nil && baton.progressEnabled {
		baton.progress.Lock()
		if time.Since(baton.progress.lastupdate) > progressInterval || ccount == baton.progress.expected {
			baton.progress.lastcount = baton.progress.count
			baton.progress.count = ccount
			baton.progress.lastupdate = time.Now()
			baton.progress.Unlock()
			baton.printProgress()
		} else {
			baton.progress.Unlock()
		}
	}
}

func (baton *Baton) endProgress() {
	if baton != nil && baton.progressEnabled {
		baton.progress.Lock()
		baton.progress.count = baton.progress.expected
		baton.progress.lastupdate = time.Now()
		baton.progress.Unlock()
		baton.progress.render(baton)
		baton.progress.Lock()
		baton.progress.tag = nil
		baton.progress.count = 0
		baton.progress.expected = 0
		baton.channel <- Message{PROGRESS, nil}
		baton.progress.Unlock()
	}
}

func (baton *Baton) WriteString(s string) (n int, err error) {
	if baton != nil {
		baton.printLog([]byte(s))
	}
	return len(s), nil
}

func (baton *Baton) Write(b []byte) (n int, err error) {
	if baton != nil {
		baton.printLog(b)
	}
	return len(b), nil
}

func (baton *Baton) Close() error {
	return nil
}

func (baton *Baton) Sync() {
	if baton != nil {
		baton.channel <- Message{SYNC, nil}
		<-baton.channel
	}
}

func (baton *Baton) render(buf io.Writer) {
	baton.process.renderPre(buf)
	baton.counter.render(buf)
	baton.progress.render(buf)
	fmt.Fprintf(buf, " (%v)", time.Since(baton.start).Round(time.Second))
	baton.twirly.render(buf)
	baton.process.renderPost(buf)
}

func (baton *Twirly) render(b io.Writer) {
	baton.RLock()
	defer baton.RUnlock()
	character := "-\\|/"[baton.count]
	b.Write([]byte{32, character})
}

func (baton *Counter) render(b io.Writer) {
	baton.RLock()
	defer baton.RUnlock()
	if baton.format != "" {
		n, _ := fmt.Fprintf(b, baton.format, baton.count)
		if n > 0 {
			b.Write([]byte{' '})
		}
	}
}

func (baton *Progress) render(b io.Writer) {
	baton.RLock()
	defer baton.RUnlock()
	scale := func(n float64) string {
		if n < 1000 {
			return fmt.Sprintf("%.0f", n)
		} else if n < 1000000 {
			return fmt.Sprintf("%.2fK", n/1000)
		} else if n < 1000000000 {
			return fmt.Sprintf("%.2fM", n/1000000)
		} else if n < 1000000000000 {
			return fmt.Sprintf("%.2fG", n/1000000000)
		} else {
			return fmt.Sprintf("%.2fT", n/1000000000000)
		}
	}
	if baton.expected > 0 {
		frac := float64(baton.count) / float64(baton.expected)
		elapsed := baton.lastupdate.Sub(baton.start)
		rate := float64(baton.count) / elapsed.Seconds()
		var ratemsg string
		if elapsed.Seconds() == 0 || math.IsInf(rate, 0) {
			ratemsg = "∞"
		} else {
			ratemsg = scale(rate)
		}
		var ratemsg2 string
		rate2 := float64(baton.count - baton.lastcount)
		if math.IsInf(rate2, 0) {
			ratemsg2 = "∞"
		} else {
			ratemsg2 = scale(rate2)
		}
		if elapsed.Seconds() > 1 {
			elapsed = elapsed.Round(time.Second)
		}
		fmt.Fprintf(b, "%s %.2f%% %s/%s, %v @ %s/s, %s/s",
			baton.tag, frac * 100, scale(float64(baton.count)), scale(float64(baton.expected)), elapsed, ratemsg, ratemsg2)
	}
}

func (baton *Process) renderPre(b io.Writer) {
	baton.RLock()
	defer baton.RUnlock()
	b.Write(baton.startmsg)
}
func (baton *Process) renderPost(b io.Writer) {
	baton.RLock()
	defer baton.RUnlock()
	b.Write(baton.endmsg)
}

func _copystr(s string) []byte {
	temp := make([]byte, len(s))
	copy(temp, s)
	return temp
}

func _copyb(s []byte) []byte {
	temp := make([]byte, len(s))
	copy(temp, s)
	return temp
}

func getTerminfoString(cap string, params ...string) []byte {
	reader, _, err := readFromProcess("tput " + cap + " " + strings.Join(params, " "))
	if err != nil {
		return nil
	}
	buf := new(bytes.Buffer)
	_, err = buf.ReadFrom(reader)
	if err != nil {
		return nil
	}
	return buf.Bytes()
}
