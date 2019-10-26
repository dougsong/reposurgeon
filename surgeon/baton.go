/*
 * Baton machinery
 */

package main
import (
	"bytes"
	"fmt"
	"io"
	"math"
	"os"
	"strings"
	"time"
)

// the overall state of the output
type μπαγκέτα struct {
	progressEnabled bool
	stream *os.File
	channel chan Message
	progressLine []byte
	start time.Time
	baton Baton
	counter Counter
	progress Progress
	process Process
}

// Baton is the state of a twirly indefinite progess meter that ships indications to stdout.
type Baton struct {
	lastupdate time.Time
	count uint8
}

type Counter struct {
	lastupdate time.Time
	format string
	count uint64
}

type Progress struct {
	start time.Time
	lastupdate time.Time
	tag []byte
	count uint64
	expected uint64
}

type Process struct {
	lastupdate time.Time
	startmsg []byte
	endmsg []byte
	start time.Time
}

type msgType uint8
const (
	NONE msgType = iota
	LOG
	PROGRESS
	SYNC
)

type Message struct {
	ty msgType
	str []byte
	currentProgress []byte
}

const twirlInterval     = 100 * time.Millisecond	// Rate-limit baton twirls
const progressInterval  =   1 * time.Second		// Rate-limit progress messages

func newBaton(interactive bool) *μπαγκέτα {
	me := new(μπαγκέτα)
	me.start = time.Now()
	tiColZero := getTerminfoString("hpa", "0")
	tiClrEol := getTerminfoString("el")
	tiScrollForward := getTerminfoString("ind")
	me.channel = make(chan Message)
	me.progressEnabled = interactive
	go func() {
		for {
			msg := <- me.channel
			if msg.ty == SYNC {
				me.channel<-msg
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
						me.stream.Write(msg.currentProgress)
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
					me.stream.Write(msg.currentProgress)
				}
			}
		}
	}()
	me.stream = os.Stdout

	return me
}

func (self *μπαγκέτα) setInteractivity(enabled bool) {
	if self != nil {
		self.channel<- Message{SYNC, nil, nil}
		self.progressEnabled = enabled
		<-self.channel
	}
}

// log prints out a simple log message
func (self *μπαγκέτα) printLog(str []byte) {
	if self != nil {
		self.channel <- Message{LOG, _copyb(str), _copyb(self.progressLine)}
	}
}

func (self *μπαγκέτα) printLogString(str string) {
	if self != nil {
		self.channel <- Message{LOG, _copystr(str), _copyb(self.progressLine)}
	}
}

// progress prints out a progress message in the status line
func (self *μπαγκέτα) printProgress() {
	if self != nil && self.progressEnabled {
		var buf bytes.Buffer
		self.render(&buf)
		self.progressLine = buf.Bytes()
		self.channel <- Message{PROGRESS, nil, _copyb(self.progressLine)}
	}
}

// twirl spins the baton
func (self *μπαγκέτα) twirl() {
	if self != nil && self.progressEnabled {
		if time.Since(self.baton.lastupdate) > twirlInterval {
			self.baton.count = (self.baton.count + 1) % 4
			self.printProgress()
			self.baton.lastupdate = time.Now()
		}
	}
}

func (self *μπαγκέτα) startProcess(startmsg string, endmsg string) {
	if self != nil && self.progressEnabled {
		self.process.startmsg = []byte(startmsg)
		self.process.endmsg = []byte(endmsg)
		self.process.start = time.Now()
	}
}

func (self *μπαγκέτα) endProcess(endmsg ...string) {
	if self != nil && self.progressEnabled {
		if endmsg != nil {
			self.process.endmsg = []byte(strings.Join(endmsg, " "))
		}
		fmt.Fprintf(self, "%s ...(%s) %s.",
			self.process.startmsg,
			time.Since(self.process.start).Round(time.Millisecond * 10),
			self.process.endmsg)
		self.process.startmsg = nil
		self.process.endmsg = nil
	}
}

func (self *μπαγκέτα) startcounter(countfmt string, initial uint64) {
	if self != nil && self.progressEnabled {
		self.counter.format = countfmt
		self.counter.count = initial
	}
}

func (self *μπαγκέτα) bumpcounter() {
	if self != nil && self.progressEnabled {
		if self.counter.format != "" {
			self.counter.count += 1
			self.printProgress()
		} else {
			self.twirl()
		}
	}
}

func (self *μπαγκέτα) endcounter() {
	if self != nil && self.progressEnabled {
		self.counter.render(self)
		self.counter.format = ""
		self.counter.count = 0
	}
}

func (self *μπαγκέτα) startProgress(tag string, expected uint64) {
	if self != nil && self.progressEnabled {
		self.progress.start = time.Now()
		self.progress.lastupdate = self.progress.start
		self.progress.tag = []byte(tag)
		self.progress.count = 0
		self.progress.expected = expected
	}
}

func (self *μπαγκέτα) percentProgress(ccount uint64) {
	if self != nil && self.progressEnabled &&
		(time.Since(self.progress.lastupdate) > progressInterval || ccount == self.progress.expected) {
		self.progress.count = ccount
		self.progress.lastupdate = time.Now()
		self.printProgress()
	}
}

func (self *μπαγκέτα) endProgress() {
	if self != nil && self.progressEnabled {
		self.progress.render(self)
		self.progress.tag = nil
		self.progress.count = 0
		self.progress.expected = 0
	}
}

func (self *μπαγκέτα) WriteString(s string) (n int, err error) {
	if self != nil {
		self.printLog([]byte(s))
	}
	return len(s), nil
}

func (self *μπαγκέτα) Write(b []byte) (n int, err error) {
	if self != nil {
		self.printLog(b)
	}
	return len(b), nil
}

func (self *μπαγκέτα) Close() error {
	return nil
}

func (self *μπαγκέτα) Sync() {
	if self != nil {
		self.channel <- Message{SYNC, nil, nil}
		<-self.channel
	}
}

func (self *μπαγκέτα) render(buf io.Writer) {
	self.process.renderPre(buf)
	self.counter.render(buf)
	self.progress.render(buf)
	fmt.Fprintf(buf, " (%v)", time.Since(self.start).Round(time.Second))
	self.baton.render(buf)
	self.process.renderPost(buf)
}

func (self *Baton) render(b io.Writer) {
	character := "-\\|/"[self.count]
	b.Write([]byte{32, character})
}

func (self *Counter) render(b io.Writer) {
	if self.format != "" {
		n, _ := fmt.Fprintf(b, self.format, self.count)
		if n > 0 {
			b.Write([]byte{' '})
		}
	}
}

func (self *Progress) render(b io.Writer) {
	scale := func(n float64) string {
		if n < 1000 {
			return fmt.Sprintf("%.2f", n)
		} else if n < 1000000 {
			return fmt.Sprintf("%.2fK", n / 1000)
		} else if n < 1000000000 {
			return fmt.Sprintf("%.2fM", n / 1000000)
		} else if n < 1000000000000 {
			return fmt.Sprintf("%.2fG", n / 1000000000)
		} else {
			return fmt.Sprintf("%.2fT", n / 1000000000000)
		}
	}
	if self.expected > 0 {
		frac := float64(self.count) / float64(self.expected)
		elapsed := self.lastupdate.Sub(self.start)
		rate := float64(self.count) / elapsed.Seconds()
		var ratemsg string
		if elapsed.Seconds() == 0 || math.IsInf(rate, 0) {
			ratemsg = "∞"
		} else {
			ratemsg = scale(rate)
		}
		if elapsed.Seconds() > 1 {
			elapsed = elapsed.Round(time.Second)
		}
		fmt.Fprintf(b, "%s %.2f%% %s/%s, %v @ %s/s",
			self.tag, frac * 100, scale(float64(self.count)), scale(float64(self.expected)), elapsed, ratemsg)
	}
}

func (self *Process) renderPre(b io.Writer) {
	b.Write(self.startmsg)
}
func (self *Process) renderPost(b io.Writer) {
	b.Write(self.endmsg)
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
