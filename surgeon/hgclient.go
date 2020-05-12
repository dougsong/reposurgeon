/*
 * Mercurial (hg) command server client, used by HgExtractor
 *
// Copyright by Eric S. Raymond
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Based on gohg https://bitbucket.org/gohg/gohg, but simplified and
 * adapted to reposurgeon's needs
*/

package main

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"strings"
	"unicode"

	shellquote "github.com/kballard/go-shellquote"
)

// HgClient is client state for a session running Mercurial
type HgClient struct {
	hgServer *exec.Cmd
	pipeIn   io.WriteCloser // client write, server read
	pipeOut  io.ReadCloser  // server write, client read
}

// NewHgClient creates a new instance of the client robot.
func NewHgClient() *HgClient {
	var err error
	me := new(HgClient)
	me.hgServer = exec.Command("hg", "--config", "ui.interactive=False",
		"serve", "--cmdserver", "pipe")
	me.hgServer.Env = append(os.Environ(), "HGENCODING=UTF-8")
	me.pipeOut, err = me.hgServer.StdoutPipe()
	if err != nil {
		panic(throw("extractor", "NewHgClient: could not connect StdoutPipe: %s", err))
	}
	me.pipeIn, err = me.hgServer.StdinPipe()
	if err != nil {
		panic(throw("extractor", "NewHgClient: could not connect StdinPipe: %s", err))
	}

	if err = me.hgServer.Start(); err != nil {
		panic(throw("extractor", "NewHgClient: could not start the Hg Command Server: %s", err))
	}
	me.readHelloMessage()
	return me
}

// Close a client connection
func (hgcl *HgClient) Close() error {
	err := hgcl.pipeIn.Close()
	if err != nil {
		return err
	}
	return hgcl.hgServer.Wait()
}

func (hgcl *HgClient) readHelloMessage() {
	ch, hello, err := hgcl.receiveFromHg()

	if err != nil {
		panic(throw("extractor", "failed to receive hello message: %s", err))
	}

	// Old hg will return a usage message beginning "hg serve [OPTION]",
	// so we'll get channel "h" and a garbage length
	if ch == "h" {
		panic(throw("extractor", "bad channel; is hg too old?  (Require >= 1.9 for command server)"))
	}
	if ch != "o" {
		panic(throw("extractor", "received unexpected channel '%s' for hello message", ch))
	}
	lines := strings.Split(string(hello), "\n")
	rc := false
	utf8 := false
	for _, line := range lines {
		parts := strings.SplitN(line, ": ", 2)
		tag, body := parts[0], parts[1]
		switch tag {
		case "capabilities":
			for _, capa := range strings.Fields(body) {
				if capa == "runcommand" {
					rc = true
					break
				}
			}
		case "encoding":
			utf8 = body == "UTF-8"
		default:
			// ignore unhandled fields
		}
	}
	if !rc {
		panic(throw("extractor", "no runcommand capability"))
	}
	if !utf8 { // Could also be unspecified, but that shouldn't happen either
		panic(throw("extractor", "encoding is not utf-8"))
	}
}

func (hgcl *HgClient) runcommand(cmd []string) (stdout []byte, stderr []byte, err error) {
	if cmd[0] != "hg" {
		err = fmt.Errorf("runcommand: not an hg command")
		return
	}
	stdout, stderr, ret, err := hgcl.runInHg("runcommand", cmd[1:])
	if err != nil {
		err = fmt.Errorf("runcommand: %s", err)
	} else if ret != 0 {
		err = fmt.Errorf("runcommand: %s failed with rc %d",
			shellquote.Join(cmd...), ret)
	}
	return
}

func (hgcl *HgClient) receiveFromHg() (string, []byte, error) {
	if hgcl == nil {
		return "", nil, errors.New("no hgclient")
	}
	// get channel and length
	data := make([]byte, 5)
	_, err := hgcl.pipeOut.Read(data)
	if err != io.EOF && err != nil {
		return "", data, err
	}
	if data == nil {
		return "", nil, errors.New("no data read")
	}
	ch := string(data[0])
	if ch == "" {
		return "", data, errors.New("no channel read")
	}

	// get the uint that the Hg CS sent us as the length value
	ln, err := parseHgUint(data[1:5])
	if err != nil {
		return ch, data, fmt.Errorf("failed to decode length: %s", err)
	}

	// now get ln bytes of data
	data = make([]byte, ln)
	_, err = hgcl.pipeOut.Read(data)
	if err != io.EOF && err != nil {
		return ch, data, err
	}

	return ch, data, nil
}

func (hgcl *HgClient) sendToHg(cmd string, args []byte) error {
	if hgcl == nil {
		return fmt.Errorf("no hgclient")
	}
	var err error

	// cmd: can only be 'runcommand' or 'getencoding' for now
	cmd = strings.TrimRight(cmd, "\n") + "\n"
	lc := len(cmd)
	la := len(args)
	l := lc
	if la > 0 {
		l = l + 4 + la
	}
	data := make([]byte, l)

	// send the command
	copy(data[0:lc], cmd)

	if la > 0 {
		// send the length of the command arguments
		ln := uint32(len(args))
		buf := new(bytes.Buffer)
		err = binary.Write(buf, binary.BigEndian, ln)
		if err != nil {
			return fmt.Errorf("failed to encode data length: %s", err)
		}
		copy(data[lc:lc+4], buf.Bytes())

		// send the command arguments
		copy(data[lc+4:], args)
	}

	// perform the actual send to the Hg CS
	var i int
	i, err = hgcl.pipeIn.Write(data)
	if i != len(data) {
		return fmt.Errorf("failed to write data: %s", err)
	}

	return nil
}

func (hgcl *HgClient) runInHg(command string, hgcmd []string) (stdout []byte, stderr []byte, rc int32, err error) {
	args := []byte(strings.Join(hgcmd, string(0x0)))

	err = hgcl.sendToHg(command, args)
	if err != nil {
		return
	}

	var buf bytes.Buffer
	var errbuf bytes.Buffer

CHANNEL_LOOP:
	for true {
		var ch string
		var data []byte
		ch, data, err = hgcl.receiveFromHg()
		if err != nil || ch == "" {
			return nil, nil, 0, fmt.Errorf("failed to receive: %s", err)
		}
		switch ch {
		case "d":
		case "e":
			errbuf.Write(data)
		case "o":
			buf.Write(data)
		case "r":
			{
				if command == "getencoding" {
					buf.Write(data)
				} else {
					rc, err = parseHgInt(data[0:4])
					if err != nil {
						return nil, nil, 0, fmt.Errorf("failed to decode return code: %s", err)
					}
				}
				break CHANNEL_LOOP
			}
		case "I":
		case "L":
		default:
			// Uppercase channels are 'required'
			if unicode.IsUpper(rune(ch[0])) {
				return nil, nil, 0, fmt.Errorf("unexpected channel: %s", ch)
			}
		}
	}

	return buf.Bytes(), errbuf.Bytes(), rc, nil

}

// hgcs communicates protocol integers as big-endian four-byte integers
func parseHgUint(s []byte) (i uint32, err error) {
	err = binary.Read(bytes.NewBuffer(s[0:4]), binary.BigEndian, &i)
	return
}

func parseHgInt(s []byte) (i int32, err error) {
	u, err := parseHgUint(s)
	if err == nil {
		i = int32(u)
	}
	return
}
