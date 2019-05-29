package main

import (
	"sync"
)

// Pool holds a thread-locked map to store coalesced string instances.
type Pool struct {
	sync.RWMutex
	lookup map[string]string
}

var pool *Pool

// enableIntern - choose to reduce memory footprint at the cost of speed
func enableIntern(b bool) {
	if b {
		pool.lookup = make(map[string]string)
		return
	}
	pool.lookup = nil
}

func intern(s string) string {
	if pool == nil {
		// speed over space
		return s
	}

	// space over speed
	pool.RLock()
	ss, exists := pool.lookup[s]
	pool.RUnlock()
	if exists {
		return ss
	}

	pool.Lock()
	defer pool.Unlock()
	ss, exists = pool.lookup[s]
	if exists {
		return ss
	}
	pool.lookup[s] = s
	return s
}

// end
