// Copyright 2024 The go-ethereum Authors
// Copyright 2026 Hemi Labs, Inc.
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package eth

import (
	"sync"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

// ttlDeduper is a small concurrency-safe rate limiter keyed by hash: allow returns true at most once per
// ttl for a given key. It rate-limits the snap-sync BTC-block peer fan-out (requestBtcBlocksFromPeers),
// which OnHvmLightState fires once per (canonical tip + each BtcAttr header) for EVERY light-state
// response while the downloader broadcasts the request to all peers — without it a single reissue cycle
// fans each hash out O(P^2) times. The dedup is purely a rate limiter: the entry expires so the fan-out
// re-fires (the downloader reissues every 30s), and the store-derived backstops (prefetchBTCBlocks's 5s
// GetMissingBtcBlocks and runHvmSnapWaiter's bitcoin-P2P refetch) never consult it and re-derive the
// missing set from the store each cycle, so a skipped fan-out can only delay a fetch, never prevent it.
type ttlDeduper struct {
	mu   sync.Mutex
	last map[common.Hash]time.Time
	ttl  time.Duration
	max  int // hard ceiling on retained entries (see allow): the map can never exceed max
}

func newTTLDeduper(ttl time.Duration, max int) *ttlDeduper {
	return &ttlDeduper{last: make(map[common.Hash]time.Time), ttl: ttl, max: max}
}

const (
	// btcReqDedupTTL bounds how often the snap-sync BTC-block fan-out re-fires the same hash. It is short
	// relative to the downloader's 30s light-state reissue, so a still-missing hash re-fans-out on the next
	// reissue while the per-response O(P^2) burst (P responses x all-P peers) collapses to O(P).
	btcReqDedupTTL = 3 * time.Second
	// btcReqDedupMaxEntries is the hard ceiling on the dedup map (see ttlDeduper.allow). Generously larger
	// than the in-flight BTC-block working set so it only ever clamps a pathological flood.
	btcReqDedupMaxEntries = 4096
)

// shouldFanOutBtcRequest reports whether a fresh all-peers fan-out for hash should happen now: false if the
// hash was fanned out within the dedup window (rate limit) or the block is already in the store. Kept
// separate from the requestBtcBlocksFromPeers closure so the dedup-before-availability ordering is
// unit-testable without a live handler. dedup.allow runs first so an already-requested hash short-circuits
// before the (cheaper-to-skip) store read; the dedup is rate-limit-only, so this never permanently
// suppresses a fetch.
func shouldFanOutBtcRequest(dedup *ttlDeduper, available func(common.Hash) bool, hash common.Hash, now time.Time) bool {
	if !dedup.allow(hash, now) {
		return false
	}
	return !available(hash)
}

// allow reports whether an action on key should proceed at time now. It returns false if key was last
// allowed less than ttl ago; otherwise it records now and returns true. now is passed in (rather than read
// internally) so the behavior is deterministically testable.
func (d *ttlDeduper) allow(key common.Hash, now time.Time) bool {
	d.mu.Lock()
	defer d.mu.Unlock()
	if t, ok := d.last[key]; ok && now.Sub(t) < d.ttl {
		return false
	}
	// Keep the map hard-bounded by max. First drop expired entries (the common case under normal churn;
	// removing only expired keys never re-permits an in-window key). If every retained entry is still
	// in-window — a flood of distinct fresh keys, e.g. a malicious peer streaming light-state responses
	// faster than the TTL — clear the whole map rather than letting it grow without limit. A cleared key
	// merely loses dedup for one window (one extra fan-out), which the store-derived backstops make
	// harmless; this mirrors the bounded missing-set reset in runHvmSnapWaiter.
	if len(d.last) >= d.max {
		for k, t := range d.last {
			if now.Sub(t) >= d.ttl {
				delete(d.last, k)
			}
		}
		if len(d.last) >= d.max {
			clear(d.last)
		}
	}
	d.last[key] = now
	return true
}
