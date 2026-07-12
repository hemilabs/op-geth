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

	"github.com/ethereum/go-ethereum/common"
)

// walkGate bounds the speculative ancestor-fetch store-walks that handleBTCBlocks spawns (one detached
// goroutine per inserted block, up to maxBtcBlocksServe per message). It (1) caps how many walks run
// concurrently so a burst cannot launch many concurrent deep TBC store-walks contending the
// consensus-shared full-node store, and (2) dedups walks for the same parent so duplicate gossip does not
// double-walk. Both are admission controls on a speculative optimization: anything a walk would fetch is
// also re-derived and re-requested by the 5s prefetchBTCBlocks backstop (GetMissingBtcBlocks), so dropping
// a walk only delays a fetch, never prevents it.
type walkGate struct {
	sem      chan struct{}
	inFlight sync.Map // common.Hash -> struct{}{}, present while a walk for that parent is running
}

func newWalkGate(maxConcurrent int) *walkGate {
	return &walkGate{sem: make(chan struct{}, maxConcurrent)}
}

// tryEnter admits a walk for key. It returns (release, true) if the walk may proceed — the caller MUST
// call release exactly once (via defer, so it also runs on panic) when the walk finishes. It returns
// (nil, false) — and admits nothing — when a walk for key is already in flight OR the concurrency cap is
// reached. The capacity-reject path clears its in-flight mark, so a later attempt for the same key is not
// permanently blocked by a rejection.
func (g *walkGate) tryEnter(key common.Hash) (release func(), ok bool) {
	if _, loaded := g.inFlight.LoadOrStore(key, struct{}{}); loaded {
		return nil, false // a walk for this parent is already running
	}
	select {
	case g.sem <- struct{}{}:
		return func() {
			<-g.sem
			g.inFlight.Delete(key)
		}, true
	default:
		g.inFlight.Delete(key) // at capacity: undo the in-flight mark we just took so retries can proceed
		return nil, false
	}
}
