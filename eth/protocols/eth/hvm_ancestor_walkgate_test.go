// Copyright 2024 The go-ethereum Authors
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
	"runtime"
	"sync"
	"testing"

	"github.com/ethereum/go-ethereum/common"
)

// A walk for a parent already in flight is dropped; once released, the same parent is admissible again.
func TestWalkGateInFlightDedup(t *testing.T) {
	g := newWalkGate(4)
	k := common.Hash{0x01}

	rel, ok := g.tryEnter(k)
	if !ok {
		t.Fatal("first tryEnter must succeed")
	}
	if _, ok2 := g.tryEnter(k); ok2 {
		t.Fatal("second tryEnter for an in-flight key must be rejected")
	}
	rel()
	rel2, ok3 := g.tryEnter(k)
	if !ok3 {
		t.Fatal("tryEnter after release must succeed")
	}
	rel2()
}

// A different parent is admitted concurrently with one already in flight (dedup is per-key, not global).
func TestWalkGateDistinctKeysConcurrent(t *testing.T) {
	g := newWalkGate(4)
	r1, ok1 := g.tryEnter(common.Hash{0x01})
	if !ok1 {
		t.Fatal("k1 must enter")
	}
	r2, ok2 := g.tryEnter(common.Hash{0x02})
	if !ok2 {
		t.Fatal("a distinct key must enter while k1 is in flight")
	}
	r1()
	r2()
}

// At capacity, a new key is rejected; and the rejection must NOT leave a stale in-flight mark, so once a
// slot frees the key is admissible.
func TestWalkGateCapacityRejectClearsInFlight(t *testing.T) {
	g := newWalkGate(2)
	r1, ok1 := g.tryEnter(common.Hash{0x01})
	if !ok1 {
		t.Fatal("k1 must enter")
	}
	r2, ok2 := g.tryEnter(common.Hash{0x02})
	if !ok2 {
		t.Fatal("k2 must enter")
	}
	if _, ok3 := g.tryEnter(common.Hash{0x03}); ok3 {
		t.Fatal("k3 must be rejected at capacity")
	}
	// Free a slot; k3 must now enter — proving the capacity rejection cleared k3's in-flight mark.
	r1()
	r3, ok3b := g.tryEnter(common.Hash{0x03})
	if !ok3b {
		t.Fatal("k3 must enter after a slot frees (capacity reject must not leave a stale in-flight mark)")
	}
	r3()
	r2()
}

// Under concurrency with distinct keys (so only the semaphore binds), admitted walks never exceed the cap.
// Run under -race for the data-race check on the shared gate.
func TestWalkGateConcurrentNeverExceedsCap(t *testing.T) {
	const cap = 3
	g := newWalkGate(cap)
	const n = 64

	var wg sync.WaitGroup
	var mu sync.Mutex
	live, peak, admitted := 0, 0, 0
	wg.Add(n)
	for i := 0; i < n; i++ {
		go func(i int) {
			defer wg.Done()
			var k common.Hash
			k[0], k[1] = byte(i), byte(i>>8)
			rel, ok := g.tryEnter(k)
			if !ok {
				return
			}
			mu.Lock()
			admitted++
			live++
			if live > peak {
				peak = live
			}
			mu.Unlock()
			runtime.Gosched()
			mu.Lock()
			live--
			mu.Unlock()
			rel()
		}(i)
	}
	wg.Wait()
	if peak > cap {
		t.Fatalf("peak concurrent admitted walks %d exceeded cap %d", peak, cap)
	}
	if admitted == 0 {
		t.Fatal("expected at least some walks to be admitted")
	}
}
