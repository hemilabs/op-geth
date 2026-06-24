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
	"sync"
	"testing"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

// allow returns true at most once per ttl for a key, and re-fires once the window passes — this is what
// keeps the dedup a pure rate limiter that can only delay, never permanently suppress, a fan-out.
func TestTTLDeduperAllowAndExpiry(t *testing.T) {
	d := newTTLDeduper(3*time.Second, 4096)
	k := common.Hash{0x01}
	base := time.Unix(1000, 0)

	if !d.allow(k, base) {
		t.Fatal("first allow must return true")
	}
	if d.allow(k, base.Add(time.Second)) {
		t.Fatal("repeat within ttl must return false")
	}
	if d.allow(k, base.Add(2999*time.Millisecond)) {
		t.Fatal("repeat just under ttl must return false")
	}
	if !d.allow(k, base.Add(3*time.Second)) {
		t.Fatal("repeat at/after ttl must re-fire (return true)")
	}
	if d.allow(k, base.Add(3*time.Second+time.Millisecond)) {
		t.Fatal("repeat within the re-fired window must return false")
	}
}

func TestTTLDeduperKeysIndependent(t *testing.T) {
	d := newTTLDeduper(3*time.Second, 4096)
	base := time.Unix(1000, 0)
	if !d.allow(common.Hash{0x01}, base) {
		t.Fatal("key1 first allow must be true")
	}
	if !d.allow(common.Hash{0x02}, base) {
		t.Fatal("key2 first allow must be true (independent of key1)")
	}
	if d.allow(common.Hash{0x01}, base.Add(time.Second)) {
		t.Fatal("key1 repeat within ttl must be false")
	}
}

// The map is swept of EXPIRED entries (only) when it grows past max, bounding memory without ever
// re-permitting an in-window key.
func TestTTLDeduperSweepsOnlyExpired(t *testing.T) {
	const max = 8
	d := newTTLDeduper(3*time.Second, max)
	base := time.Unix(1000, 0)
	for i := 0; i < max; i++ {
		var k common.Hash
		k[0], k[1] = byte(i), byte(i>>8)
		if !d.allow(k, base) {
			t.Fatalf("fill allow %d must be true", i)
		}
	}
	if got := len(d.last); got != max {
		t.Fatalf("map should hold %d entries, got %d", max, got)
	}
	// A new key well past ttl triggers the sweep (len>=max): every prior entry is expired, so all are
	// dropped and only the new key remains.
	if !d.allow(common.Hash{0xff}, base.Add(10*time.Second)) {
		t.Fatal("post-expiry allow must be true")
	}
	if got := len(d.last); got != 1 {
		t.Fatalf("sweep should drop expired entries, leaving only the new one; got %d", got)
	}
}

// Under a flood of distinct fresh (unexpired) keys, the map is HARD-bounded by max: when the expired-only
// sweep frees nothing, the map is cleared rather than growing without limit. Dropping a fresh key only lets
// that hash re-fan-out once, which the store-derived backstops make harmless.
func TestTTLDeduperHardCapUnderFreshFlood(t *testing.T) {
	const max = 4
	d := newTTLDeduper(time.Hour, max) // long ttl: nothing ever expires, so only the hard cap bounds growth
	base := time.Unix(1000, 0)
	for i := 0; i < 100; i++ {
		var k common.Hash
		k[0], k[1], k[2] = byte(i), byte(i>>8), byte(i>>16)
		d.allow(k, base)
		if len(d.last) > max {
			t.Fatalf("map exceeded hard cap %d at insert %d: len=%d", max, i, len(d.last))
		}
	}
}

// shouldFanOutBtcRequest gates the closure: dedup runs FIRST (so an already-requested hash short-circuits
// before the store read), then availability. This pins that ordering against a swap.
func TestShouldFanOutBtcRequestOrdering(t *testing.T) {
	d := newTTLDeduper(time.Hour, 4096)
	h := common.Hash{0x01}
	now := time.Unix(1000, 0)

	availCalls := 0
	availFalse := func(common.Hash) bool { availCalls++; return false }

	// First call: not deduped, not available -> fan out, and availability IS consulted.
	if !shouldFanOutBtcRequest(d, availFalse, h, now) {
		t.Fatal("first call (fresh, not available) must fan out")
	}
	if availCalls != 1 {
		t.Fatalf("availability must be checked once on the first call, got %d", availCalls)
	}
	// Immediate repeat within the window: deduped -> skip, and availability must NOT be consulted (dedup
	// runs before the availability check).
	if shouldFanOutBtcRequest(d, availFalse, h, now) {
		t.Fatal("repeat within the dedup window must be skipped")
	}
	if availCalls != 1 {
		t.Fatalf("a deduped call must short-circuit BEFORE the availability check; availCalls=%d", availCalls)
	}
	// A fresh hash that is already available -> skip (availability gate).
	if shouldFanOutBtcRequest(d, func(common.Hash) bool { return true }, common.Hash{0x02}, now) {
		t.Fatal("an already-available hash must not fan out")
	}
}

// Concurrent allow on the same key+now yields exactly one winner (mutex correctness; run under -race).
func TestTTLDeduperConcurrentSingleWinner(t *testing.T) {
	d := newTTLDeduper(time.Hour, 4096)
	k := common.Hash{0x42}
	now := time.Unix(1000, 0)
	const n = 64
	var wg sync.WaitGroup
	var mu sync.Mutex
	wins := 0
	wg.Add(n)
	for i := 0; i < n; i++ {
		go func() {
			defer wg.Done()
			if d.allow(k, now) {
				mu.Lock()
				wins++
				mu.Unlock()
			}
		}()
	}
	wg.Wait()
	if wins != 1 {
		t.Fatalf("exactly one concurrent allow must win for the same key, got %d", wins)
	}
}
