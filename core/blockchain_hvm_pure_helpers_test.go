package core

import "testing"

// TestBtcAttrFutureSkewExceeded pins the sequencer's BtcAttr future-skew gate, including the uint64-underflow
// region the ordered compare fixes. Expected values are hand-computed (not via the production expression): the
// gate must fire ONLY for a timestamp strictly more than btcAttrFutureSkewWindow (3600s) ahead of now, and
// must NOT fire for any past-or-equal timestamp (a catch-up block must still get the tx). A regression
// flipping `>` to `>=`, dropping the `timestamp > now` underflow guard, or changing the 3600s window fails here.
func TestBtcAttrFutureSkewExceeded(t *testing.T) {
	const window = uint64(3600)
	cases := []struct {
		name           string
		timestamp, now uint64
		want           bool
	}{
		// Past / equal: never drop (the catch-up case; this is the underflow region the guard protects).
		{"past-by-1000", 4000, 5000, false},
		{"equal", 1000, 1000, false},
		{"zero-both", 0, 0, false},
		// Future but within the window: keep.
		{"future-1s", 1001, 1000, false},
		{"at-window-boundary", 1000 + window, 1000, false}, // diff == 3600, not > 3600
		// Future strictly beyond the window: drop.
		{"just-over-window", 1000 + window + 1, 1000, true}, // diff == 3601
		{"far-future", 1_000_000, 1000, true},
	}
	for _, c := range cases {
		if got := btcAttrFutureSkewExceeded(c.timestamp, c.now); got != c.want {
			t.Errorf("%s: btcAttrFutureSkewExceeded(ts=%d, now=%d) = %v, want %v",
				c.name, c.timestamp, c.now, got, c.want)
		}
	}
	// Independent re-statement of the window: exactly 3600s ahead is allowed, 3601s is not.
	if btcAttrFutureSkewExceeded(btcAttrFutureSkewWindow, 0) {
		t.Errorf("a timestamp exactly btcAttrFutureSkewWindow (%d) ahead must NOT be dropped", btcAttrFutureSkewWindow)
	}
	if !btcAttrFutureSkewExceeded(btcAttrFutureSkewWindow+1, 0) {
		t.Errorf("a timestamp btcAttrFutureSkewWindow+1 (%d) ahead MUST be dropped", btcAttrFutureSkewWindow+1)
	}
}

// TestBodyAbsentShouldGiveUp pins the snap waiter give-up boundary. The give-up bound is the defense that
// stops a peer pinning never-local base bodies from holding every waiter slot and stalling snap
// completion; it lives in the live-TBC-bound runHvmSnapWaiter loop, so the boundary is
// pinned here on the extracted pure predicate. A mutation flipping >= to > (one extra poll) or to a wrong
// constant relationship fails this test.
func TestBodyAbsentShouldGiveUp(t *testing.T) {
	cases := []struct {
		polls int
		want  bool
	}{
		{0, false},
		{1, false},
		{maxHvmSnapBodyAbsentPolls - 1, false}, // one below the bound: keep waiting
		{maxHvmSnapBodyAbsentPolls, true},      // exactly at the bound: give up (this is the >= boundary)
		{maxHvmSnapBodyAbsentPolls + 1, true},  // above the bound: give up
	}
	for _, c := range cases {
		if got := bodyAbsentShouldGiveUp(c.polls); got != c.want {
			t.Errorf("bodyAbsentShouldGiveUp(%d) = %v, want %v (maxHvmSnapBodyAbsentPolls=%d)",
				c.polls, got, c.want, maxHvmSnapBodyAbsentPolls)
		}
	}
}

// TestShouldWalkBackTipLag pins the updateFullTBCToLightweight tip-lag walk-back boundary, including the
// unsigned-underflow case that the addition form fixes. The prior subtraction form
// (cursorHeight - lag > genesisOffset) wrapped to a huge value (passing the guard, then walking below
// genesis) when cursorHeight < lag — reachable right after the hVM Phase-0 transition on a near-zero-offset
// regtest network. A revert to that subtraction, or a > vs >= off-by-one at the genesis floor, fails here.
func TestShouldWalkBackTipLag(t *testing.T) {
	cases := []struct {
		name                      string
		cursorHeight, offset, lag uint64
		want                      bool
	}{
		// Underflow region: cursorHeight < lag. The old subtraction wrapped TRUE here; correct is FALSE.
		{"underflow-h1-lag2", 1, 0, 2, false},
		{"underflow-h2-lag2", 2, 0, 2, false},
		{"zero-cursor", 0, 0, 2, false},
		// Exact genesis floor: cursorHeight == offset+lag must NOT walk back (would reach exactly genesis).
		{"at-floor-offset0", 2, 0, 2, false},
		{"at-floor-mainnet", 883094, 883092, 2, false},
		// One above the floor: walks back exactly once.
		{"above-floor-offset0", 3, 0, 2, true},
		{"above-floor-mainnet", 883095, 883092, 2, true},
		// Well above the floor.
		{"steady-state", 900000, 883092, 2, true},
		// Larger lag (testnet3 diff-bomb path caps lag ~100).
		{"large-lag-at-floor", 100, 0, 100, false},
		{"large-lag-above", 101, 0, 100, true},
	}
	for _, c := range cases {
		if got := shouldWalkBackTipLag(c.cursorHeight, c.offset, c.lag); got != c.want {
			t.Errorf("%s: shouldWalkBackTipLag(cursorHeight=%d, offset=%d, lag=%d) = %v, want %v",
				c.name, c.cursorHeight, c.offset, c.lag, got, c.want)
		}
	}
}
