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

package core

import (
	"context"
	"errors"
	"fmt"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
)

// hvmIndexErrToConsensus maps the core/vm-local missing-header sentinel to the deferrable consensus error
// the block-import path handles, leaving other errors (and nil) unchanged. Locks in that mapping (and the
// errors.Is chain through a %w-wrapped sentinel) without needing a TBC node.
func TestHvmIndexErrToConsensus(t *testing.T) {
	// The vm sentinel (bare or wrapped) maps to the deferrable consensus error so the import path defers
	// (futureBlocks + delayPayloadImport SYNCING) instead of crashing.
	for _, err := range []error{
		vm.ErrTBCMissingHeader,
		fmt.Errorf("indexer: %w", vm.ErrTBCMissingHeader),
	} {
		got := hvmIndexErrToConsensus(err)
		require.ErrorIs(t, got, consensus.ErrFullTBCMissingBTCHeader,
			"vm.ErrTBCMissingHeader must map to the deferrable consensus error")
	}

	// nil stays nil.
	require.NoError(t, hvmIndexErrToConsensus(nil))

	// Any other error is returned unchanged and must not look like the deferrable error, so the caller
	// fail-stops (log.Crit) on genuine faults rather than deferring.
	for _, err := range []error{
		errors.New("data corruption in full TBC node"),
		fmt.Errorf("unexpected: %w", errors.New("boom")),
	} {
		got := hvmIndexErrToConsensus(err)
		require.Equal(t, err, got, "non-sentinel errors must pass through unchanged")
		require.False(t, errors.Is(got, consensus.ErrFullTBCMissingBTCHeader),
			"a genuine fault must NOT be treated as the deferrable missing-header error")
	}

	// Idempotent: the consensus error itself passes through and still matches.
	require.ErrorIs(t, hvmIndexErrToConsensus(consensus.ErrFullTBCMissingBTCHeader), consensus.ErrFullTBCMissingBTCHeader)
}

// btcAttrDepIsHeaderless is the load-bearing classification: a Bitcoin Attributes Deposited tx that is
// absent (nil) or present-but-empty (zero headers) makes no TBC header change, so both apply and unapply
// take the no-op (state-id-only) path. A guard matching only btcAttrDep == nil would let an
// empty-but-present tx fall through to RemoveExternalHeaders with zero headers -> log.Crit on every node at
// reorg. Pins the guard so a refactor cannot narrow it to == nil. (The full apply/unapply round-trip
// needs an embedded TBC node; this is the pure regression-prone seam.)
func TestBtcAttrDepIsHeaderless(t *testing.T) {
	// Absent tx -> headerless (no-op path).
	require.True(t, btcAttrDepIsHeaderless(nil), "nil btcAttrDep (no BtcAttr tx) must be headerless")

	// Present-but-empty tx -> headerless. The case a nil-only check would miss.
	require.True(t, btcAttrDepIsHeaderless(&types.BtcAttributesDepositData{}),
		"present-but-empty BtcAttr tx (zero headers) must be headerless — the empty-but-present case")
	require.True(t, btcAttrDepIsHeaderless(&types.BtcAttributesDepositData{Headers: [][types.BitcoinHeaderLengthBytes]byte{}}),
		"explicitly zero-length Headers must be headerless")

	// Present with >=1 header -> not headerless (real add/remove path).
	require.False(t, btcAttrDepIsHeaderless(&types.BtcAttributesDepositData{Headers: make([][types.BitcoinHeaderLengthBytes]byte, 1)}),
		"a BtcAttr tx carrying one header must NOT be headerless")
	require.False(t, btcAttrDepIsHeaderless(&types.BtcAttributesDepositData{Headers: make([][types.BitcoinHeaderLengthBytes]byte, 8)}),
		"a BtcAttr tx carrying multiple headers must NOT be headerless")
}

// isHvmFullNodeBehind is the classifier on the head-set / reorg / forkchoice path: only the two deferrable
// "full TBC node hasn't P2P-synced yet" sentinels are treated as a transient, non-fatal lag (log.Warn +
// continue); every other error — including the consensus-fatal hVM validation errors and generic faults —
// must still fail-stop. Locks that boundary so the classifier can never swallow a real validation failure.
// No chain/TBC node needed.
func TestIsHvmFullNodeBehind(t *testing.T) {
	// The two deferrable sentinels — bare and %w-wrapped (callers see them wrapped through
	// updateHvmHeaderConsensus -> updateFullTBCToLightweight) — are the only full-node-behind case.
	for _, err := range []error{
		consensus.ErrFullTBCMissingBTCHeader,
		consensus.ErrFullTBCMissingFullBTCBlock,
		fmt.Errorf("update full tbc: %w", consensus.ErrFullTBCMissingBTCHeader),
		fmt.Errorf("outer: %w", fmt.Errorf("inner: %w", consensus.ErrFullTBCMissingFullBTCBlock)),
	} {
		require.True(t, isHvmFullNodeBehind(err),
			"deferrable full-TBC-sync-lag sentinel (incl. wrapped) must be treated as full-node-behind: %v", err)
	}

	// Everything else must not be treated as full-node-behind, so it stays fail-stop. This includes the
	// consensus-fatal hVM errors — the classifier must not mask them.
	for _, err := range []error{
		nil,
		consensus.ErrInvalidHVMHeaders,
		consensus.ErrInvalidHVMBlockFormat,
		consensus.ErrUnknownAncestor,
		consensus.ErrCorruptHVMHeaderOnlyModeState,
		// Confusingly-named sibling (consensus/errors.go): "missing btc full blocks" vs the matched "missing
		// full btc block". Must not be treated as full-node-behind; guards a copy-paste mix-up with
		// ErrFullTBCMissingFullBTCBlock.
		consensus.ErrMissingBTCFullBlocks,
		errors.New("data corruption in full TBC node"),
		fmt.Errorf("io: %w", errors.New("disk error")),
	} {
		require.False(t, isHvmFullNodeBehind(err),
			"non-deferrable error must NOT be treated as full-node-behind (must stay fail-stop): %v", err)
	}
}

// These tests cover the hVM snap-sync latch and the shutdown-cancellation of SnapSyncHvm. The latch helpers
// operate only on bc.hvmSnapMu + the three bool fields, so they can be exercised on a bare &BlockChain{}
// without a full chain or a TBC node.

// Many concurrent SnapSyncHvm responses may run the wait loop, but the (non-idempotent) completion work
// must be claimed by exactly one goroutine. hvmSnapClaimCompletion is the gate; under -race this also
// proves the latch bools are race-free.
func TestHvmSnapClaimCompletionExactlyOnce(t *testing.T) {
	bc := &BlockChain{awaitingHvmSnapSync: true}

	const n = 32
	var winners int64
	var wg sync.WaitGroup
	start := make(chan struct{})
	wg.Add(n)
	for i := 0; i < n; i++ {
		go func() {
			defer wg.Done()
			<-start // maximize contention
			if bc.hvmSnapShouldRun() && bc.hvmSnapClaimCompletion() {
				atomic.AddInt64(&winners, 1)
			}
		}()
	}
	close(start)
	wg.Wait()

	require.Equal(t, int64(1), atomic.LoadInt64(&winners), "exactly one goroutine may claim the completion work")
	require.True(t, bc.processingHvmSnapSync, "the winning claim sets processing")
	require.False(t, bc.hvmSnapShouldRun(), "no further attempt may run once completion is claimed")
	require.True(t, bc.hvmSnapShouldStop(), "other in-flight waiters must stop once completion is claimed")
}

// The latch lifecycle: awaiting -> run allowed -> claim -> others stop -> finished.
func TestHvmSnapLatchLifecycle(t *testing.T) {
	bc := &BlockChain{}

	// Not awaiting: never runs (mirrors a node not paused for hVM snap sync).
	require.False(t, bc.hvmSnapShouldRun())
	require.False(t, bc.HvmSnapSyncCompleted())

	bc.hvmEnabled = true // SetAwaitingHvmSnapSync panics if hVM is disabled
	bc.SetAwaitingHvmSnapSync()
	require.True(t, bc.isAwaitingHvmSnapSync())
	// The awaiting gauge is the sole alertable "apply-path consensus gate paused" signal; pin that it tracks
	// the latch (the assertion reads the gauge right after the absolute Update, so it is order-independent).
	require.Equal(t, int64(1), hvmSnapAwaitingGauge.Snapshot().Value(), "SetAwaitingHvmSnapSync must raise the awaiting gauge")
	require.True(t, bc.hvmSnapShouldRun(), "fresh attempt may run while awaiting and not finished/claimed")
	require.False(t, bc.hvmSnapShouldStop())

	require.True(t, bc.hvmSnapClaimCompletion(), "first claim wins")
	require.False(t, bc.hvmSnapClaimCompletion(), "second claim loses")
	require.False(t, bc.HvmSnapSyncCompleted(), "claiming completion must NOT mark the snap finished (only hvmSnapMarkFinished does)")
	require.False(t, bc.hvmSnapShouldRun(), "no new attempt after claim")
	require.True(t, bc.hvmSnapShouldStop(), "waiters abandon after claim")

	bc.hvmSnapMarkFinished()
	require.True(t, bc.HvmSnapSyncCompleted())
	require.False(t, bc.isAwaitingHvmSnapSync())
	require.False(t, bc.hvmSnapShouldRun())
	require.Equal(t, int64(0), hvmSnapAwaitingGauge.Snapshot().Value(), "hvmSnapMarkFinished must clear the awaiting gauge")

	// Re-arm after completion must be a no-op: a second in-process SnapSync entry (rewind/restart-below-pivot)
	// calls SetAwaitingHvmSnapSync again, but once finished there is no path back to hvmSnapMarkFinished, so
	// re-arming would leave the apply-path hVM consensus gate permanently closed. The finished guard prevents it.
	bc.SetAwaitingHvmSnapSync()
	require.False(t, bc.isAwaitingHvmSnapSync(), "a finished node must not re-arm the await latch (would wedge the apply gate)")
	require.False(t, bc.hvmSnapShouldRun(), "a finished node must never run hVM snap sync again")
	require.Equal(t, int64(0), hvmSnapAwaitingGauge.Snapshot().Value(), "a refused re-arm must leave the awaiting gauge cleared")
}

// SnapSyncHvm returns immediately (the wait loop runs in a detached runHvmSnapWaiter goroutine so it
// cannot block the caller's per-peer snap read loop). The spawned waiter must abort promptly when quit is
// closed without touching the TBC node, and free its slot. Relies on the quit check being the first thing in
// the wait loop, before any vm.TBCFullNode access (nil here, would panic if reached). hvmSnapWg joins the
// waiter so we can assert it returned cleanly.
func TestSnapSyncHvmAbortsOnQuit(t *testing.T) {
	bc := &BlockChain{awaitingHvmSnapSync: true, ctx: context.Background()}
	tip := chainhash.Hash{0x07}

	// Claim a real slot first so this cannot pass vacuously: an aborted-and-released waiter and a
	// never-started one both leave hvmSnapWaiters empty + hvmSnapWg.Wait() returning, so the test must prove
	// a slot was actually held (Len==1) before the abort, and freed after it.
	require.True(t, bc.claimHvmSnapWaiterSlot(tip), "claiming a slot must succeed while awaiting")
	require.Len(t, bc.hvmSnapWaiters, 1, "the slot must be registered before the waiter goroutine runs")

	quit := make(chan struct{})
	close(quit)
	go bc.runHvmSnapWaiter(&tip, &types.Header{}, quit) // aborts on the closed quit before any TBC access

	done := make(chan struct{})
	go func() { bc.hvmSnapWg.Wait(); close(done) }()
	select {
	case <-done:
		// the waiter aborted on quit and released its claimed slot
	case <-time.After(5 * time.Second):
		t.Fatal("runHvmSnapWaiter did not abort on a closed quit channel")
	}
	require.False(t, bc.HvmSnapSyncCompleted(), "an aborted attempt must not mark the round finished")
	bc.hvmSnapMu.Lock()
	require.Empty(t, bc.hvmSnapWaiters, "the aborted waiter must free its claimed slot")
	bc.hvmSnapMu.Unlock()
}

// SnapSyncHvm must no-op immediately (entry guard) when the chain is not awaiting a
// snap sync, even with a nil quit/ctx — it returns before touching either or spawning a waiter.
func TestSnapSyncHvmNoopWhenNotAwaiting(t *testing.T) {
	bc := &BlockChain{} // awaitingHvmSnapSync == false
	require.NotPanics(t, func() {
		bc.SnapSyncHvm(&chainhash.Hash{}, &types.Header{}, nil)
	}, "must return at the entry guard before touching ctx/quit/TBC when not awaiting")
	bc.hvmSnapMu.Lock()
	require.Empty(t, bc.hvmSnapWaiters, "no waiter slot may be claimed when not awaiting")
	bc.hvmSnapMu.Unlock()
}

// claimHvmSnapWaiterSlot is the testable entry decision: it dedupes by tip, caps the total, and refuses once
// the round is finished/claimed or not awaiting — so a peer cannot spawn unbounded or redundant waiters.
func TestHvmSnapWaiterSlotDedupeAndCap(t *testing.T) {
	bc := &BlockChain{awaitingHvmSnapSync: true}
	tipA := chainhash.Hash{0x01}

	require.True(t, bc.claimHvmSnapWaiterSlot(tipA), "first claim for a tip succeeds")
	require.False(t, bc.claimHvmSnapWaiterSlot(tipA), "a second claim for the same tip is deduped")

	// Fill the rest of the cap with distinct tips (tipA already holds slot 0).
	claimed := []chainhash.Hash{tipA}
	for i := 1; i < maxHvmSnapWaiters; i++ {
		tip := chainhash.Hash{byte(0x10 + i)}
		require.True(t, bc.claimHvmSnapWaiterSlot(tip), "distinct tip %d within the cap succeeds", i)
		claimed = append(claimed, tip)
	}
	// Exactly maxHvmSnapWaiters slots are live at the cap, so the refusal below is the cap firing — not an
	// off-by-one in the fill loop or the >= bound coinciding with a refusal for some other reason.
	require.Len(t, bc.hvmSnapWaiters, maxHvmSnapWaiters, "exactly the cap of waiter slots must be live")
	require.False(t, bc.claimHvmSnapWaiterSlot(chainhash.Hash{0xff}), "a new distinct tip is refused once the cap is reached")
	require.Len(t, bc.hvmSnapWaiters, maxHvmSnapWaiters, "a refused claim must not grow the waiter set")

	// Releasing a slot frees room for one more.
	bc.releaseHvmSnapWaiterSlot(tipA)
	claimed = claimed[1:]
	require.True(t, bc.claimHvmSnapWaiterSlot(chainhash.Hash{0xfe}), "a freed slot can be reclaimed")
	claimed = append(claimed, chainhash.Hash{0xfe})

	// Finished/claimed/not-awaiting all refuse (independent bc to isolate each flag).
	for _, tc := range []struct {
		name string
		bc   *BlockChain
	}{
		{"not awaiting", &BlockChain{}},
		{"finished", &BlockChain{awaitingHvmSnapSync: true, finishedHvmSnapSync: true}},
		{"already claimed", &BlockChain{awaitingHvmSnapSync: true, processingHvmSnapSync: true}},
	} {
		require.False(t, tc.bc.claimHvmSnapWaiterSlot(chainhash.Hash{0x42}), "claim must be refused: %s", tc.name)
	}

	// Balance the WaitGroup (every true claim did an Add) so the join doesn't leak.
	for _, tip := range claimed {
		bc.releaseHvmSnapWaiterSlot(tip)
	}
	done := make(chan struct{})
	go func() { bc.hvmSnapWg.Wait(); close(done) }()
	select {
	case <-done:
	case <-time.After(2 * time.Second):
		t.Fatal("hvmSnapWg did not balance after releasing every claimed slot")
	}
	bc.hvmSnapMu.Lock()
	require.Empty(t, bc.hvmSnapWaiters, "all slots released")
	bc.hvmSnapMu.Unlock()
}

// claimHvmSnapWaiterSlot must refuse once shutdown has begun, so no hvmSnapWg.Add happens after
// stopWithoutSaving has started its hvmSnapWg.Wait() — localizing the no-Add-after-Wait invariant.
func TestClaimHvmSnapWaiterSlotRefusedWhenStopping(t *testing.T) {
	bc := &BlockChain{awaitingHvmSnapSync: true}
	bc.stopping.Store(true)
	require.False(t, bc.claimHvmSnapWaiterSlot(chainhash.Hash{0x01}),
		"no waiter slot may be claimed once the chain is stopping")
	bc.hvmSnapMu.Lock()
	require.Empty(t, bc.hvmSnapWaiters, "stopping must claim no slot")
	bc.hvmSnapMu.Unlock()
}

// updateHvmHeaderConsensus must no-op (return nil without touching the lightweight TBC) while a snap sync is
// in flight — the single chokepoint that pauses hVM consensus for every head-move/reorg/build caller, not
// just ProcessBlock. A bare BlockChain has a nil tbcHeaderNode/chainConfig, so a clean nil return (no panic)
// proves the awaiting check fires before any further access.
func TestUpdateHvmHeaderConsensusSkipsWhileAwaitingSnap(t *testing.T) {
	bc := &BlockChain{hvmEnabled: true, awaitingHvmSnapSync: true}
	require.NotPanics(t, func() {
		require.NoError(t, bc.updateHvmHeaderConsensus(&types.Header{}, true),
			"must return nil (no-op) while awaiting hVM snap sync, without touching the lightweight TBC")
	})
}

// recordHvmBtcAttrResult is the observability classifier for the build path:
// GetBitcoinAttributesForNextBlock does not crash the sequencer on a persistent failure to advance the
// hVM Bitcoin view, so that failure must instead be alertable via metrics. Locks in the four-way classification without a
// TBC node — the seam extracted so this consensus-irrelevant but ops-critical mapping can be unit-tested.
func TestRecordHvmBtcAttrResult(t *testing.T) {
	gaugeVal := func() int64 { return hvmBtcAttrFailingGauge.Snapshot().Value() }
	meterCount := func() int64 { return hvmBtcAttrFailMeter.Snapshot().Count() }

	// nil (success or a legitimately idle cycle): returns nil, clears the stuck gauge, does not mark the
	// fail meter.
	hvmBtcAttrFailingGauge.Update(1) // dirty it first to prove it is cleared
	startMeter := meterCount()
	require.NoError(t, recordHvmBtcAttrResult(nil))
	require.Equal(t, int64(0), gaugeVal(), "nil result must clear the stuck gauge")
	require.Equal(t, startMeter, meterCount(), "nil result must not mark the fail meter")

	// The pending-blocked sentinel (bare and %w-wrapped) is hidden from the caller (returns nil, so the
	// caller sees a plain (nil,nil) result) but raises the stuck gauge and must not mark the fail
	// meter (not a hard failure, just a non-advancing round).
	for _, err := range []error{
		errHvmBtcAttrPendingBlocked,
		fmt.Errorf("ctx: %w", errHvmBtcAttrPendingBlocked),
	} {
		hvmBtcAttrFailingGauge.Update(0)
		startMeter = meterCount()
		require.NoError(t, recordHvmBtcAttrResult(err), "the pending-blocked sentinel must be hidden from the caller")
		require.Equal(t, int64(1), gaugeVal(), "pending-blocked must raise the stuck gauge")
		require.Equal(t, startMeter, meterCount(), "pending-blocked must not mark the fail meter")
	}

	// Shutdown-class errors pass through unchanged and leave both metrics untouched (whatever the gauge
	// was), so shutdown cannot trip a spurious stuck/failure alert. Covers bare and %w-wrapped
	// errChainStopped plus context.Canceled (bare/wrapped), which the classifier folds into the shutdown
	// case. context.DeadlineExceeded is deliberately not folded (see below).
	for _, shutdownErr := range []error{
		errChainStopped,
		fmt.Errorf("tbc read: %w", errChainStopped),
		context.Canceled,
		fmt.Errorf("tbc read: %w", context.Canceled),
	} {
		for _, g := range []int64{0, 1} {
			hvmBtcAttrFailingGauge.Update(g)
			startMeter = meterCount()
			got := recordHvmBtcAttrResult(shutdownErr)
			require.ErrorIs(t, got, shutdownErr, "shutdown error must pass through unchanged")
			require.Equal(t, g, gaugeVal(), "shutdown must leave the stuck gauge untouched")
			require.Equal(t, startMeter, meterCount(), "shutdown must not mark the fail meter")
		}
	}

	// Genuine errors (incl. context.DeadlineExceeded, which bc.ctx — being cancel-only — never produces on
	// shutdown, so it can only be a real downstream timeout that must alert) pass through unchanged, mark
	// the fail meter exactly once, and raise the stuck gauge.
	for _, boom := range []error{
		errors.New("lightweight TBC returned an incorrect height"),
		context.DeadlineExceeded,
		fmt.Errorf("tbc read: %w", context.DeadlineExceeded),
	} {
		hvmBtcAttrFailingGauge.Update(0)
		startMeter = meterCount()
		got := recordHvmBtcAttrResult(boom)
		require.ErrorIs(t, got, boom, "a genuine error must pass through unchanged")
		require.Equal(t, int64(1), gaugeVal(), "a genuine error must raise the stuck gauge")
		require.Equal(t, startMeter+1, meterCount(), "a genuine error must mark the fail meter exactly once")
	}
}

// finalizeHvmBtcAttrResult is the public wrapper's pairing logic: on any error surfaced to the caller it
// must never leak a partial tx, and otherwise must return tx unchanged. Pins that contract directly (the
// inner function needs a TBC node; this seam does not).
func TestFinalizeHvmBtcAttrResult(t *testing.T) {
	someTx := &types.BtcAttributesDepositedTx{}

	// Success: the built tx is returned as-is, no error.
	gotTx, gotErr := finalizeHvmBtcAttrResult(someTx, nil)
	require.NoError(t, gotErr)
	require.Same(t, someTx, gotTx, "a successful build must return the tx unchanged")

	// Idle cycle: (nil, nil) stays (nil, nil).
	gotTx, gotErr = finalizeHvmBtcAttrResult(nil, nil)
	require.NoError(t, gotErr)
	require.Nil(t, gotTx)

	// Hidden sentinel: the inner function always pairs the pending-blocked sentinel with a nil tx,
	// and the caller must see exactly (nil, nil) — sentinel hidden, no surfaced error.
	gotTx, gotErr = finalizeHvmBtcAttrResult(nil, errHvmBtcAttrPendingBlocked)
	require.NoError(t, gotErr, "the pending-blocked sentinel must be hidden from the caller")
	require.Nil(t, gotTx)

	// Genuine error / shutdown: the error is surfaced and the tx is dropped (never leaked).
	for _, err := range []error{
		errors.New("boom"),
		errChainStopped,
		context.DeadlineExceeded,
	} {
		gotTx, gotErr = finalizeHvmBtcAttrResult(someTx, err)
		require.ErrorIs(t, gotErr, err, "the surfaced error must pass through")
		require.Nil(t, gotTx, "no partial tx may be returned alongside an error")
	}
}
