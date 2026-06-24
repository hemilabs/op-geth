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
	"bytes"
	"context"
	"errors"
	"fmt"
	"math/big"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/txscript"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
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

// Snap-sync EXIT/resumption invariant. The ENTRY gate (updateHvmHeaderConsensus short-circuits while
// isAwaitingHvmSnapSync) is covered, and the latch lifecycle is unit-tested on a bare &BlockChain{}. But no test
// drives updateHvmHeaderConsensus AFTER hvmSnapMarkFinished — the documented behavior (blockchain.go ~4364) that
// "blocks deferred during the window are caught up by the first updateHvmHeaderConsensus after the snap completes
// (it walks the gap)". A mutant that fails to clear the latch, or breaks the gap walk, would silently wedge the
// lightweight TBC view after snap yet pass every current test. Corpus-free: the deferred gap blocks are HEADERLESS
// (empty-present), so the forward walk never reaches the full-node prefetch.
func TestHvmSnapExitResumesDeferredGapForwardWalk(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)
	checkpoint := lightTip.BlockHash()

	preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockM := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})
	// Deferred gap M+1, M+2, N: headerless empty-present blocks (so walkForward dodges the full-node prefetch).
	blockM1 := emptyPresentBtcAttrBlock(t, 12, hvm0Time+1, blockM.Header(), checkpoint)
	blockM2 := emptyPresentBtcAttrBlock(t, 13, hvm0Time+2, blockM1.Header(), checkpoint)
	blockN := emptyPresentBtcAttrBlock(t, 14, hvm0Time+3, blockM2.Header(), checkpoint)

	chain.tempHeaders[preAct.Hash().String()] = preAct
	chain.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
	for _, b := range []*types.Block{blockM, blockM1, blockM2, blockN} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
		rawdb.WriteBlock(chain.db, b) // findCommonAncestor resolves the gap via bc.GetHeader (rawdb only)
	}

	// Establish state-id = M (the snap-pinned base the lightweight TBC is reconstructed to).
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockM.Header(), false, true))
	sidM, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockM.Hash().Bytes(), sidM[:])

	// ENTER snap-await: a head move to N must short-circuit (deferred), leaving the state-id at M.
	chain.SetAwaitingHvmSnapSync()
	require.True(t, chain.isAwaitingHvmSnapSync())
	require.NoError(t, chain.updateHvmHeaderConsensus(blockN.Header(), false), "while awaiting snap, the head move is a deferred no-op")
	sidAwait, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockM.Hash().Bytes(), sidAwait[:], "the awaiting gate must NOT advance the state-id")

	// EXIT snap: the first updateHvmHeaderConsensus after finish must walk the deferred gap M+1..N forward to N.
	chain.hvmSnapMarkFinished()
	require.False(t, chain.isAwaitingHvmSnapSync())
	require.NoError(t, chain.updateHvmHeaderConsensus(blockN.Header(), false), "after snap finish the deferred gap must be walked forward")
	sidN, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sidN[:], "post-snap resumption must land the state-id on N (gap M+1..N caught up)")
}

// Snap completion, end-to-end: the runHvmSnapWaiter HAPPY PATH — the detached goroutine that waits for the
// full TBC node to hold all Bitcoin blocks for a snap-sync candidate tip and then COMPLETES the sync (reset the
// lightweight view -> walk the full node back to genesis -> AddExternalHeaders -> updateFullTBCToLightweight ->
// SetSafe/SetFinalized -> mark finished) — had no coverage. Existing snap tests cover only the decomposed pieces
// (latch lifecycle, claim-once, abort-on-quit, noop-when-not-awaiting, the pure helpers) and the build-path prefetch
// gate is covered in core/vm; none drive the completion body, because it needs a REAL indexed full node holding real
// blocks. With the synthetic full node we can: arm the latch, feed a full node a synthetic regtest chain, pin an hVM
// base whose body is on local disk, call SnapSyncHvm, and assert the waiter reconstructs the lightweight view to the
// BTC tip and finishes.
//
// vm's synthetic full-node harness lives in a core/vm test file (not importable here), so this replicates it via the
// EXPORTED vm symbols (vm.SetupTBCFullNode + the vm.TBC* package vars). vm.tbcChainParams is unexported and set
// internally to regtest by SetupTBCFullNode; it cannot be restored from package core, but no core test reads it and
// the core/vm tests run in a separate test binary, so the residual is benign.
// setupCoreSyntheticFullNode stands up a real indexed tbc.Server (localnet/regtest, no P2P, no listeners, fresh temp
// leveldb) via the production vm.SetupTBCFullNode choke point and saves/restores the exported vm globals it mutates.
// Not parallel-safe (shared package globals). Mirrors core/vm's setupSyntheticFullNode.
func setupCoreSyntheticFullNode(t *testing.T) {
	t.Helper()

	prevNode, prevCfg, prevCtx := vm.TBCFullNode, vm.TBCFullNodeConfig, vm.MainCtx
	prevCancel, prevUpstream := vm.TBCFullNodeCtxCancel, vm.TBCUpstreamTip

	ctx, cancel := context.WithCancel(context.Background())

	cfg := tbc.NewDefaultConfig()
	cfg.Network = "localnet"
	cfg.LevelDBHome = t.TempDir()
	cfg.PeersWanted = 0
	cfg.ListenAddress = ""
	cfg.PrometheusListenAddress = ""
	cfg.PprofListenAddress = ""
	cfg.AutoIndex = false
	cfg.MempoolEnabled = false
	// MaxCachedTxs stays at the NewDefaultConfig default (1e6); the UTXO indexer divides by it.

	require.NoError(t, vm.SetupTBCFullNode(ctx, cfg))

	t.Cleanup(func() {
		if vm.TBCFullNodeCtxCancel != nil {
			vm.TBCFullNodeCtxCancel()
		}
		cancel()
		deadline := time.Now().Add(5 * time.Second)
		for vm.TBCFullNode != nil && vm.TBCFullNode.Running() && time.Now().Before(deadline) {
			time.Sleep(10 * time.Millisecond)
		}
		vm.TBCFullNode, vm.TBCFullNodeConfig, vm.MainCtx = prevNode, prevCfg, prevCtx
		vm.TBCFullNodeCtxCancel, vm.TBCUpstreamTip = prevCancel, prevUpstream
	})

	require.Eventually(t, func() bool {
		if vm.TBCFullNode == nil || !vm.TBCFullNode.Running() {
			return false
		}
		_, _, err := vm.TBCFullNode.BlockHeaderBest(vm.MainCtx)
		return err == nil
	}, 30*time.Second, 10*time.Millisecond, "full node must open its DB and insert the regtest genesis")
}

// mineCoreRegtestFullBlock builds a complete synthetic regtest block (BIP34 coinbase paying value to pkScript, correct
// merkle root, header mined to the regtest PowLimit). Mirrors core/vm's mineRegtestFullBlock.
func mineCoreRegtestFullBlock(t *testing.T, prev *wire.BlockHeader, bip34Height int32, pkScript []byte, value int64, extraNonce uint32) *wire.MsgBlock {
	t.Helper()
	cb := wire.NewMsgTx(wire.TxVersion)
	sig, err := txscript.NewScriptBuilder().AddInt64(int64(bip34Height)).AddInt64(int64(extraNonce)).Script()
	require.NoError(t, err)
	cb.AddTxIn(&wire.TxIn{
		PreviousOutPoint: wire.OutPoint{Hash: chainhash.Hash{}, Index: 0xffffffff},
		SignatureScript:  sig,
		Sequence:         0xffffffff,
	})
	cb.AddTxOut(&wire.TxOut{Value: value, PkScript: pkScript})

	merkles := blockchain.BuildMerkleTreeStore([]*btcutil.Tx{btcutil.NewTx(cb)}, false)
	hdr := wire.BlockHeader{
		Version:    4,
		PrevBlock:  prev.BlockHash(),
		MerkleRoot: *merkles[len(merkles)-1],
		Timestamp:  prev.Timestamp.Add(60 * time.Second),
		Bits:       uint32(0x207fffff), // chaincfg.RegressionNetParams.PowLimitBits
	}
	target := blockchain.CompactToBig(hdr.Bits)
	mined := false
	for i := uint32(0); i < 1<<22; i++ {
		hdr.Nonce = extraNonce + i
		hh := hdr.BlockHash()
		if blockchain.HashToBig(&hh).Cmp(target) <= 0 {
			mined = true
			break
		}
	}
	require.True(t, mined, "must mine a regtest full block within 2^22 nonces")
	return &wire.MsgBlock{Header: hdr, Transactions: []*wire.MsgTx{cb}}
}

// TestRunHvmSnapWaiterEndToEnd drives the full snap-sync completion path. It arms the snap latch, feeds the full node a
// 3-block synthetic regtest chain (headers + blocks, intentionally NOT pre-indexed so completion does the indexing),
// pins the hVM base to the L2 genesis (whose body is on disk), and calls SnapSyncHvm. The detached waiter must find
// all BTC data available on its first poll, claim completion, reset the lightweight view, bulk-load the headers up to
// the BTC tip, index the full node, set safe/finalized, and mark finished.
func TestRunHvmSnapWaiterEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real indexed TBC full node plus a lightweight node on disk")
	}

	now := uint64(time.Now().Unix())
	hvm0Time := now - 10_000 // IsHvm0(now) true
	// Order matters for teardown: set up the full node FIRST, the chain SECOND, so (t.Cleanup is LIFO) chain.Stop —
	// which joins the detached waiter via hvmSnapWg.Wait — runs BEFORE the full node is cancelled/nil'd. Otherwise a
	// require.Eventually timeout or a mid-test failure would tear down vm.TBCFullNode while the waiter still derefs it
	// (data race + nil-deref that masks the real failure).
	setupCoreSyntheticFullNode(t)
	chain, btcGenesis := newRegtestChainWithLightTBC(t, hvm0Time)

	// A deterministic regtest P2PKH script for the coinbases.
	pkh := bytes.Repeat([]byte{0x42}, 20)
	addr, err := btcutil.NewAddressPubKeyHash(pkh, &chaincfg.RegressionNetParams)
	require.NoError(t, err)
	pkScript, err := txscript.PayToAddrScript(addr)
	require.NoError(t, err)

	// Build BTC chain genesis -> b1 -> b2 -> b3, feed the full node (headers + blocks only; the completion path
	// indexes it via updateFullTBCToLightweight).
	const n = 3
	prev := btcGenesis
	blocks := make([]*wire.MsgBlock, 0, n)
	headers := make([]*wire.BlockHeader, 0, n)
	for i := 0; i < n; i++ {
		blk := mineCoreRegtestFullBlock(t, prev, int32(i+1), pkScript, int64(50*1e8), uint32(i)*100_000+1)
		blocks = append(blocks, blk)
		h := blk.Header
		headers = append(headers, &h)
		prev = &blocks[i].Header
	}
	_, _, _, count, err := vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, &wire.MsgHeaders{Headers: headers})
	require.NoError(t, err)
	require.Equal(t, n, count)
	for i, b := range blocks {
		_, err = vm.TBCFullNode.BlockInsert(vm.MainCtx, b)
		require.NoError(t, err, "block %d must insert", i+1)
	}
	btcTip := blocks[n-1].Header.BlockHash()

	// Arm the latch (the gate claimHvmSnapWaiterSlot checks) and pin an hVM base whose FULL block is on local disk:
	// the L2 genesis. The waiter probes this via GetBlockByHash and refuses to complete on a base whose body is absent.
	chain.hvmSnapMu.Lock()
	chain.awaitingHvmSnapSync = true
	chain.hvmSnapMu.Unlock()
	hvmTip := chain.Genesis().Header()
	require.NotNil(t, chain.GetBlockByHash(hvmTip.Hash()), "the pinned hVM base block must be present on disk")

	// Kick off the detached waiter. All BTC data is already available, so it completes without waiting.
	quit := make(chan struct{})
	chain.SnapSyncHvm(&btcTip, hvmTip, quit)

	require.Eventually(t, chain.HvmSnapSyncCompleted, 30*time.Second, 20*time.Millisecond,
		"the snap waiter must complete when all BTC data is available and the hVM base body is on disk")

	// --- Assert the completion's observable effects ---

	// The lightweight view was reset and bulk-loaded up to the snap BTC tip.
	_, lightTip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, btcTip, lightTip.BlockHash(), "the lightweight canonical tip must be the snap BTC tip after completion")

	// The full node was indexed and the upstream tip recorded as the lightweight tip.
	require.NotNil(t, vm.TBCUpstreamTip, "completion must record the upstream tip")
	require.Equal(t, btcTip, vm.TBCUpstreamTip.BlockHash(), "TBCUpstreamTip must be the lightweight tip after completion")

	// The full node's UTXO/Tx indexers — completion's core consensus output — must actually have ADVANCED off genesis
	// to (lightweight tip - hVMIndexerTipLag). With a 3-block chain and lag 2 that is block 1 (height 1). Asserting
	// this (not just the header tip / upstream pointer, which are set independently of indexing progress) is what
	// catches a regression turning updateFullTBCToLightweight's SyncIndexersToHash into a successful no-op.
	require.Equal(t, 2, hVMIndexerTipLag, "this test's expected indexed tip assumes lag==2; if the consensus constant changes, revisit the n-1-lag arithmetic below")
	wantIndexed := blocks[n-1-hVMIndexerTipLag].Header.BlockHash() // btcTip walked back lag blocks = block 1
	genesisHash := btcGenesis.BlockHash()
	si := vm.TBCFullNode.Synced(vm.MainCtx)
	require.Equal(t, wantIndexed, si.Utxo.Hash, "the UTXO indexer must advance to (tip - lag), not stay at genesis")
	require.Equal(t, wantIndexed, si.Tx.Hash, "the Tx indexer must advance to (tip - lag), not stay at genesis")
	require.NotEqual(t, genesisHash, si.Utxo.Hash, "the indexers must not have stayed at the regtest genesis")

	// Safe and finalized advanced to the pinned hVM base.
	require.Equal(t, hvmTip.Hash(), chain.CurrentSafeBlock().Hash(), "completion must set safe to the hVM snap base")
	require.Equal(t, hvmTip.Hash(), chain.CurrentFinalBlock().Hash(), "completion must set finalized to the hVM snap base")

	// The latch is finished and the waiter slot released (so Stop's hvmSnapWg.Wait returns).
	require.True(t, chain.HvmSnapSyncCompleted())
	require.False(t, chain.isAwaitingHvmSnapSync(), "a finished snap sync must clear the awaiting latch")
}

// TestRunHvmSnapWaiterRefusesBodyAbsentBase exercises the snap path's primary anti-corruption gate: the waiter must
// REFUSE to complete when the pinned hVM base block's body is not on local disk (the `else if GetBlockByHash(...) == nil`
// branch in runHvmSnapWaiter). Completing on a body-absent base would persist an unreachable upstream-state-id and
// permanently fail the post-snap reconciliation walk on every restart. The happy-path test always pins a body-PRESENT
// base, so deleting the gate survives it; this drives the gate with all BTC data available but a fabricated, not-on-disk
// hVM base and asserts the waiter never completes and the latch stays armed.
func TestRunHvmSnapWaiterRefusesBodyAbsentBase(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real indexed TBC full node plus a lightweight node on disk")
	}

	now := uint64(time.Now().Unix())
	hvm0Time := now - 10_000
	setupCoreSyntheticFullNode(t) // full node first so chain.Stop joins the waiter before the node is torn down
	chain, btcGenesis := newRegtestChainWithLightTBC(t, hvm0Time)

	pkh := bytes.Repeat([]byte{0x42}, 20)
	addr, err := btcutil.NewAddressPubKeyHash(pkh, &chaincfg.RegressionNetParams)
	require.NoError(t, err)
	pkScript, err := txscript.PayToAddrScript(addr)
	require.NoError(t, err)

	// Feed a 3-block chain so ALL BTC data is available — the waiter must reach the body-absent gate, not stall on
	// missing BTC data.
	const n = 3
	prev := btcGenesis
	blocks := make([]*wire.MsgBlock, 0, n)
	headers := make([]*wire.BlockHeader, 0, n)
	for i := 0; i < n; i++ {
		blk := mineCoreRegtestFullBlock(t, prev, int32(i+1), pkScript, int64(50*1e8), uint32(i)*100_000+1)
		blocks = append(blocks, blk)
		h := blk.Header
		headers = append(headers, &h)
		prev = &blocks[i].Header
	}
	_, _, _, _, err = vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, &wire.MsgHeaders{Headers: headers})
	require.NoError(t, err)
	for _, b := range blocks {
		_, err = vm.TBCFullNode.BlockInsert(vm.MainCtx, b)
		require.NoError(t, err)
	}
	btcTip := blocks[n-1].Header.BlockHash()

	chain.hvmSnapMu.Lock()
	chain.awaitingHvmSnapSync = true
	chain.hvmSnapMu.Unlock()

	// Pin the hVM base to a FABRICATED header whose block is NOT on local disk.
	hvmTip := &types.Header{Number: big.NewInt(999_999), Time: 1, Extra: []byte("synthetic-not-on-disk")}
	require.Nil(t, chain.GetBlockByHash(hvmTip.Hash()), "the fabricated hVM base block must NOT be present on disk")

	quit := make(chan struct{})
	chain.SnapSyncHvm(&btcTip, hvmTip, quit)

	// All BTC data is available, but the base body is absent -> the gate must keep the waiter from ever completing.
	require.Never(t, chain.HvmSnapSyncCompleted, 2500*time.Millisecond, 100*time.Millisecond,
		"the waiter must refuse to complete snap sync on a base whose block body is not on disk")
	require.True(t, chain.isAwaitingHvmSnapSync(), "the latch stays armed while the body-absent base blocks completion")

	// The waiter must still HOLD its slot — not give up and release it — within this window. The give-up horizon
	// (maxHvmSnapBodyAbsentPolls polls x ~1s) is far beyond 2.5s, so a correct waiter keeps the slot the whole time.
	// This is the assertion that actually discriminates an early-give-up mutation (which awaitingHvmSnapSync, cleared
	// only by completion, does NOT reflect: give-up releases the slot but leaves the latch armed).
	chain.hvmSnapMu.Lock()
	nWaiters := len(chain.hvmSnapWaiters)
	chain.hvmSnapMu.Unlock()
	require.Equal(t, 1, nWaiters, "the body-absent waiter must keep WAITING (slot held), not give up and release within the window")
}

// TestUpdateFullTBCToLightweightMissingData drives updateFullTBCToLightweight's !available orchestration — the
// missing-full-block and missing-header arms (blockchain.go:4247-4326), home of the back-walk nil-guard and the
// best-effort header re-injection. The happy-path snap test always feeds ALL data so available==true and this
// whole block is skipped; here the lightweight view leads the full node so the deferral arms run. (TBCAttemptBlockRefetch
// returns promptly with PeersWanted=0 — pm.Random() yields ErrNoConnectedPeers immediately — so this is in-process.)
func TestUpdateFullTBCToLightweightMissingData(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real indexed TBC full node plus a lightweight node on disk")
	}
	hvm0Time := uint64(time.Now().Unix()) - 10_000
	pkh := bytes.Repeat([]byte{0x42}, 20)
	addr, err := btcutil.NewAddressPubKeyHash(pkh, &chaincfg.RegressionNetParams)
	require.NoError(t, err)
	pkScript, err := txscript.PayToAddrScript(addr)
	require.NoError(t, err)

	build5 := func(t *testing.T, genesis *wire.BlockHeader) ([]*wire.MsgBlock, []*wire.BlockHeader) {
		blocks := make([]*wire.MsgBlock, 0, 5)
		hdrs := make([]*wire.BlockHeader, 0, 5)
		prev := genesis
		for i := 0; i < 5; i++ {
			blk := mineCoreRegtestFullBlock(t, prev, int32(i+1), pkScript, int64(50*1e8), uint32(i)*100_000+1)
			blocks = append(blocks, blk)
			h := blk.Header
			hdrs = append(hdrs, &h)
			prev = &blocks[i].Header
		}
		return blocks, hdrs
	}

	// missing-FULL-BLOCK arm: full node has all 5 headers but a HOLE in the blocks (h2 withheld) on the walk-back path
	// to (lightTip - lag) = h3 -> ErrFullTBCMissingFullBTCBlock.
	t.Run("missing-full-block", func(t *testing.T) {
		setupCoreSyntheticFullNode(t)
		chain, btcGenesis := newRegtestChainWithLightTBC(t, hvm0Time)
		blocks, hdrs := build5(t, btcGenesis)
		_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: hdrs}, hVMGenesisUpstreamId[:])
		require.NoError(t, err)
		_, _, _, _, err = vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, &wire.MsgHeaders{Headers: hdrs})
		require.NoError(t, err)
		for i, b := range blocks {
			if i == 1 {
				continue // withhold h2's full block
			}
			_, err = vm.TBCFullNode.BlockInsert(vm.MainCtx, b)
			require.NoError(t, err)
		}
		require.ErrorIs(t, chain.updateFullTBCToLightweight(), consensus.ErrFullTBCMissingFullBTCBlock,
			"a hole in the full blocks on the path to (lightTip-lag) must defer with the missing-full-block sentinel")
	})

	// missing-HEADER arm: full node has only h1 (h2..h5 headers absent), so the walk-back target h3 is unknown ->
	// the back-walk (the :4276 region) runs, re-injects the absent headers, and returns ErrFullTBCMissingBTCHeader
	// without panicking.
	t.Run("missing-header", func(t *testing.T) {
		setupCoreSyntheticFullNode(t)
		chain, btcGenesis := newRegtestChainWithLightTBC(t, hvm0Time)
		blocks, hdrs := build5(t, btcGenesis)
		_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: hdrs}, hVMGenesisUpstreamId[:])
		require.NoError(t, err)
		_, _, _, _, err = vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, &wire.MsgHeaders{Headers: hdrs[:1]})
		require.NoError(t, err)
		_, err = vm.TBCFullNode.BlockInsert(vm.MainCtx, blocks[0])
		require.NoError(t, err)
		var ufErr error
		require.NotPanics(t, func() { ufErr = chain.updateFullTBCToLightweight() }, "the missing-header back-walk must not panic")
		require.ErrorIs(t, ufErr, consensus.ErrFullTBCMissingBTCHeader,
			"an absent walk-back-target header in the full node must defer with the missing-header sentinel")
	})
}

// TestRunHvmSnapWaiterBodyAbsentGivesUp drives the body-absent GIVE-UP / slot-release path (blockchain.go:2038-2047),
// the documented anti-wedge defense. The default ~100-poll horizon is far beyond any test window, so it is lowered via
// the test-only hvmSnapBodyAbsentPollsLimit. With all BTC data available but the hVM base body absent, the waiter must
// eventually GIVE UP and release its slot — while NOT completing and leaving the latch armed (only completion clears it).
// The sibling TestRunHvmSnapWaiterRefusesBodyAbsentBase asserts the opposite (slot HELD) within its short window; this
// pins that the give-up `return` actually fires and frees the slot — a deletion of it survives that sibling test.
func TestRunHvmSnapWaiterBodyAbsentGivesUp(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real indexed TBC full node plus a lightweight node on disk")
	}
	hvm0Time := uint64(time.Now().Unix()) - 10_000
	setupCoreSyntheticFullNode(t)
	chain, btcGenesis := newRegtestChainWithLightTBC(t, hvm0Time)
	chain.hvmSnapBodyAbsentPollsLimit = 2 // lower the give-up horizon to ~2 polls so the release path is reachable

	pkh := bytes.Repeat([]byte{0x42}, 20)
	addr, err := btcutil.NewAddressPubKeyHash(pkh, &chaincfg.RegressionNetParams)
	require.NoError(t, err)
	pkScript, err := txscript.PayToAddrScript(addr)
	require.NoError(t, err)
	prev := btcGenesis
	blocks := make([]*wire.MsgBlock, 0, 3)
	headers := make([]*wire.BlockHeader, 0, 3)
	for i := 0; i < 3; i++ {
		blk := mineCoreRegtestFullBlock(t, prev, int32(i+1), pkScript, int64(50*1e8), uint32(i)*100_000+1)
		blocks = append(blocks, blk)
		h := blk.Header
		headers = append(headers, &h)
		prev = &blocks[i].Header
	}
	_, _, _, _, err = vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, &wire.MsgHeaders{Headers: headers})
	require.NoError(t, err)
	for _, b := range blocks {
		_, err = vm.TBCFullNode.BlockInsert(vm.MainCtx, b)
		require.NoError(t, err)
	}
	btcTip := blocks[2].Header.BlockHash()

	chain.hvmSnapMu.Lock()
	chain.awaitingHvmSnapSync = true
	chain.hvmSnapMu.Unlock()
	hvmTip := &types.Header{Number: big.NewInt(999_999), Time: 1, Extra: []byte("synthetic-not-on-disk")}
	require.Nil(t, chain.GetBlockByHash(hvmTip.Hash()))

	chain.SnapSyncHvm(&btcTip, hvmTip, make(chan struct{}))

	// The waiter must GIVE UP (release its slot) once the lowered horizon is hit.
	require.Eventually(t, func() bool {
		chain.hvmSnapMu.Lock()
		n := len(chain.hvmSnapWaiters)
		chain.hvmSnapMu.Unlock()
		return n == 0
	}, 15*time.Second, 100*time.Millisecond, "the body-absent waiter must give up and RELEASE its slot at the poll horizon")
	require.False(t, chain.HvmSnapSyncCompleted(), "giving up must NOT complete the snap sync")
	require.True(t, chain.isAwaitingHvmSnapSync(), "give-up releases the slot but leaves the latch armed (only completion clears it)")
}

// SnapSyncHvm's observe-only difficulty check NEVER halts (by design) — its ONLY externally-visible effect is
// marking an alert meter when a malicious/corrupt full node serves a forged snap base. That meter mark is the
// GUARDED ACTION, yet every snap-observe test asserts only the obs struct returned by observeSnapBtcDiff, never that
// the caller's dispatch actually marks the meter (the symmetric MIGRATION dispatch IS covered end-to-end). A mutant
// dropping hvmSnapBtcDiffRejectMeter.Mark / mis-mapping the switch / inverting the powFailed branch would silently
// disable the snap safety net while the whole suite stayed green. markSnapBtcDiffObservation is the extracted
// dispatch; this pins the meters fire on exactly their reject arms and stay silent on clean/skip/below-floor.
func TestMarkSnapBtcDiffObservation(t *testing.T) {
	bc := &BlockChain{tbcHeaderNodeConfig: &tbc.Config{Network: "localnet", GenesisHeightOffset: 0}}

	cases := []struct {
		name      string
		obs       snapObserveResult
		powDelta  int64
		diffDelta int64
	}{
		{"pow-failed", snapObserveResult{powFailed: true, powErr: errors.New("bad pow")}, 1, 0},
		{"ctx-reject", snapObserveResult{contextualRan: true, ctxObservation: snapObsReject, ctxErr: errors.New("bad diff")}, 0, 1},
		{"pow-and-ctx-reject", snapObserveResult{powFailed: true, contextualRan: true, ctxObservation: snapObsReject}, 1, 1},
		{"ctx-clean", snapObserveResult{contextualRan: true, ctxObservation: snapObsClean}, 0, 0},
		{"ctx-incomplete", snapObserveResult{contextualRan: true, ctxObservation: snapObsIncomplete, ctxErr: errors.New("gap")}, 0, 0},
		{"ctx-below-floor", snapObserveResult{contextualRan: true, ctxObservation: snapObsBelowFloor}, 0, 0},
		{"contextual-did-not-run", snapObserveResult{contextualRan: false}, 0, 0},
		{"clearance-err-skip", snapObserveResult{clearanceErr: errors.New("unknown net")}, 0, 0},
		{"first-height-err-skip", snapObserveResult{firstHeightErr: errors.New("read")}, 0, 0},
		// A reject verdict that the contextual validator NEVER RAN must not fire the btcdiff-reject meter (the meter
		// is gated on contextualRan, not merely on ctxObservation): kills a mutant dropping the contextualRan guard.
		{"ctx-reject-but-not-ran", snapObserveResult{contextualRan: false, ctxObservation: snapObsReject, ctxErr: errors.New("bad diff")}, 0, 0},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			powBefore := hvmSnapPoWRejectMeter.Snapshot().Count()
			diffBefore := hvmSnapBtcDiffRejectMeter.Snapshot().Count()
			bc.markSnapBtcDiffObservation(tc.obs, "abc123")
			require.Equal(t, tc.powDelta, hvmSnapPoWRejectMeter.Snapshot().Count()-powBefore, "PoW-reject meter delta")
			require.Equal(t, tc.diffDelta, hvmSnapBtcDiffRejectMeter.Snapshot().Count()-diffBefore, "BtcDiff-reject meter delta")
		})
	}
}

// observeSnapBtcDiff (the snap-sync AND migration bulk-load observe-only difficulty check) routed through a REAL
// retarget-boundary computation. The regtest harness that covers observeSnapBtcDiff (TestObserveSnapBtcDiffDispatch)
// is PoWNoRetargeting, so it structurally cannot exercise a retarget-difficulty rejection — the one place the
// migration/snap observe surface computes a 2016-block retarget. This pins that a wrong difficulty AT a real
// mainnet retarget boundary, fed through observeSnapBtcDiff, classifies as the alertable snapObsReject (never a
// skip/incomplete). Corpus-free: synthetic headers spanning only the boundary's 2016 ancestors (no real chaindata).
func TestObserveSnapBtcDiffRejectsRetargetBoundaryViolation(t *testing.T) {
	if testing.Short() {
		t.Skip("builds the boundary's 2016-header ancestry")
	}
	const mainBits = uint32(0x1d00ffff)  // mainnet PowLimitBits; the boundary retarget recomputes a different value
	const genesisOffset = uint64(883092) // mainnet hVM genesis height -> positions the enforce floor (~885119)
	const boundary = uint64(887040)      // 440*2016, the first retarget boundary above the enforce floor
	const startH = boundary - 2016       // 885024: contiguous ancestors for the 2015-hop retarget walk + MTP

	// A contiguous synthetic chain [startH .. boundary] at 10-min spacing. The boundary header carries the
	// inherited mainBits, but a retarget at 887040 recomputes a (harder) expected difficulty -> mismatch.
	f := &fakeBtcLookup{byHash: map[chainhash.Hash]*wire.BlockHeader{}, height: map[chainhash.Hash]uint64{}}
	base := int64(1_600_000_000)
	var prev chainhash.Hash
	var boundaryHdr *wire.BlockHeader
	for h := startH; h <= boundary; h++ {
		hdr := &wire.BlockHeader{
			Version:   1,
			PrevBlock: prev,
			Bits:      mainBits,
			Timestamp: time.Unix(base+int64(h-startH)*600, 0),
			Nonce:     uint32(h),
		}
		hh := hdr.BlockHash()
		f.byHash[hh] = hdr
		f.height[hh] = h
		if h == boundary {
			boundaryHdr = hdr
		}
		prev = hh
	}

	obs := observeSnapBtcDiff(context.Background(), f, "mainnet", genesisOffset, []*wire.BlockHeader{boundaryHdr})

	require.True(t, obs.contextualRan, "the above-floor boundary header must be contextually validated (not deferred)")
	require.Equal(t, 1, obs.enforcedCount, "the boundary header is above the enforce floor -> enforced")
	require.Equal(t, 1, obs.enforcedCount+obs.deferredCount, "every header is either enforced or deferred; a single above-floor header must leave 0 deferred")
	require.Equal(t, snapObsReject, obs.ctxObservation,
		"a wrong difficulty at a real retarget boundary must classify as the alertable reject verdict")
	// Specifically a difficulty rejection (the retarget computation ran), not a timestamp/version or skip verdict.
	var re blockchain.RuleError
	require.ErrorAs(t, obs.ctxErr, &re, "the rejection must be a btcd RuleError")
	require.Equal(t, blockchain.ErrUnexpectedDifficulty, re.ErrorCode,
		"the retarget recomputation must produce ErrUnexpectedDifficulty (proving the boundary math ran)")
}

// Integration coverage for SnapSyncHvm's observe-only verdict-dispatch composition. The consensus-relevant
// part — the contextual-difficulty check (PoW + above-floor suffix split + contextual validate + verdict
// classification) — lives in observeSnapBtcDiff, which takes any vm.BTCHeaderLookup. This test drives it
// against a real regtest lightweight TBC node (the same store SnapSyncHvm reconstructs into).
//
// SnapSyncHvm's full end-to-end path needs a live, block-indexed full TBC node, so these parts are not covered
// here: the block-availability wait/refetch loop, the walk-back that builds headersToAdd, and
// updateFullTBCToLightweight. SnapSyncHvm's AddExternalHeaders-into-the-lightweight-node + canonical-tip
// section is not full-node-bound and is covered by TestHvmApplyPathRollsBackOnWrongCanonicalTipRegtest.
// buildAndSeedRegtestChain mines `total` contiguous regtest headers off `genesis` and adds them to the
// lightweight node (so they are resolvable as the snap base's ancestry). The header at badIdx (if >= 0) is
// mined with badBits instead of regtestPowBits — a correct-PoW-but-wrong-difficulty header (regtest is
// PoWNoRetargeting, so the contextual rule expects regtestPowBits). Returns the header list (heights 1..N,
// since regtest genesis is height 0 / GenesisHeightOffset 0 in this harness).
func buildAndSeedRegtestChain(t *testing.T, chain *BlockChain, genesis *wire.BlockHeader, total, badIdx int, badBits uint32) []*wire.BlockHeader {
	t.Helper()
	hdrs := make([]*wire.BlockHeader, 0, total)
	prev := genesis
	for i := 0; i < total; i++ {
		var h *wire.BlockHeader
		if i == badIdx {
			h = mineRegtestChildBits(t, prev, badBits, uint32(i)*7+1)
		} else {
			h = mineRegtestChild(t, prev, uint32(i)*7+1)
		}
		hdrs = append(hdrs, h)
		prev = h
	}
	for start := 0; start < len(hdrs); start += 1000 {
		end := start + 1000
		if end > len(hdrs) {
			end = len(hdrs)
		}
		last := hdrs[end-1].BlockHash()
		_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: hdrs[start:end]}, last[:])
		require.NoError(t, err, "seeding regtest chain chunk [%d:%d]", start, end)
	}
	return hdrs
}

// TestObserveSnapBtcDiffDispatch drives the extracted observe-only contextual-difficulty composition against a real
// regtest lightweight TBC node — the verdict-dispatch SnapSyncHvm runs on its reconstructed base. Pins: a
// clean base reports clean (no alert), a wrong-difficulty above-floor header is snapObsReject (alertable
// but the function still returns, never halts), a forged-PoW header sets powFailed, an unknown network
// skips the contextual check, and the enforce/defer split is exercised (deferred near-floor headers).
func TestObserveSnapBtcDiffDispatch(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers into a real lightweight TBC node")
	}
	// regtest enforce floor = btcSnapEnforceFloor(0, floorClearance(regtest)). The chain must clear it so a
	// suffix is enforceable while near-floor headers are deferred.
	clearance, err := vm.BTCFloorClearanceForNetwork("localnet")
	require.NoError(t, err)
	enforceFloor := btcSnapEnforceFloor(0, clearance)
	total := int(enforceFloor) + 16 // a handful of enforceable headers above the floor + the deferred band below

	t.Run("clean base -> snapObsClean, no alert, enforce/defer split", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		hdrs := buildAndSeedRegtestChain(t, chain, genesis, total, -1, 0)

		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, hdrs)
		require.False(t, obs.powFailed, "a fully-mined base must not flag PoW")
		require.NoError(t, obs.clearanceErr)
		require.NoError(t, obs.firstHeightErr)
		require.False(t, obs.firstHeightMismatch, "headers[0] is genesis+1 (height 1 == offset 0 + 1)")
		require.True(t, obs.contextualRan, "an above-floor suffix must be enforced")
		require.Equal(t, snapObsClean, obs.ctxObservation, "a correct-difficulty regtest base is contextually clean")
		require.Greater(t, obs.enforcedCount, 0, "some headers are above the enforce floor")
		require.Greater(t, obs.deferredCount, 0, "the near-floor band is deferred, not checked")
		require.Equal(t, len(hdrs), obs.enforcedCount+obs.deferredCount, "every header is either enforced or deferred")
	})

	t.Run("all headers below enforce floor -> benign empty suffix, NOT a skip", func(t *testing.T) {
		// A short base entirely within the deferred near-floor band: enforceable suffix is empty, so contextualRan
		// is false WITHOUT any skip error (clearanceErr/firstHeightErr nil). The migration observe switch's
		// benign-empty arm keys on exactly this shape, distinct from a genuine skipped check. If
		// clearanceErr/firstHeightErr were set here the migration would misroute to the misleading SKIPPED warn.
		belowFloor := int(enforceFloor) - 1
		if belowFloor < 1 {
			t.Skip("enforce floor too low on this network to construct an all-below-floor base")
		}
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		hdrs := buildAndSeedRegtestChain(t, chain, genesis, belowFloor, -1, 0)
		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, hdrs)
		require.NoError(t, obs.clearanceErr, "an all-below-floor base is NOT a skipped check (clearance resolved)")
		require.NoError(t, obs.firstHeightErr, "the first header is resolvable")
		require.False(t, obs.contextualRan, "no above-floor suffix -> the contextual validator does not run")
		require.Equal(t, 0, obs.enforcedCount, "nothing is enforceable below the floor")
		require.Equal(t, len(hdrs), obs.deferredCount, "every header is deferred (the benign empty-suffix case)")
	})

	t.Run("walk not starting at genesis+1 -> firstHeightMismatch (the TRUE direction)", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		hdrs := buildAndSeedRegtestChain(t, chain, genesis, total, -1, 0)
		// Drop headers[0] so the slice now starts at the height-2 header (still resolvable in the lightweight node,
		// so firstHeightErr stays nil). firstHeight (2) != genesisOffset(0)+1, so the genesis+1 tripwire must fire.
		// This exercises the TRUE direction of the walk-start tripwire on both the snap and migration bulk-load paths.
		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, hdrs[1:])
		require.NoError(t, obs.firstHeightErr, "the first header (height 2) is resolvable, so the height read must succeed")
		require.True(t, obs.firstHeightMismatch, "a walk starting at height 2 (not genesisOffset+1==1) must set firstHeightMismatch")
		require.Equal(t, uint64(2), obs.firstHeight, "the observed first height is 2")
	})

	t.Run("wrong-difficulty header above floor -> snapObsReject (alertable, NEVER halts)", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		// A wrong (slightly harder) difficulty header well above the enforce floor: PoW still passes (target
		// barely below PowLimit -> minable), but Bits != regtestPowBits -> ErrUnexpectedDifficulty.
		badIdx := int(enforceFloor) + 4
		hdrs := buildAndSeedRegtestChain(t, chain, genesis, total, badIdx, 0x207ffffe)

		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, hdrs)
		require.False(t, obs.powFailed, "the wrong-difficulty header is still validly mined (PoW must pass) — isolates the contextual reject")
		require.True(t, obs.contextualRan)
		require.Equal(t, snapObsReject, obs.ctxObservation, "a wrong-difficulty above-floor header must be the alertable reject verdict")
		// The point of observe-only: it RETURNS (no panic / no halt). Reaching here is the assertion.
	})

	t.Run("PoW-failing header -> powFailed set (does not halt)", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		// An unmined header (correct Bits, but a nonce whose hash exceeds the target). Passed as a one-element
		// base; headers[0] is not in the lookup so the contextual check is skipped via firstHeightErr, which
		// isolates the PoW arm (the PoW check runs over the passed list, before the lookup).
		target := blockchain.CompactToBig(regtestPowBits)
		forged := &wire.BlockHeader{Version: 4, PrevBlock: genesis.BlockHash(), Bits: regtestPowBits, Nonce: 0}
		found := false
		for i := uint32(1); i < 1<<20; i++ {
			forged.Nonce = i
			hash := forged.BlockHash()
			if blockchain.HashToBig(&hash).Cmp(target) > 0 {
				found = true
				break
			}
		}
		require.True(t, found, "must find a PoW-failing nonce")

		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, []*wire.BlockHeader{forged})
		require.True(t, obs.powFailed, "an unmined header must flag the PoW observation")
		require.Error(t, obs.powErr)
		// Pin the firstHeightErr SKIP arm distinctly from the PoW arm: the forged header is not in the lookup,
		// so the contextual stage is skipped via firstHeightErr (NOT clearanceErr — localnet resolves params).
		require.Error(t, obs.firstHeightErr, "an absent first header must skip the contextual check via firstHeightErr")
		require.False(t, obs.contextualRan, "the contextual validator must not run when the first header is unresolvable")
		require.NoError(t, obs.clearanceErr, "localnet has params, so the SKIP here is firstHeightErr, not clearanceErr")
	})

	t.Run("unknown network -> contextual check skipped (clearanceErr), no PoW alert", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		h := mineRegtestChild(t, genesis, 1)
		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "nonsense-network", 0, []*wire.BlockHeader{h})
		require.False(t, obs.powFailed, "PoW over an unknown network returns the skip sentinel, not a failure")
		require.Error(t, obs.clearanceErr, "an unknown network has no chaincfg params -> contextual observation skipped")
		require.False(t, obs.contextualRan)
	})
}
