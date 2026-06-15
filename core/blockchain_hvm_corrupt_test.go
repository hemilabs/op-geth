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

// Corrupt-state classification of tbc.AddExternalHeaders errors on the hVM apply path.
//
// History (verified against git):
//   - Commit #31 (81478862a): errNotFound := database.NotFoundError(""), matched via errors.Is. Since
//     NotFoundError.Is matches by type, the corrupt branch was live but mapped every typed NotFound to
//     corrupt with no connectivity discriminator, so a non-connecting orphan self-heal-looped instead of
//     being rejected; and DuplicateError fell through to ErrInvalidHVMHeaders (the duplicate false-reject).
//   - The version this fix replaced (HEAD 05cff2d77): errNotFound = errors.New("not found"), a plain
//     *errorString that can never equal the TBC node's typed database.NotFoundError/DuplicateError, so the
//     corrupt branch was dead and every AddExternalHeaders error collapsed to ErrInvalidHVMHeaders,
//     false-rejecting canonical blocks (duplicate re-applies and torn stores) instead of self-healing.
// The fix uses typed errors.As matching plus a connectivity discriminator (NotFound->corrupt only when
// connectivity was confirmed, else bad-block) plus idempotent DuplicateError handling. Do not collapse it
// back to a single errors.Is(NotFoundError(...)) shortcut: that drops the discriminator and reintroduces
// the #31 orphan self-heal loop. These tests pin the typed, connectivity-aware mapping.

import (
	"context"
	"errors"
	"fmt"
	"math/big"
	"sync"
	"testing"
	"time"

	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"
	"github.com/syndtr/goleveldb/leveldb"

	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"

	"github.com/hemilabs/heminetwork/database"
)

// TestClassifyAddExternalHeadersError pins the pure consensus-binding classifier without a torn leveldb.
// Decisive cases: a database.NotFoundError maps to corrupt only when connectivity was confirmed (else bad
// block); a database.DuplicateError is always idempotent regardless of connectivity; and a plain
// errors.New("not found") — the string the dead errNotFound used — must not be laundered to corrupt,
// proving the fix matches type, not message.
func TestClassifyAddExternalHeadersError(t *testing.T) {
	cases := []struct {
		name      string
		err       error
		connected bool
		want      addExternalHeadersOutcome
	}{
		{"duplicate-bare", database.DuplicateError("block headers insert duplicate"), false, addHeadersDuplicate},
		{"duplicate-wrapped", fmt.Errorf("insert: %w", database.DuplicateError("dup")), true, addHeadersDuplicate},
		{"duplicate-ignores-connectivity", database.DuplicateError("dup"), true, addHeadersDuplicate},

		{"notfound-tip-confirmed->corrupt", database.NotFoundError("best block header not found"), true, addHeadersCorrupt},
		{"notfound-parent-wrapped-confirmed->corrupt", fmt.Errorf("block headers insert: %w", database.NotFoundError("block header not found: abc")), true, addHeadersCorrupt},

		{"notfound-not-confirmed->badblock", database.NotFoundError("block header not found: abc"), false, addHeadersBadBlock},
		{"notfound-parent-wrapped-not-confirmed->badblock", fmt.Errorf("block headers insert: %w", database.NotFoundError("x")), false, addHeadersBadBlock},

		{"intra-batch-noncontiguous->badblock", errors.New("add external headers: header with hash X does not connect to previous header"), true, addHeadersBadBlock},
		// Original-bug regression: a plain error whose string is "not found" must not be treated as corrupt
		// — only the typed database.NotFoundError is. This is why errors.Is(err, errNotFound), where
		// errNotFound was a local errors.New("not found"), was dead and collapsed everything to bad block.
		{"misleading-plain-not-found-string->badblock", errors.New("not found"), true, addHeadersBadBlock},
		// Known residual, pinned explicitly: a real leveldb/IO fault carries a typed goleveldb sentinel via
		// %w but is not a TBC NotFoundError/DuplicateError, so it maps to bad block — a node-local
		// false-reject under IO pressure (never a split, never a silent accept). A future leveldb-sentinel
		// discriminator would change this expectation.
		{"real-leveldb-io-fault-wrapped->badblock(residual)", fmt.Errorf("block headers insert has: %w", leveldb.ErrClosed), true, addHeadersBadBlock},
		// database.BlockNotFoundError is a distinct struct type (block-body reads), never returned by the
		// header insert path; it must not be laundered to corrupt via the NotFoundError arm.
		{"blocknotfounderror-confirmed->badblock", database.BlockNotFoundError{}, true, addHeadersBadBlock},
		{"blocknotfounderror-not-confirmed->badblock", database.BlockNotFoundError{}, false, addHeadersBadBlock},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			require.Equal(t, tc.want, classifyAddExternalHeadersError(tc.err, tc.connected),
				"classifyAddExternalHeadersError(%v, connected=%v)", tc.err, tc.connected)
		})
	}
}

// TestIsTransientAddHeadersError pins the retry-in-place gate: only the non-typed leveldb/IO fault class
// is retryable; the semantic outcomes — DuplicateError (idempotent) and the typed NotFoundError (genuine
// missing/torn, handled by classify -> bad-block/corrupt) — are not retried, and nil is not an error.
// Mirrors the typed-vs-message discipline: a plain errors.New("not found") is not the typed NotFoundError,
// so it is the retryable IO class. A reorder here would spin on a genuine bad block or fail to ride out a
// transient blip (the false-reject this fix targets).
func TestIsTransientAddHeadersError(t *testing.T) {
	// Retryable: non-typed IO/leveldb faults.
	require.True(t, isTransientAddHeadersError(errors.New("some leveldb io error")))
	require.True(t, isTransientAddHeadersError(fmt.Errorf("block headers insert: %w", leveldb.ErrClosed)),
		"a real leveldb sentinel (not a heminetwork typed error) is the transient IO class")
	require.True(t, isTransientAddHeadersError(errors.New("not found")),
		"a PLAIN 'not found' string is NOT the typed NotFoundError -> still the retryable IO class (matches by TYPE, not message)")
	require.True(t, isTransientAddHeadersError(errors.New("add external headers: header does not connect to previous header")),
		"an intra-batch non-contiguity (non-typed) is treated as the IO class for retry purposes (a retry is harmless; if persistent it still classifies bad-block)")

	// Not retryable: semantic outcomes + nil.
	require.False(t, isTransientAddHeadersError(database.DuplicateError("dup")), "DuplicateError is idempotent, not transient")
	require.False(t, isTransientAddHeadersError(fmt.Errorf("insert: %w", database.DuplicateError("dup"))), "wrapped DuplicateError")
	require.False(t, isTransientAddHeadersError(database.NotFoundError("best block header not found")), "typed NotFoundError is semantic (torn/missing)")
	require.False(t, isTransientAddHeadersError(fmt.Errorf("insert: %w", database.NotFoundError("x"))), "wrapped NotFoundError")
	require.False(t, isTransientAddHeadersError(nil), "nil is not an error")
}

// TestShouldRetryAddHeadersIO pins the gate that keeps the deterministic malformed-batch reject out of the
// retry loop: retry only when a non-typed AddExternalHeaders error can only be transient IO — i.e. the
// validator confirmed connectivity (accept / below-floor-defer), or this is restore-replay (!enforceBTCDiff,
// known-contiguous committed history). The enforcing-but-not-connectivity-confirmed case (Unconnected) is
// the deterministic contiguity reject -> must not retry.
func TestShouldRetryAddHeadersIO(t *testing.T) {
	// Forward/reorg enforcing path (enforceBTCDiff=true):
	require.True(t, shouldRetryAddHeadersIO(true, true), "validator-confirmed batch + enforcing -> a non-typed error is transient IO -> retry")
	require.False(t, shouldRetryAddHeadersIO(false, true), "enforcing + connectivity NOT confirmed (Unconnected) -> deterministic malformed reject -> NO retry")
	// Restore-replay path (enforceBTCDiff=false): contextual-difficulty validation skipped, headers known-contiguous.
	require.True(t, shouldRetryAddHeadersIO(false, false), "restore replay of known-contiguous history -> a non-typed error is transient IO -> retry")
	require.True(t, shouldRetryAddHeadersIO(true, false), "restore + (vacuously) confirmed -> retry")
}

// TestProcessBlockForWitnessRequiresChainmu pins the debug-RPC hardening: the read-only execution-witness
// RPCs (debug_executionWitness/ByHash) route through ProcessBlockForWitness, which acquires chainmu
// (chainmu.TryLock) before running ProcessBlock, so ProcessBlock's transient hVM-node mutation can no
// longer run off-lock concurrent with the import path. Per syncx.ClosableMutex semantics, TryLock blocks
// while chainmu is merely held (a witness during an in-flight import waits, race-free) and returns false
// only when the mutex is closed (chain stopping) -> errChainStopped, without reaching ProcessBlock. Pinned
// via a stopped chain (the happy path runs full ProcessBlock, covered by the witness e2e and existing
// ProcessBlock tests). Holding chainmu in-goroutine and calling the wrapper would deadlock (TryLock blocks
// on the held token); that is correct production behavior (wait), not asserted here.
func TestProcessBlockForWitnessRequiresChainmu(t *testing.T) {
	chain, _ := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	blk := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(1)})

	// Close chainmu via stopWithoutSaving, not the full Stop: it sets the stopping flag + closes chainmu and
	// is idempotent (CompareAndSwap), whereas Stop's snapshot-journaling tail is not — calling the full Stop
	// here would double-journal in the harness's cleanup Stop and hang. With chainmu closed, the wrapper's
	// TryLock returns false (not the "busy, wait" path), so it refuses with errChainStopped and never reaches
	// ProcessBlock. The harness cleanup's Stop then sees stopping already set and skips re-closing chainmu.
	chain.stopWithoutSaving()
	_, err := chain.ProcessBlockForWitness(types.EmptyRootHash, blk)
	require.ErrorIs(t, err, errChainStopped,
		"witness wrapper must consult chainmu and refuse on a stopped chain — never run ProcessBlock off-lock")
}

// TestRetryWhileTransient pins the retry loop control logic (the bound, the ctx abort, the
// re-classify-after-exhaustion handoff, and that a semantic error short-circuits) without a live TBC node,
// using stub closures. delay=0 keeps it fast. A transient error is a sentinel the stub isTransient reports
// true for; a semantic one a distinct sentinel it reports false for.
func TestRetryWhileTransient(t *testing.T) {
	transient := errors.New("transient io")
	semantic := errors.New("semantic")
	isTransient := func(e error) bool { return errors.Is(e, transient) }
	const maxRetries = 3

	t.Run("nil firstErr: no retry, returns nil", func(t *testing.T) {
		calls := 0
		err := retryWhileTransient(context.Background(), maxRetries, 0, isTransient, nil,
			func() error { calls++; return nil }, nil)
		require.NoError(t, err)
		require.Zero(t, calls, "a nil initial result must not retry")
	})

	t.Run("semantic firstErr: no retry, returns it", func(t *testing.T) {
		calls := 0
		err := retryWhileTransient(context.Background(), maxRetries, 0, isTransient, semantic,
			func() error { calls++; return nil }, nil)
		require.ErrorIs(t, err, semantic, "a semantic initial error must not be retried")
		require.Zero(t, calls)
	})

	t.Run("transient then success on first retry", func(t *testing.T) {
		calls := 0
		err := retryWhileTransient(context.Background(), maxRetries, 0, isTransient, transient,
			func() error { calls++; return nil }, nil)
		require.NoError(t, err, "a retry that succeeds clears the error")
		require.Equal(t, 1, calls, "one retry sufficed")
	})

	t.Run("transient throughout: exhausts the bound, returns the transient err", func(t *testing.T) {
		calls, retries := 0, 0
		err := retryWhileTransient(context.Background(), maxRetries, 0, isTransient, transient,
			func() error { calls++; return transient },
			func(attempt int, e error) { retries++ })
		require.ErrorIs(t, err, transient, "after the bound the final transient error is returned for classification")
		require.Equal(t, maxRetries, calls, "exactly maxRetries re-attempts")
		require.Equal(t, maxRetries, retries, "onRetry fires once per retry")
	})

	t.Run("transient then SEMANTIC on retry: stops (does not keep retrying a semantic error)", func(t *testing.T) {
		calls := 0
		err := retryWhileTransient(context.Background(), maxRetries, 0, isTransient, transient,
			func() error { calls++; return semantic }, nil)
		require.ErrorIs(t, err, semantic)
		require.Equal(t, 1, calls, "the retry produced a semantic error -> loop stops, no further retry")
	})

	t.Run("cancelled ctx: aborts before re-calling, returns the transient err", func(t *testing.T) {
		ctx, cancel := context.WithCancel(context.Background())
		cancel()
		calls := 0
		err := retryWhileTransient(ctx, maxRetries, time.Hour, isTransient, transient,
			func() error { calls++; return nil }, nil)
		require.ErrorIs(t, err, transient, "ctx cancellation returns the last error without re-attempting")
		require.Zero(t, calls, "a cancelled ctx must abort BEFORE the next call (no delay wait)")
	})
}

// TestConsensusErrorForAddHeadersOutcome pins the terminal outcome->consensus-error mapping the apply-path
// switch uses for the corrupt and bad-block arms, without a torn leveldb. Without it, a mutant flipping the
// corrupt arm's return to ErrInvalidHVMHeaders (false-rejecting a torn store) or the bad-block arm's to a
// recoverable error (self-heal loop on an invalid block) survives the integration tests, which only reach
// the duplicate and bad-block arms.
func TestConsensusErrorForAddHeadersOutcome(t *testing.T) {
	require.ErrorIs(t, consensusErrorForAddHeadersOutcome(addHeadersCorrupt), consensus.ErrCorruptHVMHeaderOnlyModeState,
		"a torn store (corrupt) must be RECOVERABLE, not a bad block")
	require.ErrorIs(t, consensusErrorForAddHeadersOutcome(addHeadersBadBlock), consensus.ErrInvalidHVMHeaders,
		"a non-connecting/malformed batch must be an INVALID block, not a recoverable corrupt state")
	// addHeadersDuplicate is handled inline (IO + returns nil on success); the mapper must fail closed to a
	// reject if ever called with it, never a silent accept (nil).
	require.ErrorIs(t, consensusErrorForAddHeadersOutcome(addHeadersDuplicate), consensus.ErrInvalidHVMHeaders,
		"the duplicate outcome must never reach the mapper, and must fail closed to a reject if it does")
}

// TestRealDuplicateErrorClassifiesAsDuplicate is a type-production tripwire on the classifier: it captures
// the actual error the real TBC node returns when re-adding an already-present header and asserts
// classifyAddExternalHeadersError maps it to addHeadersDuplicate. T_PURE only constructs
// database.DuplicateError itself (a type-definition binding), so it would stay green if the TBC node
// re-typed the all-present return. This and the light fast-lane siblings
// TestHvmApplyPathBelowFloorDuplicate{IsIdempotent,WrongCanonicalTipSelfHeals} keep that regression
// caught on the fast lane; without them only the -short-skipped heavy T_DUP_OK/T_DUP_WRONG would catch it
// and every duplicate re-apply would collapse to ErrInvalidHVMHeaders (the duplicate-header bug class). Uses the
// light harness (no >floorClearance seed) so it runs on the fast lane.
func TestRealDuplicateErrorClassifiesAsDuplicate(t *testing.T) {
	chain, lightTip := newHvmTestChainWithLightTBC(t, btcDiffTestHvm0Time)

	h := wire.BlockHeader{
		Version: lightTip.Version, PrevBlock: lightTip.BlockHash(), MerkleRoot: lightTip.MerkleRoot,
		Timestamp: lightTip.Timestamp.Add(600 * time.Second), Bits: lightTip.Bits, Nonce: 1,
	}
	last := h.BlockHash()
	_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&h}}, last[:])
	require.NoError(t, err, "first add of a header building on the effective genesis must succeed")

	// Re-add the identical header: the header insert consumes the all-duplicate prefix and
	// returns its all-present error.
	_, _, _, _, err = chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&h}}, last[:])
	require.Error(t, err, "re-adding an already-present header must return an error")
	var dup database.DuplicateError
	require.ErrorAs(t, err, &dup, "the real all-present error must still be a database.DuplicateError (type-production tripwire)")
	require.Equal(t, addHeadersDuplicate, classifyAddExternalHeadersError(err, false),
		"the REAL duplicate error must classify as addHeadersDuplicate (connectivity-independent)")
	require.Equal(t, addHeadersDuplicate, classifyAddExternalHeadersError(err, true))
}

// TestHvmApplyPathDuplicateHeadersAreIdempotent drives the end-to-end duplicate path: a block whose
// BtcAttr headers are already in the lightweight view (a post-restore retry / reorg re-apply) must be
// idempotent, not a bad block — advancing the upstream state id to the block while leaving the canonical
// tip unchanged. Pre-fix this returned ErrInvalidHVMHeaders, false-rejecting a canonical block.
func TestHvmApplyPathDuplicateHeadersAreIdempotent(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: seeds >floorClearance headers into a real lightweight TBC leveldb")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	tip := seedRegtestAboveFloor(t, chain, genesis)

	// A valid mined above-floor header extending the seeded tip (real regtest PoW, so the apply-path PoW
	// gate passes and the duplicate/idempotent arm — not a PoW reject — is exercised).
	valid := *mineRegtestChild(t, tip, 11_000)
	canon := valid.BlockHash()

	// Pre-add the header directly so the apply path's AddExternalHeaders sees an all-duplicate batch
	// (database.DuplicateError).
	last := valid.BlockHash()
	_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&valid}}, last[:])
	require.NoError(t, err, "pre-add of the header must succeed so the apply path then sees a duplicate")
	_, tipPreApply, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, valid.BlockHash(), tipPreApply.BlockHash(), "pre-add must advance the tip to the header")

	// Block N carries the same header and claims it as the canonical tip.
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, []wire.BlockHeader{valid})
	require.NoError(t, err)
	nHeader := &types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()
	// Take the "first hVM header update" branch and reset the id away from the block so the advance is observable.
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))

	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true),
		"BtcAttr headers already present must be IDEMPOTENT, not ErrInvalidHVMHeaders")

	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, valid.BlockHash(), tipAfter.BlockHash(), "duplicate apply must leave the canonical tip unchanged")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sid[:], "duplicate apply must STILL advance the upstream state id to the block")
}

// TestHvmApplyPathDuplicateWrongCanonicalTipSelfHeals pins the duplicate-path self-heal guard: when the
// BtcAttr headers are already present (DuplicateError) but the block's claimed canonical tip does not match
// the live view, the apply path must not silently accept it — it returns the recoverable
// ErrCorruptHVMHeaderOnlyModeState (self-heal) and leaves tip + state-id untouched. The sibling idempotent
// test only exercises the claim==tip branch, so without this a guard-removal mutant would silently
// false-accept a duplicate batch carrying a wrong canonical-tip claim (consensus-binding).
func TestHvmApplyPathDuplicateWrongCanonicalTipSelfHeals(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: seeds >floorClearance headers into a real lightweight TBC leveldb")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	tip := seedRegtestAboveFloor(t, chain, genesis)

	// A valid mined above-floor header (real regtest PoW so the apply path reaches the duplicate self-heal
	// guard rather than rejecting on PoW).
	valid := *mineRegtestChild(t, tip, 12_000)
	// Pre-add so the apply path sees an all-duplicate batch.
	last := valid.BlockHash()
	_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&valid}}, last[:])
	require.NoError(t, err)

	// The block carries the same (now-duplicate) header but claims the wrong canonical tip (the parent
	// `tip`, not the live tip `valid`).
	wrongClaim := tip.BlockHash()
	require.NotEqual(t, valid.BlockHash(), wrongClaim)
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&wrongClaim, []wire.BlockHeader{valid})
	require.NoError(t, err)
	nHeader := &types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))
	sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)

	// De-vacuity: the validator must accept the (already-present, valid, above-floor) header so the apply
	// path reaches AddExternalHeaders -> DuplicateError -> the curTip!=CanonicalTip self-heal guard. Without
	// this, ErrCorrupt is indistinguishable from a validator short-circuit (the
	// ErrBTCHeaderContextUnavailable->ErrCorrupt arm returns the same consensus error before
	// AddExternalHeaders), so a validator-skip mutant would pass green.
	require.NoError(t, vm.ValidateBTCHeaderBatchForNetwork(chain.ctx, chain.tbcHeaderNode,
		chain.tbcHeaderNodeConfig.Network, chain.tbcHeaderNodeConfig.GenesisHeightOffset, []*wire.BlockHeader{&valid}),
		"precondition: the validator must accept the header so the duplicate self-heal guard (not a validator skip) produces the corrupt result")

	err = chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true)
	require.ErrorIs(t, err, consensus.ErrCorruptHVMHeaderOnlyModeState,
		"a duplicate batch with a WRONG canonical-tip claim must self-heal (corrupt), never be silently accepted")

	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, valid.BlockHash(), tipAfter.BlockHash(), "the canonical tip must be unchanged")
	sid1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, sid0[:], sid1[:], "a self-healed duplicate must NOT advance the upstream state id")
}

// TestHvmApplyPathBelowFloorDefersAndCommits drives the ErrBTCBatchBelowFloor apply arm end-to-end —
// its only execution in any test tier. Every other apply test seeds above the floor (validator returns
// nil) or uses an orphan/wrong-tip; the only below-floor exercise elsewhere
// (TestHvmBtcDiffFloorAwareAgainstRealLightweightNode) calls the validator directly, never the apply switch.
// A near-genesis (below floor+clearance) header in a BtcAttr must defer enforcement (the switch's
// BelowFloor arm) and fall through to AddExternalHeaders, which commits it: no error, tip and id advance.
// Light harness, not -short-skipped. Kills a control-flow mutant that replaces the BelowFloor fall-through
// with an early `return ErrInvalidHVMHeaders` (or ErrCorrupt) — a chain halt that would false-reject every
// honest near-genesis hVM block in the floor band the fix targets.
func TestHvmApplyPathBelowFloorDefersAndCommits(t *testing.T) {
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)

	// A valid mined header one block above the effective genesis -> within floorClearance -> below-floor
	// (real regtest PoW so the apply-path PoW gate passes and the BelowFloor defer arm is exercised).
	nearFloor := *mineRegtestChild(t, genesis, 3_000)
	canon := nearFloor.BlockHash()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, []wire.BlockHeader{nearFloor})
	require.NoError(t, err)
	nHeader := &types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))

	// De-vacuity: the validator must report this near-genesis batch as BelowFloor, so the apply path
	// provably takes the BelowFloor switch arm (defer + fall through) rather than the nil/enforce path.
	require.ErrorIs(t, vm.ValidateBTCHeaderBatchForNetwork(chain.ctx, chain.tbcHeaderNode,
		chain.tbcHeaderNodeConfig.Network, chain.tbcHeaderNodeConfig.GenesisHeightOffset,
		[]*wire.BlockHeader{&nearFloor}), vm.ErrBTCBatchBelowFloor,
		"precondition: a near-genesis batch must be classified BelowFloor so the deferred apply arm is exercised")

	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true),
		"a below-floor BtcAttr header must DEFER enforcement and COMMIT via AddExternalHeaders, not be rejected")

	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, nearFloor.BlockHash(), tipAfter.BlockHash(), "the committed below-floor header must become the tip")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sid[:], "a committed below-floor block must advance the upstream state id to the block")
}

// TestHvmApplyPathBelowFloorDuplicateIsIdempotent is the fast-lane sibling of T_DUP_OK: it drives the
// inline `case addHeadersDuplicate` apply arm (the duplicate-header bug locus — already-present headers must be
// idempotent, not a false-reject) on a light, non--short-skipped harness. The heavy duplicate tests
// (T_DUP_OK / T_DUP_WRONG) are -short-skipped; T_REALDUP only calls the classifier; T_BELOWFLOOR commits a
// fresh (err==nil) header and never enters the err!=nil/duplicate branch; T_UNCONN takes the bad-block arm
// — so under `go test -short` the duplicate apply arm had zero coverage. A near-genesis (below-floor)
// header that is pre-added reaches it: the validator returns BelowFloor (confirms connectivity, falls
// through), then AddExternalHeaders sees an all-duplicate batch -> DuplicateError -> the idempotent arm.
// Kills (on the fast lane) the `return nil`->reject regression, a deleted SetUpstreamStateId advance, and
// a deleted `case addHeadersDuplicate` label.
func TestHvmApplyPathBelowFloorDuplicateIsIdempotent(t *testing.T) {
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)

	// A valid mined header one block above the effective genesis -> within floorClearance -> below-floor.
	h := *mineRegtestChild(t, genesis, 5_000)
	canon := h.BlockHash()

	// Pre-add h directly so the apply path's AddExternalHeaders sees an all-duplicate batch.
	last := h.BlockHash()
	_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&h}}, last[:])
	require.NoError(t, err, "pre-add of the near-genesis header must succeed so the apply path then sees a duplicate")
	_, tipPreApply, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, h.BlockHash(), tipPreApply.BlockHash(), "pre-add must advance the tip to the header")

	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, []wire.BlockHeader{h})
	require.NoError(t, err)
	nHeader := &types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))

	// De-vacuity: near-genesis -> BelowFloor, so the apply path takes the defer arm, sets
	// connectivityConfirmed=true, and falls through to AddExternalHeaders, which returns DuplicateError on
	// the pre-added header -> the idempotent arm. Network/offset from the node config the apply path reads.
	require.ErrorIs(t, vm.ValidateBTCHeaderBatchForNetwork(chain.ctx, chain.tbcHeaderNode,
		chain.tbcHeaderNodeConfig.Network, chain.tbcHeaderNodeConfig.GenesisHeightOffset,
		[]*wire.BlockHeader{&h}), vm.ErrBTCBatchBelowFloor,
		"precondition: a near-genesis batch must be BelowFloor so the deferred path reaches AddExternalHeaders")

	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true),
		"a below-floor BtcAttr whose headers are already present must be IDEMPOTENT (duplicate arm -> nil), not a reject")

	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, h.BlockHash(), tipAfter.BlockHash(), "duplicate apply must leave the canonical tip unchanged")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sid[:], "duplicate apply must STILL advance the upstream state id to the block")
}

// TestHvmApplyPathBelowFloorDuplicateWrongCanonicalTipSelfHeals is the fast-lane symmetric counterpart
// of T_BELOWFLOOR_DUP: that pins the duplicate arm's claim==tip (idempotent) false branch of the
// curTip!=CanonicalTip guard; this pins the claim!=tip true branch — the silent-false-accept firewall. A
// duplicate batch carrying a wrong canonical-tip claim must self-heal (ErrCorruptHVMHeaderOnlyModeState),
// not advance the state id and return nil. The only other killer (heavy T_DUP_WRONG) is -short-skipped, so
// under `go test -short` deleting the guard at blockchain.go (`if !bytes.Equal(curTipHash, CanonicalTip)
// { return ErrCorrupt }`) would silently false-accept a wrong-claim duplicate and survive; this closes it
// on the fast lane. The tip-unchanged + state-id-unchanged oracle also proves the guard fires before
// SetUpstreamStateId (the wrong-claim path never advances the id).
func TestHvmApplyPathBelowFloorDuplicateWrongCanonicalTipSelfHeals(t *testing.T) {
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)

	// A near-genesis (below floor+clearance) mined header.
	h := *mineRegtestChild(t, genesis, 7_000)
	// Pre-add h so the apply path's AddExternalHeaders sees an all-duplicate batch.
	last := h.BlockHash()
	_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&h}}, last[:])
	require.NoError(t, err)

	// The block carries the same (now-duplicate) header but claims the wrong canonical tip (the genesis,
	// i.e. h's parent — not the live tip h).
	wrongClaim := genesis.BlockHash()
	require.NotEqual(t, h.BlockHash(), wrongClaim)
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&wrongClaim, []wire.BlockHeader{h})
	require.NoError(t, err)
	nHeader := &types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))
	sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)

	// De-vacuity: near-genesis -> BelowFloor (confirms connectivity, falls through), then the pre-added h
	// makes AddExternalHeaders -> DuplicateError -> the duplicate arm, so ErrCorrupt provably comes from the
	// curTip!=CanonicalTip guard, not the validator's ErrBTCHeaderContextUnavailable->ErrCorrupt skip.
	require.ErrorIs(t, vm.ValidateBTCHeaderBatchForNetwork(chain.ctx, chain.tbcHeaderNode,
		chain.tbcHeaderNodeConfig.Network, chain.tbcHeaderNodeConfig.GenesisHeightOffset,
		[]*wire.BlockHeader{&h}), vm.ErrBTCBatchBelowFloor,
		"precondition: a near-genesis batch must be BelowFloor so the deferred path reaches the duplicate arm")

	err = chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true)
	require.ErrorIs(t, err, consensus.ErrCorruptHVMHeaderOnlyModeState,
		"a duplicate batch with a WRONG canonical-tip claim must self-heal (corrupt), never be silently accepted")
	require.NotErrorIs(t, err, consensus.ErrInvalidHVMHeaders, "must be recoverable corrupt, not a bad block")

	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, h.BlockHash(), tipAfter.BlockHash(), "the canonical tip must be unchanged")
	sid1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, sid0[:], sid1[:], "a self-healed wrong-claim duplicate must NOT advance the upstream state id")
}

// TestHvmApplyPathUnconnectedIsBadBlock drives the end-to-end non-connecting path: a block whose BtcAttr
// header builds on a parent absent from the lightweight view must be ErrInvalidHVMHeaders (bad block), not
// corrupt (which would trigger a self-heal restore loop on a genuinely invalid block), and must leave the
// view untouched. Pins that a NotFound with no connectivity confirmation stays a bad block (the other side
// of the classifier's connectivity discriminator from the corrupt mapping).
//
// Uses the light harness (genesis-only node, no >floorClearance seed) and is not -short-skipped: the
// orphan's parent is absent, so the validator's anchor loop returns ErrBTCBatchUnconnected before the floor
// gate (floor-independent), giving the apply switch's bad-block arm its only fast-lane coverage; without
// this, no applyHvmHeaderConsensusUpdate arm runs under `go test -short`.
func TestHvmApplyPathUnconnectedIsBadBlock(t *testing.T) {
	chain, lightTip := newHvmTestChainWithLightTBC(t, btcDiffTestHvm0Time)

	// A "ghost" parent we deliberately do not add to the view (builds on the effective genesis).
	ghostParent := wire.BlockHeader{
		Version: lightTip.Version, PrevBlock: lightTip.BlockHash(), MerkleRoot: lightTip.MerkleRoot,
		Timestamp: lightTip.Timestamp.Add(600 * time.Second), Bits: lightTip.Bits, Nonce: 777,
	}
	// The orphan builds on the absent ghost parent -> does not connect to the committed view.
	orphan := wire.BlockHeader{
		Version: lightTip.Version, PrevBlock: ghostParent.BlockHash(), MerkleRoot: lightTip.MerkleRoot,
		Timestamp: lightTip.Timestamp.Add(1200 * time.Second), Bits: lightTip.Bits, Nonce: 778,
	}
	canon := orphan.BlockHash()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, []wire.BlockHeader{orphan})
	require.NoError(t, err)
	nHeader := &types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))
	sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)

	// De-vacuity: the validator must report the orphan as Unconnected (leaving batchConnectivityConfirmed
	// false) so the bad-block result genuinely flows classifier->AddExternalHeaders->NotFound->badblock.
	// Without this, ErrInvalidHVMHeaders is reachable via a coincidentally-equal early return; this also
	// pins that the Unconnected switch arm does not set connectivityConfirmed (a mutant doing so would make
	// this apply path return corrupt instead). Network/offset come from the node config the apply path
	// reads, so a harness change cannot desync the precondition from the code under test.
	require.ErrorIs(t, vm.ValidateBTCHeaderBatchForNetwork(chain.ctx, chain.tbcHeaderNode,
		chain.tbcHeaderNodeConfig.Network, chain.tbcHeaderNodeConfig.GenesisHeightOffset,
		[]*wire.BlockHeader{&orphan}), vm.ErrBTCBatchUnconnected,
		"precondition: the validator must report the orphan batch as Unconnected")

	err = chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true)
	require.ErrorIs(t, err, consensus.ErrInvalidHVMHeaders,
		"a non-connecting BtcAttr batch must be a bad block, not corrupt (no self-heal loop on an invalid block)")
	require.NotErrorIs(t, err, consensus.ErrCorruptHVMHeaderOnlyModeState, "must not be classified as recoverable corrupt")

	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, lightTip.BlockHash(), tipAfter.BlockHash(), "a rejected non-connecting block must not advance the tip past the effective genesis")
	sid1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, sid0[:], sid1[:], "a rejected non-connecting block must not advance the upstream state id")
}

// TestIsHvmReapplyRecoverableError pins the classifier that routes the re-apply head-set / revert /
// canonical paths (writeHeadBlock, setHeadBeyondRoot, SetCanonical, revertHvmStateAfterInvalidBlock, the
// ProcessBlock revert) away from a fleet-halt log.Crit and toward a from-genesis recovery. On those paths
// the target block is already committed (enforced at first import), so a fresh consensus reject or a torn
// store is recoverable, not a genuine bad block. It must not classify the full-node-behind lag (handled
// separately as a warn), ErrUnknownAncestor, or generic errors as recoverable; the first-import path must
// never use this (a reject there is a real bad block -> NonStatTy, never restore).
func TestIsHvmReapplyRecoverableError(t *testing.T) {
	// Recoverable on a re-apply path: torn store + the two consensus rejects (grandfathered-rule class).
	require.True(t, isHvmReapplyRecoverableError(consensus.ErrCorruptHVMHeaderOnlyModeState))
	require.True(t, isHvmReapplyRecoverableError(consensus.ErrInvalidHVMHeaders))
	require.True(t, isHvmReapplyRecoverableError(consensus.ErrInvalidHVMBlockFormat))
	// Wrapped sentinels must still classify by identity.
	require.True(t, isHvmReapplyRecoverableError(fmt.Errorf("ctx: %w", consensus.ErrInvalidHVMHeaders)))
	require.True(t, isHvmReapplyRecoverableError(fmt.Errorf("ctx: %w", consensus.ErrCorruptHVMHeaderOnlyModeState)))

	// Not recoverable-via-restore: the full-node-behind lag is handled separately (warn, not restore);
	// ErrUnknownAncestor is a geometry error restore cannot fix; a generic/unknown error must still crit
	// (fail-stop on an unexpected condition); nil is not an error.
	require.False(t, isHvmReapplyRecoverableError(consensus.ErrFullTBCMissingBTCHeader))
	require.False(t, isHvmReapplyRecoverableError(consensus.ErrFullTBCMissingFullBTCBlock))
	require.False(t, isHvmReapplyRecoverableError(consensus.ErrUnknownAncestor))
	require.False(t, isHvmReapplyRecoverableError(errors.New("some unexpected leveldb/io error")))
	require.False(t, isHvmReapplyRecoverableError(nil))

	// Disjointness from the full-node-behind classifier (they must route to DIFFERENT arms — restore vs warn).
	for _, e := range []error{consensus.ErrFullTBCMissingBTCHeader, consensus.ErrFullTBCMissingFullBTCBlock} {
		require.True(t, isHvmFullNodeBehind(e))
		require.False(t, isHvmReapplyRecoverableError(e), "behind != reapply-recoverable (different disposition)")
	}
}

// TestRecoverReapplyHvmStateMetersAndRestores pins the site disposition the classifier feeds: a recoverable
// re-apply error must drive a node-local rebuild (performFullHvmHeaderStateRestore) that increments the
// alertable meter, not a log.Crit (which would os.Exit and kill this test process, the original fleet-halt
// behavior). The classifier test above proves membership; this proves the wiring. Observables are
// restore-internals-agnostic: (1) the meter ticks, (2) the lightweight TBC node is torn down and reset
// (seeded BTC tip discarded), (3) the process survives. Scope: bc.CurrentBlock() is the EVM genesis on this
// bare chain, so the rebuild's forward replay is genesis-only — this pins teardown + meter + no-crit, not
// the from-genesis re-apply of a non-trivial hVM history (covered by the apply-path tests, e.g.
// TestHvmApplyPathAcceptsValidMinedAboveFloor).
func TestRecoverReapplyHvmStateMetersAndRestores(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: tears down + rebuilds the lightweight TBC node")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	seedRegtestAboveFloor(t, chain, genesis) // advance the lightweight BTC tip well past genesis
	_, tipBefore, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.NotEqual(t, genesis.BlockHash(), tipBefore.BlockHash(), "seed must advance the BTC tip past genesis")

	before := hvmReapplyRestoreMeter.Snapshot().Count()
	// A recoverable reject at a re-apply site (ErrInvalidHVMHeaders — a grandfathered re-judge of
	// already-committed history). The helper must recover (meter + restore), not crit.
	chain.recoverReapplyHvmState("unit test re-apply site", consensus.ErrInvalidHVMHeaders)

	require.Equal(t, before+1, hvmReapplyRestoreMeter.Snapshot().Count(), "recovery must increment the alertable meter")
	// CurrentBlock() is the EVM genesis on this bare chain, so the rebuild winds the lightweight BTC view
	// back to (at most) the genesis tip — the seeded headers are gone, proving teardown+reset ran.
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, genesis.BlockHash(), tipAfter.BlockHash(),
		"restore must tear down + reset the lightweight node (seeded tip discarded)")
}

// TestGetMissingBtcBlocksRaceWithReset pins the tbcHeaderNodeMu fix: GetMissingBtcBlocks runs on the
// per-peer broadcast goroutine outside chainmu, so it can race resetHvmHeaderNodeToGenesis tearing down +
// reassigning bc.tbcHeaderNode, and the chainmu-held setMissingProgressionBlocks writes. Drives all three
// concurrently; under `go test -race` it fails if the synchronization regresses (e.g. the TryRLock or the
// helper's Lock is dropped) — mutation-proven by removing the reader's TryRLock.
//
// Scope: readers take the early (missingProgressionBlocks != nil) return path, exercising the lifecycle
// reads the mutex protects (the tbcHeaderNode nil-check + the missingProgressionBlocks read). After the
// priority-inversion fix, GetMissingBtcBlocks's BlockHeaderBest call sits under the same single TryRLock as
// those reads (the closure-scoped lock), so the mechanism this test exercises is exactly the one that
// protects BlockHeaderBest — there is no separately-locked span to miss. Driving readers all the way through
// BlockHeaderBest -> vm.TBCBlocksAvailableToHeader is intentionally not done: that needs a live
// vm.TBCFullNode (TBCBlocksAvailableToHeader calls TBCFullNode.Synced with no nil-guard), and it runs after
// the lock is released, outside the mutex's protection domain.
func TestGetMissingBtcBlocksRaceWithReset(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: concurrent lightweight TBC teardown/rebuild")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	seedRegtestAboveFloor(t, chain, genesis)
	// Keep readers on the early path: a non-nil cache means GetMissingBtcBlocks returns before any full-node
	// call. The writer toggles between two non-nil values so the field stays non-nil throughout.
	mpbA := &wire.MsgHeaders{Headers: []*wire.BlockHeader{genesis}}
	mpbB := &wire.MsgHeaders{Headers: []*wire.BlockHeader{genesis, genesis}}
	chain.setMissingProgressionBlocks(mpbA)

	var wg sync.WaitGroup
	stop := make(chan struct{})
	// 4 readers hammering the lock-free entry point.
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
					_ = chain.GetMissingBtcBlocks()
				}
			}
		}()
	}
	// 1 field-writer mirroring the chainmu-held apply-path writes.
	wg.Add(1)
	go func() {
		defer wg.Done()
		for {
			select {
			case <-stop:
				return
			default:
				chain.setMissingProgressionBlocks(mpbA)
				chain.setMissingProgressionBlocks(mpbB)
			}
		}
	}()
	// The writer under test: repeatedly tear down + reassign the lightweight node.
	for i := 0; i < 4; i++ {
		chain.resetHvmHeaderNodeToGenesis()
	}
	close(stop)
	wg.Wait()
}
