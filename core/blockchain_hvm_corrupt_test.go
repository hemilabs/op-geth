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
	"log/slog"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"sync"
	"testing"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/log"
	"github.com/hemilabs/heminetwork/database"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
	"github.com/syndtr/goleveldb/leveldb"
)

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
//
// The fix uses typed errors.As matching plus a connectivity discriminator (NotFound->corrupt only when
// connectivity was confirmed, else bad-block) plus idempotent DuplicateError handling. Do not collapse it
// back to a single errors.Is(NotFoundError(...)) shortcut: that drops the discriminator and reintroduces
// the #31 orphan self-heal loop. These tests pin the typed, connectivity-aware mapping.
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

// Bad-block ROUTING side-effect (the caller-side disposition of the apply error classes). walkHvmHeaderConsensusForward
// must reportBlock (rawdb.WriteBadBlock) a block that fails with ErrInvalidHVMHeaders/Format — so it is recorded as
// permanently bad and never retried — while UNWOUND recoverable predecessors and an ErrCorrupt (torn store) must NOT
// be banned (a permanent ban would defeat the self-heal). The apply-side returns are pinned elsewhere; the
// caller-side reportBlock disposition is what this covers (no other hVM test references ReadBadBlock/WriteBadBlock).
func TestHvmForwardWalkBadBlockRouting(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)

	// POSITIVE: a wrong-canonical-tip block (ErrInvalidHVMHeaders) is reportBlock'd; the unwound recoverable
	// predecessors are NOT.
	t.Run("invalid-headers-bans-only-the-offending-block", func(t *testing.T) {
		chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)
		canonTip := lightTip.BlockHash()
		var wrongTip chainhash.Hash
		for i := range wrongTip {
			wrongTip[i] = 0x42
		}
		preActivation := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
		currentHead := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preActivation.Hash()})
		block1 := emptyPresentBtcAttrBlock(t, 12, hvm0Time+1, currentHead.Header(), canonTip)
		block2 := emptyPresentBtcAttrBlock(t, 13, hvm0Time+2, block1.Header(), canonTip)
		block3 := emptyPresentBtcAttrBlock(t, 14, hvm0Time+3, block2.Header(), wrongTip)
		for _, b := range []*types.Block{currentHead, block1, block2, block3} {
			chain.tempBlocks[b.Hash().String()] = b
			chain.tempHeaders[b.Hash().String()] = b.Header()
		}
		chain.tempHeaders[preActivation.Hash().String()] = preActivation
		chain.tempBlocks[preActivation.Hash().String()] = types.NewBlockWithHeader(preActivation)
		require.NoError(t, chain.applyHvmHeaderConsensusUpdate(currentHead.Header(), false, true))

		require.ErrorIs(t, chain.walkHvmHeaderConsensusForward(currentHead.Header(), block3.Header()), consensus.ErrInvalidHVMHeaders)

		require.NotNil(t, rawdb.ReadBadBlock(chain.db, block3.Hash()), "the offending (invalid-headers) block must be reportBlock'd")
		require.Nil(t, rawdb.ReadBadBlock(chain.db, block1.Hash()), "an unwound recoverable predecessor must NOT be banned")
		require.Nil(t, rawdb.ReadBadBlock(chain.db, block2.Hash()), "an unwound recoverable predecessor must NOT be banned")
		require.Nil(t, rawdb.ReadBadBlock(chain.db, currentHead.Hash()), "the common-ancestor head must NOT be banned")
	})

	// NEGATIVE: an ErrCorrupt (torn store / orphaned prior-state) must NOT ban the block — a permanent ban would
	// defeat the self-heal that recovers from a corrupt view.
	t.Run("corrupt-state-does-not-ban", func(t *testing.T) {
		chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)
		canonTip := lightTip.BlockHash()
		// Point the upstream-state-id at an orphaned hash whose block is absent -> the next apply's prior-state
		// guard returns ErrCorruptHVMHeaderOnlyModeState.
		var orphan [32]byte
		orphan[0] = 0x77
		require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, orphan))

		preActivation := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
		currentHead := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preActivation.Hash()})
		target := emptyPresentBtcAttrBlock(t, 12, hvm0Time+1, currentHead.Header(), canonTip)
		for _, b := range []*types.Block{currentHead, target} {
			chain.tempBlocks[b.Hash().String()] = b
			chain.tempHeaders[b.Hash().String()] = b.Header()
		}
		chain.tempHeaders[preActivation.Hash().String()] = preActivation
		chain.tempBlocks[preActivation.Hash().String()] = types.NewBlockWithHeader(preActivation)

		err := chain.walkHvmHeaderConsensusForward(currentHead.Header(), target.Header())
		require.ErrorIs(t, err, consensus.ErrCorruptHVMHeaderOnlyModeState, "an orphaned prior-state must surface as recoverable corrupt")
		require.Nil(t, rawdb.ReadBadBlock(chain.db, target.Hash()), "a corrupt-state (recoverable) error must NOT permanently ban the block")
	})
}

// Upstream-state-id chaining strictness: the apply path's last-line backstop. When the prior-state block resolves
// (check != nil) but its hash != the target block's ParentHash — a skipped block (apply N+2 while the view is at N)
// or a stale/forked parent — applyHvmHeaderConsensusUpdate must FAIL-STOP (hvmMigrationAwareCrit -> log.Crit ->
// os.Exit), never silently commit the target's BTC headers onto the wrong prior state. The check==nil arm
// (orphaned prior-state) is covered; this sibling arm (resolves-but-mismatches) is the chaining enforcement and is
// asserted by no other test (the empty-present sibling test only proves the crit is AVOIDED). A deleted/weakened guard would
// silently mis-commit and the suite would stay green; log.Crit cannot be caught in-process, hence the re-exec.
const hvmChainingCritChildEnv = "HVM_APPLY_PARENT_MISMATCH_CHILD"

// TestApplyHvmHeaderParentMismatchCritChild is the subprocess child for TestApplyHvmHeaderParentMismatchCrit.
func TestApplyHvmHeaderParentMismatchCritChild(t *testing.T) {
	if os.Getenv(hvmChainingCritChildEnv) == "" {
		t.Skip("child-only: driven by TestApplyHvmHeaderParentMismatchCrit via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	// Prior-state block P (activation block, parent pre-hVM). Applying it sets the upstream-state-id to P.
	preP := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	p := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preP.Hash()})
	chain.tempHeaders[preP.Hash().String()] = preP
	chain.tempBlocks[preP.Hash().String()] = types.NewBlockWithHeader(preP)
	chain.tempHeaders[p.Hash().String()] = p.Header()
	chain.tempBlocks[p.Hash().String()] = p
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(p.Header(), false, false))
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, p.Hash().Bytes(), sid[:], "precondition: state-id is P")

	// Target T whose ParentHash is NOT P (a skipped/forked parent): the prior-state P resolves, but P.Hash() !=
	// T.ParentHash -> the chaining backstop must fire.
	target := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: common.Hash{0x99}})
	chain.tempHeaders[target.Hash().String()] = target.Header()
	chain.tempBlocks[target.Hash().String()] = target

	chain.applyHvmHeaderConsensusUpdate(target.Header(), false, false)
	t.Fatalf("applyHvmHeaderConsensusUpdate returned for a parent-mismatch block; expected the chaining backstop to os.Exit")
}

// TestApplyHvmHeaderParentMismatchCrit drives the chaining backstop via subprocess re-exec.
func TestApplyHvmHeaderParentMismatchCrit(t *testing.T) {
	cmd := exec.Command(os.Args[0], "-test.run=^TestApplyHvmHeaderParentMismatchCritChild$", "-test.v")
	cmd.Env = append(os.Environ(), hvmChainingCritChildEnv+"=1")
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "the chaining backstop must os.Exit non-zero, output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "but parent of updated block",
		"the crit must be the parent-mismatch chaining backstop, not another log.Crit site")
	require.NotContains(t, string(out), "applyHvmHeaderConsensusUpdate returned for a parent-mismatch block",
		"the backstop must os.Exit BEFORE returning; the returned-marker means it was downgraded to log.Warn")
}

// The apply-path extract-error arm: an Hvm0-ACTIVE block carrying a 0x7C tx whose calldata is CORRUPT (fails
// BtcAttributesDepositData.UnmarshalBinary) must reject as ErrInvalidHVMBlockFormat (the block is permanently
// invalid), distinct from (a) the pre-Hvm0 format-reject (valid calldata, wrong activation time) and (b) the
// wrong-difficulty ErrInvalidHVMHeaders. The corrupt-calldata extract-error arm (applyHvmHeaderConsensusUpdate
// where ExtractBtcAttrData itself errors) was uncovered. The caller-side reportBlock disposition of this class is
// covered separately by TestHvmForwardWalkBadBlockRouting.
func TestHvmApplyPathCorruptBtcAttrCalldataIsFormatReject(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)

	// A 0x7C tx whose calldata is too short to parse (just the selector) -> ExtractBtcAttrData errors.
	corrupt := types.NewTx(&types.BtcAttributesDepositedTx{
		To:   &types.BtcAttributesDepositedSenderAddress,
		Gas:  1_000_000,
		Data: types.UpdateHvmStateFuncBytes4[:], // 4 bytes, far below the minimum serialized length
	})
	blk := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time}).
		WithBody(types.Body{Transactions: types.Transactions{corrupt}})
	require.True(t, chain.chainConfig.IsHvm0(blk.Time()), "precondition: the block is Hvm0-active (isolates the extract-error arm from the pre-Hvm0 gate)")
	chain.tempHeaders[blk.Hash().String()] = blk.Header()
	chain.tempBlocks[blk.Hash().String()] = blk
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))

	err := chain.applyHvmHeaderConsensusUpdate(blk.Header(), false, true)
	require.ErrorIs(t, err, consensus.ErrInvalidHVMBlockFormat, "a corrupt-calldata BtcAttr must be a permanently-invalid format reject")
	require.NotErrorIs(t, err, consensus.ErrInvalidHVMHeaders, "it is a format reject, not a difficulty/header reject")
	require.NotErrorIs(t, err, consensus.ErrCorruptHVMHeaderOnlyModeState, "a malformed block is NOT a recoverable corrupt-store error")

	// No commit: tip + state-id unchanged.
	_, tip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, genesis.BlockHash(), tip.BlockHash(), "no commit on a format reject")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId, *sid, "no state-id advance on a format reject")
}

// TestUpdateHvmHeaderConsensusCorruptStateRecoverable pins the two currentHead==nil recoverable guards in
// updateHvmHeaderConsensus: when the lightweight TBC's upstream-state-id references an EVM header that is
// absent from both disk and the holding pen (orphaned by a rewind/deep-reorg), the function must return the
// recoverable consensus.ErrCorruptHVMHeaderOnlyModeState sentinel — NOT nil-deref/crash, and NOT silently
// return nil (which would leave a divergent committed view). Both guards had zero coverage; a mutation
// flipping `return ErrCorruptHVMHeaderOnlyModeState` to `return nil`, or removing a guard (re-introducing
// the nil-deref), fails here.
func TestUpdateHvmHeaderConsensusCorruptStateRecoverable(t *testing.T) {
	const hvm0Time = uint64(1000)

	// --- General (non-genesis) branch: upstream-state-id points at a block that is later orphaned. ---
	t.Run("general-branch-orphaned-upstream", func(t *testing.T) {
		chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)

		// Advance the upstream-state-id off genesis to a real block N via an empty-but-present BtcAttr apply
		// (the same mechanism the live apply path uses).
		canon := lightTip.BlockHash()
		btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, nil)
		require.NoError(t, err)
		tx := types.NewTx(btcAttr)
		parent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
		nHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: parent.Hash()}
		blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{tx}})
		chain.tempHeaders[parent.Hash().String()] = parent
		chain.tempBlocks[parent.Hash().String()] = types.NewBlockWithHeader(parent)
		chain.tempHeaders[blockN.Hash().String()] = blockN.Header()
		chain.tempBlocks[blockN.Hash().String()] = blockN
		require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true),
			"empty-but-present apply must advance the upstream-state-id to N")
		sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, blockN.Hash().Bytes(), sid[:], "upstream-state-id must be block N")

		// Orphan N: remove it from disk + holding pen so getHeaderFromDiskOrHoldingPen(N) returns nil.
		delete(chain.tempHeaders, blockN.Hash().String())
		delete(chain.tempBlocks, blockN.Hash().String())

		// A subsequent head-move now finds the upstream-state-id header unresolvable.
		newHead := &types.Header{Number: big.NewInt(20), Time: hvm0Time + 100, ParentHash: common.Hash{0xde, 0xad}}
		var got error
		require.NotPanics(t, func() { got = chain.updateHvmHeaderConsensus(newHead, false) },
			"an unresolvable upstream-state-id must not nil-deref")
		require.ErrorIs(t, got, consensus.ErrCorruptHVMHeaderOnlyModeState,
			"an unresolvable upstream-state-id must return the recoverable corrupt-state sentinel")
	})

	// --- Genesis branch: upstream-state-id is genesis (first hVM block) but the parent is unresolvable. ---
	t.Run("genesis-branch-orphaned-parent", func(t *testing.T) {
		chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)
		sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, hVMGenesisUpstreamId[:], sid0[:], "fresh node must be at the genesis upstream-state-id")

		// First hVM block whose parent is absent from disk + holding pen → genesis branch's
		// getHeaderFromDiskOrHoldingPen(ParentHash) is nil.
		firstHvm := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: common.Hash{0xab, 0xcd}}
		var got error
		require.NotPanics(t, func() { got = chain.updateHvmHeaderConsensus(firstHvm, false) },
			"an unresolvable first-hVM-block parent must not nil-deref in the genesis branch")
		require.ErrorIs(t, got, consensus.ErrCorruptHVMHeaderOnlyModeState,
			"the genesis-branch nil-parent must return the recoverable corrupt-state sentinel")
	})
}

// TestUpdateHvmHeaderConsensusEarlyReturns pins the two consensus-gate early-returns of
// updateHvmHeaderConsensus that must advance NOTHING in the lightweight TBC view: a PRE-activation head
// (IsHvm0(newHead.Time) == false) and a head whose hash already equals the upstream-state-id (the
// idempotent no-op). Both branches had zero coverage. They are load-bearing: the pre-activation gate keeps
// pre-Phase-0 head-moves from ever entering the apply/reorg machinery, and the no-op short-circuit makes
// re-driving the same head (e.g. a duplicate writeHeadBlock) a true no-op rather than a double-apply. A
// mutation dropping the `!IsHvm0` guard, or inverting/removing the `bytes.Equal(upstream, newHead)` no-op,
// changes the upstream-state-id (or errors) and fails here.
func TestUpdateHvmHeaderConsensusEarlyReturns(t *testing.T) {
	const hvm0Time = uint64(1000)

	t.Run("pre-activation-head-is-no-op", func(t *testing.T) {
		chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)
		sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, hVMGenesisUpstreamId[:], sid0[:], "fresh node must be at the genesis upstream-state-id")

		// A head whose time is BEFORE hVM Phase-0 activation must return nil without consulting (let alone
		// advancing) the lightweight view — even though its parent is unresolvable, which WOULD trip the
		// corrupt-state sentinel if the pre-activation gate were removed.
		preAct := &types.Header{Number: big.NewInt(5), Time: hvm0Time - 1, ParentHash: common.Hash{0x11, 0x22}}
		require.NoError(t, chain.updateHvmHeaderConsensus(preAct, false),
			"a pre-activation head must be a clean no-op")
		sid1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, sid0[:], sid1[:], "a pre-activation head must NOT advance the upstream-state-id")
		require.Equal(t, hVMGenesisUpstreamId[:], sid1[:], "still at genesis")
	})

	t.Run("already-reflected-head-is-no-op", func(t *testing.T) {
		chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)

		// Advance the upstream-state-id to a real block N via an empty-but-present apply (same mechanism the
		// live path uses), so the upstream-state-id equals blockN.Hash().
		canon := lightTip.BlockHash()
		btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, nil)
		require.NoError(t, err)
		parent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
		nHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: parent.Hash()}
		blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
		chain.tempHeaders[parent.Hash().String()] = parent
		chain.tempBlocks[parent.Hash().String()] = types.NewBlockWithHeader(parent)
		chain.tempHeaders[blockN.Hash().String()] = blockN.Header()
		chain.tempBlocks[blockN.Hash().String()] = blockN
		require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true))
		sidN, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, blockN.Hash().Bytes(), sidN[:], "upstream-state-id must be block N")

		// Re-driving updateHvmHeaderConsensus for the SAME head (upstream-state-id already == newHead.Hash())
		// must short-circuit to a no-op, NOT re-enter the apply machinery.
		require.NoError(t, chain.updateHvmHeaderConsensus(blockN.Header(), false),
			"the already-reflected head must be an idempotent no-op")
		sidAfter, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, sidN[:], sidAfter[:],
			"re-driving the already-reflected head must NOT change the upstream-state-id")
	})

	t.Run("awaiting-snap-sync-is-no-op", func(t *testing.T) {
		chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)
		sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)

		// While awaiting an in-flight hVM snap sync the lightweight TBC view is owned by SnapSyncHvm, so
		// updateHvmHeaderConsensus must short-circuit for EVERY caller (writeHeadBlock/setHeadBeyondRoot/
		// SetCanonical/reorg/build) — this is the latch's single consensus chokepoint. A real hVM head whose
		// parent is unresolvable (which WOULD trip the corrupt-state sentinel if the awaiting gate were
		// removed) must still be a clean no-op that does not advance the upstream-state-id.
		chain.SetAwaitingHvmSnapSync()
		require.True(t, chain.isAwaitingHvmSnapSync())
		head := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: common.Hash{0x11, 0x22}}
		require.NoError(t, chain.updateHvmHeaderConsensus(head, false),
			"while awaiting snap, updateHvmHeaderConsensus must short-circuit to a no-op")
		sid1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, sid0[:], sid1[:], "awaiting snap must NOT advance the upstream-state-id")
		require.False(t, chain.HvmSnapSyncCompleted(), "while awaiting snap, the finished flag must remain false")
	})
}

// TestUnapplyHvmHeaderConsensusUpdateOrphanedParentRecoverable pins the unapply-side nil-parent guard that
// mirrors the apply-side currentHead==nil guards: when the parent of the block being unapplied is absent from
// both disk and the holding pen (a deep reorg/rewind orphaned it), unapplyHvmHeaderConsensusUpdate must return
// the recoverable consensus.ErrCorruptHVMHeaderOnlyModeState sentinel — NOT nil-deref prevBlock.Time/.Hash()
// and crash the process. The walkHvmHeaderConsensusBack caller routes this sentinel through recovery, not crit.
// A mutation removing the guard (re-introducing the nil-deref) panics and fails here.
func TestUnapplyHvmHeaderConsensusUpdateOrphanedParentRecoverable(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	// A block present in the holding pen, but whose parent is absent from both disk and the holding pen.
	blk := types.NewBlockWithHeader(&types.Header{
		Number: big.NewInt(11), Time: hvm0Time, ParentHash: common.Hash{0xab, 0xcd},
	})
	chain.tempHeaders[blk.Hash().String()] = blk.Header()
	chain.tempBlocks[blk.Hash().String()] = blk

	var got error
	require.NotPanics(t, func() { got = chain.unapplyHvmHeaderConsensusUpdate(blk.Header()) },
		"an unresolvable parent on the unapply path must not nil-deref")
	require.ErrorIs(t, got, consensus.ErrCorruptHVMHeaderOnlyModeState,
		"unapply with an unresolvable parent must return the recoverable corrupt-state sentinel")
}

// TestUnapplyHvmHeaderConsensusUpdateMissingTargetBlockRecoverable pins the guard for the unapply TARGET's
// own body: unapplyHvmHeaderConsensusUpdate first fetches the block being unapplied (header.Hash()); if that
// body is absent from disk + holding pen (a deep reorg/rewind orphaned an already-applied block), it must
// return the recoverable consensus.ErrCorruptHVMHeaderOnlyModeState — NOT a plain error, which makes the
// walkHvmHeaderConsensusBack caller log.Crit (a node halt) instead of rebuilding the lightweight view from
// genesis. This mirrors the prevBlock/cursor orphaned-store guards. A mutation reverting it to a plain
// fmt.Errorf fails here (ErrorIs on the recoverable sentinel).
func TestUnapplyHvmHeaderConsensusUpdateMissingTargetBlockRecoverable(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	// A header whose own block is absent from both disk and the holding pen (never seeded into tempBlocks).
	orphan := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: common.Hash{0xab, 0xcd}}

	var got error
	require.NotPanics(t, func() { got = chain.unapplyHvmHeaderConsensusUpdate(orphan) },
		"an absent unapply-target block must not nil-deref")
	require.ErrorIs(t, got, consensus.ErrCorruptHVMHeaderOnlyModeState,
		"unapply of a block whose body is absent must return the recoverable corrupt-state sentinel, not a plain error")
}

// TestApplyHvmHeaderConsensusUpdateOrphanedPriorStateRecoverable pins the APPLY-side mirror of the
// orphaned-store guards: applyHvmHeaderConsensusUpdate's parent-sanity check resolves the upstream-state-id's
// block via the BLOCK store (getBlockFromDiskOrHoldingPen) and dereferences check.Hash(). The upstream
// currentHead==nil guard uses the HEADER store, so a parent whose header resolves but whose body is orphaned
// (a deep reorg/rewind) passes that guard yet leaves check==nil here. That must return the recoverable
// consensus.ErrCorruptHVMHeaderOnlyModeState, not nil-deref the process. A mutation removing the guard panics here.
func TestApplyHvmHeaderConsensusUpdateOrphanedPriorStateRecoverable(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	// Point the upstream-state-id at a non-genesis hash whose block is absent from disk + holding pen.
	var fake [32]byte
	fake[0] = 0x77
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, fake))

	// A present target block to apply (its body is in the holding pen, so the target-block guard does not fire);
	// its parent is the orphaned prior-state hash, so the else-branch parent-sanity check.Hash() is reached.
	target := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: common.Hash{0x99}})
	chain.tempHeaders[target.Hash().String()] = target.Header()
	chain.tempBlocks[target.Hash().String()] = target

	var got error
	require.NotPanics(t, func() { got = chain.applyHvmHeaderConsensusUpdate(target.Header(), false, false) },
		"an orphaned prior-state block body must not nil-deref the apply parent-sanity check")
	require.ErrorIs(t, got, consensus.ErrCorruptHVMHeaderOnlyModeState,
		"apply with an orphaned upstream-state-id block must return the recoverable corrupt-state sentinel")
}

// TestUpdateHvmHeaderConsensusUpstreamStateIdErrorRecoverable pins the entry-point guard in
// updateHvmHeaderConsensus: it reads the lightweight TBC view's upstream-state-id as its first step. When that
// read faults — a torn/IO-failed leveldb, or a node not in external-header mode — UpstreamStateId returns a NIL
// pointer, and the subsequent currentHeadHashRaw[:] dereference would nil-panic BEFORE any of this function's
// currentHead==nil recovery guards run. That faulted read must instead return the recoverable
// consensus.ErrCorruptHVMHeaderOnlyModeState so the re-apply callers self-heal via recoverReapplyHvmState. A
// mutation removing the err/nil guard nil-panics here.
func TestUpdateHvmHeaderConsensusUpstreamStateIdErrorRecoverable(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	// Swap in a non-external-header-mode server: its UpstreamStateId returns (nil, error) on its first check
	// (before any db access), deterministically simulating a faulted lightweight-store read. Restore the
	// healthy node before returning so the harness's teardown cleanup operates on it.
	orig := chain.tbcHeaderNode
	defer func() { chain.tbcHeaderNode = orig }()

	badCfg := tbc.NewDefaultConfig()
	badCfg.ExternalHeaderMode = false
	badCfg.Network = "testnet3"
	badCfg.LevelDBHome = t.TempDir()
	badServer, err := tbc.NewServer(badCfg)
	require.NoError(t, err)
	chain.tbcHeaderNode = badServer

	sid, sidErr := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.Error(t, sidErr, "non-external-header-mode UpstreamStateId must error")
	require.Nil(t, sid, "UpstreamStateId must return a nil pointer on error")

	newHead := &types.Header{Number: big.NewInt(11), Time: hvm0Time + 100, ParentHash: common.Hash{0x42}}
	var got error
	var logBuf bytes.Buffer
	prevLogger := log.Root()
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(&logBuf, slog.LevelDebug, false)))
	require.NotPanics(t, func() { got = chain.updateHvmHeaderConsensus(newHead, false) },
		"a faulted UpstreamStateId read must not nil-deref")
	log.SetDefault(prevLogger)
	require.ErrorIs(t, got, consensus.ErrCorruptHVMHeaderOnlyModeState,
		"a faulted UpstreamStateId read must return the recoverable corrupt-state sentinel")
	require.Contains(t, logBuf.String(), "unable to get upstream state id from lightweight TBC",
		"the faulted-store diagnostic must be logged before returning the sentinel")
}

// TestApplyHvmHeaderConsensusUpdateMissingTargetBlockBehavior pins the APPLY-side TARGET-block-absent guard: when
// the to-be-applied block's header resolves (the caller holds it) but its BODY is absent from BOTH disk and the
// holding pen, applyHvmHeaderConsensusUpdate returns a PLAIN error ("unable to get block"), NOT a sentinel. This is
// the dual-store-duality mirror of TestUnapplyHvmHeaderConsensusUpdateMissingTargetBlockRecoverable — and it is
// deliberately ASYMMETRIC: the unapply side returns the recoverable sentinel, the apply side does not. Lock both the
// non-panic (the nil-check must fire before block.Transactions()) and the exact classification, so the asymmetry is
// a test-visible contract and a dropped nil-check (re-introducing the panic) fails here.
func TestApplyHvmHeaderConsensusUpdateMissingTargetBlockBehavior(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	// A header whose own block is NEVER seeded into tempBlocks and is not on disk -> getBlockFromDiskOrHoldingPen
	// returns nil: the header exists but its body is orphaned from both stores.
	orphan := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: common.Hash{0xab, 0xcd}}

	var got error
	require.NotPanics(t, func() { got = chain.applyHvmHeaderConsensusUpdate(orphan, false, false) },
		"an absent apply-target block must not nil-deref")
	require.Error(t, got)
	require.ErrorContains(t, got, "unable to get block", "the apply target-absent guard returns the plain error")
	require.NotErrorIs(t, got, consensus.ErrCorruptHVMHeaderOnlyModeState,
		"apply-side target-absent is asymmetric with the unapply side: a plain error, not the recoverable sentinel")
	require.NotErrorIs(t, got, consensus.ErrInvalidHVMHeaders, "target-absent is not a bad-block classification")
}

// crash-window CONVERGENCE: a node that dies mid-migration must, on the next boot, classify the partial on-disk
// state correctly and RE-MIGRATE to convergence — never crit-loop, never silently keep a headerless store, never
// destroy the legacy fallback. The classification leaf (classifyMigratedMainnetStore, hvmMigrationNeeded torn-store
// case) and the single-shot SUCCESS are tested in isolation; this drives the full orchestration across each
// simulated crash window, proving the detection->rebuild loop converges and that a re-run is idempotent. Uses real
// mainnet genesis + synthetic children + a lightweight in-process tbc.Server + an in-memory EVM chain.
func TestMigrate_CrashWindowsConverge(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: builds real lightweight TBC nodes + EVM chains per crash window")
	}
	ctx := context.Background()
	mainnetGen := decodeMainnetGenesisHeader(t)

	const N = 4
	children := make([]*wire.BlockHeader, N)
	prev := mainnetGen
	for i := 0; i < N; i++ {
		h := &wire.BlockHeader{Version: prev.Version, PrevBlock: prev.BlockHash(), MerkleRoot: mainnetGen.MerkleRoot,
			Timestamp: prev.Timestamp.Add(time.Duration(i+1) * 10 * time.Minute), Bits: mainnetGen.Bits, Nonce: uint32(i + 1)}
		children[i] = h
		prev = h
	}
	tipHash := prev.BlockHash()

	newSrv := func(home, network string, stateId [32]byte) *tbc.Server {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = mainnetGen
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
		cfg.Network = network
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		_, _, _, _, addErr := srv.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: children}, stateId[:])
		require.NoError(t, addErr)
		return srv
	}

	// stage builds the standard migrate inputs at a fresh home: an EVM chain whose canonical tip == S (catch-up
	// no-op), a mainnet full node holding genesis..T, and a torn-down legacy testnet3 store committed to T with S.
	// `crash` is invoked AFTER the legacy/full are in place but BEFORE maybeMigrate, to plant the partial on-disk
	// <home>/mainnet state of a crash window. Returns the chain, cfg, home, and S.
	stage := func(t *testing.T, crash func(home string, S [32]byte)) (*BlockChain, *tbc.Config, string, [32]byte) {
		_, _, bc, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
		require.NoError(t, err)
		t.Cleanup(bc.Stop)
		S := [32]byte(bc.CurrentBlock().Hash())

		home := t.TempDir()
		full := newSrv(t.TempDir(), "mainnet", [32]byte{0x01})
		t.Cleanup(func() { _ = full.ExternalHeaderTearDown() })
		prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
		vm.TBCFullNode, vm.TBCFullNodeConfig = full, &tbc.Config{Network: "mainnet"}
		t.Cleanup(func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg })

		legacy := newSrv(home, "testnet3", S)
		require.NoError(t, legacy.ExternalHeaderTearDown())
		if crash != nil {
			crash(home, S)
		}
		return bc, mainnetMigrateConfig(mainnetGen, home), home, S
	}

	assertConverged := func(t *testing.T, bc *BlockChain, home string, S [32]byte) {
		postH, postTip, err := bc.tbcHeaderNode.BlockHeaderBest(ctx)
		require.NoError(t, err)
		require.Equal(t, tipHash.String(), postTip.BlockHash().String(), "rebuilt tip must be the committed tip T")
		require.Equal(t, vm.MainnetHvmGenesisHeight+uint64(N), postH)
		postId, err := bc.tbcHeaderNode.UpstreamStateId(ctx)
		require.NoError(t, err)
		require.Equal(t, S, *postId, "rebuilt state-id must be S")
		require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "the mainnet store must exist")
		require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be retired")
		require.DirExists(t, filepath.Join(home, fmt.Sprintf("testnet3.migrated-%x", S[:])), "legacy renamed to backup")
	}

	// (a) CRASH AFTER THE RESET, BEFORE FILL: a version-only (no best header) mainnet store -> torn -> ReMigrate.
	t.Run("crash-after-reset-torn-mainnet", func(t *testing.T) {
		bc, cfg, home, S := stage(t, func(home string, _ [32]byte) {
			require.NoError(t, openStoreGuardFree(t, ctx, home, "mainnet").Close()) // creates+version, no headers
		})
		require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "precondition: the torn store has entries")
		handled := bc.maybeMigrateHvmHeaderNode(cfg)
		t.Cleanup(func() {
			if bc.tbcHeaderNode != nil {
				_ = bc.tbcHeaderNode.ExternalHeaderTearDown()
			}
		})
		require.True(t, handled, "a torn (post-reset) mainnet store must RE-MIGRATE to convergence")
		assertConverged(t, bc, home, S)
	})

	// (b) CRASH MID FILL: headers committed but the state-id never written -> torn -> ReMigrate.
	t.Run("crash-mid-fill-no-stateid", func(t *testing.T) {
		bc, cfg, home, S := stage(t, func(home string, S [32]byte) {
			srv := newSrv(home, "mainnet", S) // headers + state-id...
			require.NoError(t, srv.ExternalHeaderTearDown())
			db := openStoreGuardFree(t, ctx, home, "mainnet")
			require.NoError(t, db.MetadataDel(ctx, upstreamStateIdMetaKey)) // ...then drop the state-id (torn)
			require.NoError(t, db.Close())
		})
		handled := bc.maybeMigrateHvmHeaderNode(cfg)
		t.Cleanup(func() {
			if bc.tbcHeaderNode != nil {
				_ = bc.tbcHeaderNode.ExternalHeaderTearDown()
			}
		})
		require.True(t, handled, "a mid-fill (no state-id) mainnet store must RE-MIGRATE")
		assertConverged(t, bc, home, S)
	})

	// (c) IDEMPOTENT RE-RUN: a second boot over an already-migrated store must NOT re-migrate or re-count completed.
	t.Run("idempotent-rerun", func(t *testing.T) {
		bc, cfg, home, S := stage(t, nil)
		require.True(t, bc.maybeMigrateHvmHeaderNode(cfg), "first run migrates")
		assertConverged(t, bc, home, S)
		// Release the migrated store's exclusive lock so the second boot can read it guard-free.
		require.NoError(t, bc.tbcHeaderNode.ExternalHeaderTearDown())

		_, _, bc2, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
		require.NoError(t, err)
		t.Cleanup(bc2.Stop)
		compBefore := hvmMigrationCompletedMeter.Snapshot().Count()
		handled2 := bc2.maybeMigrateHvmHeaderNode(mainnetMigrateConfig(mainnetGen, home))
		t.Cleanup(func() {
			if bc2.tbcHeaderNode != nil {
				_ = bc2.tbcHeaderNode.ExternalHeaderTearDown()
			}
		})
		require.False(t, handled2, "a re-run over a valid migrated store must be a no-op (ValidMigrated), not handled")
		require.Equal(t, compBefore, hvmMigrationCompletedMeter.Snapshot().Count(), "a no-op re-run must NOT re-count completed")
		require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "the migrated store must remain intact")
	})
}

// The updateHvmHeaderConsensus dispatcher's UNRECOGNIZED-error backstop (the single-block-apply arm, ~blockchain.go
// 4477): when applyHvmHeaderConsensusUpdate returns an error that is NOT one of the three handled sentinels
// (ErrInvalidHVMBlockFormat / ErrInvalidHVMHeaders / ErrCorruptHVMHeaderOnlyModeState), the dispatcher log.Crits
// ("Encountered an error applying hVM header state transition") rather than silently swallowing a torn-write. Reached
// here via a direct-child block whose BODY is absent from disk+pen (apply returns the plain "unable to get block"
// error). Downgrading the crit to log.Warn+return-nil would keep the suite green; log.Crit can't be caught in-process,
// hence the re-exec.
const hvmDispatchUnrecognizedCritChildEnv = "HVM_DISPATCH_UNRECOGNIZED_ERR_CHILD"

func TestUpdateHvmHeaderConsensusUnrecognizedErrorCritChild(t *testing.T) {
	if os.Getenv(hvmDispatchUnrecognizedCritChildEnv) == "" {
		t.Skip("child-only: driven by TestUpdateHvmHeaderConsensusUnrecognizedErrorCrit via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	// currentHead P (activation block @11). Apply it -> state-id = P. P is also written to rawdb so the dispatcher's
	// findCommonAncestor (rawdb-only GetHeader) can resolve it.
	preP := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	p := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preP.Hash()})
	chain.tempHeaders[preP.Hash().String()] = preP
	chain.tempBlocks[preP.Hash().String()] = types.NewBlockWithHeader(preP)
	chain.tempHeaders[p.Hash().String()] = p.Header()
	chain.tempBlocks[p.Hash().String()] = p
	rawdb.WriteBlock(chain.db, p)
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(p.Header(), false, false))

	// newHead T: a DIRECT CHILD of P (so the single-apply arm runs), but its BLOCK is absent from disk + pen, so
	// apply returns the plain "unable to get block" error (a non-sentinel) -> the unrecognized-error crit fires.
	target := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: p.Hash()})
	// Deliberately do NOT seed target's block anywhere.
	chain.updateHvmHeaderConsensus(target.Header(), false)
	t.Fatalf("updateHvmHeaderConsensus returned for an unrecognized apply error; expected the dispatcher backstop to os.Exit")
}

func TestUpdateHvmHeaderConsensusUnrecognizedErrorCrit(t *testing.T) {
	cmd := exec.Command(os.Args[0], "-test.run=^TestUpdateHvmHeaderConsensusUnrecognizedErrorCritChild$", "-test.v")
	cmd.Env = append(os.Environ(), hvmDispatchUnrecognizedCritChildEnv+"=1")
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "the dispatcher unrecognized-error backstop must os.Exit non-zero, output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "Encountered an error applying hVM header state transition",
		"the crit must be the dispatcher's unrecognized-error backstop")
	require.NotContains(t, string(out), "updateHvmHeaderConsensus returned for an unrecognized apply error",
		"the backstop must os.Exit BEFORE returning (a returned-marker means it was downgraded)")
}

const hvmRestoreApplyErrCritChildEnv = "HVM_RESTORE_APPLY_ERR_CHILD"

// TestPerformFullHvmHeaderStateRestoreApplyErrorCritChild is the subprocess child: it seeds a disk chain whose
// activation block carries CORRUPT BtcAttr calldata, so the restore forward-walk's first apply fails with
// ErrInvalidHVMBlockFormat -> performFullHvmHeaderStateRestore log.Crits ("Failed to fully restore hVM state").
func TestPerformFullHvmHeaderStateRestoreApplyErrorCritChild(t *testing.T) {
	if os.Getenv(hvmRestoreApplyErrCritChildEnv) == "" {
		t.Skip("child-only: driven by TestPerformFullHvmHeaderStateRestoreApplyErrorCrit via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	gen := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(0), Time: hvm0Time - 500}) // pre-hVM0
	// Activation block (#1, Hvm0-active) carrying a 0x7C tx whose calldata is just the 4-byte selector — far below the
	// minimum serialized length, so ExtractBtcAttrData fails and apply returns ErrInvalidHVMBlockFormat.
	corrupt := types.NewTx(&types.BtcAttributesDepositedTx{
		To:   &types.BtcAttributesDepositedSenderAddress,
		Gas:  1_000_000,
		Data: types.UpdateHvmStateFuncBytes4[:],
	})
	block1 := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(1), Time: hvm0Time, ParentHash: gen.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{corrupt}})
	for _, b := range []*types.Block{gen, block1} {
		rawdb.WriteBlock(chain.db, b)
		rawdb.WriteCanonicalHash(chain.db, b.Hash(), b.NumberU64())
	}
	rawdb.WriteHeadBlockHash(chain.db, block1.Hash())
	chain.currentBlock.Store(block1.Header())

	chain.performFullHvmHeaderStateRestore()
	t.Fatalf("performFullHvmHeaderStateRestore returned despite a corrupt-calldata activation block; expected log.Crit")
}

func TestPerformFullHvmHeaderStateRestoreApplyErrorCrit(t *testing.T) {
	cmd := exec.Command(os.Args[0], "-test.run=^TestPerformFullHvmHeaderStateRestoreApplyErrorCritChild$", "-test.v")
	cmd.Env = append(os.Environ(), hvmRestoreApplyErrCritChildEnv+"=1")
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "a restore apply error must os.Exit non-zero, output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "Failed to fully restore hVM state",
		"the restore apply-error crit must fire on a corrupt block during the disk forward-walk")
	require.NotContains(t, string(out), "performFullHvmHeaderStateRestore returned despite",
		"the restore must os.Exit on the apply error, not return")
}

// Corrupt-state self-heal CONVERGENCE + IDEMPOTENCY. recoverReapplyHvmState responds to a suspected-corrupt
// lightweight view (fired from writeHeadBlock / setHeadBeyondRoot / SetCanonical when the EVM head is multi-block).
// Its contract: from ANY corrupt view, the wipe-and-rebuild lands byte-exact on the view a never-corrupted node
// holds, and recovering twice == once. This injects real corruption over replayed blocks, forcing the wipe-and-
// rebuild path. Tests that restore from a clean/genesis view never reach that path: re-applying onto an already-
// golden store takes the idempotent duplicate arm, so they would not catch a reset that is content-dependent,
// skipped, or early-stopping.
func TestRecoverReapplyHvmStateConvergesFromCorruption(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers + drives two full restore disk-walks")
	}
	const hvm0Time = uint64(1000)
	chain, regGenesis := newRegtestChainWithLightTBC(t, hvm0Time)
	evmGenesis := chain.GetHeaderByNumber(0)

	mineSeg := func(prev *wire.BlockHeader, n int, nonceBase uint32) ([]wire.BlockHeader, *wire.BlockHeader) {
		hs := make([]wire.BlockHeader, 0, n)
		p := prev
		for i := 0; i < n; i++ {
			h := mineRegtestChild(t, p, nonceBase+uint32(i))
			hs = append(hs, *h)
			p = h
		}
		return hs, p
	}
	seg1, t1 := mineSeg(regGenesis, 2, 100)
	seg2, t2 := mineSeg(t1, 2, 200)
	seg3, t3 := mineSeg(t2, 1, 300)

	mkBlock := func(num int64, parent *types.Header, seg []wire.BlockHeader, tip *wire.BlockHeader) *types.Block {
		c := tip.BlockHash()
		btc, err := types.MakeBtcAttributesDepositedTx(&c, seg)
		require.NoError(t, err)
		return types.NewBlockWithHeader(&types.Header{Number: big.NewInt(num), Time: hvm0Time + uint64(num), ParentHash: parent.Hash()}).
			WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc)}})
	}
	b1 := mkBlock(1, evmGenesis, seg1, t1)
	b2 := mkBlock(2, b1.Header(), seg2, t2)
	b3 := mkBlock(3, b2.Header(), seg3, t3)
	for _, b := range []*types.Block{b1, b2, b3} {
		rawdb.WriteBlock(chain.db, b)
		rawdb.WriteCanonicalHash(chain.db, b.Hash(), b.NumberU64())
	}
	rawdb.WriteHeadBlockHash(chain.db, b3.Hash())
	chain.currentBlock.Store(b3.Header())

	// PHASE A — golden: forward-apply b1..b3 and snapshot the clean view.
	for _, b := range []*types.Block{b1, b2, b3} {
		require.NoError(t, chain.applyHvmHeaderConsensusUpdate(b.Header(), false, true))
	}
	goldH, goldTip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	goldSid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	goldTipHash := goldTip.BlockHash()

	assertGolden := func(stage string) {
		h, tip, e := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
		require.NoError(t, e)
		sid, e := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, e)
		tipHash := tip.BlockHash()
		require.Equalf(t, goldTipHash[:], tipHash[:], "%s: tip must converge to golden", stage)
		require.Equalf(t, goldH, h, "%s: height must converge to golden", stage)
		require.Equalf(t, goldSid[:], sid[:], "%s: upstream-state-id must converge to golden", stage)
	}

	// PHASE B — corrupt the live view WITHOUT touching disk: a torn state-id that disagrees with the committed
	// headers (the reliable corruption signal; reset wipes it).
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))
	tornSid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId[:], tornSid[:], "the set upstream-state-id must be read back exactly")
	require.NotEqual(t, goldSid[:], tornSid[:], "anti-vacuity: the corruption took (state-id no longer golden)")

	// PHASE C — self-heal via the real production entry point.
	chain.recoverReapplyHvmState("corrupt-recovery convergence test", consensus.ErrCorruptHVMHeaderOnlyModeState)
	assertGolden("after first recovery")

	// PHASE D — idempotency: recovering again leaves the (already-golden) view byte-exact.
	chain.recoverReapplyHvmState("idempotency re-run", consensus.ErrCorruptHVMHeaderOnlyModeState)
	assertGolden("after second recovery")
}

// TestHvmRevertUndoesHeaderBearingBlockAdvance is the consensus-critical regression for the revert path:
// when a block advances the TBC consensus state (upstream-state-id + BTC headers) but is then rejected by
// EVM Process/ValidateState, the revert must roll the lightweight TBC node fully back to the pre-insert EVM
// tip (tbcHeader) — restoring the upstream-state-id and removing every BTC header the rejected block added.
//
// Reproduces the insert sequence the revert path handles, at the lightweight (consensus) seam:
//  1. apply currentHead (activation block) -> state-id = currentHead   (this is "tbcHeader", the EVM tip
//     the TBC represents at insert entry, captured in production via getHeaderModeTBCEVMHeader).
//  2. apply a header-bearing block N -> AddExternalHeaders advances the tip and state-id to N (mirrors the
//     insert's forward updateHvmHeaderConsensus(block) advance).
//  3. "EVM rejects N" -> revert via walkHvmHeaderConsensusBack(N, tbcHeader).
//
// Step 3 is the unwind the revert helper drives: revertHvmStateAfterInvalidBlock calls
// updateHvmHeaderConsensus(tbcHeader, true), which for a linear rejected block (tbcHeader is N's ancestor,
// the common case) dispatches to walkHvmHeaderConsensusBack to remove N's headers and roll the state-id
// back. Two parts of updateHvmHeaderConsensus are not exercised: findCommonAncestor (pure geometry routing,
// and it reads headers via GetHeader from disk — in production it walks persisted canonical headers, not
// this test's holding-pen-only blocks), and the trailing full-node indexer sync
// (updateFullTBCToLightweight, gated by bool=true) which needs a live vm.TBCFullNode — out of scope, the
// same reason related tests use attemptPrefetch=false. Full-node-lag is covered by TestIsHvmFullNodeBehind.
//
// Scope: this locks in the revert unwind, not the wiring. The novel surface is the two
// revertHvmStateAfterInvalidBlock call sites in insertChain's EVM-failure paths (after processor.Process
// and validator.ValidateState, under the isHvmActivated guard); deleting both would leave this green. That
// wiring cannot run in a unit test (needs the full insert path -> a live vm.TBCFullNode, plus
// findCommonAncestor's disk reads); this test guards the behavior the wiring invokes — that the revert
// fully undoes a rejected block's TBC advance (state-id + headers).
//
// The assertion that the added BTC headers are removed (tip restored to the checkpoint), not just the
// state-id rolled back, is what makes this a revert regression rather than a generic state-id check: a
// refactor that left the rejected block's headers in the lightweight leveldb would leave the consensus view
// diverged, and this would catch it.
func TestHvmRevertUndoesHeaderBearingBlockAdvance(t *testing.T) {
	const hvm0Time = uint64(1000)
	// Regtest harness: the apply path enforces PoW, so the header-bearing block's headers must be really
	// mined (regtest PoW is mineable in ~2 nonces). Near-genesis => contextual defers; PoW passes.
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)

	// Pre-insert state: currentHead is the activation block (no BtcAttr). Applying it sets the
	// upstream-state-id to currentHead — this is the "tbcHeader" the revert must restore to.
	preActivation := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	currentHead := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preActivation.Hash()})

	// Block N: a header-bearing BtcAttr block built on currentHead, carrying 3 mined contiguous regtest
	// headers chained off the lightweight checkpoint. Near-genesis => the contextual validator defers; the
	// apply-path PoW gate requires real work, so they are really mined (cheap on regtest).
	headers := make([]wire.BlockHeader, 0, 3)
	prev := genesis
	for i := 0; i < 3; i++ {
		h := mineRegtestChild(t, prev, uint32(2000+i)*101+1)
		headers = append(headers, *h)
		prev = h
	}
	newTip := headers[len(headers)-1].BlockHash()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&newTip, headers)
	require.NoError(t, err)
	blockN := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: currentHead.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})

	// Seed the holding pen so the revert walk (updateHvmHeaderConsensus -> findCommonAncestor ->
	// walkHvmHeaderConsensusBack -> unapply) can resolve every block/header it traverses.
	chain.tempHeaders[preActivation.Hash().String()] = preActivation
	chain.tempBlocks[preActivation.Hash().String()] = types.NewBlockWithHeader(preActivation)
	for _, b := range []*types.Block{currentHead, blockN} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
	}

	checkpoint := genesis.BlockHash()

	// Step 1: establish the pre-insert state (tbcHeader == currentHead).
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(currentHead.Header(), false, true))
	sidPre, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, currentHead.Hash().Bytes(), sidPre[:], "pre-insert state-id must be currentHead (tbcHeader)")
	_, tipPre, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipPreHash := tipPre.BlockHash()
	require.Equal(t, checkpoint[:], tipPreHash[:], "pre-insert tip must be the genesis checkpoint")

	// Step 2: forward advance for block N (state-id -> N, tip -> newTip, 3 headers added).
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true))
	sidAdvanced, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sidAdvanced[:], "after forward-apply the state-id must point at block N")
	_, tipAdvanced, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipAdvancedHash := tipAdvanced.BlockHash()
	require.Equal(t, newTip[:], tipAdvancedHash[:], "after forward-apply the tip must be N's claimed canonical tip")

	// Step 3: "EVM rejects N" -> revert to tbcHeader (the unwind the revert helper drives for a linear block).
	require.NoError(t, chain.walkHvmHeaderConsensusBack(blockN.Header(), currentHead.Header()),
		"revert to the pre-insert tip must succeed")

	// ASSERTIONS: both the state-id and the added BTC headers are fully undone.
	sidReverted, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, currentHead.Hash().Bytes(), sidReverted[:],
		"revert must restore the upstream-state-id to the pre-insert tip (not leave it at the rejected block)")
	require.NotEqual(t, blockN.Hash().Bytes(), sidReverted[:],
		"a state-id left at block N means the rejected block's advance was not undone")
	_, tipReverted, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipRevertedHash := tipReverted.BlockHash()
	require.Equal(t, checkpoint[:], tipRevertedHash[:],
		"revert must REMOVE the BTC headers the rejected block added (tip back to the checkpoint)")
	for _, h := range headers {
		_, _, err := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, h.BlockHash())
		require.Error(t, err, "revert must remove header %s from the store", h.BlockHash())
	}
}

// TestHvmRevertFirstHvmBlockNilGuard exercises revertHvmStateAfterInvalidBlock on its tbcHeader==nil branch
// (the first-hVM/activation block case): the pre-state is TBC genesis, which cannot be expressed as an
// EVM-header revert target, so the helper must safely no-op (log + return) and rely on restart recovery —
// not panic and not mutate the consensus state. This branch takes no full-TBC-node path, so it runs
// directly. Guards against a change that dereferences a nil tbcHeader or reverts the activation block in
// place.
func TestHvmRevertFirstHvmBlockNilGuard(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	sidBefore, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)

	block := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time})
	require.NotPanics(t, func() { chain.revertHvmStateAfterInvalidBlock(nil, block) },
		"the first-hVM-block (nil tbcHeader) branch must be a safe no-op, never a nil deref")

	sidAfter, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, sidBefore[:], sidAfter[:], "the nil-tbcHeader branch must not mutate the upstream-state-id")
}
