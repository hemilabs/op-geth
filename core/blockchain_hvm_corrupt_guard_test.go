package core

import (
	"bytes"
	"log/slog"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/stretchr/testify/require"

	"github.com/hemilabs/heminetwork/service/tbc"
)

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
