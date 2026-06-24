package core

import (
	"bytes"
	"context"
	"fmt"
	"log/slog"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/metrics"
	"github.com/ethereum/go-ethereum/params"
	"github.com/hemilabs/heminetwork/database"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

// TestGetHvmPhase0ActivationBlock pins getHvmPhase0ActivationBlock's descent: from the current tip it must
// return the FIRST hVM-activated block (the one whose parent is the last pre-activation block). This walk is
// what performFullHvmHeaderStateRestore uses to find where to start replaying; a regression in the IsHvm0
// break or the parent-walk would start recovery at the wrong block. The function reads only the EVM header
// chain + chainConfig.IsHvm0 (never the TBC node), so a plain chain crossing Hvm0Time + hvmEnabled set
// directly exercises it without a live TBC harness. Block time is parent.Time+10 (chain_makers.go), so with
// genesis time 0 and Hvm0Time=55 the first hVM-active block is #6 (time 60); #5 (time 50) is pre-activation.
func TestGetHvmPhase0ActivationBlock(t *testing.T) {
	cfg := *params.TestChainConfig
	hvm0 := uint64(55)
	cfg.Hvm0Time = &hvm0
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}

	db, blocks, _ := GenerateChainWithGenesis(gspec, ethash.NewFaker(), 10, func(i int, b *BlockGen) {})

	chain, err := NewBlockChain(db, gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)
	_, err = chain.InsertChain(blocks)
	require.NoError(t, err)

	// getHvmPhase0ActivationBlock requires hvmEnabled; set it directly (it never touches the TBC node).
	chain.hvmEnabled = true

	act, err := chain.getHvmPhase0ActivationBlock()
	require.NoError(t, err)
	require.NotNil(t, act)

	// The returned block must be the first hVM-active one: itself activated, its parent not.
	require.True(t, cfg.IsHvm0(act.Time), "the returned activation block must be hVM-active (time=%d)", act.Time)
	require.Greater(t, act.Number.Uint64(), uint64(0), "the activation block cannot be genesis")
	parent := chain.GetHeaderByNumber(act.Number.Uint64() - 1)
	require.NotNil(t, parent)
	require.False(t, cfg.IsHvm0(parent.Time), "the activation block's parent must be pre-activation (time=%d)", parent.Time)

	// With the fixed +10s/block geometry, that is block #6.
	require.Equal(t, uint64(6), act.Number.Uint64(), "first hVM-active block must be #6 for Hvm0Time=55")
}

// TestGetHvmPhase0ActivationBlockAtGenesisBoundary pins the genesis-terminator guard: when Hvm0Time <= genesis.Time
// (an hVM-from-genesis deployment), IsHvm0(genesis) is true, so the ONLY thing stopping the parent-walk from
// descending onto genesis (#0, which cannot carry a BtcAttr tx) is the `header.Number > 0` guard — the activation
// block must be #1. The existing test uses Hvm0Time=55 (mid-chain), where the parent is naturally pre-activation
// and the >0 guard is never the load-bearing terminator. A mutant dropping `&& Number > 0` returns genesis and
// performFullHvmHeaderStateRestore would then apply genesis.
func TestGetHvmPhase0ActivationBlockAtGenesisBoundary(t *testing.T) {
	cfg := *params.TestChainConfig
	hvm0 := uint64(0) // genesis time is 0 -> IsHvm0(genesis) is true (<=)
	cfg.Hvm0Time = &hvm0
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}
	db, blocks, _ := GenerateChainWithGenesis(gspec, ethash.NewFaker(), 8, func(i int, b *BlockGen) {})
	chain, err := NewBlockChain(db, gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)
	_, err = chain.InsertChain(blocks)
	require.NoError(t, err)
	chain.hvmEnabled = true

	require.True(t, cfg.IsHvm0(chain.GetHeaderByNumber(0).Time), "precondition: genesis itself is hVM-active at this boundary")
	act, err := chain.getHvmPhase0ActivationBlock()
	require.NoError(t, err)
	require.NotNil(t, act)
	require.Equal(t, uint64(1), act.Number.Uint64(), "activation must be block #1, never genesis (the >0 terminator guard)")
	require.Equal(t, chain.GetHeaderByNumber(0).Hash(), act.ParentHash, "activation block #1's parent is genesis")
}

// TestGetHvmPhase0ActivationBlockFastDescent exercises the >1000-block FAST-DESCENT loop in
// getHvmPhase0ActivationBlock (`for cursor.Number > 1000 { header := GetHeaderByNumber(n-1000); if !IsHvm0 break; cursor = header }`)
// that the existing 8-10 block tests never reach (the loop body never executes below 1001 blocks). With a 2500-block
// chain (time = 10*number) and Hvm0Time=14995 (first hVM-active block is #1500 @15000; #1499 @14990 is not — and
// 1500 is deliberately NOT a multiple of 1000), the fast loop must jump #2500->#1500, then probe #1500->#500
// (pre-activation) and break, after which the parent-walk lands exactly on #1500. A mutant dropping `cursor = header`
// infinite-loops (test timeout); a mutant corrupting the descent lands on the wrong block. Reads only the EVM header
// chain + chainConfig.IsHvm0 (never the TBC node), so it is corpus-free.
func TestGetHvmPhase0ActivationBlockFastDescent(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: builds + inserts 2500 EVM blocks to cross the fast-descent threshold")
	}
	cfg := *params.TestChainConfig
	hvm0 := uint64(14995) // strictly between block #1499 (time 14990) and #1500 (time 15000) -> first active is #1500
	cfg.Hvm0Time = &hvm0
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}
	db, blocks, _ := GenerateChainWithGenesis(gspec, ethash.NewFaker(), 2500, func(i int, b *BlockGen) {})
	chain, err := NewBlockChain(db, gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)
	_, err = chain.InsertChain(blocks)
	require.NoError(t, err)
	chain.hvmEnabled = true

	require.Greater(t, chain.CurrentBlock().Number.Uint64(), uint64(1001), "precondition: tip must exceed the fast-descent threshold")
	act, err := chain.getHvmPhase0ActivationBlock()
	require.NoError(t, err)
	require.NotNil(t, act)
	require.Equal(t, uint64(1500), act.Number.Uint64(), "fast descent must land on the first hVM-active block #1500")
	require.True(t, cfg.IsHvm0(act.Time), "the returned activation block must be hVM-active")
	require.False(t, cfg.IsHvm0(chain.GetHeaderByNumber(act.Number.Uint64()-1).Time), "its parent must be pre-activation")
}

// Unapply of a HEADER-BEARING Hvm0 ACTIVATION block. The activation block is special: its parent is pre-hVM, so
// unapplyHvmHeaderConsensusUpdate must roll the upstream-state-id back to the genesis marker (hVMGenesisUpstreamId,
// NOT a prior BtcAttr tip) AND drive RemoveExternalHeaders to unwind the activation block's real BTC headers all the
// way to the genesis checkpoint. No existing test exercises this combination: the empty-but-present activation
// unapply takes the headerless no-op branch (no RemoveExternalHeaders); the round-trip test only unapplies a
// steady-state child back to the post-activation state, never through the activation block to genesis.
func TestUnapplyHeaderBearingActivationBlockRestoresGenesis(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
	mineHeaders := func(prev *wire.BlockHeader, n int, nonceBase uint32) ([]wire.BlockHeader, *wire.BlockHeader) {
		hs := make([]wire.BlockHeader, 0, n)
		p := prev
		for i := 0; i < n; i++ {
			h := mineRegtestChildBits(t, p, regtestPowBits, nonceBase+uint32(i))
			hs = append(hs, *h)
			p = h
		}
		return hs, p
	}

	// Snapshot the pristine genesis state (the rollback target).
	genHeight, genTip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	genSid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId, *genSid, "precondition: fresh node is at the genesis upstream-state-id")
	genTipHash := genTip.BlockHash()

	// Header-bearing activation block A (parent pre-activation) carrying 3 real mined headers off the genesis checkpoint.
	aHeaders, aTip := mineHeaders(genesis, 3, 100)
	aCanon := aTip.BlockHash()
	aBtc, err := types.MakeBtcAttributesDepositedTx(&aCanon, aHeaders)
	require.NoError(t, err)
	aParent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	aHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: aParent.Hash()}
	blockA := types.NewBlockWithHeader(aHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(aBtc)}})
	chain.tempHeaders[aParent.Hash().String()] = aParent
	chain.tempBlocks[aParent.Hash().String()] = types.NewBlockWithHeader(aParent)
	chain.tempHeaders[blockA.Hash().String()] = blockA.Header()
	chain.tempBlocks[blockA.Hash().String()] = blockA

	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	_, tipA, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, aTip.BlockHash(), tipA.BlockHash(), "apply advanced the tip to A's mined chain tip")
	sidA, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockA.Hash().Bytes(), sidA[:], "apply set the state-id to A")

	// UNAPPLY the activation block: must restore the genesis checkpoint tip AND the genesis upstream-state-id
	// (the activation special-case), having removed all of A's real headers.
	require.NoError(t, chain.unapplyHvmHeaderConsensusUpdate(blockA.Header()))
	hBack, tipBack, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, genHeight, hBack, "unapply of the activation block must restore the genesis height")
	tipBackHash := tipBack.BlockHash()
	require.Equal(t, genTipHash[:], tipBackHash[:], "unapply must restore the exact genesis checkpoint tip")
	sidBack, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId, *sidBack, "unapply of the activation block must reset the state-id to the genesis marker")
	for _, h := range aHeaders { // every activation header removed
		_, _, e := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, h.BlockHash())
		require.Error(t, e, "activation header must be removed on unapply")
	}
}

// Apply-path + snap/build observe gaps the regtest harness did not yet reach:
//   - the apply path validates the ENTIRE batch and must reject the whole block atomically (no partial prefix
//     commit) when a trailing header is contextually wrong;
//   - the apply-path PoW gate must fail CLOSED to recoverable-corrupt (not silent-accept / not bad-block) on an
//     unknown network;
//   - observeSnapBtcDiff must route an unconnected (incomplete) verdict with contextualRan set;
//   - enforceableBTCBatch must reject on the PoW-first arm (hash above target), and the gate must suppress it
//     when not enforceable;
//   - a PoW-failing header must NOT short-circuit the contextual stage of observeSnapBtcDiff.
//
// notFoundParentLookup resolves exactly one candidate header and returns a genuine (wrapped) database.NotFoundError
// for every other hash — so the batch validator classifies the candidate's absent parent as NOT-FOUND (unconnected),
// distinct from an IO error (which the generic-error fakeBtcLookup would produce -> unavailable).
type notFoundParentLookup struct {
	candidate  *wire.BlockHeader
	candHeight uint64
}

func (l *notFoundParentLookup) BlockHeaderByHash(_ context.Context, h chainhash.Hash) (*wire.BlockHeader, uint64, error) {
	if h == l.candidate.BlockHash() {
		return l.candidate, l.candHeight, nil
	}
	return nil, 0, fmt.Errorf("db block header by hash: %w", database.NotFoundError("block header not found"))
}

// forgePoWFailingChild builds a child of prev with the regtest Bits but a nonce whose hash EXCEEDS the regtest
// target (no real work). The mining oracle (HashToBig/CompactToBig) is independent of the production PoW check.
func forgePoWFailingChild(t *testing.T, prev *wire.BlockHeader, nonceBase uint32) *wire.BlockHeader {
	t.Helper()
	target := blockchain.CompactToBig(regtestPowBits)
	h := &wire.BlockHeader{Version: 4, PrevBlock: prev.BlockHash(), Timestamp: prev.Timestamp.Add(60 * time.Second), Bits: regtestPowBits}
	for i := uint32(0); i < 1<<22; i++ {
		h.Nonce = nonceBase + i
		hash := h.BlockHash()
		if blockchain.HashToBig(&hash).Cmp(target) > 0 {
			return h
		}
	}
	t.Fatal("failed to forge a PoW-failing regtest child within 2^22 nonces")
	return nil
}

// TestHvmApplyPathRejectsWholeBatchOnWrongTrailingHeader: the apply path validates the ENTIRE batch and must
// reject the block atomically when a trailing header is contextually wrong — it must NOT commit the valid leading
// headers and drop only the bad one (the build path truncates; the apply path is all-or-nothing). The tip-unchanged
// + leading-headers-absent oracle is what kills a partial-commit mutant; ErrInvalidHVMHeaders alone would not.
func TestHvmApplyPathRejectsWholeBatchOnWrongTrailingHeader(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)

	h1 := *mineRegtestChild(t, p, 100)
	h2 := *mineRegtestChild(t, &h1, 110)
	h3 := *mineRegtestChildBits(t, &h2, 0x207ffffe, 120) // PoW-valid but contextually-wrong difficulty

	// Precondition: the leading headers h1,h2 pass PoW, so the whole-batch rejection below is caused by the
	// CONTEXTUAL (difficulty) arm on h3 — not a PoW failure on h1/h2 (which would make the not-committed asserts vacuous).
	require.NoError(t, vm.CheckBTCHeaderBatchPoWForNetwork("localnet", []*wire.BlockHeader{&h1, &h2}),
		"precondition: the leading headers must pass PoW so only the contextual arm rejects the batch")

	err := applyForkBtcAttr(t, chain, 11, h3, []wire.BlockHeader{h1, h2, h3}, true)
	require.ErrorIs(t, err, consensus.ErrInvalidHVMHeaders, "a batch with a contextually-wrong trailing header must reject the whole block")

	_, tip, berr := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, berr)
	require.Equal(t, p.BlockHash(), tip.BlockHash(), "no partial commit: the tip must still be the pre-apply seeded tip")
	_, _, e1 := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, h1.BlockHash())
	require.Error(t, e1, "the valid leading header h1 must NOT be committed (whole-batch atomic reject)")
	_, _, e2 := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, h2.BlockHash())
	require.Error(t, e2, "the valid leading header h2 must NOT be committed")
}

// TestHvmApplyPathPoWGateUnknownNetworkIsCorrupt: the apply-path PoW gate must fail CLOSED to recoverable corrupt
// state (never silent-accept, never bad-block) when the network has no chaincfg params — the PoW-gate twin of the
// contextual-validator unavailable->corrupt arm. The only unknown-network coverage is the snap-observe path, which
// has the OPPOSITE (skip-and-proceed) semantics.
func TestHvmApplyPathPoWGateUnknownNetworkIsCorrupt(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	chain.tbcHeaderNodeConfig.Network = "zzz-no-chaincfg-params" // SupportsBTCNetwork == false
	require.True(t, chain.hvmDiffEnforceable.Load(), "precondition: the regtest boot is enforceable, so the gate runs")

	h := *mineRegtestChild(t, genesis, 1) // PoW-valid; the gate fails on the network, not the work
	require.ErrorIs(t, vm.CheckBTCHeaderBatchPoWForNetwork("zzz-no-chaincfg-params", []*wire.BlockHeader{&h}),
		vm.ErrBTCHeaderContextUnavailable, "precondition: the PoW gate yields the skip sentinel for an unknown network")

	err := applyForkBtcAttr(t, chain, 11, h, []wire.BlockHeader{h}, true)
	require.ErrorIs(t, err, consensus.ErrCorruptHVMHeaderOnlyModeState, "an unknown-network PoW gate must fail closed to recoverable corrupt")
	require.NotErrorIs(t, err, consensus.ErrInvalidHVMHeaders, "it must NOT be classified a bad block")

	_, tip, berr := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, berr)
	require.Equal(t, genesis.BlockHash(), tip.BlockHash(), "no commit on the corrupt arm: tip stays at genesis")
}

// TestObserveSnapBtcDiffIncompleteOnUnconnected: an above-floor header whose parent is absent must flow through
// observeSnapBtcDiff to the snapObsIncomplete arm WITH contextualRan set (ErrBTCBatchUnconnected). This is the
// exact result shape the snap + migration callers route to a distinct INCOMPLETE warn; the regtest harness always
// has fully-seeded ancestry, so it never produces this.
func TestObserveSnapBtcDiffIncompleteOnUnconnected(t *testing.T) {
	const genesisOffset = uint64(883092)
	var absentParent chainhash.Hash
	absentParent[0] = 0xde
	hdr := &wire.BlockHeader{Version: 1, PrevBlock: absentParent, Bits: 0x1d00ffff, Timestamp: time.Unix(1_600_000_000, 0), Nonce: 1}
	// The candidate resolves (above the enforce floor) but its parent is genuinely NotFound -> unconnected.
	f := &notFoundParentLookup{candidate: hdr, candHeight: 887040}

	obs := observeSnapBtcDiff(context.Background(), f, "mainnet", genesisOffset, []*wire.BlockHeader{hdr})
	require.True(t, obs.contextualRan, "the above-floor header must be contextually validated")
	require.Equal(t, 1, obs.enforcedCount)
	require.Equal(t, snapObsIncomplete, obs.ctxObservation, "an unconnected above-floor header must classify INCOMPLETE")
	require.ErrorIs(t, obs.ctxErr, vm.ErrBTCBatchUnconnected)
}

// TestEnforceableBTCBatchPoWArm: enforceableBTCBatch checks PoW BEFORE contextual difficulty, so a header whose
// hash misses its target must be rejected on the PoW arm — the build path must never package it. The existing gate
// test only feeds a PoW-VALID header (it asserts PoW passes as a precondition), leaving the PoW-first arm unrun.
func TestEnforceableBTCBatchPoWArm(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)
	forged := forgePoWFailingChild(t, p, 1)
	batch := []*wire.BlockHeader{forged}

	require.Error(t, vm.CheckBTCHeaderBatchPoWForNetwork("localnet", batch), "precondition: the forged header fails PoW")
	require.True(t, chain.hvmDiffEnforceable.Load())
	require.Error(t, chain.enforceableBTCBatch(batch), "enforceable: a hash-above-target header must be rejected on the PoW arm")

	chain.hvmDiffEnforceable.Store(false)
	require.NoError(t, chain.enforceableBTCBatch(batch), "not enforceable: the gate suppresses even the PoW judgement")
}

// TestObserveSnapBtcDiffPoWFailDoesNotShortCircuitContextual: observeSnapBtcDiff runs the PoW check over ALL
// headers but must still run the contextual stage afterward. A base containing BOTH a PoW-failing header AND a
// resolvable above-floor enforceable suffix must set powFailed AND contextualRan — a `return r` after powFailed
// would silence the contextual observation.
func TestObserveSnapBtcDiffPoWFailDoesNotShortCircuitContextual(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	clearance, err := vm.BTCFloorClearanceForNetwork("localnet")
	require.NoError(t, err)
	enforceFloor := btcSnapEnforceFloor(0, clearance)
	total := int(enforceFloor) + 16
	hdrs := buildAndSeedRegtestChain(t, chain, genesis, total, -1, 0) // clean, fully-mined above-floor base

	// Append a PoW-failing child (correct difficulty, hash above target) as the LAST element so firstHeight still
	// resolves on headers[0] and the clean above-floor prefix is still contextually validated.
	forged := forgePoWFailingChild(t, hdrs[len(hdrs)-1], 1)
	allHdrs := append(append([]*wire.BlockHeader{}, hdrs...), forged)

	obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, allHdrs)
	require.True(t, obs.powFailed, "the appended forged header must flag the PoW observation")
	require.True(t, obs.contextualRan, "PoW failure must NOT short-circuit the contextual stage")
}

// TestApplyUnapplyHeaderBearingRoundTrip is a property test for hVM apply/unapply symmetry — the invariant a
// reorg depends on: applying a header-bearing BtcAttr block then unapplying it must leave the lightweight TBC
// view (tip hash, tip height, upstream-state-id) BYTE-IDENTICAL to before, for any header count. The existing
// empty-but-present tests cover the no-header case and a single header-bearing apply; this exercises the
// steady-state unapply (parent is itself an hVM block, so the rollback target is a real prior BtcAttr tip,
// not the activation special-case) across several header counts. A regression where unapply removes too few
// or too many headers, or restores the wrong upstream-state-id, fails the round-trip assertion.
func TestApplyUnapplyHeaderBearingRoundTrip(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)

	mineHeaders := func(prev *wire.BlockHeader, n int, nonceBase uint32) ([]wire.BlockHeader, *wire.BlockHeader) {
		hs := make([]wire.BlockHeader, 0, n)
		p := prev
		for i := 0; i < n; i++ {
			h := mineRegtestChildBits(t, p, regtestPowBits, nonceBase+uint32(i))
			hs = append(hs, *h)
			p = h
		}
		return hs, p
	}

	// Activation block A: 2 mined headers off the genesis checkpoint, parent pre-activation. After this, the
	// lightweight node is in a steady (post-activation) state whose upstream-state-id is A.
	aHeaders, aTip := mineHeaders(genesis, 2, 100)
	aCanon := aTip.BlockHash()
	aBtc, err := types.MakeBtcAttributesDepositedTx(&aCanon, aHeaders)
	require.NoError(t, err)
	aParent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	aHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: aParent.Hash()}
	blockA := types.NewBlockWithHeader(aHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(aBtc)}})
	chain.tempHeaders[aParent.Hash().String()] = aParent
	chain.tempBlocks[aParent.Hash().String()] = types.NewBlockWithHeader(aParent)
	chain.tempHeaders[blockA.Hash().String()] = blockA.Header()
	chain.tempBlocks[blockA.Hash().String()] = blockA
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true), "apply activation block A")

	// Snapshot the post-A steady state — the round-trip target.
	heightA, tipAHeader, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	sidA, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockA.Hash().Bytes(), sidA[:], "post-A upstream-state-id must be A")
	tipAHash := tipAHeader.BlockHash()

	for _, n := range []int{1, 2, 3, 5} {
		// Steady-state block B (parent A) carrying n real headers off the post-A tip.
		bHeaders, _ := mineHeaders(tipAHeader, n, 1000+uint32(n)*37)
		bTip := bHeaders[len(bHeaders)-1].BlockHash()
		bBtc, err := types.MakeBtcAttributesDepositedTx(&bTip, bHeaders)
		require.NoError(t, err)
		bHeader := &types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: blockA.Hash()}
		blockB := types.NewBlockWithHeader(bHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(bBtc)}})
		chain.tempHeaders[blockB.Hash().String()] = blockB.Header()
		chain.tempBlocks[blockB.Hash().String()] = blockB

		require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockB.Header(), false, true), "apply B with %d headers", n)
		_, tipB, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
		require.NoError(t, err)
		tipBHash := tipB.BlockHash()
		require.Equal(t, bTip[:], tipBHash[:], "apply of B (%d headers) must advance the tip to B's chain tip", n)

		require.NoError(t, chain.unapplyHvmHeaderConsensusUpdate(blockB.Header()), "unapply B with %d headers", n)

		// Round-trip property: post-unapply view must equal the post-A view exactly.
		heightBack, tipBack, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
		require.NoError(t, err)
		sidBack, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		tipBackHash := tipBack.BlockHash()
		require.Equal(t, heightA, heightBack, "unapply of B (%d headers) must restore the tip height", n)
		require.Equal(t, tipAHash[:], tipBackHash[:], "unapply of B (%d headers) must restore the exact tip", n)
		require.Equal(t, sidA[:], sidBack[:], "unapply of B (%d headers) must restore the exact upstream-state-id", n)

		delete(chain.tempHeaders, blockB.Hash().String())
		delete(chain.tempBlocks, blockB.Hash().String())
	}
}

// TestUnapplyHvmHeaderConsensusUpdateOrphanedParentBlockRecoverable pins the BLOCK-store half of the unapply
// orphaned-parent guard. unapplyHvmHeaderConsensusUpdate guards the parent-HEADER lookup (prevBlock==nil), but
// for a header-bearing block it then walks back to the previous BtcAttr tip via the separate BLOCK store
// (getBlockFromDiskOrHoldingPen) and dereferences cursor.Time(). The two stores differ: a parent's header can
// resolve while its full block is absent (a deep reorg/rewind orphaned the body). That cursor.Time() must not
// nil-panic — the function returns the recoverable consensus.ErrCorruptHVMHeaderOnlyModeState sentinel (which
// the walkHvmHeaderConsensusBack caller routes through recovery, not crit). A mutation removing the cursor==nil
// guard panics here; without the guard a header-resolves/block-absent parent crashes the process on reorg.
func TestUnapplyHvmHeaderConsensusUpdateOrphanedParentBlockRecoverable(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)

	mine := func(prev *wire.BlockHeader, n int, nonceBase uint32) ([]wire.BlockHeader, *wire.BlockHeader) {
		hs := make([]wire.BlockHeader, 0, n)
		p := prev
		for i := 0; i < n; i++ {
			h := mineRegtestChildBits(t, p, regtestPowBits, nonceBase+uint32(i))
			hs = append(hs, *h)
			p = h
		}
		return hs, p
	}

	// Activation block A (header-bearing, parent pre-activation), then steady-state block B (parent A).
	aHeaders, aTip := mine(genesis, 2, 100)
	aCanon := aTip.BlockHash()
	aBtc, err := types.MakeBtcAttributesDepositedTx(&aCanon, aHeaders)
	require.NoError(t, err)
	aParent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: aParent.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(aBtc)}})
	chain.tempHeaders[aParent.Hash().String()] = aParent
	chain.tempBlocks[aParent.Hash().String()] = types.NewBlockWithHeader(aParent)
	chain.tempHeaders[blockA.Hash().String()] = blockA.Header()
	chain.tempBlocks[blockA.Hash().String()] = blockA
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true), "apply activation block A")

	_, tipA, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	bHeaders, _ := mine(tipA, 1, 5000)
	bTip := bHeaders[len(bHeaders)-1].BlockHash()
	bBtc, err := types.MakeBtcAttributesDepositedTx(&bTip, bHeaders)
	require.NoError(t, err)
	blockB := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: blockA.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(bBtc)}})
	chain.tempHeaders[blockB.Hash().String()] = blockB.Header()
	chain.tempBlocks[blockB.Hash().String()] = blockB
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockB.Header(), false, true), "apply steady-state block B")

	// Orphan A's BLOCK but keep its HEADER: the prevBlock (header) guard passes, but the walk-back's
	// getBlockFromDiskOrHoldingPen(A) returns nil → cursor.Time() would nil-panic without the nil-cursor guard.
	delete(chain.tempBlocks, blockA.Hash().String())
	require.NotNil(t, chain.getHeaderFromDiskOrHoldingPen(blockA.Hash()),
		"A's header must still resolve (only the block is orphaned, so the prevBlock guard does not fire first)")

	var got error
	require.NotPanics(t, func() { got = chain.unapplyHvmHeaderConsensusUpdate(blockB.Header()) },
		"an orphaned parent BLOCK on the unapply walk-back must not nil-deref")
	require.ErrorIs(t, got, consensus.ErrCorruptHVMHeaderOnlyModeState,
		"unapply with an unresolvable parent block must return the recoverable corrupt-state sentinel")

	// The recoverable corrupt return must NOT have mutated the consensus view: B stays applied (tip + state-id
	// unchanged) and all of B's headers remain present. Kills a mutant that removes headers or rolls the state-id
	// back BEFORE returning the sentinel (such a side-effect would pass the error-class check above but silently
	// diverge the lightweight TBC view).
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, bTip, tipAfter.BlockHash(), "a corrupt-return unapply must leave the BTC tip at B unchanged")
	sidAfter, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockB.Hash().Bytes(), sidAfter[:], "a corrupt-return unapply must leave the upstream-state-id at B")
	for _, h := range bHeaders {
		_, _, e := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, h.BlockHash())
		require.NoError(t, e, "B's headers must remain present after a corrupt-return unapply")
	}
}

// Operator-facing diagnostics on the walkHvmHeaderConsensusBack entry/loop guards. Both return the bare sentinel
// consensus.ErrBadTraversalGeometry (whose .Error() is "bad traversal geometry", NOT the diagnostic string), so the
// descriptive message lives only in log.Error — pinned here via log capture, alongside the sentinel. Existing walkBack
// callers (reorg_fork, revert) pass only valid geometry, so neither guard was covered.
func TestWalkHvmHeaderConsensusBackBadGeometry(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)
	lower := &types.Header{Number: big.NewInt(15), Time: hvm0Time}
	higher := &types.Header{Number: big.NewInt(20), Time: hvm0Time}

	var buf bytes.Buffer
	prev := log.Root()
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(&buf, slog.LevelDebug, false)))
	err := chain.walkHvmHeaderConsensusBack(lower, higher) // currentHead(15) <= newHead(20) -> bad geometry
	log.SetDefault(prev)

	require.ErrorIs(t, err, consensus.ErrBadTraversalGeometry, "walking back to a higher target is bad geometry")
	require.Contains(t, buf.String(), "Cannot walk hVM consensus backwards", "the backwards bad-geometry diagnostic must be logged")
	require.Contains(t, buf.String(), "bad geometry")
	// Equal height is also bad geometry (the guard is <=).
	require.ErrorIs(t, chain.walkHvmHeaderConsensusBack(lower, lower), consensus.ErrBadTraversalGeometry,
		"equal-height currentHead/newHead is also bad geometry")
}

func TestWalkHvmHeaderConsensusBackBadAncestor(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)
	checkpoint := lightTip.BlockHash()

	preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})
	// currentHead: a headerless empty-present block @12 whose real parent is blockA @11 (so its unwind is corpus-free).
	currentHead := emptyPresentBtcAttrBlock(t, 12, hvm0Time+1, blockA.Header(), checkpoint)
	chain.tempHeaders[preAct.Hash().String()] = preAct
	chain.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
	for _, b := range []*types.Block{blockA, currentHead} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
	}
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(currentHead.Header(), false, true))

	// A WRONG ancestor at height 11, distinct from blockA: walking back from currentHead@12 unapplies it, reaches
	// blockA@11 (currentHead's real parent) whose height collides with wrongAncestor@11 but whose hash differs ->
	// the "impossible" broken-ancestry branch fires (bad ancestor), not a real unwind to a wrong target.
	wrongAncestor := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: common.HexToHash("0xfeedface")}
	require.NotEqual(t, blockA.Hash(), wrongAncestor.Hash(), "anti-vacuity: the wrong ancestor must differ from the real one")

	var buf bytes.Buffer
	prev := log.Root()
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(&buf, slog.LevelDebug, false)))
	err := chain.walkHvmHeaderConsensusBack(currentHead.Header(), wrongAncestor)
	log.SetDefault(prev)

	require.ErrorIs(t, err, consensus.ErrBadTraversalGeometry, "a height-collision with a hash mismatch is a broken ancestry (bad traversal geometry)")
	require.Contains(t, buf.String(), "was expecting", "the bad-ancestor diagnostic must be logged")
}

// The Bitcoin-Attributes-Deposited build cache is keyed on btcAttrCacheKey{evmTip, lightTip, fullTip}. The
// end-to-end builder (getBitcoinAttributesForNextBlock) needs a live vm.TBCFullNode and is out of unit-test
// scope, so these tests pin the liveness-relevant property of the fix directly (this is the sequencer build
// path — a cache bug halts the local sequencer; it is not a consensus-safety/split concern, since
// validators re-derive the BtcAttr independently): the cache is invalidated by a change in any of the three
// dimensions, in particular the full-node BTC view (fullTip), which the original EVM-tip-only key ignored,
// causing a stale BtcAttr to be re-served after a full-node sync/reorg and pinning the sequencer into a
// permanent self-halt.
func TestBtcAttrCacheKey(t *testing.T) {
	evm := common.HexToHash("0x11")
	light := chainhash.Hash{0xaa}
	full := chainhash.Hash{0xbb}
	base := btcAttrCacheKey{evmTip: evm, lightTip: light, fullTip: full}

	// All three identical -> cache hit.
	require.Equal(t, base, btcAttrCacheKey{evmTip: evm, lightTip: light, fullTip: full},
		"identical (evmTip, lightTip, fullTip) must compare equal (cache hit)")

	// EVM tip differs -> miss (the original key already covered this).
	require.NotEqual(t, base, btcAttrCacheKey{evmTip: common.HexToHash("0x22"), lightTip: light, fullTip: full},
		"a new EVM tip must invalidate the cache")

	// Lightweight BTC view differs -> miss.
	require.NotEqual(t, base, btcAttrCacheKey{evmTip: evm, lightTip: chainhash.Hash{0xcc}, fullTip: full},
		"a lightweight-TBC view change must invalidate the cache")

	// Full-node BTC view differs -> miss. This is the case the original EVM-tip-only key missed: a
	// full-node sync/reorg changes fullTip while the EVM tip is unchanged; re-serving the stale BtcAttr here
	// is the permanent self-inflicted sequencer halt the fix removes.
	require.NotEqual(t, base, btcAttrCacheKey{evmTip: evm, lightTip: light, fullTip: chainhash.Hash{0xdd}},
		"a full-node BTC view change (sync/reorg) must invalidate the cache")
}

// TestBtcAttrCacheRoundTrip pins the inline cache check and write of getBitcoinAttributesForNextBlock via
// the cachedBtcAttrFor / storeBtcAttrCache helpers it calls (the function body itself needs a full node).
// Catches: a write that drops a key dimension, a check that matches the wrong key, and a missing
// non-nil-entry guard.
func TestBtcAttrCacheRoundTrip(t *testing.T) {
	bc := &BlockChain{}
	key := btcAttrCacheKey{
		evmTip:   common.HexToHash("0x11"),
		lightTip: chainhash.Hash{0xaa},
		fullTip:  chainhash.Hash{0xbb},
	}
	tx := &types.BtcAttributesDepositedTx{}

	// Empty cache (nil entry) -> always a miss, even for a key that happens to equal the zero key.
	require.Nil(t, bc.cachedBtcAttrFor(key), "an unwritten cache must miss")
	require.Nil(t, bc.cachedBtcAttrFor(btcAttrCacheKey{}), "the zero key must miss while the entry is nil (the guard)")

	bc.storeBtcAttrCache(key, tx)

	// Exact-key match -> the stored entry.
	require.Same(t, tx, bc.cachedBtcAttrFor(key), "an exact (evmTip, lightTip, fullTip) match must return the stored tx")

	// Any single dimension differing -> miss (so a BTC-view change forces a rebuild).
	require.Nil(t, bc.cachedBtcAttrFor(btcAttrCacheKey{evmTip: common.HexToHash("0x22"), lightTip: key.lightTip, fullTip: key.fullTip}), "a different EVM tip must miss")
	require.Nil(t, bc.cachedBtcAttrFor(btcAttrCacheKey{evmTip: key.evmTip, lightTip: chainhash.Hash{0xcc}, fullTip: key.fullTip}), "a different lightweight tip must miss")
	require.Nil(t, bc.cachedBtcAttrFor(btcAttrCacheKey{evmTip: key.evmTip, lightTip: key.lightTip, fullTip: chainhash.Hash{0xdd}}), "a different full-node tip must miss")
}

// Build-path LIVENESS: the sequencer build path must always yield a PROPOSABLE result, never a halting error that
// would stall block production. GetBitcoinAttributesForNextBlock returns a clean (nil tx, nil err) on a degenerate
// full-node feed via two arms: (a) the light tip already equals the full tip (idle), and (b) the light view LEADS
// the full node on the same chain (the deliberately-deferred arm that returns nil only after both cursors walk down
// to the lower common height). This is the only end-to-end coverage of GetBitcoinAttributesForNextBlock; the
// decomposed pure helpers (recordHvmBtcAttrResult, btcAttrFutureSkewExceeded, the prefix arms) are covered separately. A
// regression returning an error or the pending sentinel on these arms would stall the sequencer whenever its own
// view briefly leads the full node, and pass every existing test.
func TestGetBitcoinAttributesForNextBlockNonStall(t *testing.T) {
	if testing.Short() {
		t.Skip("builds real lightweight TBC nodes")
	}
	ctx := context.Background()
	now := uint64(time.Now().Unix())
	hvm0Time := now - 10_000 // so IsHvm0(now) is true and now is not future-skewed

	// A second external-header tbc.Server stands in for vm.TBCFullNode (the "full-node feed"). Same regtest genesis.
	newFullNode := func() *tbc.Server {
		g := &chaincfg.RegressionNetParams.GenesisBlock.Header
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = g
		cfg.GenesisHeightOffset = 0
		cfg.LevelDBHome = t.TempDir()
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, true, 0, false
		cfg.Network = "localnet"
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		return srv
	}
	withFullNode := func(t *testing.T, full *tbc.Server) {
		prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
		vm.TBCFullNode, vm.TBCFullNodeConfig = full, &tbc.Config{Network: "localnet"}
		t.Cleanup(func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg })
	}

	// (a) IDLE: light and full both at the genesis checkpoint (equal tips) -> (nil, nil), no stall.
	t.Run("equal-tips-idle", func(t *testing.T) {
		chain, _ := newRegtestChainWithLightTBC(t, hvm0Time)
		full := newFullNode()
		t.Cleanup(func() { _ = full.ExternalHeaderTearDown() })
		withFullNode(t, full)

		tx, err := chain.GetBitcoinAttributesForNextBlock(now)
		require.NoError(t, err, "an idle (equal-tip) feed must not stall the build path")
		require.Nil(t, tx, "no BtcAttr tx is proposed when the BTC view is already caught up")
	})

	// (b) LIGHT-AHEAD on the same chain: the light node holds h1..h4, the full node only h1..h2 -> after walking
	// both cursors down to the common height the light view leads -> (nil, nil), no stall.
	t.Run("light-ahead-same-chain", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
		full := newFullNode()
		t.Cleanup(func() { _ = full.ExternalHeaderTearDown() })
		withFullNode(t, full)

		// One shared chain h1..h4.
		hdrs := make([]*wire.BlockHeader, 0, 4)
		prev := genesis
		for i := 0; i < 4; i++ {
			h := mineRegtestChild(t, prev, uint32(i)*53+1)
			hdrs = append(hdrs, h)
			prev = h
		}
		// Light gets all four; full only the first two prefix. State-id kept at genesis on the light node so the
		// build path's getHeaderModeTBCEVMHeader stays on the clean (nil) arm.
		_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: hdrs}, hVMGenesisUpstreamId[:])
		require.NoError(t, err)
		_, _, _, _, err = full.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: hdrs[:2]}, hVMGenesisUpstreamId[:])
		require.NoError(t, err)

		_, lightTipBefore, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
		require.NoError(t, err)
		sidBefore, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		tx, err := chain.GetBitcoinAttributesForNextBlock(now)
		require.NoError(t, err, "a light-ahead same-chain feed must not stall the build path")
		require.Nil(t, tx, "no BtcAttr tx is proposed when the light view already leads the full node")
		// The build/query path is READ-ONLY w.r.t. the lightweight consensus view: deciding there is nothing to
		// propose must not move the tip or advance the upstream-state-id.
		_, lightTipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, lightTipBefore.BlockHash(), lightTipAfter.BlockHash(), "the build path must not move the lightweight tip")
		sidAfter, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
		require.NoError(t, err)
		require.Equal(t, sidBefore[:], sidAfter[:], "the build path must not advance the upstream-state-id")
	})
}

// Apply-caller EQUIVALENCE over real BTC-header commits: forward-apply (enforce=true) and
// performFullHvmHeaderStateRestore (enforce=false) are two production callers of applyHvmHeaderConsensusUpdate with
// DIFFERENT enforce args. The recovery contract is that replaying the SAME canonical disk blocks with enforcement
// OFF reproduces the EXACT lightweight BTC view forward-apply with enforcement ON produced (tip hash + height +
// upstream-state-id, byte-exact) — enforce=false must only skip the difficulty REJECT, never drop/alter a header.
// Existing coverage is two disjoint slices: enforce=false suppresses a reject for ONE direct apply (not via restore),
// and the restore disk-walk reaches tip but only over PLAIN blocks (BTC tip never moves). This composes them: a
// multi-block BtcAttr commit chain, forward then restore, byte-exact.
func TestForwardApplyAndRestoreConvergeOverBtcAttrCommits(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers + drives a full restore disk-walk")
	}
	const hvm0Time = uint64(1000)
	chain, regGenesis := newRegtestChainWithLightTBC(t, hvm0Time)
	evmGenesis := chain.GetHeaderByNumber(0) // L2 genesis, Time 0 -> pre-hVM, so block #1 is the activation block

	// One growing BTC chain split across three L2 blocks: seg1 off the BTC genesis, seg2 off seg1's tip, seg3 off
	// seg2's tip. Each L2 block's BtcAttr claims its segment's (new) canonical tip.
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
	blocks := []*types.Block{b1, b2, b3}

	// Place the L2 blocks on the canonical disk chain (rawdb, bypassing EVM execution — the hVM apply path only
	// reads the header + the BtcAttr tx) and set the head so GetHeaderByNumber / CurrentBlock resolve them.
	for _, b := range blocks {
		rawdb.WriteBlock(chain.db, b)
		rawdb.WriteCanonicalHash(chain.db, b.Hash(), b.NumberU64())
	}
	rawdb.WriteHeadBlockHash(chain.db, b3.Hash())
	chain.currentBlock.Store(b3.Header())
	require.Equal(t, uint64(3), chain.CurrentBlock().Number.Uint64())

	// PHASE 1 — forward-apply (enforce=true), the real sequencer/insert path.
	for _, b := range blocks {
		require.NoError(t, chain.applyHvmHeaderConsensusUpdate(b.Header(), false, true), "forward-apply %d", b.NumberU64())
	}
	fwdHeight, fwdTip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	fwdSid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	fwdTipHash := fwdTip.BlockHash()
	seg3Tip := t3.BlockHash()
	require.Equal(t, seg3Tip[:], fwdTipHash[:], "anti-vacuity: forward-apply moved the BTC tip to seg3's tip")
	require.Equal(t, b3.Hash().Bytes(), fwdSid[:], "forward-apply state-id is the tip block")

	// PHASE 2 — restore (enforce=false): wipe the light node and re-walk the canonical disk chain.
	chain.performFullHvmHeaderStateRestore()
	resHeight, resTip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	resSid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	resTipHash := resTip.BlockHash()

	// EQUIVALENCE: the enforce=false restore reproduces the enforce=true forward view byte-exact.
	require.Equal(t, fwdTipHash[:], resTipHash[:], "restore (enforce=false) must reproduce the forward-apply BTC tip")
	require.Equal(t, fwdHeight, resHeight, "restore must reproduce the forward-apply tip height")
	require.Equal(t, fwdSid[:], resSid[:], "restore must reproduce the forward-apply upstream-state-id (no dropped header)")
}

// getBlockFromDiskOrHoldingPen / getHeaderFromDiskOrHoldingPen: disk-first (GetBlockByHash/GetHeaderByHash), then the
// tempBlocks/tempHeaders holding pen, nil if absent in both. Dozens of hVM tests USE these helpers but none pins the
// precedence/fallback contract directly; a pen-first reversal (or a dropped pen fallback) would silently change which
// header/block the apply/walk paths read. Corpus-free.
func TestGetFromDiskOrHoldingPenPrecedence(t *testing.T) {
	chain, _ := newHvmTestChainWithLightTBC(t, uint64(1000))

	// Disk-only: a block written to rawdb resolves via the disk path.
	onDisk := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(5), Time: 1})
	rawdb.WriteBlock(chain.db, onDisk)
	require.NotNil(t, chain.getBlockFromDiskOrHoldingPen(onDisk.Hash()), "a disk-only block must resolve")
	require.NotNil(t, chain.getHeaderFromDiskOrHoldingPen(onDisk.Hash()), "a disk-only header must resolve")

	// Pen-only: a block only in tempBlocks/tempHeaders resolves via the fallback.
	inPen := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(6), Time: 2})
	chain.tempBlocks[inPen.Hash().String()] = inPen
	chain.tempHeaders[inPen.Hash().String()] = inPen.Header()
	require.NotNil(t, chain.getBlockFromDiskOrHoldingPen(inPen.Hash()), "a holding-pen-only block must resolve")
	require.NotNil(t, chain.getHeaderFromDiskOrHoldingPen(inPen.Hash()), "a holding-pen-only header must resolve")

	// Pen-only source check: the header helper must read tempHeaders, NOT tempBlocks[hash].Header().
	// Store a DIFFERENT header in tempHeaders than the block's own header under the same key.
	inPen2 := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(8), Time: 5})
	differentHdr := &types.Header{Number: big.NewInt(7), Time: 3}
	require.NotEqual(t, inPen2.Header().Hash(), differentHdr.Hash(), "anti-vacuity: pen header must differ from block header")
	chain.tempBlocks[inPen2.Hash().String()] = inPen2
	chain.tempHeaders[inPen2.Hash().String()] = differentHdr
	gotPenHdr := chain.getHeaderFromDiskOrHoldingPen(inPen2.Hash())
	require.NotNil(t, gotPenHdr)
	require.Equal(t, differentHdr.Hash(), gotPenHdr.Hash(), "pen header helper must read tempHeaders, not tempBlocks[hash].Header()")

	// Absent in both -> nil (callers must nil-check).
	require.Nil(t, chain.getBlockFromDiskOrHoldingPen(common.Hash{0xab}), "an absent block must resolve to nil")
	require.Nil(t, chain.getHeaderFromDiskOrHoldingPen(common.Hash{0xab}), "an absent header must resolve to nil")

	// Precedence: DISK wins. Force a mismatched pen entry (a DIFFERENT block stored under onDisk's hash key) and
	// assert the DISK block is returned — a pen-first reversal would return the decoy.
	decoy := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(99), Time: 3})
	require.NotEqual(t, onDisk.Hash(), decoy.Hash(), "anti-vacuity: the decoy must differ from the disk block")
	chain.tempBlocks[onDisk.Hash().String()] = decoy
	got := chain.getBlockFromDiskOrHoldingPen(onDisk.Hash())
	require.NotNil(t, got)
	require.Equal(t, onDisk.Hash(), got.Hash(), "disk must take precedence over the holding pen (kills a pen-first mutant)")

	// Same precedence for the HEADER helper: a decoy header under onDisk's hash key must not shadow the disk header.
	decoyHdr := &types.Header{Number: big.NewInt(98), Time: 4}
	require.NotEqual(t, onDisk.Hash(), decoyHdr.Hash())
	chain.tempHeaders[onDisk.Hash().String()] = decoyHdr
	gotHdr := chain.getHeaderFromDiskOrHoldingPen(onDisk.Hash())
	require.NotNil(t, gotHdr)
	require.Equal(t, onDisk.Hash(), gotHdr.Hash(), "disk must take precedence over the holding pen for headers too")
}

// The 3-way FORK arm of updateHvmHeaderConsensus and its findCommonAncestor geometry router. Every existing reorg
// test (TestHvmReorgForkConvergesToCompetingBranch) deliberately BYPASSES the dispatcher — it calls
// walkHvmHeaderConsensusBack + a direct applyHvmHeaderConsensusUpdate, because the dispatcher's forward walk forces a
// block-availability prefetch that needs a real FULL TBC node. The revert test drives updateHvmHeaderConsensus but
// only its LINEAR-back arm and explicitly documents findCommonAncestor fork-routing as uncovered. So neither
// findCommonAncestor (blockchain.go ~1649) nor the final fork arm (~4518: walkBack(currentHead,ancestor) then
// walkForward(ancestor,newHead)) is ever exercised by test code; a mutant corrupting the height-equality routing
// would survive the whole suite.
//
// Corpus-free: the competing branch C is HEADERLESS (empty-present BtcAttr). The forward walk's prefetch is gated on
// headersToAdd>0, so a zero-header apply never touches the (absent) full node. findCommonAncestor resolves the
// ancestor via bc.GetHeader (rawdb only, NOT the holding pen), so the ancestor block is written to rawdb.
func TestUpdateHvmHeaderConsensusForkArmFindsCommonAncestor(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	node, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
	ref, _ := newRegtestChainWithLightTBC(t, hvm0Time)
	checkpoint := genesis.BlockHash() // the lightweight TBC genesis-checkpoint tip (no headers applied)

	// Common ancestor A: a no-BtcAttr activation block (parent pre-activation). Applying it sets state-id=A with the
	// BTC tip still at the genesis checkpoint, so both competing siblings build off the same checkpoint.
	preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})

	// Orphan branch B (#12, parent A): header-bearing, so the unwind genuinely UN-applies real BTC headers.
	xHeaders := make([]wire.BlockHeader, 0, 3)
	prev := genesis
	for i := 0; i < 3; i++ {
		h := mineRegtestChild(t, prev, 2000+uint32(i))
		xHeaders = append(xHeaders, *h)
		prev = h
	}
	xTip := xHeaders[len(xHeaders)-1].BlockHash()
	bBtc, err := types.MakeBtcAttributesDepositedTx(&xTip, xHeaders)
	require.NoError(t, err)
	blockB := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: blockA.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(bBtc)}})

	// Competing branch C (#12, parent A, same height as B, distinct body): HEADERLESS, claiming the genesis
	// checkpoint as its canonical tip (the tip the node sits at after the unwind back to A).
	cBtc, err := types.MakeBtcAttributesDepositedTx(&checkpoint, nil)
	require.NoError(t, err)
	blockC := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 2, ParentHash: blockA.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(cBtc)}})
	require.NotEqual(t, blockB.Hash(), blockC.Hash(), "competing siblings must differ")

	seed := func(c *BlockChain) {
		c.tempHeaders[preAct.Hash().String()] = preAct
		c.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
		for _, b := range []*types.Block{blockA, blockB, blockC} {
			c.tempBlocks[b.Hash().String()] = b
			c.tempHeaders[b.Hash().String()] = b.Header()
		}
		// findCommonAncestor reads the ancestor via bc.GetHeader (rawdb only). Persist A to disk so the fork
		// router can resolve it (the holding pen alone would make GetHeader return nil and nil-panic the walk).
		rawdb.WriteBlock(c.db, blockA)
	}
	seed(node)
	seed(ref)

	// REFERENCE: only ever sees A then the competing branch C (linear single-block applies).
	require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockC.Header(), false, true))
	refSid, err := ref.tbcHeaderNode.UpstreamStateId(ref.ctx)
	require.NoError(t, err)
	require.Equal(t, blockC.Hash().Bytes(), refSid[:], "reference converges to C")
	_, refTip, err := ref.tbcHeaderNode.BlockHeaderBest(ref.ctx)
	require.NoError(t, err)

	// NODE under test: apply A then the ORPHAN branch B (state-id=B, tip=xTip).
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockB.Header(), false, true))
	_, orphTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
	require.NoError(t, err)
	require.Equal(t, xTip, orphTip.BlockHash(), "node is on the orphan branch tip before the reorg")

	// THE TARGET: drive the REAL dispatcher. state-id=B, newHead=C, neither is the ancestor A -> the final fork arm
	// runs findCommonAncestor(C,B)=A, then walkBack(B,A) (unwinds the orphan X headers) and walkForward(A,C).
	require.NoError(t, node.updateHvmHeaderConsensus(blockC.Header(), false),
		"the 3-way fork dispatch (findCommonAncestor + walkBack + walkForward) must converge to C")

	// CONVERGENCE with the competing-branch-only reference, and the orphan headers fully unwound.
	nodeSid, err := node.tbcHeaderNode.UpstreamStateId(node.ctx)
	require.NoError(t, err)
	require.Equal(t, refSid[:], nodeSid[:], "post-fork state-id must converge to C (the reference view)")
	require.Equal(t, blockC.Hash().Bytes(), nodeSid[:], "the fork walk must land the state-id exactly on newHead C")
	_, nodeTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
	require.NoError(t, err)
	require.Equal(t, refTip.BlockHash(), nodeTip.BlockHash(), "post-fork tip must converge")
	require.Equal(t, checkpoint, nodeTip.BlockHash(), "headerless C leaves the tip at the genesis checkpoint")
	for _, h := range xHeaders {
		_, _, e := node.tbcHeaderNode.BlockHeaderByHash(node.ctx, h.BlockHash())
		require.Error(t, e, "the orphan-branch header must be fully removed by the fork unwind")
	}
}

// TestUpdateHvmHeaderConsensusForkArmDepthMultiBlock extends the depth-1 fork test to a DEEPER, unequal-depth fork
// so findCommonAncestor's two loops actually iterate: the first walk-down loop (skipped entirely at depth-1 because
// both heads start at the same height) AND the joint walk-back loop iterating more than once. Geometry: ancestor
// A@11; orphan branch B1@12->B2@13->B3@14 (each adds one mined BTC header); competing branch C1@12->C2@13 (both
// HEADERLESS, so the forward walk dodges the full-node prefetch). updateHvmHeaderConsensus(C2) -> findCommonAncestor
// (C2@13,B3@14): first loop walks B3 14->13, joint loop walks 13->12->11 to A. Then walkBack(B3,A) unwinds three
// real header blocks and walkForward(A,C2) applies two headerless blocks. An off-by-one in either loop survives the
// depth-1 test but diverges here. Corpus-free (regtest); intermediates are written to rawdb because findCommonAncestor
// resolves via bc.GetHeader (rawdb only, not the holding pen).
func TestUpdateHvmHeaderConsensusForkArmDepthMultiBlock(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	node, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
	ref, _ := newRegtestChainWithLightTBC(t, hvm0Time)
	checkpoint := genesis.BlockHash()

	preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})

	// Orphan branch: three header-bearing blocks, each adding one mined BTC header chained off the previous.
	x1 := mineRegtestChild(t, genesis, 3000)
	x2 := mineRegtestChild(t, x1, 3100)
	x3 := mineRegtestChild(t, x2, 3200)
	mkHdrBlock := func(num int64, toff uint64, parent *types.Block, claim *wire.BlockHeader, hdrs []wire.BlockHeader) *types.Block {
		tip := claim.BlockHash()
		btc, err := types.MakeBtcAttributesDepositedTx(&tip, hdrs)
		require.NoError(t, err)
		return types.NewBlockWithHeader(&types.Header{Number: big.NewInt(num), Time: hvm0Time + toff, ParentHash: parent.Hash()}).
			WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc)}})
	}
	blockB1 := mkHdrBlock(12, 1, blockA, x1, []wire.BlockHeader{*x1})
	blockB2 := mkHdrBlock(13, 1, blockB1, x2, []wire.BlockHeader{*x2})
	blockB3 := mkHdrBlock(14, 1, blockB2, x3, []wire.BlockHeader{*x3})

	// Competing branch: two HEADERLESS blocks claiming the genesis checkpoint (the tip after the unwind back to A).
	mkHeaderless := func(num int64, toff uint64, parent *types.Block) *types.Block {
		btc, err := types.MakeBtcAttributesDepositedTx(&checkpoint, nil)
		require.NoError(t, err)
		return types.NewBlockWithHeader(&types.Header{Number: big.NewInt(num), Time: hvm0Time + toff, ParentHash: parent.Hash()}).
			WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc)}})
	}
	blockC1 := mkHeaderless(12, 2, blockA)
	blockC2 := mkHeaderless(13, 2, blockC1)

	all := []*types.Block{blockA, blockB1, blockB2, blockB3, blockC1, blockC2}
	seed := func(c *BlockChain) {
		c.tempHeaders[preAct.Hash().String()] = preAct
		c.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
		for _, b := range all {
			c.tempBlocks[b.Hash().String()] = b
			c.tempHeaders[b.Hash().String()] = b.Header()
			rawdb.WriteBlock(c.db, b) // findCommonAncestor resolves intermediates via bc.GetHeader (rawdb only)
		}
	}
	seed(node)
	seed(ref)

	// Reference: A then the competing branch C1, C2 (linear headerless applies).
	require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockC1.Header(), false, true))
	require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockC2.Header(), false, true))
	refSid, err := ref.tbcHeaderNode.UpstreamStateId(ref.ctx)
	require.NoError(t, err)
	require.Equal(t, blockC2.Hash().Bytes(), refSid[:], "reference converges to C2")

	// Node: A, then the orphan branch B1->B2->B3 (state-id=B3@14, tip=x3).
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockB1.Header(), false, true))
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockB2.Header(), false, true))
	require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockB3.Header(), false, true))
	_, orphTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
	require.NoError(t, err)
	require.Equal(t, x3.BlockHash(), orphTip.BlockHash(), "node is on the orphan-branch tip x3 before the reorg")

	// THE TARGET: the DEPTH>1 fork dispatch.
	require.NoError(t, node.updateHvmHeaderConsensus(blockC2.Header(), false),
		"the depth>1 fork dispatch must converge to C2")

	nodeSid, err := node.tbcHeaderNode.UpstreamStateId(node.ctx)
	require.NoError(t, err)
	require.Equal(t, refSid[:], nodeSid[:], "depth>1 fork must converge to the competing-branch reference (C2)")
	require.Equal(t, blockC2.Hash().Bytes(), nodeSid[:], "the fork walk must land the state-id on newHead C2")
	_, nodeTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
	require.NoError(t, err)
	require.Equal(t, checkpoint, nodeTip.BlockHash(), "headerless competing branch leaves the tip at the genesis checkpoint")
	for _, h := range []*wire.BlockHeader{x1, x2, x3} {
		_, _, e := node.tbcHeaderNode.BlockHeaderByHash(node.ctx, h.BlockHash())
		require.Error(t, e, "every orphan-branch header must be unwound by the multi-step fork back-walk")
	}
}

// TestUpdateHvmHeaderConsensusSingleApplyBansBadBlock pins the DISPATCH-level single-block-apply ban arm of
// updateHvmHeaderConsensus (~4471): when newHead is a direct child of currentHead and its apply fails with
// ErrInvalidHVMHeaders, the dispatcher reportBlocks it (rawdb.WriteBadBlock). The existing bad-block-routing test
// drives the FORWARD-WALK reportBlock path (via walkHvmHeaderConsensusForward directly); this drives the distinct
// single-apply arm via the dispatcher. Deleting the dispatch-level reportBlock would survive every test that calls
// applyHvmHeaderConsensusUpdate or walkHvmHeaderConsensusForward directly. Corpus-free (headerless wrong-tip block).
func TestUpdateHvmHeaderConsensusSingleApplyBansBadBlock(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)
	var wrongTip chainhash.Hash
	for i := range wrongTip {
		wrongTip[i] = 0x42
	}

	preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	currentHead := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})
	// newHead is a DIRECT CHILD of currentHead, headerless with a WRONG canonical tip -> apply -> ErrInvalidHVMHeaders.
	newHead := emptyPresentBtcAttrBlock(t, 12, hvm0Time+1, currentHead.Header(), wrongTip)

	chain.tempHeaders[preAct.Hash().String()] = preAct
	chain.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
	for _, b := range []*types.Block{currentHead, newHead} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
	}
	// findCommonAncestor resolves currentHead via bc.GetHeader (rawdb only).
	rawdb.WriteBlock(chain.db, currentHead)

	// Establish state-id = currentHead so the dispatcher takes the single-block-apply arm for the direct child.
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(currentHead.Header(), false, true))
	require.Nil(t, rawdb.ReadBadBlock(chain.db, newHead.Hash()), "precondition: newHead is not yet banned")

	err := chain.updateHvmHeaderConsensus(newHead.Header(), false)
	require.ErrorIs(t, err, consensus.ErrInvalidHVMHeaders, "a wrong-tip direct child must be rejected via the single-apply arm")
	require.NotNil(t, rawdb.ReadBadBlock(chain.db, newHead.Hash()),
		"the dispatch-level single-apply arm must reportBlock (ban) the invalid direct-child block")
}

// emptyPresentBtcAttrBlock builds a block carrying an "empty-but-present" Bitcoin Attributes Deposited tx
// (present, zero headers) claiming canonicalTip, on the given parent/number/time. The empty-present
// apply/unapply paths make no TBC header change (no AddExternalHeaders, hence no full-TBC-node prefetch) —
// they only move the upstream-state-id — which lets this test drive walkHvmHeaderConsensusForward (which
// hardcodes attemptPrefetch=true) without a vm.TBCFullNode.
func emptyPresentBtcAttrBlock(t *testing.T, num int64, time uint64, parent *types.Header, canonicalTip chainhash.Hash) *types.Block {
	t.Helper()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canonicalTip, nil)
	require.NoError(t, err)
	h := &types.Header{Number: big.NewInt(num), Time: time, ParentHash: parent.Hash()}
	return types.NewBlockWithHeader(h).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
}

// TestHvmForwardWalkRollbackUnwindsPredecessors covers the error-recovery loop in
// walkHvmHeaderConsensusForward. It drives a multi-block forward walk that applies two predecessors
// (block1, block2) and then fails on block3 with ErrInvalidHVMHeaders, and asserts the loop rolls the live TBC
// upstream-state-id back exactly to currentHead — i.e. it unwinds the genuinely-applied predecessors
// headers[index-1..1], not the failing block headers[index].
//
// The recovery loop must unapply headers[backIndex] (the applied predecessors, backIndex varying 2 then 1), NOT the
// constant failing block headers[index]. Unapplying the constant index — with the btcAttrDepIsHeaderless guard in
// place — would no-op-unapply block3 twice (rolling the state-id to block3's parent, block2) and leave block1/block2
// applied, so the state-id would end at block2, not currentHead. This test fails deterministically under the
// constant-index form and passes only when the loop walks back the predecessors via backIndex.
//
// Two predecessors (failure at slice index 3) are used so the recovery loop iterates twice with distinct
// backIndex values (2 then 1), exercising the varying-vs-constant index distinction at the core of correct recovery.
// Empty-but-present blocks keep the walk on the no-AddExternalHeaders path so no full TBC node is required;
// header-removal mechanics on unapply are covered by the empty-but-present round-trip tests.
func TestHvmForwardWalkRollbackUnwindsPredecessors(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)

	// canonTip = the lightweight tip (genesis checkpoint). The successful predecessors claim this
	// (it matches the tip, which empty-present blocks never move), so they apply cleanly.
	canonTip := lightTip.BlockHash()

	// A deliberately wrong canonical-tip claim for the failing block: any hash != the live tip. This makes
	// block3's empty-present CanonicalTip check fail -> ErrInvalidHVMHeaders, returned before it advances the
	// state-id (so block3 itself commits no state — why it must not be unwound).
	var wrongTip chainhash.Hash
	for i := range wrongTip {
		wrongTip[i] = 0x42
	}
	require.NotEqual(t, canonTip[:], wrongTip[:])

	// Geometry: pre-activation parent -> currentHead (activation, no BtcAttr) -> block1 -> block2
	// (both empty-present, valid) -> block3 (empty-present, invalid canonical claim).
	preActivation := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	currentHead := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preActivation.Hash()})
	block1 := emptyPresentBtcAttrBlock(t, 12, hvm0Time+1, currentHead.Header(), canonTip)
	block2 := emptyPresentBtcAttrBlock(t, 13, hvm0Time+2, block1.Header(), canonTip)
	block3 := emptyPresentBtcAttrBlock(t, 14, hvm0Time+3, block2.Header(), wrongTip)

	// Seed every block+header into the holding pen: headersBetweenBlocks walks newHead->currentHead
	// via parent headers, and apply/unapply resolve blocks and the descend-target parent header.
	for _, b := range []*types.Block{currentHead, block1, block2, block3} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
	}
	chain.tempHeaders[preActivation.Hash().String()] = preActivation
	chain.tempBlocks[preActivation.Hash().String()] = types.NewBlockWithHeader(preActivation)

	// Establish the starting state the walk assumes: currentHead already applied -> state-id == currentHead.
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(currentHead.Header(), false, true))
	sidStart, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, currentHead.Hash().Bytes(), sidStart[:], "precondition: state-id starts at currentHead")

	_, tipStart, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipStartHash := tipStart.BlockHash()
	require.Equal(t, canonTip[:], tipStartHash[:], "precondition: tip starts at the genesis checkpoint")

	// Drive the forward walk currentHead -> block3. block1/block2 apply (advancing state-id to block2),
	// then block3 fails; the recovery loop must unwind block2 then block1 back to currentHead.
	err = chain.walkHvmHeaderConsensusForward(currentHead.Header(), block3.Header())
	require.Error(t, err, "the walk must surface the invalid block3's error")
	require.ErrorIs(t, err, consensus.ErrInvalidHVMHeaders,
		"block3's wrong canonical-tip claim must fail as ErrInvalidHVMHeaders")

	// The recovery loop must unwind the applied predecessors (block1, block2) and restore the state-id exactly to
	// currentHead. A constant-headers[index] unapply would instead leave it at block2 (predecessors left applied,
	// block3 no-op-unapplied to its parent).
	sidEnd, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, currentHead.Hash().Bytes(), sidEnd[:],
		"error-recovery must unwind the applied predecessors back to currentHead, not the failing block")
	require.NotEqual(t, block2.Hash().Bytes(), sidEnd[:],
		"a state-id left at block2 means the predecessors were not unwound (constant-index unapply)")

	// The lightweight tip never moved (empty-present blocks add no headers); it must still be the checkpoint.
	_, tipEnd, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipEndHash := tipEnd.BlockHash()
	require.Equal(t, canonTip[:], tipEndHash[:], "tip must be unchanged after the rolled-back walk")
}

// TestWalkHvmHeaderConsensusForwardBadGeometry pins the operator-facing "bad geometry" diagnostic emitted by
// walkHvmHeaderConsensusForward when currentHead is at or above newHead (blockchain.go ~3919). This guard is the
// first line of the function — reached before any TBC interaction — so it is trivially corpus-free. The string is a
// stable diagnostic external tooling may match; no test pinned it (existing walkForward tests pass valid geometry).
func TestWalkHvmHeaderConsensusForwardBadGeometry(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	higher := &types.Header{Number: big.NewInt(20), Time: hvm0Time}
	lower := &types.Header{Number: big.NewInt(15), Time: hvm0Time}
	sidBefore, sErr := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, sErr)
	err := chain.walkHvmHeaderConsensusForward(higher, lower)
	require.Error(t, err)
	sidAfter, sErr := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, sErr)
	require.Equal(t, sidBefore[:], sidAfter[:], "the bad-geometry guard returns BEFORE any work; it must not mutate the state-id")
	require.Contains(t, err.Error(), "Cannot walk hVM consensus forewards", "the bad-geometry diagnostic must be emitted")
	require.Contains(t, err.Error(), "bad geometry")

	// Equal height is also bad geometry (the guard is >=, not >).
	require.ErrorContains(t, chain.walkHvmHeaderConsensusForward(lower, lower), "bad geometry",
		"equal-height currentHead/newHead must also be rejected as bad geometry")
}

// TestWalkHvmHeaderConsensusForwardPathNotFound pins the "unable to find a path" diagnostic emitted when
// headersBetweenBlocks cannot connect currentHead to newHead (a missing intermediate header; blockchain.go ~3936).
// Corpus-free: newHead's parent hash resolves to nothing in disk + holding pen, so headersBetweenBlocks fails on the
// first walk-back step.
func TestWalkHvmHeaderConsensusForwardPathNotFound(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, _ := newHvmTestChainWithLightTBC(t, hvm0Time)

	currentHead := &types.Header{Number: big.NewInt(10), Time: hvm0Time}
	// newHead is 2 above currentHead, but its parent (the intermediate at #11) is absent from disk + holding pen.
	newHead := &types.Header{Number: big.NewInt(12), Time: hvm0Time + 2, ParentHash: common.HexToHash("0xdeadbeefdeadbeef")}
	err := chain.walkHvmHeaderConsensusForward(currentHead, newHead)
	require.Error(t, err)
	require.Contains(t, err.Error(), "unable to find a path", "the path-not-found diagnostic must be emitted")
}

// Headerless (empty-but-present) BtcAttr apply+unapply in STEADY STATE — the one uncovered corner of the 2x2
// {headerless / header-bearing} x {genesis-tip / non-genesis-tip}. Existing headerless tests use ACTIVATION
// geometry (tip pinned at the genesis checkpoint; unapply rolls the state-id to genesis), and the steady-state
// round-trip tests are all header-BEARING. This applies a headerless block on top of a header-bearing predecessor
// whose tip is already NON-genesis, exercising (a) the headerless-apply CanonicalTip check against a non-genesis
// tip, and (b) the headerless-unapply state-id rollback to a REAL prior block (not genesis).
func TestHvmHeaderlessSteadyStateApplyUnapply(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)

	// Header-bearing activation block A advances the BTC tip to a NON-genesis value aTip.
	aHeaders := make([]wire.BlockHeader, 0, 3)
	prev := genesis
	for i := 0; i < 3; i++ {
		h := mineRegtestChildBits(t, prev, regtestPowBits, uint32(100+i))
		aHeaders = append(aHeaders, *h)
		prev = h
	}
	aTip := aHeaders[len(aHeaders)-1].BlockHash()
	aBtc, err := types.MakeBtcAttributesDepositedTx(&aTip, aHeaders)
	require.NoError(t, err)
	aParent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: aParent.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(aBtc)}})
	chain.tempHeaders[aParent.Hash().String()] = aParent
	chain.tempBlocks[aParent.Hash().String()] = types.NewBlockWithHeader(aParent)
	chain.tempHeaders[blockA.Hash().String()] = blockA.Header()
	chain.tempBlocks[blockA.Hash().String()] = blockA
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
	_, tipA, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, aTip, tipA.BlockHash(), "post-A tip is non-genesis")

	// Steady-state HEADERLESS block H (parent A), CanonicalTip = the current non-genesis tip aTip.
	hBtc, err := types.MakeBtcAttributesDepositedTx(&aTip, nil)
	require.NoError(t, err)
	blockH := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: blockA.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(hBtc)}})
	chain.tempHeaders[blockH.Hash().String()] = blockH.Header()
	chain.tempBlocks[blockH.Hash().String()] = blockH

	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockH.Header(), false, true), "headerless apply against a non-genesis tip must succeed")
	_, tipH, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, aTip, tipH.BlockHash(), "headerless apply must NOT move the BTC tip")
	sidH, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockH.Hash().Bytes(), sidH[:], "headerless apply advances the state-id to H")

	// Unapply H: the steady-state arm rolls the state-id back to the REAL prior block A (not genesis), tip unchanged.
	require.NoError(t, chain.unapplyHvmHeaderConsensusUpdate(blockH.Header()))
	_, tipBack, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, aTip, tipBack.BlockHash(), "headerless unapply leaves the BTC tip unchanged")
	sidBack, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockA.Hash().Bytes(), sidBack[:], "headerless unapply rolls the state-id to the real prior block A, NOT genesis")
	require.NotEqual(t, hVMGenesisUpstreamId[:], sidBack[:], "anti-vacuity: the rollback target is non-genesis")

	// Negative control: a headerless block with a WRONG CanonicalTip against the non-genesis tip must be rejected
	// (proving the headerless-apply CanonicalTip check is live for a non-genesis tip).
	var wrong chainhash.Hash
	wrong[0] = 0x42
	wBtc, err := types.MakeBtcAttributesDepositedTx(&wrong, nil)
	require.NoError(t, err)
	blockW := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: hvm0Time + 2, ParentHash: blockA.Hash()}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(wBtc)}})
	chain.tempHeaders[blockW.Hash().String()] = blockW.Header()
	chain.tempBlocks[blockW.Hash().String()] = blockW
	require.ErrorIs(t, chain.applyHvmHeaderConsensusUpdate(blockW.Header(), false, true), consensus.ErrInvalidHVMHeaders,
		"a headerless block claiming the wrong CanonicalTip against a non-genesis tip must reject")
}

// TestInsertChainEvictsHoldingPenButKeepsDiskFallback drives real InsertChain across multiple calls on a
// production-wired (hVM-enabled) BlockChain and asserts the two load-bearing properties of the holding-pen
// lifecycle in insertChain (core/blockchain.go — the `defer { clear(bc.tempBlocks); clear(bc.tempHeaders) }`):
//
//	(1) No leak: tempBlocks/tempHeaders are emptied after every insertChain return. Without the clear these maps
//	    would grow unbounded for the node's lifetime (a *types.Block + *types.Header per distinct hash ever
//	    imported, including every block during initial sync) -> heap exhaustion / OOM. The per-block store
//	    at the top of the insertChain loop is hVM-independent, so plain blocks exercise the pen write + the
//	    defer-clear exactly as BtcAttr-bearing blocks do.
//
//	(2) Disk fallback preserved: a block imported in an earlier InsertChain call (whose pen entry was
//	    therefore already cleared on that call's return) remains resolvable via
//	    getBlockFromDiskOrHoldingPen / getHeaderFromDiskOrHoldingPen — the disk-first accessors the hVM
//	    consensus-update machinery (updateHvmHeaderConsensus and its apply/unapply/walk helpers) uses to
//	    walk ancestry. Guards the cross-call dependency: a change that widened the clear to drop a
//	    not-yet-flushed entry, or regressed the writeBlockWithState-before-updateHvmHeaderConsensus ordering
//	    (so a block were not durably on disk at return), would make these accessors return nil.
//
// hVM activation is set far in the future so the generated plain blocks import without a seeded Bitcoin
// view; the pen write + clear and the accessors are hVM-independent, so the pen lifecycle is still exercised
// end to end on a real, production-wired chain.
func TestInsertChainEvictsHoldingPenButKeepsDiskFallback(t *testing.T) {
	const farFutureHvm0 = uint64(1) << 62 // no generated block reaches hVM activation
	chain, _ := newRegtestChainWithLightTBC(t, farFutureHvm0)

	const total = 8
	parent := chain.GetBlockByHash(chain.CurrentBlock().Hash()) // genesis
	require.NotNil(t, parent, "genesis must be present")
	blocks, _ := GenerateChain(chain.chainConfig, parent, ethash.NewFaker(), chain.db, total, func(i int, b *BlockGen) {})
	require.Len(t, blocks, total)

	penEmpty := func(label string) {
		require.Lenf(t, chain.tempBlocks, 0, "tempBlocks must be empty after insertChain (%s)", label)
		require.Lenf(t, chain.tempHeaders, 0, "tempHeaders must be empty after insertChain (%s)", label)
	}
	resolvableFromDisk := func(blks []*types.Block, label string) {
		for _, blk := range blks {
			h := blk.Hash()
			// The pen is empty here, so these must resolve from disk — the disk-first path the hVM consensus
			// ancestry walk depends on after the pen has been evicted.
			require.NotNilf(t, chain.getBlockFromDiskOrHoldingPen(h), "%s: block #%d must resolve from disk after pen eviction", label, blk.NumberU64())
			require.NotNilf(t, chain.getHeaderFromDiskOrHoldingPen(h), "%s: header #%d must resolve from disk after pen eviction", label, blk.NumberU64())
			require.NotNilf(t, chain.GetBlockByHash(h), "%s: block #%d must be durably on disk", label, blk.NumberU64())
		}
	}

	// Call #1 — import the first half in one InsertChain call.
	n, err := chain.InsertChain(blocks[:total/2])
	require.NoError(t, err, "first InsertChain call")
	require.Equal(t, total/2, n)
	penEmpty("after call #1")
	resolvableFromDisk(blocks[:total/2], "after call #1")

	// Call #2 — import the second half in a separate InsertChain call. The first half's pen entries were
	// already evicted when call #1 returned, so the cross-call lookups below are served from disk.
	n, err = chain.InsertChain(blocks[total/2:])
	require.NoError(t, err, "second InsertChain call")
	require.Equal(t, total-total/2, n)
	penEmpty("after call #2")
	// All blocks — including the first half whose pen entries were cleared after call #1 — must still
	// resolve via the hVM accessors (from disk). This is the cross-call dependency that must be preserved.
	resolvableFromDisk(blocks, "after call #2 (cross-call)")
	require.Equal(t, blocks[total-1].Hash(), chain.CurrentBlock().Hash(), "the full chain must be canonical")
}

// TestInsertChainEvictsHoldingPenOnRejectedBatch pins the ERROR-return path of the holding-pen lifecycle: when a
// multi-block batch is partially rejected, the pen's unconditional defer-clear must still fire AND the rejected
// block (written to the pen at the top of the loop, then never committed to disk because ProcessBlock failed) must
// NOT remain resolvable via either accessor. The existing lifecycle test only drives SUCCESSFUL InsertChain calls,
// where every penned hash is also on disk — so it structurally cannot detect a leaked pen entry for a rejected block.
func TestInsertChainEvictsHoldingPenOnRejectedBatch(t *testing.T) {
	const farFutureHvm0 = uint64(1) << 62 // blocks stay hVM-independent; the pen write+clear are still exercised
	chain, _ := newRegtestChainWithLightTBC(t, farFutureHvm0)

	parent := chain.GetBlockByHash(chain.CurrentBlock().Hash())
	require.NotNil(t, parent)
	blocks, _ := GenerateChain(chain.chainConfig, parent, ethash.NewFaker(), chain.db, 3, func(i int, b *BlockGen) {})

	// Rebuild the LAST block with a tampered state Root: passes ethash.NewFaker() header verification (which does
	// not check Root) but fails validateState inside ProcessBlock, so it reaches the pen write then triggers the
	// early error return.
	badHeader := *blocks[2].Header()
	badHeader.Root = common.Hash{0xde, 0xad, 0xbe, 0xef}
	badBlock := types.NewBlockWithHeader(&badHeader).WithBody(*blocks[2].Body())
	require.NotEqual(t, blocks[2].Hash(), badBlock.Hash(), "the tampered block must differ from the original")

	n, err := chain.InsertChain([]*types.Block{blocks[0], blocks[1], badBlock})
	require.Error(t, err, "the tampered-state-root block must be rejected")
	require.Equal(t, 2, n, "the two good blocks are inserted before the failure")

	// The defer-clear fired on the error path.
	require.Len(t, chain.tempBlocks, 0, "tempBlocks must be cleared on the error-return path")
	require.Len(t, chain.tempHeaders, 0, "tempHeaders must be cleared on the error-return path")

	// The good prefix is durably on disk (partial-success preserved).
	for _, b := range []*types.Block{blocks[0], blocks[1]} {
		require.NotNil(t, chain.getBlockFromDiskOrHoldingPen(b.Hash()), "good block #%d must resolve from disk", b.NumberU64())
	}
	// The load-bearing assertion: the rejected block must NOT be resolvable through either accessor (never written
	// to disk, and its pen entry was evicted) — a leak would let the hVM ancestry walk resolve an uncommitted block.
	require.Nil(t, chain.getBlockFromDiskOrHoldingPen(badBlock.Hash()), "a rejected block must not leak in the holding pen / disk")
	require.Nil(t, chain.getHeaderFromDiskOrHoldingPen(badBlock.Hash()), "a rejected block's header must not leak either")
}

// Direct tests of the initHvmHeaderNode wrapper policy (the verdict->action mapping), the
// classifier's multi-checkpoint loop, and the checkpoint map's well-formedness.
// TestClassifyHvmGenesisPairing pins the pure classifier verdict; these pin what the wrapper does with it:
// Canonical->proceed, localnet-Custom->warn+proceed (in-process), and Mismatch / non-localnet-Custom->
// refuse-to-start (subprocess, because log.Crit calls os.Exit).
// newHvmInitTestChain builds a real BlockChain with hVM Phase 0 enabled but WITHOUT attaching the lightweight
// TBC node, so a test can drive initHvmHeaderNode with an arbitrary (network, genesis, offset) config.
func newHvmInitTestChain(t *testing.T) *BlockChain {
	t.Helper()
	hvm0Time := btcDiffTestHvm0Time
	cfg := *params.TestChainConfig
	cfg.Hvm0Time = &hvm0Time
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}
	chain, err := NewBlockChain(rawdb.NewMemoryDatabase(), gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)
	return chain
}

// hvmInitLightTBCConfig builds an ExternalHeaderMode TBC config mirroring eth/backend.go for an arbitrary
// network / effective-genesis / offset, so the genesis-pairing guard's policy arms can be exercised
// independently of the canonical harness.
func hvmInitLightTBCConfig(t *testing.T, network string, genesis *wire.BlockHeader, offset uint64) *tbc.Config {
	t.Helper()
	tbcCfg := tbc.NewDefaultConfig()
	tbcCfg.ExternalHeaderMode = true
	tbcCfg.EffectiveGenesisBlock = genesis
	tbcCfg.GenesisHeightOffset = offset
	tbcCfg.LevelDBHome = t.TempDir()
	tbcCfg.BlockheaderCacheSize = "0"
	tbcCfg.BlockCacheSize = "0"
	tbcCfg.AutoIndex = false
	tbcCfg.BlockSanity = true
	tbcCfg.MaxCachedTxs = 0
	tbcCfg.MempoolEnabled = false
	tbcCfg.Network = network
	return tbcCfg
}

// TestInitHvmHeaderNodeLocalnetCustomProceeds pins the localnet-Custom warn-and-proceed carve-out — the
// only reachable non-exit wrapper arm, and the most dangerous to get wrong. A Custom pairing (uncheckpointed
// network) is refused on every network except localnet, where it warns and proceeds. Without this,
// inverting `if config.Network != "localnet"` to `== "localnet"` (or deleting the carve-out) would brick
// localnet dev nodes while letting every real non-canonical network boot — a fail-open — and the suite
// would stay green.
func TestInitHvmHeaderNodeLocalnetCustomProceeds(t *testing.T) {
	chain := newHvmInitTestChain(t)
	// localnet has no checkpoint -> a self-consistent custom pair classifies Custom.
	cfg := hvmInitLightTBCConfig(t, "localnet", mustEffectiveGenesisHeader(t), 0)
	require.Equal(t, hvmGenesisPairingCustom,
		classifyHvmGenesisPairing(cfg.Network, cfg.GenesisHeightOffset, cfg.EffectiveGenesisBlock.BlockHash().String()),
		"precondition: a localnet custom pair must classify Custom")

	chain.initHvmHeaderNode(cfg) // must warn and proceed, not os.Exit
	t.Cleanup(func() { _ = chain.tbcHeaderNode.ExternalHeaderTearDown() })

	require.True(t, chain.hvmEnabled, "localnet-Custom must warn-and-proceed (hVM enabled), not refuse")
	require.NotNil(t, chain.tbcHeaderNode, "the lightweight node must have been built")
	_, _, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err, "the node must be queryable after proceeding")
}

// hvmInitCritChildEnv selects which refuse-to-start config the subprocess child builds.
const hvmInitCritChildEnv = "HVM_INIT_CRIT_CHILD_MODE"

// TestInitHvmHeaderNodeRefusesDesyncedChild is the subprocess child for TestInitHvmHeaderNodeRefuses. It is
// a no-op unless invoked with hvmInitCritChildEnv set; the parent re-execs the test binary with that env var so
// it can observe the os.Exit(1) from log.Crit (which cannot be caught in-process).
func TestInitHvmHeaderNodeRefusesDesyncedChild(t *testing.T) {
	mode := os.Getenv(hvmInitCritChildEnv)
	if mode == "" {
		t.Skip("child-only: driven by TestInitHvmHeaderNodeRefuses via subprocess re-exec")
	}
	// The root logger defaults to DiscardHandler in a bare test binary, so log.Crit would emit nothing
	// before os.Exit(1). Route it to stderr so the parent can assert on the genesis-pairing guard's refuse
	// message (not just the exit code), distinguishing it from any other log.Crit site that also exits non-zero.
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	chain := newHvmInitTestChain(t)
	var cfg *tbc.Config
	switch mode {
	case "mismatch":
		// testnet3, canonical header, wrong offset -> half-match -> Mismatch -> refuse (any network).
		cfg = hvmInitLightTBCConfig(t, "testnet3", mustEffectiveGenesisHeader(t), 999999)
	case "custom-mainnet":
		// mainnet (uncheckpointed) with the exact canonical pair -> Custom -> non-localnet -> refuse.
		cfg = hvmInitLightTBCConfig(t, "mainnet", mustEffectiveGenesisHeader(t), canonicalHvmGenesisHeight)
	case "custom-testnet3":
		// testnet3 (checkpointed/enforced) with a non-canonical pair: perturb the canonical header so its
		// hash misses, and use offset 0 so the height misses too -> the pair touches neither checkpoint field
		// -> Custom -> non-localnet -> refuse. Proves the Custom-refuse arm fires on the production network
		// (testnet3), not only the never-deployed mainnet. The correct code crits at the pairing guard before
		// tbc setup, so the perturbed header's broken PoW is never reached.
		h := mustEffectiveGenesisHeader(t)
		h.Nonce++
		cfg = hvmInitLightTBCConfig(t, "testnet3", h, 0)
	case "nil-genesis-chaincfg-unknown":
		// EffectiveGenesisBlock==nil skips the entire pairing switch (the `!= nil` guard), but the UNCONDITIONAL
		// chaincfg<->genesis lockstep crit that follows must still fire on a chaincfg-unknown network. Pins that
		// the nil-skip bypasses ONLY the pairing switch, not the lockstep guard (a mutant moving the lockstep
		// inside the `!= nil` block would let a nil-genesis chaincfg-unknown node boot and then per-block wedge).
		cfg = hvmInitLightTBCConfig(t, "zzz-no-chaincfg-params", nil, 0)
		cfg.EffectiveGenesisBlock = nil
	case "no-external-header":
		// The FIRST guard in initHvmHeaderNode: a TBC config without ExternalHeaderMode must refuse-to-start
		// (a non-external-header node would index the full Bitcoin chain — never what the consensus header node
		// wants). localnet + the canonical pair would otherwise warn-and-proceed, so reaching the crit proves
		// the ExternalHeaderMode guard fired (not the pairing guard). Distinct crit text ("ExternalHeaderMode").
		cfg = hvmInitLightTBCConfig(t, "localnet", mustEffectiveGenesisHeader(t), 0)
		cfg.ExternalHeaderMode = false
	case "chaincfg-unknown":
		// chaincfg<->genesis lockstep: a network with a pinned checkpoint (so the pairing guard classifies it
		// Canonical and passes) but no btcd chaincfg params must refuse at startup, not boot and then
		// per-block ErrCorrupt-wedge. Inject a checkpoint for a chaincfg-unknown network so the pairing guard
		// passes, reaching the lockstep crit. (This subprocess has a fresh package var; the injection is local.)
		const noChaincfgNet = "zzz-no-chaincfg-params"
		hh := mustEffectiveGenesisHeader(t)
		hvmGenesisCheckpoints[noChaincfgNet] = []btcGenesisCheckpoint{{height: canonicalHvmGenesisHeight, hash: hh.BlockHash().String()}}
		require.Equal(t, hvmGenesisPairingCanonical,
			classifyHvmGenesisPairing(noChaincfgNet, canonicalHvmGenesisHeight, hh.BlockHash().String()),
			"precondition: the injected checkpoint must make this network classify Canonical so the pairing guard passes to the lockstep check")
		cfg = hvmInitLightTBCConfig(t, noChaincfgNet, hh, canonicalHvmGenesisHeight)
	default:
		t.Fatalf("unknown child mode %q", mode)
	}
	chain.initHvmHeaderNode(cfg)
	// initHvmHeaderNode must log.Crit -> os.Exit(1) before returning. Reaching here means the refuse arm
	// did not fire; exit 0 so the parent's non-zero-exit assertion fails loudly.
	t.Fatalf("initHvmHeaderNode returned for mode %q; expected refuse-to-start (log.Crit)", mode)
}

// TestInitHvmHeaderNodeRefuses drives the two refuse-to-start wrapper arms (Mismatch on any network;
// non-localnet Custom) via subprocess re-exec, asserting both a non-zero exit and a pairing-guard-specific
// stderr substring — a bare exit!=0 is vacuity-prone (initHvmHeaderNode has other log.Crit sites that also
// exit non-zero for the wrong reason). Mutants killed: downgrading either log.Crit to log.Warn (node boots
// on a desynced/non-canonical pair), swapping the Mismatch/Custom bodies, or inverting the
// EffectiveGenesisBlock!=nil guard — none observable in-process, all survive the classifier-only test.
func TestInitHvmHeaderNodeRefuses(t *testing.T) {
	cases := []struct {
		mode            string
		wantSub         string   // a substring UNIQUE to the intended refuse arm's crit message
		wantNotSub      string   // the OTHER refuse arm's unique substring — must be ABSENT (proves the right arm)
		wantContains    []string // operator-remediation hint values the crit MUST carry (the recovery path)
		wantNotContains []string // values the crit must NOT carry (proves the network-specific hint branch)
	}{
		{"mismatch", "DESYNCED", "NOT a pinned canonical", nil, nil},
		// custom-mainnet: the Custom-refuse crit emits the canonical mainnet pair AND the wantHeader bytes (the
		// mainnet-only branch) so a bricked mainnet build has a recovery path.
		{"custom-mainnet", "NOT a pinned canonical", "DESYNCED",
			[]string{vm.MainnetHvmGenesisHash, vm.MainnetHvmGenesisHeader}, nil},
		// custom-testnet3: the canonHint is testnet3's checkpoint hash; wantHeader is mainnet-only, so the mainnet
		// header bytes must be ABSENT (proves the canonicalBTCNetwork=="mainnet" guard on the wantHeader branch).
		{"custom-testnet3", "NOT a pinned canonical", "DESYNCED",
			[]string{hvmGenesisCheckpoints["testnet3"][0].hash}, []string{vm.MainnetHvmGenesisHeader}},
		{"chaincfg-unknown", "no btcd chaincfg params", "DESYNCED", nil, nil},
	}
	for i, tc := range cases {
		// The refuse arms are the pairing guard's core protection (verdict->refuse). Keep the first on the
		// fast lane: under -short, run only the Mismatch case and skip the rest. The child crits before
		// tbc.NewServer, so it opens no leveldb — each spawn is ~0.05s, cheaper than the ungated
		// localnet-proceed test which builds a real node.
		if testing.Short() && i > 0 {
			continue
		}
		t.Run(tc.mode, func(t *testing.T) {
			cmd := exec.Command(os.Args[0], "-test.run=^TestInitHvmHeaderNodeRefusesDesyncedChild$", "-test.v")
			cmd.Env = append(os.Environ(), hvmInitCritChildEnv+"="+tc.mode)
			out, err := cmd.CombinedOutput()

			var ee *exec.ExitError
			require.ErrorAs(t, err, &ee, "child must exit non-zero (refuse-to-start), got output:\n%s", string(out))
			require.False(t, ee.Success(), "child must report failure")
			require.Contains(t, string(out), tc.wantSub,
				"child stderr must carry the pairing guard's refuse reason for mode %q", tc.mode)
			require.NotContains(t, string(out), tc.wantNotSub,
				"the OTHER refuse arm must not have fired for mode %q (arms must be discriminable)", tc.mode)
			// Negative control: a generic crash would not carry the pairing guard's refuse vocabulary.
			require.Contains(t, string(out), "Refusing to start",
				"the exit must be the pairing guard's refuse-to-start, not another log.Crit site")
			// Kills the log.Crit -> log.Warn downgrade mutant. A downgrade keeps the same message text (so
			// "Refusing to start"/"DESYNCED" still appear, now from the warn) and lets execution fall through
			// to the child's post-call t.Fatalf ("initHvmHeaderNode returned for mode"), which also exits
			// non-zero — so without this assertion the test passes though the node did not refuse. A genuine
			// log.Crit os.Exits before that marker, so the marker must be absent.
			require.NotContains(t, string(out), "initHvmHeaderNode returned for mode",
				"the pairing guard must REFUSE (os.Exit via log.Crit) before returning; the returned-marker means a refuse "+
					"arm was downgraded to log.Warn for mode %q", tc.mode)
			// Also kills the downgrade mutant for the chaincfg-lockstep 'chaincfg-unknown' arm: there the
			// witness network is rejected by both layers, so a Crit->Warn downgrade of the lockstep guard lets
			// execution fall through to tbc.NewServer, which crit-exits on the same unknown network — masking
			// the downgrade from the exit-code + "returned for mode" marker checks above (the marker is never
			// printed because tbc.NewServer crits first). A genuine refusal (pairing guard or lockstep crit)
			// happens before tbc.NewServer, so its "unable to create new TBC server" message must be absent;
			// if present, a refuse arm was downgraded and execution reached tbc.NewServer.
			require.NotContains(t, string(out), "unable to create new TBC server",
				"a refuse arm must os.Exit BEFORE tbc.NewServer for mode %q; the TBC-create crit means it was "+
					"downgraded to log.Warn and fell through", tc.mode)
			// Operator-remediation hints: the Custom-refuse crit's only recovery path. A blanked canonHint or a
			// broken wantHeader branch would leave operators no values, yet keep the message substrings above green.
			for _, want := range tc.wantContains {
				require.Contains(t, string(out), want, "mode %q crit must carry the remediation hint %q", tc.mode, want)
			}
			for _, notWant := range tc.wantNotContains {
				require.NotContains(t, string(out), notWant, "mode %q crit must NOT carry %q (wrong network hint branch)", tc.mode, notWant)
			}
		})
	}
}

// TestInitHvmHeaderNodeRefusesWithoutExternalHeaderMode drives the FIRST initHvmHeaderNode guard (line ~859) via
// subprocess re-exec: a TBC config without ExternalHeaderMode must refuse-to-start. The existing refuse harness
// only exercises the genesis-pairing/lockstep guards (all of which assume ExternalHeaderMode is already set), so
// this distinct crit had no coverage. A separate parent (not folded into TestInitHvmHeaderNodeRefuses) because its
// crit text carries neither "Refusing to start" nor the pairing vocabulary that test asserts. Mutants killed:
// inverting/deleting the `ExternalHeaderMode != true` guard, or downgrading its log.Crit to log.Warn.
func TestInitHvmHeaderNodeRefusesWithoutExternalHeaderMode(t *testing.T) {
	cmd := exec.Command(os.Args[0], "-test.run=^TestInitHvmHeaderNodeRefusesDesyncedChild$", "-test.v")
	cmd.Env = append(os.Environ(), hvmInitCritChildEnv+"=no-external-header")
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "child must exit non-zero (refuse-to-start), got output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "does not have ExternalHeaderMode set",
		"the crit must be the ExternalHeaderMode guard's, not another log.Crit site")
	require.NotContains(t, string(out), "initHvmHeaderNode returned for mode",
		"the ExternalHeaderMode guard must os.Exit (via log.Crit) before returning; the returned-marker means a downgrade to log.Warn")
}

// TestInitHvmHeaderNodeRefusesNilGenesisChaincfgUnknown drives the EffectiveGenesisBlock==nil skip via subprocess
// re-exec: with a nil genesis the pairing switch is bypassed, but the unconditional chaincfg<->genesis lockstep
// crit must still refuse a chaincfg-unknown network (else it would boot and per-block ErrCorrupt-wedge). Asserts
// the lockstep crit fired and neither pairing arm ran.
func TestInitHvmHeaderNodeRefusesNilGenesisChaincfgUnknown(t *testing.T) {
	cmd := exec.Command(os.Args[0], "-test.run=^TestInitHvmHeaderNodeRefusesDesyncedChild$", "-test.v")
	cmd.Env = append(os.Environ(), hvmInitCritChildEnv+"=nil-genesis-chaincfg-unknown")
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "child must exit non-zero (refuse-to-start), got output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "no btcd chaincfg params", "the chaincfg-lockstep crit must fire on a chaincfg-unknown network even with a nil genesis")
	require.NotContains(t, string(out), "DESYNCED", "the pairing switch must be SKIPPED (nil genesis), not entered")
	require.NotContains(t, string(out), "NOT a pinned canonical", "the pairing switch must be SKIPPED (nil genesis)")
	require.NotContains(t, string(out), "initHvmHeaderNode returned for mode", "the lockstep crit must os.Exit before returning")
}

// TestClassifyHvmGenesisPairingMultiCheckpoint exercises the classifier's loop over a network with more
// than one checkpoint — invisible in production today (every network has exactly one), but the ordering and
// the Mismatch accumulator are real code. Injects a synthetic 2-entry network with defer-restore.
func TestClassifyHvmGenesisPairingMultiCheckpoint(t *testing.T) {
	// This test mutates the package global hvmGenesisCheckpoints (with defer-restore). Safe only because Go
	// runs a package's tests sequentially and no pairing-guard test calls t.Parallel(). Do not add
	// t.Parallel() here or to any test that reads hvmGenesisCheckpoints, or this becomes a data race.
	const net = "hvminitmultitest"
	require.NotContains(t, hvmGenesisCheckpoints, net, "precondition: synthetic test network must not pre-exist")
	hashA := strings.Repeat("a", 64)
	hashB := strings.Repeat("b", 64)

	t.Run("canonical-at-index1-wins-over-latched-mismatch", func(t *testing.T) {
		// index0 half-matches the candidate (same height 200, different hash) -> mismatch=true; index1 fully
		// matches (200, B) -> must return Canonical immediately. A mutant that moves the
		// `if mismatch { return Mismatch }` check inside the loop, or defers the Canonical return behind a
		// flag, would wrongly return Mismatch here.
		hvmGenesisCheckpoints[net] = []btcGenesisCheckpoint{{height: 200, hash: hashA}, {height: 200, hash: hashB}}
		defer delete(hvmGenesisCheckpoints, net)
		require.Equal(t, hvmGenesisPairingCanonical, classifyHvmGenesisPairing(net, 200, hashB))
	})

	t.Run("latched-mismatch-survives-a-full-miss", func(t *testing.T) {
		// index0 half-matches (height 200) -> mismatch=true; index1 fully misses (999, different hash) ->
		// contributes nothing. After the loop the latched mismatch must yield Mismatch. A mutant turning the
		// latch `if hEq != sEq { mismatch = true }` into `mismatch = (hEq != sEq)` would reset it to false at
		// index1 and wrongly return Custom.
		hvmGenesisCheckpoints[net] = []btcGenesisCheckpoint{{height: 200, hash: hashA}, {height: 999, hash: hashB}}
		defer delete(hvmGenesisCheckpoints, net)
		require.Equal(t, hvmGenesisPairingMismatch, classifyHvmGenesisPairing(net, 200, "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"))
	})
}

// TestHvmGenesisCheckpointsWellFormed is the map-domain meta-test: a forward tripwire so a future mainnet
// checkpoint (or a typo'd key / malformed hash / duplicate entry) cannot slip in unnoticed. The
// checkpoint-inspection test only inspects testnet3[0]; the classifier test only checks NotEmpty/Empty;
// nothing else iterates the whole map.
func TestHvmGenesisCheckpointsWellFormed(t *testing.T) {
	// testnet3 pins two pairs ([0] compiled default, [1] DEFER-state mainnet pair); mainnet pins the single
	// MIGRATED-state pair (the dual-pin with testnet3[1]); upgradetest tracks the single default — see
	// core.hvmGenesisCheckpoints.
	allowed := map[string]int{"testnet3": 2, "mainnet": 1, "upgradetest": 1}
	require.Len(t, hvmGenesisCheckpoints, len(allowed), "testnet3, mainnet and upgradetest are pinned")
	for net, cps := range hvmGenesisCheckpoints {
		wantN, ok := allowed[net]
		require.Truef(t, ok, "unexpected checkpoint network key %q (a typo like 'mainet', or a new network that needs its own lockstep test?)", net)
		require.Lenf(t, cps, wantN, "network %q: %d checkpoint(s) expected today", net, wantN)
		for _, cp := range cps {
			require.Greaterf(t, cp.height, uint64(0), "network %q: checkpoint height must be > 0", net)
			require.Regexpf(t, "^[0-9a-f]{64}$", cp.hash, "network %q: checkpoint hash must be 64-char lowercase hex with no 0x prefix", net)
		}
	}
	// mainnet's pinned pair is the shared {883092,…eda8} constant, dual-pinned identically as testnet3[1].
	require.Equal(t, []btcGenesisCheckpoint{{height: vm.MainnetHvmGenesisHeight, hash: vm.MainnetHvmGenesisHash}}, hvmGenesisCheckpoints["mainnet"],
		"mainnet pins the shared migrated-state pair")
	require.Contains(t, hvmGenesisCheckpoints["testnet3"], btcGenesisCheckpoint{height: vm.MainnetHvmGenesisHeight, hash: vm.MainnetHvmGenesisHash},
		"testnet3 dual-pins the SAME pair (the DEFER state) — both must stay in lockstep")
	require.NotContains(t, hvmGenesisCheckpoints, "localnet", "localnet is intentionally unpinned (Custom -> warn)")
}

// TestHvmGenesisCheckpointChaincfgLockstep pins the cross-package weld between the genesis-pairing map
// (core: hvmGenesisCheckpoints, network -> checkpoint) and the validator-params map (core/vm:
// paramsForNetwork, network -> btcd chaincfg.Params). Every network with a pinned checkpoint must also
// resolve to chaincfg params, else a node boots past the genesis-pairing guard (Canonical) but cannot
// parameterize contextual-difficulty validation -> every block maps to ErrCorruptHVMHeaderOnlyModeState -> a per-block restore
// wedge. This is the CI tripwire for that drift (the same invariant initHvmHeaderNode also enforces at
// startup via the chaincfg-lockstep runtime crit, exercised by the "chaincfg-unknown" subprocess case
// above). vm.SupportsBTCNetwork resolves iff the network has chaincfg params, so it is the probe.
func TestHvmGenesisCheckpointChaincfgLockstep(t *testing.T) {
	require.NotEmpty(t, hvmGenesisCheckpoints)
	for net := range hvmGenesisCheckpoints {
		require.Truef(t, vm.SupportsBTCNetwork(net),
			"checkpointed network %q must have btcd chaincfg params (chaincfg<->genesis lockstep)", net)
	}
	// The production consensus node's hardcoded network (eth/backend.go buildHvmHeaderNodeConfig) must be
	// both checkpointed and chaincfg-resolvable. Pinned so a future change to either map for testnet3 is
	// caught. (upgradetest is the TBC alias, covered by the loop above.)
	require.True(t, vm.SupportsBTCNetwork("testnet3"), "the shipped consensus network (testnet3) must resolve to chaincfg params")
	require.Contains(t, hvmGenesisCheckpoints, "testnet3", "the shipped consensus network (testnet3) must be checkpointed")
	// The dev network localnet, which the pairing guard lets boot Custom, must also be chaincfg-resolvable
	// (else a localnet dev node would boot then wedge).
	require.True(t, vm.SupportsBTCNetwork("localnet"), "localnet must resolve to chaincfg params even though it is intentionally uncheckpointed")
	// Negative control: a network with neither checkpoint nor chaincfg params is what the lockstep forbids
	// (and what the chaincfg-lockstep startup crit relies on rejecting).
	require.False(t, vm.SupportsBTCNetwork("zzz-no-chaincfg-params"), "an unknown network must fail the chaincfg probe")
}

// TestHvmMigration_LaggedStore_CatchUpAdvancesToBodiedTip exercises the forward-catch-up apply loop of
// catchUpMigratedStoreToTip ([S+1 .. tip]) over a genuinely lagged lightweight store. The pre-loop guards
// (no-op-at-tip, unknown-id, from>tip, non-canonical-ancestor) are covered elsewhere; this drives the loop body.
// Needs no real full node or mainnet data.
//
// The seam: build the bodied EVM chain BEFORE attaching the light TBC node, so the node lags by construction.
// Plain Hvm0-active blocks (no BtcAttr tx) are inserted while hvmEnabled==false — the apply path is gated on
// bc.hvmEnabled, so InsertChain touches no TBC store. Then the light node is attached (initHvmHeaderNode does
// only ExternalHeaderSetup, no state restore), leaving the store at the genesis upstream-state-id while
// CurrentBlock() leads it. catchUpMigratedStoreToTip must then walk the store forward to the bodied tip via the
// no-BtcAttr Hvm0 apply branch, which only SetUpstreamStateId's (no full node needed).
func TestHvmMigration_LaggedStore_CatchUpAdvancesToBodiedTip(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	// Hvm0Time=0 so genesis AND every generated block is Hvm0-active (no activation-transition special case, and
	// every no-BtcAttr block takes the IsHvm0 SetUpstreamStateId branch, keeping the parent-chain check valid).
	cfg := *params.TestChainConfig
	hvm0 := uint64(0)
	cfg.Hvm0Time = &hvm0
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}

	// Plain bodied blocks (NO BtcAttr tx), generated + inserted BEFORE the hVM node is attached.
	db, blocks, _ := GenerateChainWithGenesis(gspec, ethash.NewFaker(), 8, func(i int, b *BlockGen) {})
	chain, err := NewBlockChain(db, gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)
	require.False(t, chain.hvmEnabled, "precondition: hVM node not yet attached, so InsertChain touches no TBC store")

	_, err = chain.InsertChain(blocks)
	require.NoError(t, err)
	require.Equal(t, uint64(8), chain.CurrentBlock().Number.Uint64(), "bodied tip lands on disk")

	// Attach the light TBC node LATE (same config as newRegtestChainWithLightTBC) — it does no state restore, so
	// it sits at the genesis upstream-state-id while CurrentBlock() leads it: a genuine lag.
	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header
	tbcCfg := tbc.NewDefaultConfig()
	tbcCfg.ExternalHeaderMode = true
	tbcCfg.EffectiveGenesisBlock = genesis
	tbcCfg.GenesisHeightOffset = 0
	tbcCfg.LevelDBHome = t.TempDir()
	tbcCfg.BlockheaderCacheSize, tbcCfg.BlockCacheSize = "0", "0"
	tbcCfg.AutoIndex, tbcCfg.BlockSanity, tbcCfg.MaxCachedTxs, tbcCfg.MempoolEnabled = false, true, 0, false
	tbcCfg.Network = "localnet"
	chain.initHvmHeaderNode(tbcCfg)
	t.Cleanup(func() { _ = chain.tbcHeaderNode.ExternalHeaderTearDown() })
	require.True(t, chain.hvmEnabled)

	// Set the store's upstream-state-id to an EARLY canonical block S (strictly below the bodied tip).
	s := chain.GetCanonicalHash(2)
	require.NotEqual(t, common.Hash{}, s)
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, [32]byte(s)))
	require.True(t, chain.legacyStateIdIsCanonical([32]byte(s)), "precondition: S is a canonical ancestor at/below the bodied tip")

	// Drive the catch-up apply loop n=3..8. Capture logs: applyHvmHeaderConsensusUpdate emits "Nothing to apply..."
	// per plain block, proving the loop actually walked and applied each [S+1..tip] block rather than jumping
	// straight to SetUpstreamStateId(tip) (which would land the same final state-id but emit none of these logs).
	var ccBuf bytes.Buffer
	ccPrev := log.Root()
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(&ccBuf, slog.LevelDebug, false)))
	require.NoError(t, chain.catchUpMigratedStoreToTip([32]byte(s)))
	log.SetDefault(ccPrev)
	require.Contains(t, ccBuf.String(), "Nothing to apply in hVM state for block",
		"the catch-up loop must apply each intermediate block (not jump straight to the tip state-id)")

	// The store's upstream-state-id must advance exactly to the bodied tip. An off-by-one in the n<=tipN loop bound
	// or a dropped SetUpstreamStateId in the no-BtcAttr branch would both leave it short of CurrentBlock.
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, chain.CurrentBlock().Hash(), common.Hash(*sid),
		"after catch-up the store upstream-state-id must equal the bodied tip")
}

// TestMigrate_LaggedStore_CatchUpThroughOrchestration drives a genuinely lagged store through the full migrate
// orchestration (maybeMigrateHvmHeaderNode), not the standalone catchUpMigratedStoreToTip. The other orchestration
// success tests set S = CurrentBlock().Hash(), making the catch-up a no-op (from==tip early return), so the
// catchUpMigratedStoreToTip call inside migrateHvmHeaderNode and the S->bodied-tip advance go unexercised at the
// orchestration level; dropping that call would still pass those tests yet brick a real lagged-store boot. Needs no
// corpus: real mainnet BTC genesis + synthetic children + an Hvm0 plain-block EVM chain.
func TestMigrate_LaggedStore_CatchUpThroughOrchestration(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node + migrate fixture")
	}
	ctx := context.Background()
	mainnetGen := decodeMainnetGenesisHeader(t)

	// Synthetic children hash-linked from the real mainnet genesis (observe-only never halts on their easy PoW).
	const N = 4
	children := make([]*wire.BlockHeader, N)
	prev := mainnetGen
	for i := 0; i < N; i++ {
		h := &wire.BlockHeader{Version: prev.Version, PrevBlock: prev.BlockHash(), MerkleRoot: mainnetGen.MerkleRoot,
			Timestamp: prev.Timestamp.Add(time.Duration(i+1) * 10 * time.Minute), Bits: mainnetGen.Bits, Nonce: uint32(i + 1)}
		children[i] = h
		prev = h
	}
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

	// An Hvm0-active (Hvm0Time=0) EVM chain of plain (no-BtcAttr) blocks, built BEFORE the hVM node attaches so it
	// lags by construction; the catch-up walks the no-BtcAttr SetUpstreamStateId branch (no full-node read).
	ecfg := *params.TestChainConfig
	hvm0 := uint64(0)
	ecfg.Hvm0Time = &hvm0
	gspec := &Genesis{Config: &ecfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}
	edb, blocks, _ := GenerateChainWithGenesis(gspec, ethash.NewFaker(), 8, func(i int, b *BlockGen) {})
	bc, err := NewBlockChain(edb, gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, ctx)
	require.NoError(t, err)
	defer bc.Stop()
	require.False(t, bc.hvmEnabled, "precondition: no hVM node yet, so InsertChain touches no TBC store")
	_, err = bc.InsertChain(blocks)
	require.NoError(t, err)
	require.Equal(t, uint64(8), bc.CurrentBlock().Number.Uint64())

	// The legacy store records an early canonical state-id S (strictly below the bodied tip) so the catch-up must run.
	S := [32]byte(bc.GetCanonicalHash(2))
	require.True(t, bc.legacyStateIdIsCanonical(S), "precondition: S is canonical and below the bodied tip")
	require.NotEqual(t, bc.CurrentBlock().Hash(), common.Hash(S), "precondition: S lags the bodied tip (catch-up is not a no-op)")

	home := t.TempDir()
	full := newSrv(t.TempDir(), "mainnet", [32]byte{0x01})
	defer func() { _ = full.ExternalHeaderTearDown() }()
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	vm.TBCFullNode, vm.TBCFullNodeConfig = full, &tbc.Config{Network: "mainnet"}
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	legacy := newSrv(home, "testnet3", S)
	require.NoError(t, legacy.ExternalHeaderTearDown())

	cfg := mainnetMigrateConfig(mainnetGen, home)
	handled := bc.maybeMigrateHvmHeaderNode(cfg)
	t.Cleanup(func() {
		if bc.tbcHeaderNode != nil {
			_ = bc.tbcHeaderNode.ExternalHeaderTearDown()
		}
	})
	require.True(t, handled, "a ready full node + a progressed lagged legacy store must MIGRATE")
	require.Equal(t, "mainnet", cfg.Network)

	// The catch-up ran through the orchestration and advanced the rebuilt store from S to the bodied tip.
	sid, err := bc.tbcHeaderNode.UpstreamStateId(ctx)
	require.NoError(t, err)
	require.Equal(t, bc.CurrentBlock().Hash(), common.Hash(*sid),
		"after migration the rebuilt store's upstream-state-id must equal the bodied tip (catch-up advanced S->tip)")

	// Retirement: the backup is named by the legacy (pre-catch-up) state-id S, not the advanced bodied tip.
	// Rollback expects the backup keyed by the pre-migration legacy S. This is the only orchestration success test
	// where S != tip, so naming the backup by the advanced tip would only be detectable here (every other test sets
	// S == CurrentBlock, making the two names identical).
	require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be retired after a lagged migration")
	require.DirExists(t, filepath.Join(home, fmt.Sprintf("testnet3.migrated-%x", S[:])),
		"the backup must be named by the LEGACY state-id S (block-2 hash), not the post-catch-up tip")
	require.NoDirExists(t, filepath.Join(home, fmt.Sprintf("testnet3.migrated-%x", bc.CurrentBlock().Hash().Bytes())),
		"the backup must NOT be named by the post-catch-up bodied tip (S != tip here)")
}

// newHvmTestChainWithLightTBC builds a real BlockChain with hVM Phase 0 activating at hvm0Time and a real
// embedded lightweight (external-header-mode) TBC node attached, returning the chain and the lightweight
// node's current best (genesis-checkpoint) BTC tip header. It does not use the full SetupHvmHeaderNode
// (which would try a state restore against the EVM tip); it attaches the node directly via
// initHvmHeaderNode, which is what the empty-but-present BtcAttr fix's apply/unapply paths exercise.
func newHvmTestChainWithLightTBC(t *testing.T, hvm0Time uint64) (*BlockChain, *wire.BlockHeader) {
	t.Helper()

	cfg := *params.TestChainConfig
	cfg.Hvm0Time = &hvm0Time
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}

	chain, err := NewBlockChain(rawdb.NewMemoryDatabase(), gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)

	// Attach a real lightweight TBC node, mirroring eth/backend.go's external-header config. Use the
	// synthetic min-difficulty testnet3 genesis (hvmSynthetic*, the old 3488421/0x1d00ffff), not the
	// production canonical genesis (now 3522419, a retarget-difficulty block), because the synthetic seeding
	// mines min-difficulty children that must be contextually valid building on the genesis. Temporarily
	// override the testnet3 checkpoint to this pair so initHvmHeaderNode's genesis-pairing assertion accepts
	// it (restored on cleanup; safe — package tests are sequential, none t.Parallel). This decouples the
	// synthetic harness from the production genesis value.
	savedCp := hvmGenesisCheckpoints["testnet3"]
	hvmGenesisCheckpoints["testnet3"] = []btcGenesisCheckpoint{{height: hvmSyntheticGenesisHeight, hash: hvmSyntheticGenesisHash}}
	t.Cleanup(func() { hvmGenesisCheckpoints["testnet3"] = savedCp })
	tbcCfg := tbc.NewDefaultConfig()
	tbcCfg.ExternalHeaderMode = true
	tbcCfg.EffectiveGenesisBlock = hvmSyntheticGenesisHeader(t)
	tbcCfg.GenesisHeightOffset = hvmSyntheticGenesisHeight
	tbcCfg.LevelDBHome = t.TempDir()
	tbcCfg.BlockheaderCacheSize = "0"
	tbcCfg.BlockCacheSize = "0"
	tbcCfg.AutoIndex = false
	tbcCfg.BlockSanity = true
	tbcCfg.MaxCachedTxs = 0
	tbcCfg.MempoolEnabled = false
	tbcCfg.Network = "testnet3"

	chain.initHvmHeaderNode(tbcCfg)
	t.Cleanup(func() { _ = chain.tbcHeaderNode.ExternalHeaderTearDown() })

	height, lightTip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)

	// Canonical-arm oracle (load-bearing for every empty-present / revert / unapply / contextual-difficulty test using this
	// harness): initHvmHeaderNode above ran the genesis-pairing assertion on the canonical production config;
	// any verdict but Canonical would have log.Crit-exited. Pin that the real node seated the canonical
	// (offset, header) pair so the Canonical-accept arm cannot silently regress (e.g. into the localnet warn
	// arm). Without this, the only proof the wrapper accepted is "the process did not exit".
	require.True(t, chain.hvmEnabled, "initHvmHeaderNode must have proceeded (hVM enabled) on the (overridden) canonical pair")
	require.Equal(t, hvmSyntheticGenesisHeight, height,
		"lightweight node must seat the effective genesis at the synthetic GenesisHeightOffset")
	require.Equal(t, hvmSyntheticGenesisHeader(t).BlockHash().String(), lightTip.BlockHash().String(),
		"best header at startup must be the synthetic effective-genesis header")
	// The integration accept/reject/defer difficulty oracles (TestHvmBtcDiffFloorAwareAgainstRealLightweightNode, TestHvmApplyPath*) assume the
	// seed carries testnet3 PowLimitBits (min difficulty). Anchor it here so a genesis re-pin to a
	// non-min-diff header cannot silently vacate those oracles (e.g. make a wrong-difficulty header
	// accidentally correct).
	require.Equal(t, uint32(0x1d00ffff), lightTip.Bits,
		"effective-genesis header must carry testnet3 PowLimitBits (0x1d00ffff)")
	return chain, lightTip
}

// TestHvmEmptyPresentApplyUnapplyRoundTrip is the integration regression for the empty-but-present BtcAttr
// fix against a real embedded TBC node. An "empty-but-present" Bitcoin Attributes Deposited tx (present,
// zero headers) must:
//   - forward-apply by advancing the TBC upstream-state-id to this block (the original bug left it at the
//     parent, which then crashed the next block / state restore); and
//   - reorg-unapply as a no-op that rolls the state-id back, without calling RemoveExternalHeaders (which
//     a zero-header set is an invalid RemoveExternalHeaders call -> crash on unfixed code).
//
// Drives the real applyHvmHeaderConsensusUpdate / unapplyHvmHeaderConsensusUpdate against a real *tbc.Server
// and asserts the upstream-state-id round-trips genesis -> N -> genesis with no crash. The activation-block
// geometry (parent pre-activation) keeps the apply on the genesis "first hVM header update" branch and the
// unapply on the activation special-case (rolls to genesis), exercising the empty-but-present edits.
func TestHvmEmptyPresentApplyUnapplyRoundTrip(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)

	// Sanity: a freshly initialized lightweight node reports the genesis upstream-state-id.
	sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId[:], sid0[:], "fresh lightweight TBC must start at the genesis upstream-state-id")

	// Build an empty-but-present BtcAttr tx whose CanonicalTip matches the lightweight tip (so the
	// forward CanonicalTip acceptance check passes) and carries zero headers.
	canon := lightTip.BlockHash()
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, nil)
	require.NoError(t, err)
	tx := types.NewTx(btcAttr)

	// Activation block N (Time >= hvm0Time), built on a pre-activation parent (Time < hvm0Time).
	parentHeader := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	nHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: parentHeader.Hash()}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{tx}})

	// Confirm the tx really is an empty-but-present BtcAttr.
	btcAttrDep, err := blockN.Transactions().ExtractBtcAttrData()
	require.NoError(t, err)
	require.NotNil(t, btcAttrDep, "BtcAttr tx must be present")
	require.Len(t, btcAttrDep.Headers, 0, "this must be the empty-but-present (zero-header) case")
	require.True(t, btcAttrDepIsHeaderless(btcAttrDep))

	// Make the block + parent retrievable via the holding pen (apply/unapply look them up). The parent is
	// seeded as both a header and a block: the fixed unapply only needs the parent header (its no-op branch
	// reads getHeaderFromDiskOrHoldingPen for the rollback target), but pre-fix code falls through to the
	// backward-walk, which fetches the parent block via getBlockFromDiskOrHoldingPen and would otherwise
	// nil-deref there instead of reaching the RemoveExternalHeaders-empty log.Crit. Seeding the parent block
	// makes the pre-fix failure the genuine empty-header crash this test guards against.
	chain.tempHeaders[parentHeader.Hash().String()] = parentHeader
	chain.tempBlocks[parentHeader.Hash().String()] = types.NewBlockWithHeader(parentHeader)
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()

	// Forward apply: must not crash and must advance the upstream-state-id to block N.
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true),
		"forward-apply of an empty-but-present BtcAttr block must succeed")
	sid1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sid1[:],
		"forward-apply must advance the upstream-state-id to this block (the state-id-advance fix)")

	// Reorg unapply: must not crash and must roll the upstream-state-id back to genesis (parent is
	// pre-activation). Pre-fix failure signature: the bug is a hard crash, so on unfixed code this fails by
	// process abort (log.Crit -> os.Exit when RemoveExternalHeaders is called with the zero-header set), not
	// a clean require failure — that abort is the empty-header-crash regression this asserts is gone.
	require.NoError(t, chain.unapplyHvmHeaderConsensusUpdate(blockN.Header()),
		"reorg-unapply of an empty-but-present BtcAttr block must succeed (the empty-header unapply no-op fix)")
	sid2, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId[:], sid2[:],
		"unapplying the activation block must roll the upstream-state-id back to genesis")

	// Confirm the crash trigger the unapply fix avoids: RemoveExternalHeaders with a zero-header set returns
	// an error in the pinned TBC node (on the precondition before any write, so it does not mutate state).
	_, _, errEmpty := chain.tbcHeaderNode.RemoveExternalHeaders(chain.ctx, &wire.MsgHeaders{}, lightTip, hVMGenesisUpstreamId[:])
	require.Error(t, errEmpty,
		"empty RemoveExternalHeaders must error — exactly the crash the empty-but-present BtcAttr unapply no-op avoids by skipping the call")
}

// TestHvmEmptyPresentNextBlockAppliesCleanly reproduces the empty-but-present forward-crash case — the more
// severe, no-reorg-needed manifestation. Pre-fix, a mid-chain empty-but-present BtcAttr block (parent
// already hVM-active, so the state-id was at the parent) failed to advance the upstream-state-id, leaving
// it pinned at the grandparent; the next block then tripped the parent-mismatch log.Crit in
// applyHvmHeaderConsensusUpdate because the state-id no longer matched its parent — a crash on unfixed code with no reorg. With the
// fix, the empty block advances the state-id to itself, so the next block applies cleanly. Drives the real
// applyHvmHeaderConsensusUpdate against a real *tbc.Server.
func TestHvmEmptyPresentNextBlockAppliesCleanly(t *testing.T) {
	const hvm0Time = uint64(1000)
	chain, lightTip := newHvmTestChainWithLightTBC(t, hvm0Time)
	canon := lightTip.BlockHash()

	// M: activation block, a normal (no-BtcAttr) hVM-active block -> advances state-id to M.
	parent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1} // pre-activation parent of M
	mHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: parent.Hash()}
	blockM := types.NewBlockWithHeader(mHeader)

	// N: mid-chain empty-but-present BtcAttr block (parent M is already hVM-active).
	btcAttr, err := types.MakeBtcAttributesDepositedTx(&canon, nil)
	require.NoError(t, err)
	nHeader := &types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: mHeader.Hash()}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})

	// N1: the next normal block, built on N.
	n1Header := &types.Header{Number: big.NewInt(13), Time: hvm0Time + 2, ParentHash: nHeader.Hash()}
	blockN1 := types.NewBlockWithHeader(n1Header)

	// Seed M, N, N1 as blocks+headers. Load-bearing: when applying N1 the forward prev-state sanity check
	// resolves the prior-state block via getBlockFromDiskOrHoldingPen and
	// dereferences it, so the intermediate blocks must be present or it would nil-deref instead of
	// exercising the parent-mismatch path.
	chain.tempHeaders[parent.Hash().String()] = parent
	for _, b := range []*types.Block{blockM, blockN, blockN1} {
		chain.tempBlocks[b.Hash().String()] = b
		chain.tempHeaders[b.Hash().String()] = b.Header()
	}

	// Apply M (activation, no BtcAttr) -> state-id = M.
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockM.Header(), false, true))
	sidM, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockM.Hash().Bytes(), sidM[:])

	// Apply N (empty-but-present, mid-chain) -> must advance state-id to N (the fix).
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true))
	sidN, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sidN[:],
		"mid-chain empty-but-present block must advance the state-id to itself (pre-fix it stayed at M)")

	// The next block must apply without the parent-mismatch crit. Pre-fix the state-id was stuck at M,
	// so block N1 (parent N) found state-id(M) != parent(N) and hit log.Crit (os.Exit).
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN1.Header(), false, true),
		"the block after an empty-but-present block must apply cleanly (pre-fix the stale state-id crashed the parent-mismatch check)")
	sidN1, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN1.Hash().Bytes(), sidN1[:])
}

// TestHvmNonEmptyBtcAttrTakesRealHeaderPath is the negative control: it proves the btcAttrDepIsHeaderless
// guard does not swallow a populated BtcAttr block. A block carrying real BTC headers must take the genuine
// AddExternalHeaders path (advancing the lightweight tip), not the headerless no-op — so an over-broadening
// of the guard (the symmetric inverse of the empty-but-present bug) would make this fail (the tip would not
// advance). External-header insertion validates contiguity + cumulative work (CalcWork from Bits), not PoW,
// so synthetic headers chained off the genesis checkpoint with the genesis Bits are accepted. Apply only:
// the unapply of a real-header activation block walks back for a prior BtcAttr tip that does not exist
// (parent is pre-activation), a separate edge; the apply assertion alone proves the non-swallow guard.
func TestHvmNonEmptyBtcAttrTakesRealHeaderPath(t *testing.T) {
	const hvm0Time = uint64(1000)
	// Regtest harness: once the apply path enforces proof-of-work, the headers must be really mined (regtest
	// PoW is mineable in ~2 nonces). These near-genesis headers are below the floor clearance so contextual
	// difficulty defers, exercising the real AddExternalHeaders header path (the fix's subject).
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)

	// Build a 3-header mined chain off the lightweight tip (the genesis checkpoint).
	headers := make([]wire.BlockHeader, 0, 3)
	prev := genesis
	for i := 0; i < 3; i++ {
		h := mineRegtestChild(t, prev, uint32(1000+i)*101+1)
		headers = append(headers, *h)
		prev = h
	}
	newTip := headers[len(headers)-1].BlockHash()

	btcAttr, err := types.MakeBtcAttributesDepositedTx(&newTip, headers)
	require.NoError(t, err)

	parentHeader := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	nHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: parentHeader.Hash()}
	blockN := types.NewBlockWithHeader(nHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})

	// Sanity: this is a populated (not headerless) BtcAttr tx.
	dep, err := blockN.Transactions().ExtractBtcAttrData()
	require.NoError(t, err)
	require.Len(t, dep.Headers, 3)
	require.False(t, btcAttrDepIsHeaderless(dep), "a 3-header BtcAttr tx must NOT be classified headerless")

	chain.tempHeaders[parentHeader.Hash().String()] = parentHeader
	chain.tempBlocks[parentHeader.Hash().String()] = types.NewBlockWithHeader(parentHeader)
	chain.tempBlocks[blockN.Hash().String()] = blockN
	chain.tempHeaders[blockN.Hash().String()] = blockN.Header()

	// Apply: the populated block must take the real AddExternalHeaders path, advancing the lightweight tip
	// to the new chain tip and the state-id to block N. If the headerless guard wrongly swallowed it, the
	// tip would stay at the genesis checkpoint and this would fail.
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockN.Header(), false, true))
	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	tipAfterHash := tipAfter.BlockHash()
	require.Equal(t, newTip[:], tipAfterHash[:],
		"a real-header BtcAttr block must advance the lightweight tip via AddExternalHeaders (proves it did NOT take the headerless no-op)")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockN.Hash().Bytes(), sid[:])
}

// Metric NAME-stability tripwire. Dashboards and alerts scrape these meters and gauges by their registered NAME
// strings, an external contract a rename silently breaks. Other tests check the VALUES via the Go package variable,
// never the literal name, so a typo'd rename leaves them green while breaking the dashboard query. This pins each
// metric to its exact name and sweeps for any stray sibling under chain/hvm/.
func TestHvmMetricNamesStable(t *testing.T) {
	meters := map[string]*metrics.Meter{
		"chain/hvm/migration/triggered":      hvmMigrationTriggeredMeter,
		"chain/hvm/migration/deferred":       hvmMigrationDeferredMeter,
		"chain/hvm/migration/completed":      hvmMigrationCompletedMeter,
		"chain/hvm/migration/failed":         hvmMigrationFailedMeter,
		"chain/hvm/migration/pow_reject":     hvmMigrationPoWRejectMeter,
		"chain/hvm/migration/btcdiff_reject": hvmMigrationBtcDiffRejectMeter,
		"chain/hvm/snap/pow_reject":          hvmSnapPoWRejectMeter,
		"chain/hvm/snap/btcdiff_reject":      hvmSnapBtcDiffRejectMeter,
		"chain/hvm/btcattr/fail":             hvmBtcAttrFailMeter,
		"chain/hvm/btcattr/diff_trunc":       hvmBtcAttrDiffTruncMeter,
		"chain/hvm/reapply/restore":          hvmReapplyRestoreMeter,
	}
	gauges := map[string]*metrics.Gauge{
		"chain/hvm/migration/in_progress": hvmMigrationInProgressGauge,
		"chain/hvm/btcattr/failing":       hvmBtcAttrFailingGauge,
		"chain/hvm/fulltbc/behind":        hvmFullTBCBehindGauge,
		"chain/hvm/snap/awaiting":         hvmSnapAwaitingGauge,
	}

	expected := make(map[string]bool)
	for name, want := range meters {
		got, ok := metrics.DefaultRegistry.Get(name).(*metrics.Meter)
		require.Truef(t, ok, "meter %q must be registered under its exact name", name)
		require.Samef(t, want, got, "meter %q must resolve to its own variable (rename/collision detector)", name)
		expected[name] = true
	}
	for name, want := range gauges {
		got, ok := metrics.DefaultRegistry.Get(name).(*metrics.Gauge)
		require.Truef(t, ok, "gauge %q must be registered under its exact name", name)
		require.Samef(t, want, got, "gauge %q must resolve to its own variable", name)
		expected[name] = true
	}

	// Prefix-exclusivity: every registered chain/hvm/ metric must be in the pinned set, so a stray or typo'd
	// sibling like chain/hvm/migraton/... cannot slip in unnoticed.
	metrics.DefaultRegistry.Each(func(name string, _ interface{}) {
		if strings.HasPrefix(name, "chain/hvm/") {
			require.Truef(t, expected[name], "unexpected chain/hvm/ metric %q — pin it here (typo, or a new metric)", name)
		}
	})
}

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
		polls, maxPolls int
		want            bool
	}{
		// Production horizon (maxHvmSnapBodyAbsentPolls). The live give-up site now CALLS this predicate with
		// bc.effectiveMaxBodyAbsentPolls(), so these rows pin the ACTUAL live boundary, not a copy of it.
		{0, maxHvmSnapBodyAbsentPolls, false},
		{1, maxHvmSnapBodyAbsentPolls, false},
		{maxHvmSnapBodyAbsentPolls - 1, maxHvmSnapBodyAbsentPolls, false}, // one below the bound: keep waiting
		{maxHvmSnapBodyAbsentPolls, maxHvmSnapBodyAbsentPolls, true},      // exactly at the bound: give up (>= boundary)
		{maxHvmSnapBodyAbsentPolls + 1, maxHvmSnapBodyAbsentPolls, true},  // above the bound: give up
		// Injectable override horizon (the test-only hvmSnapBodyAbsentPollsLimit path). A > vs >= off-by-one at the
		// bound is discriminated here regardless of the horizon value the live waiter resolves.
		{2, 3, false}, // one below the lowered bound: keep waiting
		{3, 3, true},  // exactly at the lowered bound: give up
		{4, 3, true},  // above the lowered bound: give up
	}
	for _, c := range cases {
		if got := bodyAbsentShouldGiveUp(c.polls, c.maxPolls); got != c.want {
			t.Errorf("bodyAbsentShouldGiveUp(%d, %d) = %v, want %v", c.polls, c.maxPolls, got, c.want)
		}
	}
}

// TestShouldWalkBackTipLag pins the updateFullTBCToLightweight tip-lag walk-back boundary, including the
// unsigned-underflow case the addition form (cursorHeight > genesisOffset+lag) avoids. A subtraction form
// (cursorHeight - lag > genesisOffset) wraps to a huge value (passing the guard, then walking below genesis)
// when cursorHeight < lag — reachable right after the hVM Phase-0 transition on a near-zero-offset regtest
// network. That subtraction form, or a > vs >= off-by-one at the genesis floor, fails here.
func TestShouldWalkBackTipLag(t *testing.T) {
	cases := []struct {
		name                      string
		cursorHeight, offset, lag uint64
		want                      bool
	}{
		// Underflow region: cursorHeight < lag. A subtraction form (cursorHeight - lag > genesisOffset) would wrap TRUE here; correct is FALSE.
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

// L2 reorg onto a COMPETING branch: the only updateHvmHeaderConsensus arm that composes
// walkHvmHeaderConsensusBack (unwind the orphaned branch) THEN walkHvmHeaderConsensusForward (apply the competing
// branch). Every existing apply/unapply test is single-branch (apply-then-unapply the SAME branch, or back-only, or
// forward-only) — none unwinds one branch's REAL BTC headers and re-applies a DIFFERENT branch's headers. A same-
// branch round-trip cannot catch a cross-branch residue because the re-applied headers are identical to the
// unapplied ones. Oracle: a node that reorgs from the orphaned branch onto the competing branch must reach a view
// (tip hash + height + upstream-state-id) byte-IDENTICAL to a reference node that only ever saw the competing branch.
func TestHvmReorgForkConvergesToCompetingBranch(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into real lightweight TBC nodes")
	}
	const hvm0Time = uint64(1000)

	for _, tc := range []struct {
		name           string
		orphanN, compN int
	}{
		{"orphan-deeper", 3, 1}, // unwind 3, re-apply 1
		{"competing-deeper", 1, 3},
	} {
		t.Run(tc.name, func(t *testing.T) {
			node, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
			ref, _ := newRegtestChainWithLightTBC(t, hvm0Time)

			mineN := func(n int, nonceBase uint32) ([]wire.BlockHeader, chainhash.Hash) {
				hs := make([]wire.BlockHeader, 0, n)
				prev := genesis
				for i := 0; i < n; i++ {
					h := mineRegtestChild(t, prev, nonceBase+uint32(i))
					hs = append(hs, *h)
					prev = h
				}
				return hs, hs[len(hs)-1].BlockHash()
			}
			// timeOff distinguishes the two competing blocks: block.Hash() is header-only (WithBody does not recompute
			// the TxHash), so same-header competing blocks would otherwise collide.
			branchBlock := func(num int64, timeOff uint64, parent *types.Block, headers []wire.BlockHeader, tip chainhash.Hash) *types.Block {
				btc, err := types.MakeBtcAttributesDepositedTx(&tip, headers)
				require.NoError(t, err)
				return types.NewBlockWithHeader(&types.Header{Number: big.NewInt(num), Time: hvm0Time + timeOff, ParentHash: parent.Hash()}).
					WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc)}})
			}

			// Common ancestor: a no-BtcAttr activation block A (parent pre-activation). Applying it sets state-id=A
			// with the tip still at the genesis checkpoint, so both competing branches build off the same checkpoint.
			preAct := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
			blockA := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: preAct.Hash()})

			xHeaders, xTip := mineN(tc.orphanN, 2000) // orphaned branch X
			yHeaders, yTip := mineN(tc.compN, 9000)   // competing branch Y (distinct nonce base -> distinct hashes)
			require.NotEqual(t, xTip, yTip, "the two branches must have distinct tips")
			blockB := branchBlock(12, 1, blockA, xHeaders, xTip) // orphan branch block (parent A)
			blockC := branchBlock(12, 2, blockA, yHeaders, yTip) // competing branch block (parent A, same height, diff body)
			require.NotEqual(t, blockB.Hash(), blockC.Hash(), "competing blocks must differ")

			seed := func(c *BlockChain) {
				c.tempHeaders[preAct.Hash().String()] = preAct
				c.tempBlocks[preAct.Hash().String()] = types.NewBlockWithHeader(preAct)
				for _, b := range []*types.Block{blockA, blockB, blockC} {
					c.tempBlocks[b.Hash().String()] = b
					c.tempHeaders[b.Hash().String()] = b.Header()
				}
			}
			seed(node)
			seed(ref)

			// REFERENCE: only ever sees A then the competing branch C.
			require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
			require.NoError(t, ref.applyHvmHeaderConsensusUpdate(blockC.Header(), false, true))
			refHeight, refTip, err := ref.tbcHeaderNode.BlockHeaderBest(ref.ctx)
			require.NoError(t, err)
			refSid, err := ref.tbcHeaderNode.UpstreamStateId(ref.ctx)
			require.NoError(t, err)
			require.Equal(t, blockC.Hash().Bytes(), refSid[:])
			refTipHash := refTip.BlockHash()
			require.Equal(t, yTip[:], refTipHash[:])

			// NODE under test: apply A then the ORPHAN branch B, then reorg (unwind B, re-apply C).
			require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))
			require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockB.Header(), false, true))
			_, orphTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
			require.NoError(t, err)
			orphTipHash := orphTip.BlockHash()
			require.Equal(t, xTip[:], orphTipHash[:], "node is on the orphan branch tip before the reorg")

			// The fork: unwind the orphan branch back to the common ancestor A (the production walk that genuinely
			// UN-applies committed real BTC headers), then re-apply the competing branch C. (The re-apply uses the
			// direct apply with attemptPrefetch=false rather than walkHvmHeaderConsensusForward, because the forward
			// walk forces a block-availability prefetch that requires a real FULL TBC node — out of corpus-free
			// scope; it is a best-effort fetch optimization that logs-and-continues and does not affect the committed
			// consensus view this test asserts.)
			require.NoError(t, node.walkHvmHeaderConsensusBack(blockB.Header(), blockA.Header()))
			// Intermediate: back at the common ancestor (state-id A, tip at the genesis checkpoint, X removed).
			midSid, err := node.tbcHeaderNode.UpstreamStateId(node.ctx)
			require.NoError(t, err)
			require.Equal(t, blockA.Hash().Bytes(), midSid[:], "after unwind the state-id is the common ancestor A")
			for _, h := range xHeaders {
				_, _, e := node.tbcHeaderNode.BlockHeaderByHash(node.ctx, h.BlockHash())
				require.Error(t, e, "orphan-branch header must be fully removed by the unwind")
			}
			require.NoError(t, node.applyHvmHeaderConsensusUpdate(blockC.Header(), false, true))

			// CONVERGENCE: byte-exact with the reference node that only ever saw the competing branch.
			nodeHeight, nodeTip, err := node.tbcHeaderNode.BlockHeaderBest(node.ctx)
			require.NoError(t, err)
			nodeSid, err := node.tbcHeaderNode.UpstreamStateId(node.ctx)
			require.NoError(t, err)
			nodeTipHash := nodeTip.BlockHash()
			require.Equal(t, refTipHash[:], nodeTipHash[:], "post-reorg tip must equal the competing-branch-only reference")
			require.Equal(t, refHeight, nodeHeight, "post-reorg height must converge")
			require.Equal(t, refSid[:], nodeSid[:], "post-reorg upstream-state-id must converge (no orphan residue)")
		})
	}
}

// Boot-sequence coverage for performFullHvmHeaderStateRestore — the steady-state recovery path SetupHvmHeaderNode
// takes (after NewBlockChain) when the lightweight store sits at the genesis upstream-state-id while the persisted
// EVM tip is already Hvm0-active. It is a DISTINCT implementation from catchUpMigratedStoreToTip (which the lagged
// tests cover): restore (a) resets the node to genesis, then (b) forward-walks from the Phase-0 activation block to
// CurrentBlock() reading DISK blocks and applying each, crit-ing on any error. No test exercises this disk
// forward-walk over a real lightweight node with bodied blocks: the only restore test runs on a genesis-only chain
// (zero blocks replayed, only proving teardown ran). Corpus-free: plain (no-BtcAttr) Hvm0 blocks take the
// SetUpstreamStateId-only apply branch, so no full node / Bitcoin corpus is needed.
func TestPerformFullHvmHeaderStateRestoreWalksDiskToTip(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	// Hvm0Time=0 so genesis and every block are Hvm0-active and every (no-BtcAttr) block takes the
	// SetUpstreamStateId apply branch.
	cfg := *params.TestChainConfig
	hvm0 := uint64(0)
	cfg.Hvm0Time = &hvm0
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}

	db, blocks, _ := GenerateChainWithGenesis(gspec, ethash.NewFaker(), 8, func(i int, b *BlockGen) {})
	chain, err := NewBlockChain(db, gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)
	require.False(t, chain.hvmEnabled, "precondition: no hVM node yet, so InsertChain touches no TBC store")
	_, err = chain.InsertChain(blocks)
	require.NoError(t, err)
	require.Equal(t, uint64(8), chain.CurrentBlock().Number.Uint64())

	// Attach the light node LATE -> it sits at the genesis upstream-state-id while the EVM tip leads it (a genuine
	// lag, the exact boot state SetupHvmHeaderNode's restore branch handles).
	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header
	tbcCfg := tbc.NewDefaultConfig()
	tbcCfg.ExternalHeaderMode = true
	tbcCfg.EffectiveGenesisBlock = genesis
	tbcCfg.GenesisHeightOffset = 0
	tbcCfg.LevelDBHome = t.TempDir()
	tbcCfg.BlockheaderCacheSize, tbcCfg.BlockCacheSize = "0", "0"
	tbcCfg.AutoIndex, tbcCfg.BlockSanity, tbcCfg.MaxCachedTxs, tbcCfg.MempoolEnabled = false, true, 0, false
	tbcCfg.Network = "localnet"
	chain.initHvmHeaderNode(tbcCfg)
	t.Cleanup(func() { _ = chain.tbcHeaderNode.ExternalHeaderTearDown() })
	require.True(t, chain.hvmEnabled)
	sid0, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId, *sid0, "precondition: the freshly-attached store lags at the genesis upstream-state-id")

	// Drive the disk forward-walk (resets to genesis, replays activation..tip from disk).
	chain.performFullHvmHeaderStateRestore()

	// ORACLE: the forward-walk advanced the store's upstream-state-id exactly to the bodied disk tip (block 8).
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, chain.CurrentBlock().Hash(), common.Hash(*sid),
		"performFullHvmHeaderStateRestore must forward-walk the disk chain to CurrentBlock and set the state-id to the tip")
}

// Rollback RESIDUE fidelity for the apply-path CanonicalTip-mismatch reject arm (RemoveExternalHeaders). Existing
// reject tests assert the tip is restored and the bad headers absent; these pin the residual properties they miss:
// (1) the upstream-state-id is restored BYTE-EXACTLY to the prior value (not the rejected block's hash), and (2) a
// rejected apply leaves ZERO residue so a SUBSEQUENT honest apply lands identically to one on a never-touched store.
// TestHvmRejectRestoresStateIdExactly drives the STEADY-STATE reject arm (prev state-id is a real prior BtcAttr
// block A, not genesis) and asserts RemoveExternalHeaders restores the upstream-state-id byte-exactly to A's hash —
// NOT the rejected block B's hash. A mutant passing the rejected block's hash (stateTransitionTargetHash) instead of
// previousStateTransitionHash restores the TIP correctly yet leaves a wrong state-id that trips the next apply's
// parent-mismatch check — invisible to every tip-only reject assertion.
func TestHvmRejectRestoresStateIdExactly(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines regtest headers into a real lightweight TBC node")
	}
	const hvm0Time = uint64(1000)
	chain, genesis := newRegtestChainWithLightTBC(t, hvm0Time)
	mineHeaders := func(prev *wire.BlockHeader, n int, nonceBase uint32) ([]wire.BlockHeader, *wire.BlockHeader) {
		hs := make([]wire.BlockHeader, 0, n)
		p := prev
		for i := 0; i < n; i++ {
			h := mineRegtestChildBits(t, p, regtestPowBits, nonceBase+uint32(i))
			hs = append(hs, *h)
			p = h
		}
		return hs, p
	}

	// Activation block A (2 headers, parent pre-activation) -> steady state with upstream-state-id == A.
	aHeaders, aTip := mineHeaders(genesis, 2, 100)
	aCanon := aTip.BlockHash()
	aBtc, err := types.MakeBtcAttributesDepositedTx(&aCanon, aHeaders)
	require.NoError(t, err)
	aParent := &types.Header{Number: big.NewInt(10), Time: hvm0Time - 1}
	aHeader := &types.Header{Number: big.NewInt(11), Time: hvm0Time, ParentHash: aParent.Hash()}
	blockA := types.NewBlockWithHeader(aHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(aBtc)}})
	chain.tempHeaders[aParent.Hash().String()] = aParent
	chain.tempBlocks[aParent.Hash().String()] = types.NewBlockWithHeader(aParent)
	chain.tempHeaders[blockA.Hash().String()] = blockA.Header()
	chain.tempBlocks[blockA.Hash().String()] = blockA
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(blockA.Header(), false, true))

	_, tipAHeader, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	sidA, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, blockA.Hash().Bytes(), sidA[:], "precondition: post-A state-id is A")

	// Steady-state block B (parent A) carrying c1->c2 off the A-tip but DISHONESTLY claiming c1 (interior, not the
	// cumulative-work tip c2) -> cbh(c2) != claim(c1) -> reject via RemoveExternalHeaders.
	cHeaders, _ := mineHeaders(tipAHeader, 2, 5000)
	dishonest := cHeaders[0].BlockHash() // claim c1, not c2
	cBtc, err := types.MakeBtcAttributesDepositedTx(&dishonest, cHeaders)
	require.NoError(t, err)
	bHeader := &types.Header{Number: big.NewInt(12), Time: hvm0Time + 1, ParentHash: blockA.Hash()}
	blockB := types.NewBlockWithHeader(bHeader).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(cBtc)}})
	chain.tempHeaders[blockB.Hash().String()] = blockB.Header()
	chain.tempBlocks[blockB.Hash().String()] = blockB
	require.ErrorIs(t, chain.applyHvmHeaderConsensusUpdate(blockB.Header(), false, true), consensus.ErrInvalidHVMHeaders)

	// ORACLE: the state-id is restored byte-exactly to A, NOT left at the rejected block B's hash.
	sidPost, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, sidA[:], sidPost[:], "reject must restore the upstream-state-id to the prior value (A)")
	require.NotEqual(t, blockB.Hash().Bytes(), sidPost[:], "the state-id must NOT be left at the rejected block's own hash")
	_, tipPost, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, tipAHeader.BlockHash(), tipPost.BlockHash(), "tip restored to A")
	for _, c := range cHeaders {
		_, _, e := chain.tbcHeaderNode.BlockHeaderByHash(chain.ctx, c.BlockHash())
		require.Error(t, e, "rolled-back header must be absent")
	}
}

// TestHvmRejectLeavesZeroResidueForLaterHonestApply is a two-store differential: a clean store does an honest apply;
// a dirty store does a REJECTED apply first, then the SAME honest apply. Both must end byte-identically (tip AND
// upstream-state-id) — proving the rejected apply's RemoveExternalHeaders left zero residue (no half-written header
// that could perturb a later fork-choice, no stale state-id).
func TestHvmRejectLeavesZeroResidueForLaterHonestApply(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: seeds two >floorClearance regtest chains")
	}
	build := func() (*BlockChain, *wire.BlockHeader) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		return chain, seedRegtestAboveFloor(t, chain, genesis)
	}
	honest := func(chain *BlockChain, p *wire.BlockHeader) (a1, a2, a3 wire.BlockHeader) {
		a1 = *mineRegtestChild(t, p, 100)
		a2 = *mineRegtestChild(t, &a1, 110)
		a3 = *mineRegtestChild(t, &a2, 120)
		return
	}

	// CLEAN baseline: honest apply only.
	chainC, pC := build()
	a1, a2, a3 := honest(chainC, pC)
	require.NoError(t, applyForkBtcAttr(t, chainC, 11, a3, []wire.BlockHeader{a1, a2, a3}, true))
	_, cleanTip, err := chainC.tbcHeaderNode.BlockHeaderBest(chainC.ctx)
	require.NoError(t, err)
	cleanSid, err := chainC.tbcHeaderNode.UpstreamStateId(chainC.ctx)
	require.NoError(t, err)

	// DIRTY: a REJECTED apply (dishonest interior claim) THEN the identical honest apply.
	chainD, pD := build()
	require.Equal(t, pC.BlockHash(), pD.BlockHash(), "the deterministic seed yields the same incumbent tip on both chains")
	b1 := *mineRegtestChild(t, pD, 200)
	b2 := *mineRegtestChild(t, &b1, 210)
	require.ErrorIs(t, applyForkBtcAttr(t, chainD, 12, b1, []wire.BlockHeader{b1, b2}, true), consensus.ErrInvalidHVMHeaders,
		"dishonest interior CanonicalTip claim must reject")
	for _, b := range []wire.BlockHeader{b1, b2} { // probe: no header residue before the honest apply
		_, _, e := chainD.tbcHeaderNode.BlockHeaderByHash(chainD.ctx, b.BlockHash())
		require.Error(t, e, "rejected-branch header must be absent after rollback")
	}
	d1, d2, d3 := honest(chainD, pD)
	require.NoError(t, applyForkBtcAttr(t, chainD, 11, d3, []wire.BlockHeader{d1, d2, d3}, true))
	_, dirtyTip, err := chainD.tbcHeaderNode.BlockHeaderBest(chainD.ctx)
	require.NoError(t, err)
	dirtySid, err := chainD.tbcHeaderNode.UpstreamStateId(chainD.ctx)
	require.NoError(t, err)

	require.Equal(t, cleanTip.BlockHash(), dirtyTip.BlockHash(), "a rejected apply must leave NO tip residue for a later honest apply")
	require.Equal(t, cleanSid[:], dirtySid[:], "a rejected apply must leave NO upstream-state-id residue")
}

// Cross-path DIFFERENTIAL coverage: the sequencer BUILD path (longestEnforceableBTCHeaderPrefix +
// bc.enforceableBTCBatch, which TRUNCATES to the honest prefix) and the consensus APPLY path
// (applyHvmHeaderConsensusUpdate, which REJECTS the whole block) must AGREE on the same crafted batch against the
// SAME seeded node — the closure that justifies both paths existing. Each path is also tested in isolation on its own
// chain elsewhere; these feed ONE batch to BOTH and assert: apply rejects the full batch (no partial commit) AND
// apply accepts-and-commits exactly the build path's truncated prefix.
// TestHvmBuildPrefixIsExactlyWhatApplyCommits: build truncates a mid-batch contextually-wrong header to the honest
// prefix; the apply path rejects the full batch atomically (tip unchanged) and then accepts+commits exactly that
// prefix. A drift between the two enforcement points (floor clearance, PoW-vs-context order, acceptable-verdict set)
// would make build truncate to a length apply rejects (sequencer stall) or keep a header apply rejects.
func TestHvmBuildPrefixIsExactlyWhatApplyCommits(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	p := seedRegtestAboveFloor(t, chain, genesis)
	pHeight, _, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)

	h1 := *mineRegtestChild(t, p, 100)
	h2 := *mineRegtestChild(t, &h1, 110)
	h3 := *mineRegtestChildBits(t, &h2, 0x207ffffe, 120) // PoW-valid, contextually-wrong difficulty
	h4 := *mineRegtestChild(t, &h3, 130)

	// BUILD: the real production classifier (with its PoW arm) truncates before the bad header -> prefix [h1,h2].
	prefix, skip, err := longestEnforceableBTCHeaderPrefix([]*wire.BlockHeader{&h1, &h2, &h3, &h4}, chain.enforceableBTCBatch)
	require.NoError(t, err)
	require.False(t, skip)
	require.Len(t, prefix, 2, "build must truncate before the contextually-wrong h3")
	require.Equal(t, h2.BlockHash(), prefix[1].BlockHash(), "the build prefix ends at h2")

	// APPLY the FULL batch: atomic reject, no partial commit (tip still p).
	require.ErrorIs(t, applyForkBtcAttr(t, chain, 11, h4, []wire.BlockHeader{h1, h2, h3, h4}, true), consensus.ErrInvalidHVMHeaders)
	hReject, tip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, p.BlockHash(), tip.BlockHash(), "apply must NOT partially commit the honest prefix")
	require.Equal(t, pHeight, hReject, "an atomic reject must not advance the tip HEIGHT either")

	// APPLY the build's truncated prefix on the SAME node: accepted and committed (tip -> h2). This closes the
	// round-trip — the prefix the sequencer would package is exactly what every validator's apply path commits.
	require.NoError(t, applyForkBtcAttr(t, chain, 12, h2, []wire.BlockHeader{h1, h2}, true),
		"apply must ACCEPT exactly the build path's truncated prefix")
	h2Height, tip2, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, h2.BlockHash(), tip2.BlockHash(), "apply must commit the build prefix to its tip h2")
	require.Equal(t, pHeight+2, h2Height, "committing the 2-header prefix must advance the tip height by exactly 2")
}

// TestHvmBuildApplyAgreeOnMixedFaultBoundary: a batch with BOTH a contextual fault and a PoW fault at different
// indices. The build path converges on the FIRST fault of either kind; the apply path rejects the whole block.
// Pins that the two gates (PoW-then-context in both paths) pick the same first-bad boundary regardless of which
// fault class comes first.
func TestHvmBuildApplyAgreeOnMixedFaultBoundary(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers")
	}
	for _, tc := range []struct {
		name    string
		mkBatch func(t *testing.T, p *wire.BlockHeader) []wire.BlockHeader
	}{
		{
			// contextual fault at idx1, PoW fault at idx3 -> first fault is the contextual one -> prefix len 1.
			name: "ctx-before-pow",
			mkBatch: func(t *testing.T, p *wire.BlockHeader) []wire.BlockHeader {
				h1 := *mineRegtestChild(t, p, 100)
				h2 := *mineRegtestChildBits(t, &h1, 0x207ffffe, 110) // ctx-wrong
				h3 := *mineRegtestChild(t, &h2, 120)
				h4 := *forgePoWFailingChild(t, &h3, 1) // PoW-bad
				return []wire.BlockHeader{h1, h2, h3, h4}
			},
		},
		{
			// PoW fault at idx1, contextual fault at idx3 -> first fault is the PoW one -> prefix len 1.
			name: "pow-before-ctx",
			mkBatch: func(t *testing.T, p *wire.BlockHeader) []wire.BlockHeader {
				h1 := *mineRegtestChild(t, p, 100)
				h2 := *forgePoWFailingChild(t, &h1, 1) // PoW-bad
				h3 := *mineRegtestChild(t, &h2, 120)
				h4 := *mineRegtestChildBits(t, &h3, 0x207ffffe, 130) // ctx-wrong
				return []wire.BlockHeader{h1, h2, h3, h4}
			},
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
			p := seedRegtestAboveFloor(t, chain, genesis)
			batch := tc.mkBatch(t, p)
			ptrs := make([]*wire.BlockHeader, len(batch))
			for i := range batch {
				ptrs[i] = &batch[i]
			}

			prefix, skip, err := longestEnforceableBTCHeaderPrefix(ptrs, chain.enforceableBTCBatch)
			require.NoError(t, err)
			require.False(t, skip)
			require.Len(t, prefix, 1, "build converges on the FIRST fault of either kind (index 1)")

			require.ErrorIs(t, applyForkBtcAttr(t, chain, 11, batch[len(batch)-1], batch, true), consensus.ErrInvalidHVMHeaders,
				"apply rejects the whole mixed-fault batch")
			_, tip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
			require.NoError(t, err)
			require.Equal(t, p.BlockHash(), tip.BlockHash(), "no partial commit on a mixed-fault batch")

			// The build prefix {h1} re-applies cleanly on the same node.
			require.NoError(t, applyForkBtcAttr(t, chain, 12, batch[0], []wire.BlockHeader{batch[0]}, true))
			_, tip2, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
			require.NoError(t, err)
			require.Equal(t, batch[0].BlockHash(), tip2.BlockHash())
		})
	}
}
