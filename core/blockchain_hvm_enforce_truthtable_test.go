// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Apply-path PRE-Hvm0-TIME enforce-flag truth-table cells. Enforcement is gated by enforceBTCDiff =
// enforce && hvmDiffEnforceable, and the whole BtcAttr handling is gated by IsHvm0(header.Time). The DEFER cell
// (hvmDiffEnforceable=false) is covered. The PRE-activation-TIME cells (IsHvm0(header.Time)==false) are not: every
// existing direct apply uses a Time at/after activation. These pin that a pre-activation block is handled by the
// FORMAT/no-op branches, never the difficulty/PoW gate, even with enforce=true && hvmDiffEnforceable=true.

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

// TestApplyPathPreHvm0HeaderBearingIsFormatReject: a header-bearing BtcAttr block whose timestamp is BEFORE
// activation must reject as ErrInvalidHVMBlockFormat (a permanently-invalid block), NOT ErrInvalidHVMHeaders, and
// must never reach the difficulty/PoW gate — independent of the enforce flags. A reorder running the difficulty gate
// before the format guard would mis-classify (or, if suppressed, silently accept) a pre-activation header batch.
func TestApplyPathPreHvm0HeaderBearingIsFormatReject(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	require.True(t, chain.hvmDiffEnforceable.Load(), "precondition: enforceable boot")

	h := *mineRegtestChild(t, genesis, 1) // a PoW-valid header (so only the format/difficulty path could reject)
	c := h.BlockHash()
	btc, err := types.MakeBtcAttributesDepositedTx(&c, []wire.BlockHeader{h})
	require.NoError(t, err)
	// PRE-activation timestamp.
	blk := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time - 1}).
		WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btc)}})
	require.False(t, chain.chainConfig.IsHvm0(blk.Time()), "precondition: the block is pre-activation")
	chain.tempHeaders[blk.Hash().String()] = blk.Header()
	chain.tempBlocks[blk.Hash().String()] = blk
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))

	err = chain.applyHvmHeaderConsensusUpdate(blk.Header(), false, true) // enforce=true + enforceable
	require.ErrorIs(t, err, consensus.ErrInvalidHVMBlockFormat, "a pre-activation header-bearing block is a format reject")
	require.NotErrorIs(t, err, consensus.ErrInvalidHVMHeaders, "the difficulty arm must NOT be the one that fires")
	// The difficulty/PoW gate and AddExternalHeaders were skipped: tip + state-id unchanged.
	_, tip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, genesis.BlockHash(), tip.BlockHash(), "no commit: tip stays at genesis")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId, *sid, "no state-id advance on a format reject")
}

// TestApplyPathPreHvm0HeaderlessDoesNotAdvanceStateId: a headerless (no-BtcAttr) block BEFORE activation must
// return nil WITHOUT advancing the upstream-state-id (the IsHvm0(time) guard around SetUpstreamStateId is false),
// whereas the SAME shape at/after activation MUST advance it. A mutant making that SetUpstreamStateId unconditional
// would corrupt the genesis-upstream-id invariant for a pre-activation block and survive every existing test.
func TestApplyPathPreHvm0HeaderlessDoesNotAdvanceStateId(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	chain, _ := newHvmTestChainWithLightTBC(t, btcDiffTestHvm0Time)
	require.NoError(t, chain.tbcHeaderNode.SetUpstreamStateId(chain.ctx, hVMGenesisUpstreamId))

	// PRE-activation headerless block: must be a no-op that does NOT advance the state-id.
	pre := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(11), Time: btcDiffTestHvm0Time - 1})
	require.False(t, chain.chainConfig.IsHvm0(pre.Time()))
	chain.tempHeaders[pre.Hash().String()] = pre.Header()
	chain.tempBlocks[pre.Hash().String()] = pre
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(pre.Header(), false, true), "pre-activation headerless block is a clean no-op")
	sid, err := chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, hVMGenesisUpstreamId, *sid, "a pre-activation headerless block must NOT advance the upstream-state-id")

	// Differential: the SAME headerless shape AT activation DOES advance the state-id (the IsHvm0 gate is the diff).
	active := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(12), Time: btcDiffTestHvm0Time})
	require.True(t, chain.chainConfig.IsHvm0(active.Time()))
	chain.tempHeaders[active.Hash().String()] = active.Header()
	chain.tempBlocks[active.Hash().String()] = active
	require.NoError(t, chain.applyHvmHeaderConsensusUpdate(active.Header(), false, true))
	sid, err = chain.tbcHeaderNode.UpstreamStateId(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, active.Hash().Bytes(), sid[:], "an Hvm0-active headerless block MUST advance the upstream-state-id")
}
