// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Unapply of a HEADER-BEARING Hvm0 ACTIVATION block. The activation block is special: its parent is pre-hVM, so
// unapplyHvmHeaderConsensusUpdate must roll the upstream-state-id back to the genesis marker (hVMGenesisUpstreamId,
// NOT a prior BtcAttr tip) AND drive RemoveExternalHeaders to unwind the activation block's real BTC headers all the
// way to the genesis checkpoint. No existing test exercises this combination: the empty-but-present activation
// unapply takes the headerless no-op branch (no RemoveExternalHeaders); the round-trip test only unapplies a
// steady-state child back to the post-activation state, never through the activation block to genesis.

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

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
