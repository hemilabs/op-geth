// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Headerless (empty-but-present) BtcAttr apply+unapply in STEADY STATE — the one uncovered corner of the 2x2
// {headerless / header-bearing} x {genesis-tip / non-genesis-tip}. Existing headerless tests use ACTIVATION
// geometry (tip pinned at the genesis checkpoint; unapply rolls the state-id to genesis), and the steady-state
// round-trip tests are all header-BEARING. This applies a headerless block on top of a header-bearing predecessor
// whose tip is already NON-genesis, exercising (a) the headerless-apply CanonicalTip check against a non-genesis
// tip, and (b) the headerless-unapply state-id rollback to a REAL prior block (not genesis).

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

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
