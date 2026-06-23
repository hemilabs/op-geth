// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// The apply-path extract-error arm: an Hvm0-ACTIVE block carrying a 0x7C tx whose calldata is CORRUPT (fails
// BtcAttributesDepositData.UnmarshalBinary) must reject as ErrInvalidHVMBlockFormat (the block is permanently
// invalid), distinct from (a) the pre-Hvm0 format-reject (valid calldata, wrong activation time) and (b) the
// wrong-difficulty ErrInvalidHVMHeaders. The corrupt-calldata extract-error arm (applyHvmHeaderConsensusUpdate
// where ExtractBtcAttrData itself errors) was uncovered. The caller-side reportBlock disposition of this class is
// covered separately by TestHvmForwardWalkBadBlockRouting.

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

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
