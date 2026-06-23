// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Bad-block ROUTING side-effect (the caller-side disposition of the apply error classes). walkHvmHeaderConsensusForward
// must reportBlock (rawdb.WriteBadBlock) a block that fails with ErrInvalidHVMHeaders/Format — so it is recorded as
// permanently bad and never retried — while UNWOUND recoverable predecessors and an ErrCorrupt (torn store) must NOT
// be banned (a permanent ban would defeat the self-heal). The apply-side returns are pinned elsewhere; the
// caller-side reportBlock disposition is what this covers (no other hVM test references ReadBadBlock/WriteBadBlock).

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

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
