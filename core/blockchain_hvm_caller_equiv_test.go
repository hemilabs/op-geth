// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Apply-caller EQUIVALENCE over real BTC-header commits: forward-apply (enforce=true) and
// performFullHvmHeaderStateRestore (enforce=false) are two production callers of applyHvmHeaderConsensusUpdate with
// DIFFERENT enforce args. The recovery contract is that replaying the SAME canonical disk blocks with enforcement
// OFF reproduces the EXACT lightweight BTC view forward-apply with enforcement ON produced (tip hash + height +
// upstream-state-id, byte-exact) — enforce=false must only skip the difficulty REJECT, never drop/alter a header.
// Existing coverage is two disjoint slices: enforce=false suppresses a reject for ONE direct apply (not via restore),
// and the restore disk-walk reaches tip but only over PLAIN blocks (BTC tip never moves). This composes them: a
// multi-block BtcAttr commit chain, forward then restore, byte-exact.

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

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
