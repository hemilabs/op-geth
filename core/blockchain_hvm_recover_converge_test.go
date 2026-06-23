// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Corrupt-state self-heal CONVERGENCE + IDEMPOTENCY. recoverReapplyHvmState responds to a suspected-corrupt
// lightweight view (fired from writeHeadBlock / setHeadBeyondRoot / SetCanonical when the EVM head is multi-block).
// Its contract: from ANY corrupt view, the wipe-and-rebuild lands byte-exact on the view a never-corrupted node
// holds, and recovering twice == once. This injects real corruption over replayed blocks, forcing the wipe-and-
// rebuild path. Tests that restore from a clean/genesis view never reach that path: re-applying onto an already-
// golden store takes the idempotent duplicate arm, so they would not catch a reset that is content-dependent,
// skipped, or early-stopping.

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/stretchr/testify/require"
)

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
