package core

import (
	"context"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
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
