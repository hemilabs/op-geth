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
