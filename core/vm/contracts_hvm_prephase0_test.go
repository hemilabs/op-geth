// Copyright 2026 Hemi Labs, Inc.
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package vm

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"
	"github.com/stretchr/testify/require"
)

// These tests pin the pre-phase0 legacy window on Hemi testnet (params.HemiTestnetChainID): testnet history
// produced while hVM Phase 0 was scheduled earlier called the hVM precompiles before the (current) Hvm0Time.
// Inside the window the precompiles must exist (warm, RequiredGas charged) but return empty without ever
// querying TBC, so re-execution reproduces the canonical gas, receipts and state root.

const (
	prePhase0BlockTime = uint64(1)
	prePhase0Hvm0Time  = uint64(1_000)
	hemiMainnetChainID = uint64(43111)
)

// newPrePhase0EVM builds an EVM at prePhase0BlockTime (before Hvm0Time) on Hemi testnet (window active) or
// on Hemi mainnet (no window).
func newPrePhase0EVM(t *testing.T, window bool) (*EVM, *state.StateDB) {
	t.Helper()
	cfg := *params.MergedTestChainConfig
	hvm0 := prePhase0Hvm0Time
	cfg.Hvm0Time = &hvm0
	cfg.ChainID = new(big.Int).SetUint64(hemiMainnetChainID)
	if window {
		cfg.ChainID = big.NewInt(params.HemiTestnetChainID)
	}
	statedb, err := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
	require.NoError(t, err)
	evm := NewEVM(BlockContext{
		BlockNumber: big.NewInt(1),
		Time:        prePhase0BlockTime,
		CanTransfer: func(StateDB, common.Address, *uint256.Int) bool { return true },
		Transfer:    func(StateDB, common.Address, common.Address, *uint256.Int) {},
	}, statedb, &cfg, Config{})
	require.False(t, evm.chainRules.IsHvm0, "precondition: hVM Phase 0 must not be active")
	require.Equal(t, window, evm.chainRules.IsHvmPrecompiles, "precondition: legacy window flag")
	return evm, statedb
}

func TestConfigIsHvmPrecompiles(t *testing.T) {
	hvm0 := uint64(100)
	testnet := big.NewInt(params.HemiTestnetChainID)

	c := &params.ChainConfig{ChainID: testnet, Hvm0Time: &hvm0}
	require.True(t, c.IsHemiTestnet())
	require.True(t, c.IsHvmPrecompiles(0), "testnet: window from genesis")
	require.True(t, c.IsHvmPrecompiles(99), "testnet: window up to phase0")
	require.False(t, c.IsHvm0(99), "window is pre-phase0")
	require.True(t, c.IsHvmPrecompiles(100), "phase0 implies precompiles")

	// Testnet without a scheduled phase0: there is no "before phase0", so no window.
	require.False(t, (&params.ChainConfig{ChainID: testnet}).IsHvmPrecompiles(0))

	// Any other chain (mainnet, devnets, no chain ID): precompiles follow Hvm0Time exactly, as before.
	for _, id := range []*big.Int{new(big.Int).SetUint64(hemiMainnetChainID), big.NewInt(1337), nil} {
		m := &params.ChainConfig{ChainID: id, Hvm0Time: &hvm0}
		require.False(t, m.IsHemiTestnet())
		require.Falsef(t, m.IsHvmPrecompiles(99), "chain %v before phase0", id)
		require.Truef(t, m.IsHvmPrecompiles(100), "chain %v at phase0", id)
	}
}

// Without the window, pre-phase0 behavior is unchanged: 0x40 is not a precompile and not pre-warmed.
func TestPrePhase0NoWindowUnchanged(t *testing.T) {
	evm, _ := newPrePhase0EVM(t, false)
	_, ok := evm.precompile(common.BytesToAddress([]byte{0x40}))
	require.False(t, ok)
	for _, a := range PrecompiledAddressesHvm0 {
		require.NotContains(t, ActivePrecompiles(evm.chainRules), a)
	}
}

// Inside the window every hVM precompile dispatches and is in the warm set.
func TestPrePhase0WindowExposesHvmPrecompiles(t *testing.T) {
	evm, _ := newPrePhase0EVM(t, true)
	active := ActivePrecompiles(evm.chainRules)
	for b := byte(0x40); b <= 0x49; b++ {
		a := common.BytesToAddress([]byte{b})
		p, ok := evm.precompile(a)
		require.Truef(t, ok, "%s must dispatch inside the window", a)
		require.True(t, isHVMPrecompile(p))
		require.Contains(t, active, a)
	}
}

// Inside the window runPrecompile must never call Run (no TBC), charge exactly RequiredGas and return empty.
func TestPrePhase0WindowNoopNeverRuns(t *testing.T) {
	p := panickingHVMPrecompile{} // Run panics: proves the no-op path never reaches it
	hvmPrecompileSet[p] = struct{}{}
	defer delete(hvmPrecompileSet, p)

	evm, _ := newPrePhase0EVM(t, true)
	const gas = uint64(100_000)
	beforeNoop := hvmPrecompilePrePhase0Counter.Snapshot().Count()
	beforeInvalid := hvmPrecompileInvalidDataCounter.Snapshot().Count()

	var (
		ret []byte
		rem uint64
		err error
	)
	require.NotPanics(t, func() { ret, rem, err = evm.runPrecompile(p, []byte{0x01}, gas) })
	require.NoError(t, err)
	require.Nil(t, ret)
	require.Equal(t, gas-panickingHVMGas, rem)
	require.Equal(t, beforeNoop+1, hvmPrecompilePrePhase0Counter.Snapshot().Count())
	require.Equal(t, beforeInvalid, hvmPrecompileInvalidDataCounter.Snapshot().Count(),
		"the pre-phase0 no-op is expected history, not an invalid-data alert")

	// Insufficient gas behaves like any precompile: out of gas, everything consumed.
	_, rem, err = evm.runPrecompile(p, nil, panickingHVMGas-1)
	require.ErrorIs(t, err, ErrOutOfGas)
	require.Zero(t, rem)
}

// Regression for the sepolia/testnet3 sync failure shape: a contract STATICCALLs 0x40 before hVM Phase 0.
// Inside the window the call costs a warm access plus btcBalAddr's RequiredGas and returns empty; without it
// the call is a cold access to an empty account. The difference is what split gasUsed/state root.
func TestPrePhase0ContractCallTo0x40(t *testing.T) {
	// PUSH1 0 x4 (ret/args), PUSH1 0x40, GAS, STATICCALL, POP, STOP
	code := common.FromHex("600060006000600060405afa5000")
	sender := common.HexToAddress("0x1111111111111111111111111111111111111111")
	coinbase := common.HexToAddress("0x2222222222222222222222222222222222222222")
	contract := common.HexToAddress("0x3333333333333333333333333333333333333333")
	const gas = uint64(1_000_000)
	const opsGas = 5*3 + 2 + 2 // 5x PUSH1, GAS, POP

	run := func(window bool) uint64 {
		evm, statedb := newPrePhase0EVM(t, window)
		statedb.SetCode(contract, code, 0)
		statedb.Prepare(evm.chainRules, sender, coinbase, &contract, ActivePrecompiles(evm.chainRules), nil)
		ret, left, err := evm.Call(sender, contract, nil, gas, new(uint256.Int))
		require.NoError(t, err)
		require.Empty(t, ret)
		return gas - left
	}

	require.Equal(t, uint64(opsGas+params.ColdAccountAccessCostEIP2929), run(false),
		"no window: cold call to an empty account (behavior unchanged)")
	require.Equal(t, uint64(opsGas+params.WarmStorageReadCostEIP2929+params.BtcAddrBal), run(true),
		"window: warm hVM precompile charging RequiredGas, empty no-op")
}
