// Copyright 2017 The go-ethereum Authors
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
	"bytes"
	"errors"
	"math"
	"math/big"
	"sort"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"
)

func TestMemoryGasCost(t *testing.T) {
	tests := []struct {
		size     uint64
		cost     uint64
		overflow bool
	}{
		{0x1fffffffe0, 36028809887088637, false},
		{0x1fffffffe1, 0, true},
	}
	for i, tt := range tests {
		v, err := memoryGasCost(&Memory{}, tt.size)
		if (err == ErrGasUintOverflow) != tt.overflow {
			t.Errorf("test %d: overflow mismatch: have %v, want %v", i, err == ErrGasUintOverflow, tt.overflow)
		}
		if v != tt.cost {
			t.Errorf("test %d: gas cost mismatch: have %v, want %v", i, v, tt.cost)
		}
	}
}

var eip2200Tests = []struct {
	original byte
	gaspool  uint64
	input    string
	used     uint64
	refund   uint64
	failure  error
}{
	{0, math.MaxUint64, "0x60006000556000600055", 1612, 0, nil},                // 0 -> 0 -> 0
	{0, math.MaxUint64, "0x60006000556001600055", 20812, 0, nil},               // 0 -> 0 -> 1
	{0, math.MaxUint64, "0x60016000556000600055", 20812, 19200, nil},           // 0 -> 1 -> 0
	{0, math.MaxUint64, "0x60016000556002600055", 20812, 0, nil},               // 0 -> 1 -> 2
	{0, math.MaxUint64, "0x60016000556001600055", 20812, 0, nil},               // 0 -> 1 -> 1
	{1, math.MaxUint64, "0x60006000556000600055", 5812, 15000, nil},            // 1 -> 0 -> 0
	{1, math.MaxUint64, "0x60006000556001600055", 5812, 4200, nil},             // 1 -> 0 -> 1
	{1, math.MaxUint64, "0x60006000556002600055", 5812, 0, nil},                // 1 -> 0 -> 2
	{1, math.MaxUint64, "0x60026000556000600055", 5812, 15000, nil},            // 1 -> 2 -> 0
	{1, math.MaxUint64, "0x60026000556003600055", 5812, 0, nil},                // 1 -> 2 -> 3
	{1, math.MaxUint64, "0x60026000556001600055", 5812, 4200, nil},             // 1 -> 2 -> 1
	{1, math.MaxUint64, "0x60026000556002600055", 5812, 0, nil},                // 1 -> 2 -> 2
	{1, math.MaxUint64, "0x60016000556000600055", 5812, 15000, nil},            // 1 -> 1 -> 0
	{1, math.MaxUint64, "0x60016000556002600055", 5812, 0, nil},                // 1 -> 1 -> 2
	{1, math.MaxUint64, "0x60016000556001600055", 1612, 0, nil},                // 1 -> 1 -> 1
	{0, math.MaxUint64, "0x600160005560006000556001600055", 40818, 19200, nil}, // 0 -> 1 -> 0 -> 1
	{1, math.MaxUint64, "0x600060005560016000556000600055", 10818, 19200, nil}, // 1 -> 0 -> 1 -> 0
	{1, 2306, "0x6001600055", 2306, 0, ErrOutOfGas},                            // 1 -> 1 (2300 sentry + 2xPUSH)
	{1, 2307, "0x6001600055", 806, 0, nil},                                     // 1 -> 1 (2301 sentry + 2xPUSH)
}

func TestEIP2200(t *testing.T) {
	for i, tt := range eip2200Tests {
		address := common.BytesToAddress([]byte("contract"))

		statedb, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
		statedb.CreateAccount(address)
		statedb.SetCode(address, hexutil.MustDecode(tt.input), tracing.CodeChangeUnspecified)
		statedb.SetState(address, common.Hash{}, common.BytesToHash([]byte{tt.original}))
		statedb.Finalise(true) // Push the state into the "original" slot

		vmctx := BlockContext{
			CanTransfer: func(StateDB, common.Address, *uint256.Int) bool { return true },
			Transfer:    func(StateDB, common.Address, common.Address, *uint256.Int) {},
		}
		evm := NewEVM(vmctx, statedb, params.AllEthashProtocolChanges, Config{ExtraEips: []int{2200}})

		_, gas, err := evm.Call(common.Address{}, address, nil, tt.gaspool, new(uint256.Int))
		if !errors.Is(err, tt.failure) {
			t.Errorf("test %d: failure mismatch: have %v, want %v", i, err, tt.failure)
		}
		if used := tt.gaspool - gas; used != tt.used {
			t.Errorf("test %d: gas used mismatch: have %v, want %v", i, used, tt.used)
		}
		if refund := evm.StateDB.GetRefund(); refund != tt.refund {
			t.Errorf("test %d: gas refund mismatch: have %v, want %v", i, refund, tt.refund)
		}
	}
}

// TestEIP8038AccountCheck checks the repriced cold-account-access surcharge
// (2600->3000, i.e. cold-warm = 2900 vs 2500) used by BALANCE/EXTCODEHASH/
// EXTCODESIZE under EIP-8038.
func TestEIP8038AccountCheck(t *testing.T) {
	statedb, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
	addr := common.Address{1}
	contract := NewContract(common.Address{}, common.Address{2}, new(uint256.Int), 0, nil)
	stack := newstack()
	stack.push(new(uint256.Int).SetBytes(addr.Bytes()))
	evm := NewEVM(BlockContext{}, statedb, params.TestChainConfig, Config{})

	got, err := gasEip8038AccountCheck(evm, contract, stack, nil, 0)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want := params.ColdAccountAccessCostEIP8038 - params.WarmStorageReadCostEIP2929
	if got != want {
		t.Fatalf("cold cost = %d; want %d", got, want)
	}
	if got != 2900 {
		t.Fatalf("cold cost = %d; want 2900 (EIP-8038's 3000 - 100)", got)
	}

	// Now warm: should be free.
	stack2 := newstack()
	stack2.push(new(uint256.Int).SetBytes(addr.Bytes()))
	got, err = gasEip8038AccountCheck(evm, contract, stack2, nil, 0)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if got != 0 {
		t.Fatalf("warm cost = %d; want 0", got)
	}
}

// TestEIP8038SStoreRefund checks the repriced storage-clear refund
// (4800->11616) used by SSTORE under EIP-8038.
func TestEIP8038SStoreRefund(t *testing.T) {
	address := common.BytesToAddress([]byte("contract"))
	statedb, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
	statedb.CreateAccount(address)
	// SSTORE(0, 0): clear an existing non-zero slot to zero.
	statedb.SetCode(address, hexutil.MustDecode("0x60006000556000600055"), tracing.CodeChangeUnspecified)
	statedb.SetState(address, common.Hash{}, common.BytesToHash([]byte{1}))
	statedb.Finalise(true)

	vmctx := BlockContext{
		CanTransfer: func(StateDB, common.Address, *uint256.Int) bool { return true },
		Transfer:    func(StateDB, common.Address, common.Address, *uint256.Int) {},
	}
	evm := NewEVM(vmctx, statedb, params.TestChainConfig, Config{ExtraEips: []int{8038}})
	_, _, err := evm.Call(common.Address{}, address, nil, 100000, new(uint256.Int))
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if refund := evm.StateDB.GetRefund(); refund != params.SstoreClearsScheduleRefundEIP8038 {
		t.Fatalf("refund = %d; want %d", refund, params.SstoreClearsScheduleRefundEIP8038)
	}
}

// TestEIP8038SStoreWriteCost checks that SSTORE charges the repriced
// StorageWriteGasEIP8038 (10,000, up from the legacy ~2,900 write component)
// for both writing an existing slot (gasSStoreEIP8038) and creating a new one
// (gasSStoreEIP8037, which additionally spills the EIP-8037 state-gas
// account-creation charge into execution gas since no reservoir is set up in
// this raw-gas-function test).
func TestEIP8038SStoreWriteCost(t *testing.T) {
	statedb, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
	address := common.Address{1}
	statedb.CreateAccount(address)
	statedb.SetState(address, common.Hash{}, common.BytesToHash([]byte{1}))
	statedb.Finalise(true)

	contract := NewContract(common.Address{}, address, new(uint256.Int), 100000, nil)
	stack := newstack()
	stack.push(uint256.NewInt(2)) // value
	stack.push(uint256.NewInt(0)) // slot
	evm := NewEVM(BlockContext{}, statedb, params.TestChainConfig, Config{})

	got, err := gasSStoreEIP8038(evm, contract, stack, nil, 0)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want := params.ColdSloadCostEIP2929 + params.StorageWriteGasEIP8038
	if got != want {
		t.Fatalf("write-existing-slot cost = %d; want %d (ColdSloadCostEIP2929 + StorageWriteGasEIP8038)", got, want)
	}

	// Creating a brand new slot from zero: same StorageWriteGasEIP8038
	// execution-gas write cost, plus EIP-8037's state-gas charge (which, with
	// no reservoir configured on this bare *EVM, spills entirely into the
	// returned execution gas).
	statedb2, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
	statedb2.CreateAccount(address)
	statedb2.Finalise(true)
	contract2 := NewContract(common.Address{}, address, new(uint256.Int), 100000, nil)
	stack2 := newstack()
	stack2.push(uint256.NewInt(2))
	stack2.push(uint256.NewInt(0))
	evm2 := NewEVM(BlockContext{}, statedb2, params.TestChainConfig, Config{})

	got, err = gasSStoreEIP8037(evm2, contract2, stack2, nil, 0)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want = params.ColdSloadCostEIP2929 + params.StorageWriteGasEIP8038 + params.GasStorageSetStateEIP8037
	if got != want {
		t.Fatalf("create-slot cost = %d; want %d (ColdSloadCostEIP2929 + StorageWriteGasEIP8038 + GasStorageSetStateEIP8037)", got, want)
	}
}

// TestEIP8038SelfdestructAccountWrite checks that SELFDESTRUCT charges
// AccountWriteGasEIP8038 (9,000) - not the legacy CreateBySelfdestructGas
// (25,000) - when a positive balance is sent to a dead (empty) beneficiary,
// for both the standalone-EIP-8038 and the EIP-8037 (state-gas) variants.
func TestEIP8038SelfdestructAccountWrite(t *testing.T) {
	beneficiary := common.Address{2}
	contractAddr := common.Address{1}

	newEnv := func() (*EVM, *Contract, *Stack) {
		statedb, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
		statedb.CreateAccount(contractAddr)
		statedb.AddBalance(contractAddr, uint256.NewInt(100), tracing.BalanceChangeUnspecified)
		statedb.Finalise(true)
		contract := NewContract(common.Address{}, contractAddr, new(uint256.Int), 100000, nil)
		stack := newstack()
		stack.push(new(uint256.Int).SetBytes(beneficiary.Bytes()))
		evm := NewEVM(BlockContext{}, statedb, params.TestChainConfig, Config{})
		return evm, contract, stack
	}

	evm, contract, stack := newEnv()
	got, err := gasSelfdestructEIP8038(evm, contract, stack, nil, 0)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want := params.ColdAccountAccessCostEIP8038 + params.AccountWriteGasEIP8038
	if got != want {
		t.Fatalf("gasSelfdestructEIP8038 = %d; want %d (ColdAccountAccessCostEIP8038 + AccountWriteGasEIP8038)", got, want)
	}

	evm2, contract2, stack2 := newEnv()
	got, err = gasSelfdestructEIP8037(evm2, contract2, stack2, nil, 0)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want = params.ColdAccountAccessCostEIP8038 + params.AccountWriteGasEIP8038 + params.GasNewAccountStateEIP8037
	if got != want {
		t.Fatalf("gasSelfdestructEIP8037 = %d; want %d (ColdAccountAccessCostEIP8038 + AccountWriteGasEIP8038 + GasNewAccountStateEIP8037)", got, want)
	}
}

// TestEIP8038CallCodeValueTransferCost checks that CALLCODE's notional
// value-transfer surcharge uses the repriced CallValueTransferGasEIP8038
// (11,300) under Amsterdam, not the legacy flat CallValueTransferGas (9,000).
func TestEIP8038CallCodeValueTransferCost(t *testing.T) {
	statedb, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
	contract := NewContract(common.Address{}, common.Address{1}, new(uint256.Int), 100000, nil)
	stack := newstack()
	// Push order is bottom-to-top; Stack.Back(n) counts from the top, so the
	// last-pushed item (gas) is Back(0), then addr is Back(1), value Back(2).
	stack.push(uint256.NewInt(1))                                    // value (nonzero)
	stack.push(new(uint256.Int).SetBytes(common.Address{2}.Bytes())) // addr
	stack.push(uint256.NewInt(1))                                    // gas
	evm := NewEVM(BlockContext{}, statedb, params.TestChainConfig, Config{})

	got, err := gasCallCodeEIP8038Repriced(evm, contract, stack, nil, 0)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	// got includes the forwarded call gas (stack.Back(0) = 1) on top of the
	// value-transfer surcharge; isolate the surcharge by comparing against a
	// zero-value call, which charges no surcharge at all.
	stackNoValue := newstack()
	stackNoValue.push(uint256.NewInt(0)) // value = 0
	stackNoValue.push(new(uint256.Int).SetBytes(common.Address{2}.Bytes()))
	stackNoValue.push(uint256.NewInt(1)) // gas
	base, err := gasCallCodeEIP8038Repriced(evm, contract, stackNoValue, nil, 0)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if surcharge := got - base; surcharge != params.CallValueTransferGasEIP8038 {
		t.Fatalf("value-transfer surcharge = %d; want %d (CallValueTransferGasEIP8038)", surcharge, params.CallValueTransferGasEIP8038)
	}
}

var createGasTests = []struct {
	code       string
	eip3860    bool
	gasUsed    uint64
	minimumGas uint64
}{
	// legacy create(0, 0, 0xc000) without 3860 used
	{"0x61C00060006000f0" + "600052" + "60206000F3", false, 41237, 41237}, //nolint:all
	// legacy create(0, 0, 0xc000) _with_ 3860
	{"0x61C00060006000f0" + "600052" + "60206000F3", true, 44309, 44309},
	// create2(0, 0, 0xc001, 0) without 3860
	{"0x600061C00160006000f5" + "600052" + "60206000F3", false, 50471, 50471},
	// create2(0, 0, 0xc001, 0) (too large), with 3860
	{"0x600061C00160006000f5" + "600052" + "60206000F3", true, 32012, 100_000},
	// create2(0, 0, 0xc000, 0)
	// This case is trying to deploy code at (within) the limit
	{"0x600061C00060006000f5" + "600052" + "60206000F3", true, 53528, 53528},
	// create2(0, 0, 0xc001, 0)
	// This case is trying to deploy code exceeding the limit
	{"0x600061C00160006000f5" + "600052" + "60206000F3", true, 32024, 100000},
}

func TestCreateGas(t *testing.T) {
	for i, tt := range createGasTests {
		var gasUsed = uint64(0)
		doCheck := func(testGas int) bool {
			address := common.BytesToAddress([]byte("contract"))
			statedb, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
			statedb.CreateAccount(address)
			statedb.SetCode(address, hexutil.MustDecode(tt.code), tracing.CodeChangeUnspecified)
			statedb.Finalise(true)
			vmctx := BlockContext{
				CanTransfer: func(StateDB, common.Address, *uint256.Int) bool { return true },
				Transfer:    func(StateDB, common.Address, common.Address, *uint256.Int) {},
				BlockNumber: big.NewInt(0),
			}
			config := Config{}
			if tt.eip3860 {
				config.ExtraEips = []int{3860}
			}

			evm := NewEVM(vmctx, statedb, params.AllEthashProtocolChanges, config)
			var startGas = uint64(testGas)
			ret, gas, err := evm.Call(common.Address{}, address, nil, startGas, new(uint256.Int))
			if err != nil {
				return false
			}
			gasUsed = startGas - gas
			if len(ret) != 32 {
				t.Fatalf("test %d: expected 32 bytes returned, have %d", i, len(ret))
			}
			if bytes.Equal(ret, make([]byte, 32)) {
				// Failure
				return false
			}
			return true
		}
		minGas := sort.Search(100_000, doCheck)
		if uint64(minGas) != tt.minimumGas {
			t.Fatalf("test %d: min gas error, want %d, have %d", i, tt.minimumGas, minGas)
		}
		// If the deployment succeeded, we also check the gas used
		if minGas < 100_000 {
			if gasUsed != tt.gasUsed {
				t.Errorf("test %d: gas used mismatch: have %v, want %v", i, gasUsed, tt.gasUsed)
			}
		}
	}
}
