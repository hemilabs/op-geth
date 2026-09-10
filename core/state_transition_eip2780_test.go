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

package core

import (
	"crypto/ecdsa"
	"errors"
	"math"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"
)

// TestIntrinsicGasEIP2780 checks the itemized Amsterdam intrinsic-gas formula
// (EIP-2780/8038) against the pre-Amsterdam flat-cost formula, for the
// representative transaction shapes the EIP is meant to reprice.
func TestIntrinsicGasEIP2780(t *testing.T) {
	tests := []struct {
		name                    string
		data                    []byte
		isContractCreation      bool
		touchesDifferentAccount bool
		chargeValueCost         bool
		wantAmsterdam           uint64
	}{
		{
			name:          "self-transfer, no value",
			wantAmsterdam: params.TxBaseCostEIP2780,
		},
		{
			// EIP-2780: a call to a different account is charged
			// COLD_ACCOUNT_ACCESS regardless of whether value moves.
			name:                    "call to different account, no value",
			touchesDifferentAccount: true,
			wantAmsterdam:           params.TxBaseCostEIP2780 + params.ColdAccountAccessCostEIP8038,
		},
		{
			name:                    "transfer with value, distinct accounts",
			touchesDifferentAccount: true,
			chargeValueCost:         true,
			wantAmsterdam:           params.TxBaseCostEIP2780 + params.ColdAccountAccessCostEIP8038 + params.TxValueCostEIP2780,
		},
		{
			// EIP-2780: "if non-zero and self-transfer, there are no charges" -
			// the caller is responsible for excluding this case from both
			// touchesDifferentAccount and chargeValueCost, verified here by
			// passing both false despite a nonzero value.
			name:                    "self-transfer with value",
			touchesDifferentAccount: false,
			chargeValueCost:         false,
			wantAmsterdam:           params.TxBaseCostEIP2780,
		},
		{
			// EIP-2780: CREATE_ACCESS (EIP-8038's execution-gas access+write
			// component) IS part of intrinsic gas for contract creation; only
			// the state-gas new-account charge is a separate runtime charge
			// (chargeAmsterdamCreateCost), not reflected here.
			name:               "contract creation",
			isContractCreation: true,
			wantAmsterdam:      params.TxBaseCostEIP2780 + params.CreateAccessGasEIP8038,
		},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got, err := IntrinsicGas(tc.data, nil, nil, tc.isContractCreation, true, true, true, true, tc.touchesDifferentAccount, tc.chargeValueCost)
			if err != nil {
				t.Fatalf("unexpected error: %v", err)
			}
			if got != tc.wantAmsterdam {
				t.Fatalf("IntrinsicGas = %d; want %d", got, tc.wantAmsterdam)
			}
		})
	}

	// Pre-Amsterdam behavior must be unchanged: flat TxGas/TxGasContractCreation,
	// regardless of value.
	got, err := IntrinsicGas(nil, nil, nil, false, true, true, true, false, true, true)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if got != params.TxGas {
		t.Fatalf("pre-Amsterdam IntrinsicGas = %d; want %d (TxGas, value should not matter)", got, params.TxGas)
	}
	got, err = IntrinsicGas(nil, nil, nil, true, true, true, true, false, false, false)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if got != params.TxGasContractCreation {
		t.Fatalf("pre-Amsterdam contract-creation IntrinsicGas = %d; want %d", got, params.TxGasContractCreation)
	}
}

// TestFloorDataGasEIP2780 checks that EIP-7623's calldata floor uses EIP-2780's
// decomposed base under Amsterdam instead of the legacy flat TxGas (21,000) -
// without this, the pre-existing EIP-7623 floor would force every Amsterdam
// transaction to pay at least 21,000 gas regardless of its real, lower
// intrinsic cost, defeating EIP-2780 entirely.
func TestFloorDataGasEIP2780(t *testing.T) {
	// No calldata, so the floor is exactly the base (tokens = 0).
	tests := []struct {
		name                    string
		isContractCreation      bool
		touchesDifferentAccount bool
		chargeValueCost         bool
		want                    uint64
	}{
		{name: "self-transfer, no value", want: params.TxBaseCostEIP2780},
		{
			name:                    "call to different account, no value",
			touchesDifferentAccount: true,
			want:                    params.TxBaseCostEIP2780 + params.ColdAccountAccessCostEIP8038,
		},
		{
			name:                    "transfer with value, distinct accounts",
			touchesDifferentAccount: true,
			chargeValueCost:         true,
			want:                    params.TxBaseCostEIP2780 + params.ColdAccountAccessCostEIP8038 + params.TxValueCostEIP2780,
		},
		{
			name:               "contract creation",
			isContractCreation: true,
			want:               params.TxBaseCostEIP2780 + params.CreateAccessGasEIP8038,
		},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got, err := FloorDataGas(nil, tc.isContractCreation, true, tc.touchesDifferentAccount, tc.chargeValueCost)
			if err != nil {
				t.Fatalf("unexpected error: %v", err)
			}
			if got != tc.want {
				t.Fatalf("FloorDataGas = %d; want %d", got, tc.want)
			}
		})
	}

	// Pre-Amsterdam behavior must be unchanged: flat TxGas base regardless of
	// the (now-irrelevant) recipient/value/creation flags.
	got, err := FloorDataGas(nil, false, false, true, true)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if got != params.TxGas {
		t.Fatalf("pre-Amsterdam FloorDataGas = %d; want %d", got, params.TxGas)
	}
}

// TestIntrinsicGasEIP7702AuthListAmsterdam checks that EIP-7702 authorization
// tuples are priced with EIP-2780/8037's ExecutionPerAuthBaseCostEIP8037
// under Amsterdam instead of the pre-Amsterdam flat CallNewAccountGas cost.
func TestIntrinsicGasEIP7702AuthListAmsterdam(t *testing.T) {
	authList := []types.SetCodeAuthorization{{}, {}, {}} // 3 tuples, contents irrelevant to the cost formula

	got, err := IntrinsicGas(nil, nil, authList, false, true, true, true, true, false, false)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want := params.TxBaseCostEIP2780 + uint64(len(authList))*params.ExecutionPerAuthBaseCostEIP8037
	if got != want {
		t.Fatalf("Amsterdam IntrinsicGas with authList = %d; want %d", got, want)
	}

	got, err = IntrinsicGas(nil, nil, authList, false, true, true, true, false, false, false)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	want = params.TxGas + uint64(len(authList))*params.CallNewAccountGas
	if got != want {
		t.Fatalf("pre-Amsterdam IntrinsicGas with authList = %d; want %d", got, want)
	}
}

// amsterdamTestChainConfig returns a chain config with Amsterdam active from genesis.
func amsterdamTestChainConfig() *params.ChainConfig {
	cfg := *params.TestChainConfig
	zero := uint64(0)
	cfg.AmsterdamTime = &zero
	return &cfg
}

// TestApplyAuthorizationAccountWriteEIP8037 checks EIP-2780/8037's
// ACCOUNT_WRITE charge on EIP-7702 authorizations: charged once per distinct
// authority per transaction, skipped for tx.sender (seeded as an exemption in
// innerExecute) and for a repeated authorization to an already-charged
// authority within the same transaction.
func TestApplyAuthorizationAccountWriteEIP8037(t *testing.T) {
	statedb, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())

	senderKey, _ := crypto.GenerateKey()
	senderAddr := crypto.PubkeyToAddress(senderKey.PublicKey)
	authorityAKey, _ := crypto.GenerateKey()
	authorityBKey, _ := crypto.GenerateKey()
	delegateTo := common.Address{0xAA}

	sign := func(key *ecdsa.PrivateKey, nonce uint64) types.SetCodeAuthorization {
		auth, err := types.SignSetCode(key, types.SetCodeAuthorization{Address: delegateTo, Nonce: nonce})
		if err != nil {
			t.Fatalf("SignSetCode: %v", err)
		}
		return auth
	}
	authSelf := sign(senderKey, 0)   // authority == tx.sender: exempt
	authA1 := sign(authorityAKey, 0) // first write to a new authority: charged
	authA2 := sign(authorityAKey, 1) // second write, same tx, same authority: exempt (dedup)
	authB := sign(authorityBKey, 0)  // first write to a different new authority: charged

	msg := &Message{From: senderAddr, To: &delegateTo, Value: big.NewInt(0), GasLimit: 10_000_000, GasPrice: big.NewInt(0)}
	random := common.Hash{}
	evm := vm.NewEVM(vm.BlockContext{BlockNumber: big.NewInt(0), Random: &random}, statedb, amsterdamTestChainConfig(), vm.Config{})
	evm.SetTxContext(NewEVMTxContext(msg))
	// Give the state-gas reservoir plenty of headroom so EIP-8037's
	// new-account state-gas charge never spills into execution gas here -
	// isolates the assertions below to just the ACCOUNT_WRITE charge.
	evm.StateGasReservoir = 10_000_000

	st := newStateTransition(evm, msg, new(GasPool).AddGas(msg.GasLimit), new(StateGasPool).AddGas(msg.GasLimit))
	st.gasRemaining = msg.GasLimit
	st.accountWriteCharged = map[common.Address]bool{msg.From: true}

	apply := func(name string, auth types.SetCodeAuthorization, wantCharged bool) {
		before := st.gasRemaining
		if err := st.applyAuthorization(&auth); err != nil {
			t.Fatalf("%s: applyAuthorization: %v", name, err)
		}
		delta := before - st.gasRemaining
		want := uint64(0)
		if wantCharged {
			want = params.AccountWriteGasEIP8038
		}
		if delta != want {
			t.Fatalf("%s: gas charged = %d; want %d", name, delta, want)
		}
	}

	apply("authority == sender", authSelf, false)
	apply("new authority A", authA1, true)
	apply("repeated authority A", authA2, false)
	apply("new authority B", authB, true)
}

// TestAmsterdamExecutionGasCapped checks EIP-8037's core invariant end to
// end: a transaction's execution gas is capped at MaxTxGas under Amsterdam
// regardless of how much larger msg.GasLimit is declared (the excess funds
// the state-gas reservoir instead, which this callee never draws on).
//
// The callee does a single MSTORE at an offset sized so the resulting memory-
// expansion cost sits strictly between gasLeft (= MaxTxGas - intrinsicGas,
// what the EVM should actually receive) and evmGas (= msg.GasLimit -
// intrinsicGas, the uncapped amount a missing cap would hand it instead). If
// the cap is enforced, this must run out of gas; if it isn't, the call
// succeeds. Deliberately not a scenario that touches the state-gas reservoir
// (no SSTORE/CREATE/etc.) - an earlier, unconditional-loop version of this
// test could pass even with the cap missing, because folding an untouched
// reservoir back into gasRemaining at the end (a separate, also-required fix)
// happened to reproduce the same final UsedGas by coincidence. Measuring
// success/failure of a fixed amount of work, rather than the final UsedGas
// total, actually isolates the cap.
func TestAmsterdamExecutionGasCapped(t *testing.T) {
	const intrinsic = params.TxBaseCostEIP2780 + params.ColdAccountAccessCostEIP8038 // to != from, no value
	gasLimit := params.MaxTxGas + 5_000_000                                          // well above MaxTxGas, to fund a nonzero reservoir
	evmGas := gasLimit - intrinsic
	gasLeft := params.MaxTxGas - intrinsic

	// Size a single MSTORE's memory expansion to land at the midpoint between
	// gasLeft and evmGas, using the real cost formula (words*MemoryGas +
	// words^2/QuadCoeffDiv) so this stays correct if those constants change.
	target := (gasLeft + evmGas) / 2
	words := uint64(math.Sqrt(float64(target) * float64(params.QuadCoeffDiv)))
	actualCost := words*params.MemoryGas + words*words/params.QuadCoeffDiv
	if actualCost <= gasLeft || actualCost >= evmGas {
		t.Fatalf("test setup: memory-expansion cost %d not strictly between gasLeft %d and evmGas %d", actualCost, gasLeft, evmGas)
	}
	offset := uint256.NewInt(words*32 - 32)
	// MSTORE pops [offset, value] with offset on top of stack, so the offset
	// must be pushed last: PUSH1 0 (value), PUSH32 offset, MSTORE, STOP.
	code := []byte{0x60, 0x00, 0x7f}
	code = append(code, offset.PaddedBytes(32)...)
	code = append(code, 0x52, 0x00) // MSTORE, STOP

	statedb, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
	sender := common.Address{1}
	callee := common.Address{2}
	statedb.CreateAccount(callee)
	statedb.SetCode(callee, code, tracing.CodeChangeUnspecified)
	statedb.Finalise(true)

	random := common.Hash{}
	vmctx := vm.BlockContext{
		CanTransfer: func(vm.StateDB, common.Address, *uint256.Int) bool { return true },
		Transfer:    func(vm.StateDB, common.Address, common.Address, *uint256.Int) {},
		BlockNumber: big.NewInt(0),
		BaseFee:     big.NewInt(0),
		Random:      &random, // post-merge, required for rules.IsAmsterdam to evaluate true
	}
	evm := vm.NewEVM(vmctx, statedb, amsterdamTestChainConfig(), vm.Config{NoBaseFee: true})

	msg := &Message{
		From:      sender,
		To:        &callee,
		Value:     big.NewInt(0),
		GasLimit:  gasLimit,
		GasPrice:  big.NewInt(0),
		GasFeeCap: big.NewInt(0),
		GasTipCap: big.NewInt(0),
	}

	result, err := ApplyMessage(evm, msg, new(GasPool).AddGas(gasLimit))
	if err != nil {
		t.Fatalf("ApplyMessage: %v", err)
	}
	if !errors.Is(result.Err, vm.ErrOutOfGas) {
		t.Fatalf("err = %v; want %v - the callee's memory expansion (%d gas) fits within the uncapped evmGas (%d) but must exceed the enforced execution-gas cap gasLeft (%d)",
			result.Err, vm.ErrOutOfGas, actualCost, evmGas, gasLeft)
	}
	// The OOG should consume exactly gasLeft of execution gas, on top of
	// intrinsic gas, landing UsedGas exactly at MaxTxGas - independent of the
	// much larger declared gasLimit.
	if result.UsedGas != params.MaxTxGas {
		t.Fatalf("UsedGas = %d; want %d (MaxTxGas)", result.UsedGas, params.MaxTxGas)
	}
}
