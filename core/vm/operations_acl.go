// Copyright 2020 The go-ethereum Authors
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
	"errors"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/math"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
)

func makeGasSStoreFunc(clearingRefund uint64) gasFunc {
	return func(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
		// If we fail the minimum gas availability invariant, fail (0)
		if contract.Gas <= params.SstoreSentryGasEIP2200 {
			return 0, errors.New("not enough gas for reentrancy sentry")
		}
		// Gas sentry honoured, do the actual gas calculation based on the stored value
		var (
			y, x              = stack.Back(1), stack.peek()
			slot              = common.Hash(x.Bytes32())
			current, original = evm.StateDB.GetStateAndCommittedState(contract.Address(), slot)
			cost              = uint64(0)
		)
		// Check slot presence in the access list
		if _, slotPresent := evm.StateDB.SlotInAccessList(contract.Address(), slot); !slotPresent {
			cost = params.ColdSloadCostEIP2929
			// If the caller cannot afford the cost, this change will be rolled back
			evm.StateDB.AddSlotToAccessList(contract.Address(), slot)
		}
		value := common.Hash(y.Bytes32())

		if current == value { // noop (1)
			// EIP 2200 original clause:
			//		return params.SloadGasEIP2200, nil
			return cost + params.WarmStorageReadCostEIP2929, nil // SLOAD_GAS
		}
		if original == current {
			if original == (common.Hash{}) { // create slot (2.1.1)
				return cost + params.SstoreSetGasEIP2200, nil
			}
			if value == (common.Hash{}) { // delete slot (2.1.2b)
				evm.StateDB.AddRefund(clearingRefund)
			}
			// EIP-2200 original clause:
			//		return params.SstoreResetGasEIP2200, nil // write existing slot (2.1.2)
			return cost + (params.SstoreResetGasEIP2200 - params.ColdSloadCostEIP2929), nil // write existing slot (2.1.2)
		}
		if original != (common.Hash{}) {
			if current == (common.Hash{}) { // recreate slot (2.2.1.1)
				evm.StateDB.SubRefund(clearingRefund)
			} else if value == (common.Hash{}) { // delete slot (2.2.1.2)
				evm.StateDB.AddRefund(clearingRefund)
			}
		}
		if original == value {
			if original == (common.Hash{}) { // reset to original inexistent slot (2.2.2.1)
				// EIP 2200 Original clause:
				//evm.StateDB.AddRefund(params.SstoreSetGasEIP2200 - params.SloadGasEIP2200)
				evm.StateDB.AddRefund(params.SstoreSetGasEIP2200 - params.WarmStorageReadCostEIP2929)
			} else { // reset to original existing slot (2.2.2.2)
				// EIP 2200 Original clause:
				//	evm.StateDB.AddRefund(params.SstoreResetGasEIP2200 - params.SloadGasEIP2200)
				// - SSTORE_RESET_GAS redefined as (5000 - COLD_SLOAD_COST)
				// - SLOAD_GAS redefined as WARM_STORAGE_READ_COST
				// Final: (5000 - COLD_SLOAD_COST) - WARM_STORAGE_READ_COST
				evm.StateDB.AddRefund((params.SstoreResetGasEIP2200 - params.ColdSloadCostEIP2929) - params.WarmStorageReadCostEIP2929)
			}
		}
		// EIP-2200 original clause:
		//return params.SloadGasEIP2200, nil // dirty update (2.2)
		return cost + params.WarmStorageReadCostEIP2929, nil // dirty update (2.2)
	}
}

// gasSStoreEIP8037 is the Amsterdam (EIP-8037+8038) counterpart of
// makeGasSStoreFunc: EIP-8038 replaces the legacy SstoreResetGasEIP2200-derived
// write cost with a flat StorageWriteGasEIP8038 (10,000) execution-gas
// component, charged uniformly whenever a slot's value actually changes
// (create, write, or delete); on top of that, EIP-8037 additionally charges
// GasStorageSetStateEIP8037 as state-gas (via evm.ChargeStateGas) when the
// slot is created from zero. Since both "reset to original inexistent slot"
// and "reset to original existing slot" now refund against the same
// StorageWriteGasEIP8038 execution-gas write cost, they collapse into a
// single refund magnitude below. State-gas charges are treated as
// non-refundable state-growth costs in this implementation (see
// EVM.ChargeStateGas), so a same-tx create-then-reset doesn't get back the
// state-gas portion, only the execution-gas portion it originally spilled
// (if any). This is a deliberate simplification, not a spec guarantee.
func gasSStoreEIP8037(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
	if contract.Gas <= params.SstoreSentryGasEIP2200 {
		return 0, errors.New("not enough gas for reentrancy sentry")
	}
	var (
		y, x              = stack.Back(1), stack.peek()
		slot              = common.Hash(x.Bytes32())
		current, original = evm.StateDB.GetStateAndCommittedState(contract.Address(), slot)
		cost              = uint64(0)
	)
	if _, slotPresent := evm.StateDB.SlotInAccessList(contract.Address(), slot); !slotPresent {
		cost = params.ColdSloadCostEIP2929
		evm.StateDB.AddSlotToAccessList(contract.Address(), slot)
	}
	value := common.Hash(y.Bytes32())

	if current == value { // noop (1)
		return cost + params.WarmStorageReadCostEIP2929, nil
	}
	if original == current {
		if original == (common.Hash{}) { // create slot (2.1.1)
			execSpill := evm.ChargeStateGas(params.GasStorageSetStateEIP8037)
			return cost + params.StorageWriteGasEIP8038 + execSpill, nil
		}
		if value == (common.Hash{}) { // delete slot (2.1.2b)
			evm.StateDB.AddRefund(params.SstoreClearsScheduleRefundEIP8038)
		}
		return cost + params.StorageWriteGasEIP8038, nil // write existing slot (2.1.2)
	}
	if original != (common.Hash{}) {
		if current == (common.Hash{}) { // recreate slot (2.2.1.1)
			evm.StateDB.SubRefund(params.SstoreClearsScheduleRefundEIP8038)
		} else if value == (common.Hash{}) { // delete slot (2.2.1.2)
			evm.StateDB.AddRefund(params.SstoreClearsScheduleRefundEIP8038)
		}
	}
	if original == value { // reset to original value, whether inexistent or existing (2.2.2.1/2.2.2.2)
		evm.StateDB.AddRefund(params.StorageWriteGasEIP8038 - params.WarmStorageReadCostEIP2929)
	}
	return cost + params.WarmStorageReadCostEIP2929, nil // dirty update (2.2)
}

// gasSStoreEIP8038 is the standalone-EIP-8038 counterpart of gasSStoreEIP8037,
// for chain configs that enable EIP-8038 without EIP-8037 (e.g. via
// Config.ExtraEips): same StorageWriteGasEIP8038 write-cost repricing and
// SstoreClearsScheduleRefundEIP8038 refund, but the "create slot from zero"
// case has no EIP-8037 state-gas dimension to redirect into, so it charges
// the same flat StorageWriteGasEIP8038 execution-gas cost as any other write.
func gasSStoreEIP8038(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
	if contract.Gas <= params.SstoreSentryGasEIP2200 {
		return 0, errors.New("not enough gas for reentrancy sentry")
	}
	var (
		y, x              = stack.Back(1), stack.peek()
		slot              = common.Hash(x.Bytes32())
		current, original = evm.StateDB.GetStateAndCommittedState(contract.Address(), slot)
		cost              = uint64(0)
	)
	if _, slotPresent := evm.StateDB.SlotInAccessList(contract.Address(), slot); !slotPresent {
		cost = params.ColdSloadCostEIP2929
		evm.StateDB.AddSlotToAccessList(contract.Address(), slot)
	}
	value := common.Hash(y.Bytes32())

	if current == value { // noop (1)
		return cost + params.WarmStorageReadCostEIP2929, nil
	}
	if original == current {
		if value == (common.Hash{}) && original != (common.Hash{}) { // delete slot (2.1.2b)
			evm.StateDB.AddRefund(params.SstoreClearsScheduleRefundEIP8038)
		}
		return cost + params.StorageWriteGasEIP8038, nil // create/write slot (2.1.1/2.1.2)
	}
	if original != (common.Hash{}) {
		if current == (common.Hash{}) { // recreate slot (2.2.1.1)
			evm.StateDB.SubRefund(params.SstoreClearsScheduleRefundEIP8038)
		} else if value == (common.Hash{}) { // delete slot (2.2.1.2)
			evm.StateDB.AddRefund(params.SstoreClearsScheduleRefundEIP8038)
		}
	}
	if original == value { // reset to original value, whether inexistent or existing (2.2.2.1/2.2.2.2)
		evm.StateDB.AddRefund(params.StorageWriteGasEIP8038 - params.WarmStorageReadCostEIP2929)
	}
	return cost + params.WarmStorageReadCostEIP2929, nil // dirty update (2.2)
}

// gasSLoadEIP2929 calculates dynamic gas for SLOAD according to EIP-2929
// For SLOAD, if the (address, storage_key) pair (where address is the address of the contract
// whose storage is being read) is not yet in accessed_storage_keys,
// charge 2100 gas and add the pair to accessed_storage_keys.
// If the pair is already in accessed_storage_keys, charge 100 gas.
func gasSLoadEIP2929(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
	loc := stack.peek()
	slot := common.Hash(loc.Bytes32())
	// Check slot presence in the access list
	if _, slotPresent := evm.StateDB.SlotInAccessList(contract.Address(), slot); !slotPresent {
		// If the caller cannot afford the cost, this change will be rolled back
		// If he does afford it, we can skip checking the same thing later on, during execution
		evm.StateDB.AddSlotToAccessList(contract.Address(), slot)
		return params.ColdSloadCostEIP2929, nil
	}
	return params.WarmStorageReadCostEIP2929, nil
}

// gasExtCodeCopyEIP2929 implements extcodecopy according to EIP-2929
// EIP spec:
// > If the target is not in accessed_addresses,
// > charge COLD_ACCOUNT_ACCESS_COST gas, and add the address to accessed_addresses.
// > Otherwise, charge WARM_STORAGE_READ_COST gas.
func gasExtCodeCopyEIP2929(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
	// memory expansion first (dynamic part of pre-2929 implementation)
	gas, err := gasExtCodeCopy(evm, contract, stack, mem, memorySize)
	if err != nil {
		return 0, err
	}
	addr := common.Address(stack.peek().Bytes20())
	// Check slot presence in the access list
	if !evm.StateDB.AddressInAccessList(addr) {
		evm.StateDB.AddAddressToAccessList(addr)
		var overflow bool
		// We charge (cold-warm), since 'warm' is already charged as constantGas
		if gas, overflow = math.SafeAdd(gas, params.ColdAccountAccessCostEIP2929-params.WarmStorageReadCostEIP2929); overflow {
			return 0, ErrGasUintOverflow
		}
		return gas, nil
	}
	return gas, nil
}

// gasEip2929AccountCheck checks whether the first stack item (as address) is present in the access list.
// If it is, this method returns '0', otherwise 'cold-warm' gas, presuming that the opcode using it
// is also using 'warm' as constant factor.
// This method is used by:
// - extcodehash,
// - extcodesize,
// - (ext) balance
func gasEip2929AccountCheck(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
	addr := common.Address(stack.peek().Bytes20())
	// Check slot presence in the access list
	if !evm.StateDB.AddressInAccessList(addr) {
		// If the caller cannot afford the cost, this change will be rolled back
		evm.StateDB.AddAddressToAccessList(addr)
		// The warm storage read cost is already charged as constantGas
		return params.ColdAccountAccessCostEIP2929 - params.WarmStorageReadCostEIP2929, nil
	}
	return 0, nil
}

func makeCallVariantGasCallEIP2929(oldCalculator gasFunc, addressPosition int) gasFunc {
	return func(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
		addr := common.Address(stack.Back(addressPosition).Bytes20())
		// Check slot presence in the access list
		warmAccess := evm.StateDB.AddressInAccessList(addr)
		// The WarmStorageReadCostEIP2929 (100) is already deducted in the form of a constant cost, so
		// the cost to charge for cold access, if any, is Cold - Warm
		coldCost := params.ColdAccountAccessCostEIP2929 - params.WarmStorageReadCostEIP2929
		if !warmAccess {
			evm.StateDB.AddAddressToAccessList(addr)
			// Charge the remaining difference here already, to correctly calculate available
			// gas for call
			if !contract.UseGas(coldCost, evm.Config.Tracer, tracing.GasChangeCallStorageColdAccess) {
				return 0, ErrOutOfGas
			}
		}
		// Now call the old calculator, which takes into account
		// - create new account
		// - transfer value
		// - memory expansion
		// - 63/64ths rule
		gas, err := oldCalculator(evm, contract, stack, mem, memorySize)
		if warmAccess || err != nil {
			return gas, err
		}
		// In case of a cold access, we temporarily add the cold charge back, and also
		// add it to the returned gas. By adding it to the return, it will be charged
		// outside of this function, as part of the dynamic gas, and that will make it
		// also become correctly reported to tracers.
		contract.Gas += coldCost

		var overflow bool
		if gas, overflow = math.SafeAdd(gas, coldCost); overflow {
			return 0, ErrGasUintOverflow
		}
		return gas, nil
	}
}

var (
	gasCallEIP2929         = makeCallVariantGasCallEIP2929(gasCall, 1)
	gasDelegateCallEIP2929 = makeCallVariantGasCallEIP2929(gasDelegateCall, 1)
	gasStaticCallEIP2929   = makeCallVariantGasCallEIP2929(gasStaticCall, 1)
	gasCallCodeEIP2929     = makeCallVariantGasCallEIP2929(gasCallCode, 1)
	gasSelfdestructEIP2929 = makeSelfdestructGasFn(true)
	// gasSelfdestructEIP3529 implements the changes in EIP-3529 (no refunds)
	gasSelfdestructEIP3529 = makeSelfdestructGasFn(false)

	// gasSStoreEIP2929 implements gas cost for SSTORE according to EIP-2929
	//
	// When calling SSTORE, check if the (address, storage_key) pair is in accessed_storage_keys.
	// If it is not, charge an additional COLD_SLOAD_COST gas, and add the pair to accessed_storage_keys.
	// Additionally, modify the parameters defined in EIP 2200 as follows:
	//
	// Parameter 	Old value 	New value
	// SLOAD_GAS 	800 	= WARM_STORAGE_READ_COST
	// SSTORE_RESET_GAS 	5000 	5000 - COLD_SLOAD_COST
	//
	//The other parameters defined in EIP 2200 are unchanged.
	// see gasSStoreEIP2200(...) in core/vm/gas_table.go for more info about how EIP 2200 is specified
	gasSStoreEIP2929 = makeGasSStoreFunc(params.SstoreClearsScheduleRefundEIP2200)

	// gasSStoreEIP3529 implements gas cost for SSTORE according to EIP-3529
	// Replace `SSTORE_CLEARS_SCHEDULE` with `SSTORE_RESET_GAS + ACCESS_LIST_STORAGE_KEY_COST` (4,800)
	gasSStoreEIP3529 = makeGasSStoreFunc(params.SstoreClearsScheduleRefundEIP3529)
)

// makeSelfdestructGasFn can create the selfdestruct dynamic gas function for EIP-2929 and EIP-3529
func makeSelfdestructGasFn(refundsEnabled bool) gasFunc {
	gasFunc := func(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
		var (
			gas     uint64
			address = common.Address(stack.peek().Bytes20())
		)
		if !evm.StateDB.AddressInAccessList(address) {
			// If the caller cannot afford the cost, this change will be rolled back
			evm.StateDB.AddAddressToAccessList(address)
			gas = params.ColdAccountAccessCostEIP2929
		}
		// if empty and transfers value
		if evm.StateDB.Empty(address) && evm.StateDB.GetBalance(contract.Address()).Sign() != 0 {
			gas += params.CreateBySelfdestructGas
		}
		if refundsEnabled && !evm.StateDB.HasSelfDestructed(contract.Address()) {
			evm.StateDB.AddRefund(params.SelfdestructRefundGas)
		}
		return gas, nil
	}
	return gasFunc
}

var (
	gasCallEIP7702         = makeCallVariantGasCallEIP7702(gasCall, params.ColdAccountAccessCostEIP2929)
	gasDelegateCallEIP7702 = makeCallVariantGasCallEIP7702(gasDelegateCall, params.ColdAccountAccessCostEIP2929)
	gasStaticCallEIP7702   = makeCallVariantGasCallEIP7702(gasStaticCall, params.ColdAccountAccessCostEIP2929)
	gasCallCodeEIP7702     = makeCallVariantGasCallEIP7702(gasCallCode, params.ColdAccountAccessCostEIP2929)
)

// gasEip8038AccountCheck is the EIP-8038 (Amsterdam) counterpart of
// gasEip2929AccountCheck: same account-access-list bookkeeping, but the cold
// surcharge is derived from the repriced ColdAccountAccessCostEIP8038 (3000)
// instead of ColdAccountAccessCostEIP2929 (2600). Used by BALANCE,
// EXTCODEHASH and EXTCODESIZE.
func gasEip8038AccountCheck(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
	addr := common.Address(stack.peek().Bytes20())
	if !evm.StateDB.AddressInAccessList(addr) {
		evm.StateDB.AddAddressToAccessList(addr)
		return params.ColdAccountAccessCostEIP8038 - params.WarmStorageReadCostEIP2929, nil
	}
	return 0, nil
}

// gasExtCodeCopyEIP8038 is the EIP-8038 counterpart of gasExtCodeCopyEIP2929,
// using the repriced cold-access cost.
func gasExtCodeCopyEIP8038(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
	gas, err := gasExtCodeCopy(evm, contract, stack, mem, memorySize)
	if err != nil {
		return 0, err
	}
	addr := common.Address(stack.peek().Bytes20())
	if !evm.StateDB.AddressInAccessList(addr) {
		evm.StateDB.AddAddressToAccessList(addr)
		var overflow bool
		if gas, overflow = math.SafeAdd(gas, params.ColdAccountAccessCostEIP8038-params.WarmStorageReadCostEIP2929); overflow {
			return 0, ErrGasUintOverflow
		}
		return gas, nil
	}
	return gas, nil
}

var (
	// Amsterdam inherits EIP-7702 (Prague) delegation-resolution gas accounting for
	// the CALL family, so the EIP-8038 repricing is layered on top of
	// makeCallVariantGasCallEIP7702 (parameterized below), not the plain EIP-2929
	// wrapper - using the latter would silently drop EIP-7702's delegation-resolution
	// charge starting at Amsterdam.
	gasCallEIP8038         = makeCallVariantGasCallEIP7702(gasCall, params.ColdAccountAccessCostEIP8038)
	gasDelegateCallEIP8038 = makeCallVariantGasCallEIP7702(gasDelegateCall, params.ColdAccountAccessCostEIP8038)
	gasStaticCallEIP8038   = makeCallVariantGasCallEIP7702(gasStaticCall, params.ColdAccountAccessCostEIP8038)
	// CALLCODE's notional value-transfer surcharge is repriced under EIP-8038
	// too (see gasCallCodeEIP8038Repriced) - wrapping plain gasCallCode here
	// would silently keep charging the legacy CallValueTransferGas.
	gasCallCodeEIP8038     = makeCallVariantGasCallEIP7702(gasCallCodeEIP8038Repriced, params.ColdAccountAccessCostEIP8038)
	gasSelfdestructEIP8038 = makeSelfdestructGasFnEIP8038(false) // EIP-3529 (no self-destruct refunds) already applies by Amsterdam
)

// makeSelfdestructGasFnEIP8038 is the EIP-8038 counterpart of
// makeSelfdestructGasFn: repriced cold-access cost, and - per the spec, "an
// additional charge of ACCOUNT_WRITE is added if a positive balance is sent
// to a dead account" - the new-account cost is now AccountWriteGasEIP8038
// (9,000), replacing the legacy flat CreateBySelfdestructGas (25,000).
func makeSelfdestructGasFnEIP8038(refundsEnabled bool) gasFunc {
	return func(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
		var (
			gas     uint64
			address = common.Address(stack.peek().Bytes20())
		)
		if !evm.StateDB.AddressInAccessList(address) {
			evm.StateDB.AddAddressToAccessList(address)
			gas = params.ColdAccountAccessCostEIP8038
		}
		if evm.StateDB.Empty(address) && evm.StateDB.GetBalance(contract.Address()).Sign() != 0 {
			gas += params.AccountWriteGasEIP8038
		}
		if refundsEnabled && !evm.StateDB.HasSelfDestructed(contract.Address()) {
			evm.StateDB.AddRefund(params.SelfdestructRefundGas)
		}
		return gas, nil
	}
}

// makeSelfdestructGasFnEIP8037 is the EIP-8037 counterpart of
// makeSelfdestructGasFnEIP8038: same repriced cold-access cost and
// AccountWriteGasEIP8038 charge, plus EIP-8037's state-gas GasNewAccountStateEIP8037
// charge (via evm.ChargeStateGas) for the same dead-beneficiary case - the two
// components are additive, not alternatives (ACCOUNT_WRITE is execution gas;
// GAS_NEW_ACCOUNT is the separate state-gas dimension EIP-8037 introduces).
func makeSelfdestructGasFnEIP8037(refundsEnabled bool) gasFunc {
	return func(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
		var (
			gas     uint64
			address = common.Address(stack.peek().Bytes20())
		)
		if !evm.StateDB.AddressInAccessList(address) {
			evm.StateDB.AddAddressToAccessList(address)
			gas = params.ColdAccountAccessCostEIP8038
		}
		if evm.StateDB.Empty(address) && evm.StateDB.GetBalance(contract.Address()).Sign() != 0 {
			gas += params.AccountWriteGasEIP8038
			gas += evm.ChargeStateGas(params.GasNewAccountStateEIP8037)
		}
		if refundsEnabled && !evm.StateDB.HasSelfDestructed(contract.Address()) {
			evm.StateDB.AddRefund(params.SelfdestructRefundGas)
		}
		return gas, nil
	}
}

var (
	// gasCallEIP8037Full layers the EIP-7702 delegation-resolution wrapper over
	// gasCallEIP8037 (which itself redirects the new-account cost to state-gas),
	// using the EIP-8038 cold-access cost - the Amsterdam CALL dynamic-gas
	// function combining all three EIPs' effects on CALL.
	gasCallEIP8037Full     = makeCallVariantGasCallEIP7702(gasCallEIP8037, params.ColdAccountAccessCostEIP8038)
	gasSelfdestructEIP8037 = makeSelfdestructGasFnEIP8037(false) // EIP-3529 (no self-destruct refunds) already applies by Amsterdam
)

// makeCallVariantGasCallEIP7702 builds the CALL-family dynamic-gas function
// used from Prague (EIP-7702) onward: cold-account-access accounting plus a
// charge for resolving an EIP-7702 delegation, if the target is one.
// coldAccountAccessCost is the fork's cold-access constant - callers pass
// params.ColdAccountAccessCostEIP2929 (Prague..Osaka) or the repriced
// params.ColdAccountAccessCostEIP8038 (Amsterdam+), so this single
// implementation stays correct as EIP-8038 changes that constant, instead of
// silently reverting to pre-7702 behavior the way stacking a separate
// EIP-8038-only wrapper on top of plain gasCall would.
func makeCallVariantGasCallEIP7702(oldCalculator gasFunc, coldAccountAccessCost uint64) gasFunc {
	return func(evm *EVM, contract *Contract, stack *Stack, mem *Memory, memorySize uint64) (uint64, error) {
		var (
			total uint64 // total dynamic gas used
			addr  = common.Address(stack.Back(1).Bytes20())
		)

		// Check slot presence in the access list
		if !evm.StateDB.AddressInAccessList(addr) {
			evm.StateDB.AddAddressToAccessList(addr)
			// The WarmStorageReadCostEIP2929 (100) is already deducted in the form of a constant cost, so
			// the cost to charge for cold access, if any, is Cold - Warm
			coldCost := coldAccountAccessCost - params.WarmStorageReadCostEIP2929
			// Charge the remaining difference here already, to correctly calculate available
			// gas for call
			if !contract.UseGas(coldCost, evm.Config.Tracer, tracing.GasChangeCallStorageColdAccess) {
				return 0, ErrOutOfGas
			}
			total += coldCost
		}

		// Check if code is a delegation and if so, charge for resolution.
		if target, ok := types.ParseDelegation(evm.StateDB.GetCode(addr)); ok {
			var cost uint64
			if evm.StateDB.AddressInAccessList(target) {
				cost = params.WarmStorageReadCostEIP2929
			} else {
				evm.StateDB.AddAddressToAccessList(target)
				cost = coldAccountAccessCost
			}
			if !contract.UseGas(cost, evm.Config.Tracer, tracing.GasChangeCallStorageColdAccess) {
				return 0, ErrOutOfGas
			}
			total += cost
		}

		// Now call the old calculator, which takes into account
		// - create new account
		// - transfer value
		// - memory expansion
		// - 63/64ths rule
		old, err := oldCalculator(evm, contract, stack, mem, memorySize)
		if err != nil {
			return old, err
		}

		// Temporarily add the gas charge back to the contract and return value. By
		// adding it to the return, it will be charged outside of this function, as
		// part of the dynamic gas. This will ensure it is correctly reported to
		// tracers.
		contract.Gas += total

		var overflow bool
		if total, overflow = math.SafeAdd(old, total); overflow {
			return 0, ErrGasUintOverflow
		}
		return total, nil
	}
}
