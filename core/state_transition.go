// Copyright 2014 The go-ethereum Authors
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
	"bytes"
	"fmt"
	"math"
	"math/big"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/crypto/kzg4844"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"
)

// ExecutionResult includes all output after executing given evm
// message no matter the execution itself is successful or not.
type ExecutionResult struct {
	UsedGas    uint64 // Total used gas, not including the refunded gas
	MaxUsedGas uint64 // Maximum gas consumed during execution, excluding gas refunds.
	Err        error  // Any error encountered during the execution(listed in core/vm/errors.go)
	ReturnData []byte // Returned data from evm(function result or data supplied with revert opcode)
}

// Unwrap returns the internal evm error which allows us for further
// analysis outside.
func (result *ExecutionResult) Unwrap() error {
	return result.Err
}

// Failed returns the indicator whether the execution is successful or not
func (result *ExecutionResult) Failed() bool { return result.Err != nil }

// Return is a helper function to help caller distinguish between revert reason
// and function return. Return returns the data after execution if no error occurs.
func (result *ExecutionResult) Return() []byte {
	if result.Err != nil {
		return nil
	}
	return common.CopyBytes(result.ReturnData)
}

// Revert returns the concrete revert reason if the execution is aborted by `REVERT`
// opcode. Note the reason can be nil if no data supplied with revert opcode.
func (result *ExecutionResult) Revert() []byte {
	if result.Err != vm.ErrExecutionReverted {
		return nil
	}
	return common.CopyBytes(result.ReturnData)
}

// amsterdamBaseCost computes EIP-2780's decomposed base cost - TX_BASE_COST
// plus the applicable recipient/value primitive - shared by IntrinsicGas and
// FloorDataGas so the two bases can't silently drift apart. touchesDifferentAccount
// is EIP-2780's condition for charging COLD_ACCOUNT_ACCESS (EIP-8038's
// cold-account-access cost): true when the transaction's recipient exists and
// differs from the sender - "if self-transfer, there are no charges;
// otherwise, charge COLD_ACCOUNT_ACCESS" - regardless of whether value moves.
// chargeValueCost is EIP-2780's separate TX_VALUE_COST condition; both are
// precomputed by the caller since neither function has access to the
// sender/recipient addresses.
func amsterdamBaseCost(isContractCreation, touchesDifferentAccount, chargeValueCost bool) uint64 {
	if isContractCreation { // EIP-2780: "charge CREATE_ACCESS in execution gas"
		// for a contract-creation transaction - CREATE_ACCESS (EIP-8038's
		// execution-gas access+write component) IS intrinsic gas; only the
		// state-gas new-account charge (STATE_BYTES_PER_NEW_ACCOUNT * CPSB)
		// is a separate runtime charge applied later - see
		// stateTransition.chargeAmsterdamCreateCost, called from innerExecute.
		return params.TxBaseCostEIP2780 + params.CreateAccessGasEIP8038
	}
	base := params.TxBaseCostEIP2780
	if touchesDifferentAccount {
		base += params.ColdAccountAccessCostEIP8038
	}
	if chargeValueCost {
		base += params.TxValueCostEIP2780
	}
	return base
}

// IntrinsicGas computes the 'intrinsic gas' for a message with the given data.
// See amsterdamBaseCost for touchesDifferentAccount/chargeValueCost.
func IntrinsicGas(data []byte, accessList types.AccessList, authList []types.SetCodeAuthorization, isContractCreation, isHomestead, isEIP2028, isEIP3860, isAmsterdam bool, touchesDifferentAccount, chargeValueCost bool) (uint64, error) {
	// Set the starting gas for the raw transaction
	var gas uint64
	switch {
	case isAmsterdam: // EIP-2780
		gas = amsterdamBaseCost(isContractCreation, touchesDifferentAccount, chargeValueCost)
	case isContractCreation && isHomestead:
		gas = params.TxGasContractCreation
	default:
		gas = params.TxGas
	}
	dataLen := uint64(len(data))
	// Bump the required gas by the amount of transactional data
	if dataLen > 0 {
		// Zero and non-zero bytes are priced differently
		z := uint64(bytes.Count(data, []byte{0}))
		nz := dataLen - z

		// Make sure we don't exceed uint64 for all data combinations
		nonZeroGas := params.TxDataNonZeroGasFrontier
		if isEIP2028 {
			nonZeroGas = params.TxDataNonZeroGasEIP2028
		}
		if (math.MaxUint64-gas)/nonZeroGas < nz {
			return 0, ErrGasUintOverflow
		}
		gas += nz * nonZeroGas

		if (math.MaxUint64-gas)/params.TxDataZeroGas < z {
			return 0, ErrGasUintOverflow
		}
		gas += z * params.TxDataZeroGas

		if isContractCreation && isEIP3860 {
			lenWords := toWordSize(dataLen)
			if (math.MaxUint64-gas)/params.InitCodeWordGas < lenWords {
				return 0, ErrGasUintOverflow
			}
			gas += lenWords * params.InitCodeWordGas
		}
	}
	addressGas, storageKeyGas := params.TxAccessListAddressGas, params.TxAccessListStorageKeyGas
	if isAmsterdam { // EIP-8038 repricing
		addressGas, storageKeyGas = params.TxAccessListAddressGasEIP8038, params.TxAccessListStorageKeyGasEIP8038
	}
	if accessList != nil {
		gas += uint64(len(accessList)) * addressGas
		gas += uint64(accessList.StorageKeys()) * storageKeyGas
	}
	if authList != nil {
		// EIP-2780: "each EIP-7702 authorization is charged
		// EXECUTION_PER_AUTH_BASE_COST in execution gas" - this is intrinsic,
		// unconditional per authorization tuple. The state-gas new-account
		// component (STATE_BYTES_PER_AUTH_BASE * CPSB) is a separate,
		// existence-conditional runtime charge applied in applyAuthorization.
		if isAmsterdam {
			gas += uint64(len(authList)) * params.ExecutionPerAuthBaseCostEIP8037
		} else {
			gas += uint64(len(authList)) * params.CallNewAccountGas
		}
	}
	return gas, nil
}

// FloorDataGas computes the minimum gas required for a transaction based on
// its data tokens (EIP-7623). Under Amsterdam, EIP-2780 replaces the floor's
// flat TxGas base term with its own decomposed base - "TX_BASE_COST plus the
// applicable recipient and value primitives... per-authorization charges and
// initcode word charges are excluded from this base, ensuring the floor
// rests on the same state-independent primitives as the intrinsic gas
// validity check itself" - see amsterdamBaseCost. Without this, the
// pre-existing EIP-7623 floor would silently force every Amsterdam
// transaction to pay at least the legacy flat 21,000 gas, negating EIP-2780's
// cost reduction entirely.
func FloorDataGas(data []byte, isContractCreation, isAmsterdam, touchesDifferentAccount, chargeValueCost bool) (uint64, error) {
	base := params.TxGas
	if isAmsterdam {
		base = amsterdamBaseCost(isContractCreation, touchesDifferentAccount, chargeValueCost)
	}
	var (
		z      = uint64(bytes.Count(data, []byte{0}))
		nz     = uint64(len(data)) - z
		tokens = nz*params.TxTokenPerNonZeroByte + z
	)
	// Check for overflow
	if (math.MaxUint64-base)/params.TxCostFloorPerToken < tokens {
		return 0, ErrGasUintOverflow
	}
	// Minimum gas required for a transaction based on its data tokens (EIP-7623).
	return base + tokens*params.TxCostFloorPerToken, nil
}

// toWordSize returns the ceiled word size required for init code payment calculation.
func toWordSize(size uint64) uint64 {
	if size > math.MaxUint64-31 {
		return math.MaxUint64/32 + 1
	}

	return (size + 31) / 32
}

// A Message contains the data derived from a single transaction that is relevant to state
// processing.
type Message struct {
	To                    *common.Address
	From                  common.Address
	Nonce                 uint64
	Value                 *big.Int
	GasLimit              uint64
	GasPrice              *big.Int
	GasFeeCap             *big.Int
	GasTipCap             *big.Int
	Data                  []byte
	AccessList            types.AccessList
	BlobGasFeeCap         *big.Int
	BlobHashes            []common.Hash
	SetCodeAuthorizations []types.SetCodeAuthorization

	// When SkipNonceChecks is true, the message nonce is not checked against the
	// account nonce in state.
	//
	// This field will be set to true for operations like RPC eth_call
	// or the state prefetching.
	SkipNonceChecks bool

	// When set, the message is not treated as a transaction, and certain
	// transaction-specific checks are skipped:
	//
	// - From is not verified to be an EOA
	// - GasLimit is not checked against the protocol defined tx gaslimit
	SkipTransactionChecks bool

	IsSystemTx                 bool                 // IsSystemTx indicates the message, if also a deposit, does not emit gas usage.
	IsDepositTx                bool                 // IsDepositTx indicates the message is force-included and can persist a mint.
	Mint                       *big.Int             // Mint is the amount to mint before EVM processing, or nil if there is no minting.
	RollupCostData             types.RollupCostData // RollupCostData caches data to compute the fee we charge for data availability
	IsPopPayoutTx              bool                 // IsPopPayoutTx indicates whether the message performs a PoP payout (protocol-only)
	IsBtcAttributesDepositedTx bool                 // IsBtcAttributesDepositedTx indicates whether the message is a BTC Attr Dep tx (protocol-only)
}

// TransactionToMessage converts a transaction into a Message.
func TransactionToMessage(tx *types.Transaction, s types.Signer, baseFee *big.Int) (*Message, error) {
	msg := &Message{
		Nonce:                      tx.Nonce(),
		GasLimit:                   tx.Gas(),
		GasPrice:                   new(big.Int).Set(tx.GasPrice()),
		GasFeeCap:                  new(big.Int).Set(tx.GasFeeCap()),
		GasTipCap:                  new(big.Int).Set(tx.GasTipCap()),
		To:                         tx.To(),
		Value:                      tx.Value(),
		Data:                       tx.Data(),
		AccessList:                 tx.AccessList(),
		IsSystemTx:                 tx.IsSystemTx(),
		IsDepositTx:                tx.IsDepositTx(),
		Mint:                       tx.Mint(),
		RollupCostData:             tx.RollupCostData(),
		IsPopPayoutTx:              tx.IsPopPayoutTx(),
		IsBtcAttributesDepositedTx: tx.IsBtcAttributesDepositedTx(),

		SetCodeAuthorizations: tx.SetCodeAuthorizations(),
		SkipNonceChecks:       false,
		SkipTransactionChecks: false,
		BlobHashes:            tx.BlobHashes(),
		BlobGasFeeCap:         tx.BlobGasFeeCap(),
	}
	// If baseFee provided, set gasPrice to effectiveGasPrice.
	if baseFee != nil {
		msg.GasPrice = msg.GasPrice.Add(msg.GasTipCap, baseFee)
		if msg.GasPrice.Cmp(msg.GasFeeCap) > 0 {
			msg.GasPrice = msg.GasFeeCap
		}
	}
	var err error
	msg.From, err = types.Sender(s, tx)
	return msg, err
}

// ApplyMessage computes the new state by applying the given message
// against the old state within the environment.
//
// ApplyMessage returns the bytes returned by any EVM execution (if it took place),
// the gas used (which includes gas refunds) and an error if it failed. An error always
// indicates a core error meaning that the message would always fail for that particular
// state and would never be accepted within a block.
func ApplyMessage(evm *vm.EVM, msg *Message, gp *GasPool) (*ExecutionResult, error) {
	return ApplyMessageWithStateGas(evm, msg, gp, new(StateGasPool).AddGas(msg.GasLimit))
}

// ApplyMessageWithStateGas is like ApplyMessage, but takes an explicit
// EIP-8037 state-gas pool. Real block processing (core/state_processor.go,
// miner/worker.go) shares one pool across every transaction in the block,
// seeded from the block gas limit, matching the execution GasPool. Other
// callers (eth_call, gas estimation, tracing, single-tx execution) have no
// sibling transactions to share a budget with, so ApplyMessage gives each
// call its own fresh pool sized to that message's own gas limit, mirroring
// how those callers already size their own per-call GasPool.
func ApplyMessageWithStateGas(evm *vm.EVM, msg *Message, gp *GasPool, sgp *StateGasPool) (*ExecutionResult, error) {
	evm.SetTxContext(NewEVMTxContext(msg))
	return newStateTransition(evm, msg, gp, sgp).execute()
}

// stateTransition represents a state transition.
//
// == The State Transitioning Model
//
// A state transition is a change made when a transaction is applied to the current world
// state. The state transitioning model does all the necessary work to work out a valid new
// state root.
//
//  1. Nonce handling
//  2. Pre pay gas
//  3. Create a new state object if the recipient is nil
//  4. Value transfer
//
// == If contract creation ==
//
//	4a. Attempt to run transaction data
//	4b. If valid, use result as code for the new state object
//
// == end ==
//
//  5. Run Script section
//  6. Derive new state root
type stateTransition struct {
	gp              *GasPool
	sgp             *StateGasPool // EIP-8037 block-level state-gas pool
	initialStateGas uint64        // this tx's EIP-8037 reservoir at the moment it was sized, for computing state-gas actually used
	msg             *Message
	gasRemaining    uint64
	initialGas      uint64
	state           vm.StateDB
	evm             *vm.EVM

	// accountWriteCharged tracks, for EIP-2780/8037's ACCOUNT_WRITE charge on
	// EIP-7702 authorizations, which authority addresses have already had
	// their "first write this transaction" paid for - either by an earlier
	// authorization to the same authority, or by exemption (seeded in
	// innerExecute with tx.sender, and tx.to when the transaction is
	// value-bearing to a different account). nil outside Amsterdam.
	accountWriteCharged map[common.Address]bool
}

// newStateTransition initialises and returns a new state transition object.
func newStateTransition(evm *vm.EVM, msg *Message, gp *GasPool, sgp *StateGasPool) *stateTransition {
	return &stateTransition{
		gp:    gp,
		sgp:   sgp,
		evm:   evm,
		msg:   msg,
		state: evm.StateDB,
	}
}

// to returns the recipient of the message.
func (st *stateTransition) to() common.Address {
	if st.msg == nil || st.msg.To == nil /* contract creation */ {
		return common.Address{}
	}
	return *st.msg.To
}

func (st *stateTransition) buyGas() error {
	mgval := new(big.Int).SetUint64(st.msg.GasLimit)
	mgval.Mul(mgval, st.msg.GasPrice)
	var l1Cost *big.Int
	var operatorCost *uint256.Int
	if !st.msg.SkipNonceChecks && !st.msg.SkipTransactionChecks {
		if st.evm.Context.L1CostFunc != nil {
			l1Cost = st.evm.Context.L1CostFunc(st.msg.RollupCostData, st.evm.Context.Time)
			if l1Cost != nil {
				mgval = mgval.Add(mgval, l1Cost)
			}
		}
		if st.evm.Context.OperatorCostFunc != nil {
			operatorCost = st.evm.Context.OperatorCostFunc(st.msg.GasLimit, st.evm.Context.Time)
			mgval = mgval.Add(mgval, operatorCost.ToBig())
		}
	}
	balanceCheck := new(big.Int).Set(mgval)
	if st.msg.GasFeeCap != nil {
		balanceCheck.SetUint64(st.msg.GasLimit)
		balanceCheck = balanceCheck.Mul(balanceCheck, st.msg.GasFeeCap)
		if l1Cost != nil {
			balanceCheck.Add(balanceCheck, l1Cost)
		}
		if operatorCost != nil {
			balanceCheck.Add(balanceCheck, operatorCost.ToBig())
		}
	}
	balanceCheck.Add(balanceCheck, st.msg.Value)

	if st.evm.ChainConfig().IsCancun(st.evm.Context.BlockNumber, st.evm.Context.Time) {
		if blobGas := st.blobGasUsed(); blobGas > 0 {
			// Check that the user has enough funds to cover blobGasUsed * tx.BlobGasFeeCap
			blobBalanceCheck := new(big.Int).SetUint64(blobGas)
			blobBalanceCheck.Mul(blobBalanceCheck, st.msg.BlobGasFeeCap)
			balanceCheck.Add(balanceCheck, blobBalanceCheck)
			// Pay for blobGasUsed * actual blob fee
			blobFee := new(big.Int).SetUint64(blobGas)
			blobFee.Mul(blobFee, st.evm.Context.BlobBaseFee)
			mgval.Add(mgval, blobFee)
		}
	}
	balanceCheckU256, overflow := uint256.FromBig(balanceCheck)
	if overflow {
		return fmt.Errorf("%w: address %v required balance exceeds 256 bits", ErrInsufficientFunds, st.msg.From.Hex())
	}
	if have, want := st.state.GetBalance(st.msg.From), balanceCheckU256; have.Cmp(want) < 0 {
		return fmt.Errorf("%w: address %v have %v want %v", ErrInsufficientFunds, st.msg.From.Hex(), have, want)
	}
	if err := st.gp.SubGas(st.msg.GasLimit); err != nil {
		return err
	}
	// EIP-8037: reserve this transaction's full declared gas limit from the
	// block-level state-gas pool too, mirroring gp exactly (checked before
	// execution, per the spec: "tx.gas <= state_gas_available ... performed
	// before transaction inclusion"). The unused portion is credited back in
	// refundGas below, exactly like gp's gasRemaining refund.
	if err := st.sgp.SubGas(st.msg.GasLimit); err != nil {
		return err
	}

	if st.evm.Config.Tracer != nil && st.evm.Config.Tracer.OnGasChange != nil {
		st.evm.Config.Tracer.OnGasChange(0, st.msg.GasLimit, tracing.GasChangeTxInitialBalance)
	}
	st.gasRemaining = st.msg.GasLimit

	st.initialGas = st.msg.GasLimit
	mgvalU256, _ := uint256.FromBig(mgval)
	st.state.SubBalance(st.msg.From, mgvalU256, tracing.BalanceDecreaseGasBuy)
	return nil
}

func (st *stateTransition) preCheck() error {
	if st.msg.IsDepositTx || st.msg.IsPopPayoutTx || st.msg.IsBtcAttributesDepositedTx {
		// No fee fields to check, no nonce to check, and no need to check if EOA (L1 already verified it for us)
		// Gas is free, but no refunds!
		st.initialGas = st.msg.GasLimit
		st.gasRemaining = st.msg.GasLimit // Add gas here in order to be able to execute calls.
		// Don't touch the gas pool for system transactions
		if st.msg.IsSystemTx {
			if st.evm.ChainConfig().IsOptimismRegolith(st.evm.Context.Time) {
				return fmt.Errorf("%w: address %v", ErrSystemTxNotSupported,
					st.msg.From.Hex())
			}
			return nil
		}
		if err := st.sgp.SubGas(st.msg.GasLimit); err != nil { // mirrors gp: no refunds for deposits
			return err
		}
		return st.gp.SubGas(st.msg.GasLimit) // gas used by deposits may not be used by other txs
	}
	// Only check transactions that are not fake
	msg := st.msg
	if !msg.SkipNonceChecks {
		// Make sure this transaction's nonce is correct.
		stNonce := st.state.GetNonce(msg.From)
		if msgNonce := msg.Nonce; stNonce < msgNonce {
			return fmt.Errorf("%w: address %v, tx: %d state: %d", ErrNonceTooHigh,
				msg.From.Hex(), msgNonce, stNonce)
		} else if stNonce > msgNonce {
			return fmt.Errorf("%w: address %v, tx: %d state: %d", ErrNonceTooLow,
				msg.From.Hex(), msgNonce, stNonce)
		} else if stNonce+1 < stNonce {
			return fmt.Errorf("%w: address %v, nonce: %d", ErrNonceMax,
				msg.From.Hex(), stNonce)
		}
	}
	isOsaka := st.evm.ChainConfig().IsOsaka(st.evm.Context.BlockNumber, st.evm.Context.Time)
	isAmsterdam := st.evm.ChainConfig().IsAmsterdam(st.evm.Context.BlockNumber, st.evm.Context.Time)
	if !msg.SkipTransactionChecks {
		// Verify tx gas limit does not exceed EIP-7825 cap. EIP-8037 redefines
		// this cap to bound only the execution-gas portion of a transaction
		// (see the state-gas reservoir computation below) once Amsterdam is
		// active, so tx.gas itself may exceed MaxTxGas from Amsterdam onward -
		// the excess funds the state-gas reservoir instead of being rejected.
		if isOsaka && !isAmsterdam && msg.GasLimit > params.MaxTxGas {
			return fmt.Errorf("%w (cap: %d, tx: %d)", ErrGasLimitTooHigh, params.MaxTxGas, msg.GasLimit)
		}
		// Make sure the sender is an EOA
		code := st.state.GetCode(msg.From)
		_, delegated := types.ParseDelegation(code)
		if len(code) > 0 && !delegated {
			return fmt.Errorf("%w: address %v, len(code): %d", ErrSenderNoEOA, msg.From.Hex(), len(code))
		}
	}
	// Make sure that transaction gasFeeCap is greater than the baseFee (post london)
	if st.evm.ChainConfig().IsLondon(st.evm.Context.BlockNumber) {
		// Skip the checks if gas fields are zero and baseFee was explicitly disabled (eth_call)
		skipCheck := st.evm.Config.NoBaseFee && msg.GasFeeCap.BitLen() == 0 && msg.GasTipCap.BitLen() == 0
		if !skipCheck {
			if l := msg.GasFeeCap.BitLen(); l > 256 {
				return fmt.Errorf("%w: address %v, maxFeePerGas bit length: %d", ErrFeeCapVeryHigh,
					msg.From.Hex(), l)
			}
			if l := msg.GasTipCap.BitLen(); l > 256 {
				return fmt.Errorf("%w: address %v, maxPriorityFeePerGas bit length: %d", ErrTipVeryHigh,
					msg.From.Hex(), l)
			}
			if msg.GasFeeCap.Cmp(msg.GasTipCap) < 0 {
				return fmt.Errorf("%w: address %v, maxPriorityFeePerGas: %s, maxFeePerGas: %s", ErrTipAboveFeeCap,
					msg.From.Hex(), msg.GasTipCap, msg.GasFeeCap)
			}
			// This will panic if baseFee is nil, but basefee presence is verified
			// as part of header validation.
			if msg.GasFeeCap.Cmp(st.evm.Context.BaseFee) < 0 {
				return fmt.Errorf("%w: address %v, maxFeePerGas: %s, baseFee: %s", ErrFeeCapTooLow,
					msg.From.Hex(), msg.GasFeeCap, st.evm.Context.BaseFee)
			}
		}
	}

	if msg.BlobHashes != nil {
		// The to field of a blob tx type is mandatory, and a `BlobTx` transaction internally
		// has it as a non-nillable value, so any msg derived from blob transaction has it non-nil.
		// However, messages created through RPC (eth_call) don't have this restriction.
		if msg.To == nil {
			return ErrBlobTxCreate
		}
		if len(msg.BlobHashes) == 0 {
			return ErrMissingBlobHashes
		}
		if isOsaka && len(msg.BlobHashes) > params.BlobTxMaxBlobs {
			return ErrTooManyBlobs
		}
		for i, hash := range msg.BlobHashes {
			if !kzg4844.IsValidVersionedHash(hash[:]) {
				return fmt.Errorf("blob %d has invalid hash version", i)
			}
		}
	}
	// Check that the user is paying at least the current blob fee
	if st.evm.ChainConfig().IsCancun(st.evm.Context.BlockNumber, st.evm.Context.Time) {
		if st.blobGasUsed() > 0 {
			// Skip the checks if gas fields are zero and blobBaseFee was explicitly disabled (eth_call)
			skipCheck := st.evm.Config.NoBaseFee && msg.BlobGasFeeCap.BitLen() == 0
			if !skipCheck {
				// This will panic if blobBaseFee is nil, but blobBaseFee presence
				// is verified as part of header validation.
				if msg.BlobGasFeeCap.Cmp(st.evm.Context.BlobBaseFee) < 0 {
					return fmt.Errorf("%w: address %v blobGasFeeCap: %v, blobBaseFee: %v", ErrBlobFeeCapTooLow,
						msg.From.Hex(), msg.BlobGasFeeCap, st.evm.Context.BlobBaseFee)
				}
			}
		}
	}
	// Check that EIP-7702 authorization list signatures are well formed.
	if msg.SetCodeAuthorizations != nil {
		if msg.To == nil {
			return fmt.Errorf("%w (sender %v)", ErrSetCodeTxCreate, msg.From)
		}
		if len(msg.SetCodeAuthorizations) == 0 {
			return fmt.Errorf("%w (sender %v)", ErrEmptyAuthList, msg.From)
		}
	}
	return st.buyGas()
}

// execute will transition the state by applying the current message and
// returning the evm execution result with following fields.
//
//   - used gas: total gas used (including gas being refunded)
//   - returndata: the returned data from evm
//   - concrete execution error: various EVM errors which abort the execution, e.g.
//     ErrOutOfGas, ErrExecutionReverted
//
// However if any consensus issue encountered, return the error directly with
// nil evm execution result.
func (st *stateTransition) execute() (*ExecutionResult, error) {
	if mint := st.msg.Mint; mint != nil {
		mintU256, overflow := uint256.FromBig(mint)
		if overflow {
			return nil, fmt.Errorf("mint value exceeds uint256: %d", mintU256)
		}
		st.state.AddBalance(st.msg.From, mintU256, tracing.BalanceMint)
	}
	snap := st.state.Snapshot()

	result, err := st.innerExecute()
	// Failed deposits must still be included. Unless we cannot produce the block at all due to the gas limit.
	// On deposit failure, we rewind any state changes from after the minting, and increment the nonce.
	if err != nil && err != ErrGasLimitReached && st.msg.IsDepositTx {
		if st.evm.Config.Tracer != nil && st.evm.Config.Tracer.OnEnter != nil {
			st.evm.Config.Tracer.OnEnter(0, byte(vm.STOP), common.Address{}, common.Address{}, nil, 0, nil)
		}

		st.state.RevertToSnapshot(snap)
		// Even though we revert the state changes, always increment the nonce for the next deposit transaction
		st.state.SetNonce(st.msg.From, st.state.GetNonce(st.msg.From)+1, tracing.NonceChangeEoACall)
		// Record deposits as using all their gas (matches the gas pool)
		// System Transactions are special & are not recorded as using any gas (anywhere)
		// Regolith changes this behaviour so the actual gas used is reported.
		// In this case the tx is invalid so is recorded as using all gas.
		gasUsed := st.msg.GasLimit
		if st.msg.IsSystemTx && !st.evm.ChainConfig().IsRegolith(st.evm.Context.Time) {
			gasUsed = 0
		}
		result = &ExecutionResult{
			UsedGas:    gasUsed,
			MaxUsedGas: gasUsed,
			Err:        fmt.Errorf("failed deposit: %w", err),
			ReturnData: nil,
		}
		err = nil
	}
	return result, err
}

func (st *stateTransition) innerExecute() (*ExecutionResult, error) {
	// First check this message satisfies all consensus rules before
	// applying the message. The rules include these clauses
	//
	// 1. the nonce of the message caller is correct
	// 2. caller has enough balance to cover transaction fee(gaslimit * gasprice)
	// 3. the amount of gas required is available in the block
	// 4. the purchased gas is enough to cover intrinsic usage
	// 5. there is no overflow when calculating intrinsic gas
	// 6. caller has enough balance to cover asset transfer for **topmost** call

	// Check clauses 1-3, buy gas if everything is correct
	if err := st.preCheck(); err != nil {
		return nil, err
	}

	var (
		msg              = st.msg
		rules            = st.evm.ChainConfig().Rules(st.evm.Context.BlockNumber, st.evm.Context.Random != nil, st.evm.Context.Time)
		contractCreation = msg.To == nil
		floorDataGas     uint64
	)

	// Check clauses 4-5, subtract intrinsic gas if everything is correct
	touchesDifferentAccount := !contractCreation && *msg.To != msg.From
	chargeValueCost := touchesDifferentAccount && msg.Value != nil && msg.Value.Sign() != 0
	gas, err := IntrinsicGas(msg.Data, msg.AccessList, msg.SetCodeAuthorizations, contractCreation, rules.IsHomestead, rules.IsIstanbul, rules.IsShanghai, rules.IsAmsterdam, touchesDifferentAccount, chargeValueCost)
	if err != nil {
		return nil, err
	}
	if st.gasRemaining < gas {
		return nil, fmt.Errorf("%w: have %d, want %d", ErrIntrinsicGas, st.gasRemaining, gas)
	}
	// Gas limit suffices for the floor data cost (EIP-7623)
	if rules.IsPrague {
		floorDataGas, err = FloorDataGas(msg.Data, contractCreation, rules.IsAmsterdam, touchesDifferentAccount, chargeValueCost)
		if err != nil {
			return nil, err
		}
		if msg.GasLimit < floorDataGas {
			return nil, fmt.Errorf("%w: have %d, want %d", ErrFloorDataGas, msg.GasLimit, floorDataGas)
		}
	}
	if t := st.evm.Config.Tracer; t != nil && t.OnGasChange != nil {
		if st.msg.IsDepositTx {
			t.OnGasChange(st.gasRemaining, 0, tracing.GasChangeTxIntrinsicGas)
		} else {
			t.OnGasChange(st.gasRemaining, st.gasRemaining-gas, tracing.GasChangeTxIntrinsicGas)
		}
	}
	st.gasRemaining -= gas

	if rules.IsAmsterdam {
		// EIP-8037's reservoir model: execution_gas_budget = min(TX_MAX_GAS_LIMIT,
		// msg.GasLimit) - intrinsicGas; gas_left = min(execution_gas_budget, evm_gas);
		// state_gas_reservoir = evm_gas - gas_left. preCheck relaxes EIP-7825's
		// msg.GasLimit <= MaxTxGas cap under Amsterdam (that cap now bounds only
		// the execution portion, per EIP-8037), so a transaction can declare a
		// gas limit above MaxTxGas specifically to fund a nonzero reservoir here.
		evmGas := st.gasRemaining
		executionGasBudget := msg.GasLimit
		if params.MaxTxGas < executionGasBudget {
			executionGasBudget = params.MaxTxGas
		}
		executionGasBudget -= gas
		gasLeft := evmGas
		if executionGasBudget < gasLeft {
			gasLeft = executionGasBudget
		}
		st.evm.StateGasReservoir = evmGas - gasLeft
		st.initialStateGas = st.evm.StateGasReservoir
		// Actually cap the gas handed to the EVM at gasLeft - without this,
		// Create/Call below would run with the full, uncapped evmGas (the
		// reservoir computation above would size StateGasReservoir correctly
		// but never actually constrain execution), silently defeating
		// EIP-7825/8037's whole purpose of bounding a transaction's
		// execution-gas footprint.
		st.gasRemaining = gasLeft
	}

	if rules.IsEIP4762 {
		st.evm.AccessEvents.AddTxOrigin(msg.From)

		if targetAddr := msg.To; targetAddr != nil {
			st.evm.AccessEvents.AddTxDestination(*targetAddr, msg.Value.Sign() != 0, !st.state.Exist(*targetAddr))
		}
	}

	// Check clause 6
	value, overflow := uint256.FromBig(msg.Value)
	if overflow {
		return nil, fmt.Errorf("%w: address %v", ErrInsufficientFundsForTransfer, msg.From.Hex())
	}
	if !value.IsZero() && !st.evm.Context.CanTransfer(st.state, msg.From, value) {
		return nil, fmt.Errorf("%w: address %v", ErrInsufficientFundsForTransfer, msg.From.Hex())
	}

	// Check whether the init code size has been exceeded.
	if maxInitCodeSize := params.MaxInitCodeSizeFor(rules.IsAmsterdam); rules.IsShanghai && contractCreation && len(msg.Data) > maxInitCodeSize {
		return nil, fmt.Errorf("%w: code size %v limit %v", ErrMaxInitCodeSizeExceeded, len(msg.Data), maxInitCodeSize)
	}

	// Execute the preparatory steps for state transition which includes:
	// - prepare accessList(post-berlin)
	// - reset transient storage(eip 1153)
	st.state.Prepare(rules, msg.From, st.evm.Context.Coinbase, msg.To, vm.ActivePrecompiles(rules), msg.AccessList)

	var (
		ret   []byte
		vmerr error // vm errors do not effect consensus and are therefore not assigned to err
	)
	if contractCreation {
		if rules.IsAmsterdam && !st.chargeAmsterdamCreateCost() {
			vmerr = vm.ErrOutOfGas
		} else {
			ret, _, st.gasRemaining, vmerr = st.evm.Create(msg.From, msg.Data, st.gasRemaining, value)
		}
	} else {
		// Increment the nonce for the next transaction.
		st.state.SetNonce(msg.From, st.state.GetNonce(msg.From)+1, tracing.NonceChangeEoACall)

		// Apply EIP-7702 authorizations.
		if msg.SetCodeAuthorizations != nil {
			if rules.IsAmsterdam {
				// EIP-2780/8037: seed ACCOUNT_WRITE exemptions - tx.sender's
				// first write is covered by TX_BASE_COST, and tx.to's (if the
				// transaction is value-bearing to a different account) by
				// TX_VALUE_COST. See applyAuthorization.
				st.accountWriteCharged = map[common.Address]bool{msg.From: true}
				if chargeValueCost {
					st.accountWriteCharged[*msg.To] = true
				}
			}
			for _, auth := range msg.SetCodeAuthorizations {
				// Note errors are ignored, we simply skip invalid authorizations here.
				st.applyAuthorization(&auth)
			}
		}

		// Perform convenience warming of sender's delegation target. Although the
		// sender is already warmed in Prepare(..), it's possible a delegation to
		// the account was deployed during this transaction. To handle correctly,
		// simply wait until the final state of delegations is determined before
		// performing the resolution and warming.
		if addr, ok := types.ParseDelegation(st.state.GetCode(*msg.To)); ok {
			st.state.AddAddressToAccessList(addr)
		}

		// Execute the transaction's call.
		ret, st.gasRemaining, vmerr = st.evm.Call(msg.From, st.to(), msg.Data, st.gasRemaining, value)
	}

	// OP-Stack: pre-Regolith: if deposit, skip refunds, skip tipping coinbase
	// Regolith changes this behaviour to report the actual gasUsed instead of always reporting all gas used.
	if (st.msg.IsDepositTx || st.msg.IsPopPayoutTx || st.msg.IsBtcAttributesDepositedTx) && !rules.IsOptimismRegolith {
		// Record deposits as using all their gas (matches the gas pool)
		// System Transactions and PoP Payout transactions are special & are not recorded as using any gas (anywhere)
		gasUsed := st.msg.GasLimit
		if st.msg.IsSystemTx || st.msg.IsPopPayoutTx || st.msg.IsBtcAttributesDepositedTx {
			gasUsed = 0
		}
		return &ExecutionResult{
			UsedGas:    gasUsed,
			MaxUsedGas: gasUsed,
			Err:        vmerr,
			ReturnData: ret,
		}, nil
	}

	// Record the gas used excluding gas refunds. This value represents the actual
	// gas allowance required to complete execution.
	peakGasUsed := st.gasUsed()

	// Compute refund counter, capped to a refund quotient.
	st.gasRemaining += st.calcRefund()
	if rules.IsPrague {
		// After EIP-7623: Data-heavy transactions pay the floor gas.
		if st.gasUsed() < floorDataGas {
			prev := st.gasRemaining
			st.gasRemaining = st.initialGas - floorDataGas
			if t := st.evm.Config.Tracer; t != nil && t.OnGasChange != nil {
				t.OnGasChange(prev, st.gasRemaining, tracing.GasChangeTxDataFloor)
			}
		}
		if peakGasUsed < floorDataGas {
			peakGasUsed = floorDataGas
		}
	}
	st.returnGas()

	// OP-Stack: Note for deposit tx there is no ETH refunded for unused gas, but that's taken care of by the fact that gasPrice
	// is always 0 for deposit tx. So calling refundGas will ensure the gasUsed accounting is correct without actually
	// changing the sender's balance.
	if (st.msg.IsDepositTx || st.msg.IsPopPayoutTx || st.msg.IsBtcAttributesDepositedTx) && rules.IsOptimismRegolith {
		// Skip coinbase payments for deposit, PoP payout, and BTC Attr Dep tx in Regolith
		return &ExecutionResult{
			UsedGas:    st.gasUsed(),
			MaxUsedGas: peakGasUsed,
			Err:        vmerr,
			ReturnData: ret,
		}, nil
	}

	effectiveTip := msg.GasPrice
	if rules.IsLondon {
		effectiveTip = new(big.Int).Sub(msg.GasPrice, st.evm.Context.BaseFee)
	}
	effectiveTipU256, _ := uint256.FromBig(effectiveTip)

	if st.evm.Config.NoBaseFee && msg.GasFeeCap.Sign() == 0 && msg.GasTipCap.Sign() == 0 {
		// Skip fee payment when NoBaseFee is set and the fee fields
		// are 0. This avoids a negative effectiveTip being applied to
		// the coinbase when simulating calls.
	} else {
		fee := new(uint256.Int).SetUint64(st.gasUsed())
		fee.Mul(fee, effectiveTipU256)
		st.state.AddBalance(st.evm.Context.Coinbase, fee, tracing.BalanceIncreaseRewardTransactionFee)

		// add the coinbase to the witness iff the fee is greater than 0
		if rules.IsEIP4762 && fee.Sign() != 0 {
			st.evm.AccessEvents.AddAccount(st.evm.Context.Coinbase, true, math.MaxUint64)
		}

		// Check that we are post bedrock to enable op-geth to be able to create pseudo pre-bedrock blocks (these are pre-bedrock, but don't follow l2 geth rules)
		// Note optimismConfig will not be nil if rules.IsOptimismBedrock is true
		//
		// PoP payout (0x7D) and BTC Attributes Deposited (0x7C) are excluded alongside deposits: they pay
		// no base/L1/operator fee. The Regolith-partitioned deposit-class early-returns above already
		// return for them, so this guard is a no-op today, but it keeps the L1CostFunc(RollupCostData)
		// charge from applying if those early-returns are later refactored.
		if optimismConfig := st.evm.ChainConfig().Optimism; optimismConfig != nil && rules.IsOptimismBedrock && !st.msg.IsDepositTx && !st.msg.IsPopPayoutTx && !st.msg.IsBtcAttributesDepositedTx {
			gasCost := new(big.Int).Mul(new(big.Int).SetUint64(st.gasUsed()), st.evm.Context.BaseFee)
			amtU256, overflow := uint256.FromBig(gasCost)
			if overflow {
				return nil, fmt.Errorf("optimism gas cost overflows U256: %d", gasCost)
			}
			st.state.AddBalance(params.OptimismBaseFeeRecipient, amtU256, tracing.BalanceIncreaseRewardTransactionFee)
			if l1Cost := st.evm.Context.L1CostFunc(st.msg.RollupCostData, st.evm.Context.Time); l1Cost != nil {
				amtU256, overflow = uint256.FromBig(l1Cost)
				if overflow {
					return nil, fmt.Errorf("optimism l1 cost overflows U256: %d", l1Cost)
				}
				st.state.AddBalance(params.OptimismL1FeeRecipient, amtU256, tracing.BalanceIncreaseRewardTransactionFee)
			}
			if rules.IsOptimismIsthmus {
				// Operator Fee refunds are only applied if Isthmus is active and the transaction is *not* a deposit.
				st.refundIsthmusOperatorCost()

				operatorFeeCost := st.evm.Context.OperatorCostFunc(st.gasUsed(), st.evm.Context.Time)
				st.state.AddBalance(params.OptimismOperatorFeeRecipient, operatorFeeCost, tracing.BalanceIncreaseRewardTransactionFee)
			}
		}
	}

	return &ExecutionResult{
		UsedGas:    st.gasUsed(),
		MaxUsedGas: peakGasUsed,
		Err:        vmerr,
		ReturnData: ret,
	}, nil
}

// validateAuthorization validates an EIP-7702 authorization against the state.
func (st *stateTransition) validateAuthorization(auth *types.SetCodeAuthorization) (authority common.Address, err error) {
	// Verify chain ID is null or equal to current chain ID.
	if !auth.ChainID.IsZero() && auth.ChainID.CmpBig(st.evm.ChainConfig().ChainID) != 0 {
		return authority, ErrAuthorizationWrongChainID
	}
	// Limit nonce to 2^64-1 per EIP-2681.
	if auth.Nonce+1 < auth.Nonce {
		return authority, ErrAuthorizationNonceOverflow
	}
	// Validate signature values and recover authority.
	authority, err = auth.Authority()
	if err != nil {
		return authority, fmt.Errorf("%w: %v", ErrAuthorizationInvalidSignature, err)
	}
	// Check the authority account
	//  1) doesn't have code or has exisiting delegation
	//  2) matches the auth's nonce
	//
	// Note it is added to the access list even if the authorization is invalid.
	st.state.AddAddressToAccessList(authority)
	code := st.state.GetCode(authority)
	if _, ok := types.ParseDelegation(code); len(code) != 0 && !ok {
		return authority, ErrAuthorizationDestinationHasCode
	}
	if have := st.state.GetNonce(authority); have != auth.Nonce {
		return authority, ErrAuthorizationNonceMismatch
	}
	return authority, nil
}

// chargeAmsterdamCreateCost applies EIP-8037's account-creation *state-gas*
// runtime charge for a top-level contract-creation transaction: per the
// spec, "the STATE_BYTES_PER_NEW_ACCOUNT × CPSB account-creation charge is
// not part of intrinsic gas and is not reserved up front; it is applied as a
// runtime charge in the pre-execution phase" (i.e. after intrinsic gas /
// balance / nonce checks, but before the first EVM frame is entered). This
// covers only the state-gas component - CREATE_ACCESS, the execution-gas
// access+write component, IS part of intrinsic gas for a contract-creation
// transaction (see IntrinsicGas) and is not charged again here, unlike the
// CREATE/CREATE2 opcode's own gas_table function, which a top-level creation
// transaction never goes through. Draws from the state-gas reservoir first,
// spilling any remainder into execution gas like any other state-gas charge
// (see evm.ChargeStateGas). Returns false if st.gasRemaining can't cover the
// spillover, which the caller treats as an out-of-gas failure of the
// transaction.
func (st *stateTransition) chargeAmsterdamCreateCost() bool {
	execSpill := st.evm.ChargeStateGas(params.GasNewAccountStateEIP8037)
	if st.gasRemaining < execSpill {
		st.gasRemaining = 0
		return false
	}
	st.gasRemaining -= execSpill
	return true
}

// applyAuthorization applies an EIP-7702 code delegation to the state.
func (st *stateTransition) applyAuthorization(auth *types.SetCodeAuthorization) error {
	authority, err := st.validateAuthorization(auth)
	if err != nil {
		return err
	}

	if st.evm.ChainConfig().IsAmsterdam(st.evm.Context.BlockNumber, st.evm.Context.Time) {
		// EIP-2780/8037: "if this is the first write to the authority within
		// the transaction, charge ACCOUNT_WRITE in execution gas" - skipped
		// when already exempted (sender/tx.to, seeded in innerExecute) or
		// already charged by a preceding authorization to the same authority
		// this tx. Charged as a plain execution-gas deduction, clamped to
		// zero rather than erroring: like the state-gas charge below, running
		// out of gas during these post-intrinsic runtime charges does not
		// invalidate the transaction.
		if !st.accountWriteCharged[authority] {
			if st.gasRemaining < params.AccountWriteGasEIP8038 {
				st.gasRemaining = 0
			} else {
				st.gasRemaining -= params.AccountWriteGasEIP8038
			}
			st.accountWriteCharged[authority] = true
		}
		// IntrinsicGas already charged EXECUTION_PER_AUTH_BASE_COST per
		// authorization unconditionally; the state-gas new-account component
		// (GasAuthStateEIP8037) is charged here only when the authority
		// doesn't already exist, mirroring CALL/CREATE/SELFDESTRUCT's
		// conditional new-account state-gas charge - no refund needed, unlike
		// the pre-Amsterdam path below, since nothing extra was charged upfront.
		if !st.state.Exist(authority) {
			if execSpill := st.evm.ChargeStateGas(params.GasAuthStateEIP8037); execSpill > 0 {
				if st.gasRemaining < execSpill {
					st.gasRemaining = 0
				} else {
					st.gasRemaining -= execSpill
				}
			}
		}
	} else if st.state.Exist(authority) {
		// If the account already exists in state, refund the new account cost
		// charged in the intrinsic calculation.
		st.state.AddRefund(params.CallNewAccountGas - params.TxAuthTupleGas)
	}

	// Update nonce and account code.
	st.state.SetNonce(authority, auth.Nonce+1, tracing.NonceChangeAuthorization)
	if auth.Address == (common.Address{}) {
		// Delegation to zero address means clear.
		st.state.SetCode(authority, nil, tracing.CodeChangeAuthorizationClear)
		return nil
	}

	// Otherwise install delegation to auth.Address.
	st.state.SetCode(authority, types.AddressToDelegation(auth.Address), tracing.CodeChangeAuthorization)

	return nil
}

// calcRefund computes refund counter, capped to a refund quotient.
func (st *stateTransition) calcRefund() uint64 {
	var refund uint64
	if !st.evm.ChainConfig().IsLondon(st.evm.Context.BlockNumber) {
		// Before EIP-3529: refunds were capped to gasUsed / 2
		refund = st.gasUsed() / params.RefundQuotient
	} else {
		// After EIP-3529: refunds are capped to gasUsed / 5
		refund = st.gasUsed() / params.RefundQuotientEIP3529
	}
	if refund > st.state.GetRefund() {
		refund = st.state.GetRefund()
	}
	if st.evm.Config.Tracer != nil && st.evm.Config.Tracer.OnGasChange != nil && refund > 0 {
		st.evm.Config.Tracer.OnGasChange(st.gasRemaining, st.gasRemaining+refund, tracing.GasChangeTxRefunds)
	}
	return refund
}

// returnGas returns ETH for remaining gas,
// exchanged at the original rate.
func (st *stateTransition) returnGas() {
	// Also return remaining execution gas to the block gas counter so it is
	// available for the next transaction. This must use the execution-only
	// st.gasRemaining, before EIP-8037's reservoir leftover is folded into it
	// below - gp is a dedicated execution-gas ledger, kept separate from sgp.
	st.gp.AddGas(st.gasRemaining)

	// Return this transaction's unused state-gas capacity to the block-level
	// state-gas pool, mirroring gp.AddGas(gasRemaining) above exactly:
	// buyGas/preCheck reserved the full msg.GasLimit from sgp upfront (so an
	// over-committed block correctly rejects the transaction before it runs,
	// per EIP-8037's "checked before inclusion" admission rule), and only
	// stateGasUsed - the portion actually drawn from this tx's own reservoir -
	// is kept. For every non-Amsterdam transaction stateGasUsed is always 0
	// (initialStateGas and StateGasReservoir are both never set away from
	// their zero value), so this is a full round-trip refund, a no-op on sgp.
	stateGasUsed := st.initialStateGas - st.evm.StateGasReservoir
	st.sgp.AddGas(st.msg.GasLimit - stateGasUsed)

	// EIP-8037: "the unspent reservoir...returned to the sender by the normal
	// end-of-transaction settlement" - fold any leftover state-gas reservoir
	// back into gasRemaining before computing the sender's ETH refund and
	// before the caller reads gasUsed() (initialGas - gasRemaining) for the
	// receipt/UsedGas figure. Without this, unused reservoir capacity would
	// be neither refunded to the sender nor excluded from UsedGas - the
	// sender would silently lose that ETH, and the block/miner would be
	// credited as if that gas had actually been spent. A no-op pre-Amsterdam,
	// where StateGasReservoir is always 0.
	st.gasRemaining += st.evm.StateGasReservoir
	st.evm.StateGasReservoir = 0
	st.initialStateGas = 0

	remaining := uint256.NewInt(st.gasRemaining)
	remaining.Mul(remaining, uint256.MustFromBig(st.msg.GasPrice))
	st.state.AddBalance(st.msg.From, remaining, tracing.BalanceIncreaseGasReturn)

	if st.evm.Config.Tracer != nil && st.evm.Config.Tracer.OnGasChange != nil && st.gasRemaining > 0 {
		st.evm.Config.Tracer.OnGasChange(st.gasRemaining, 0, tracing.GasChangeTxLeftOverReturned)
	}
}

func (st *stateTransition) refundIsthmusOperatorCost() {
	// Return ETH to transaction sender for operator cost overcharge.
	operatorCostGasLimit := st.evm.Context.OperatorCostFunc(st.msg.GasLimit, st.evm.Context.Time)
	operatorCostGasUsed := st.evm.Context.OperatorCostFunc(st.gasUsed(), st.evm.Context.Time)

	if operatorCostGasUsed.Cmp(operatorCostGasLimit) > 0 { // Sanity check.
		panic(fmt.Sprintf("operator cost gas used (%d) > operator cost gas limit (%d)", operatorCostGasUsed, operatorCostGasLimit))
	}

	st.state.AddBalance(st.msg.From, new(uint256.Int).Sub(operatorCostGasLimit, operatorCostGasUsed), tracing.BalanceIncreaseGasReturn)
}

// gasUsed returns the amount of gas used up by the state transition.
func (st *stateTransition) gasUsed() uint64 {
	return st.initialGas - st.gasRemaining
}

// blobGasUsed returns the amount of blob gas used by the message.
func (st *stateTransition) blobGasUsed() uint64 {
	return uint64(len(st.msg.BlobHashes) * params.BlobTxBlobGasPerBlob)
}
