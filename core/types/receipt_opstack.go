package types

import (
	"fmt"

	"github.com/ethereum/go-ethereum/params"
)

// deriveOPStackFields derives the OP Stack specific fields for each receipt.
// It must only be called for blocks with at least one transaction (the L1 attributes deposit).
func (rs Receipts) deriveOPStackFields(config *params.ChainConfig, blockTime uint64, txs []*Transaction) error {
	// Exit early only if the block has NO user transactions at all — system txs (deposit / PoP payout / BTC
	// Attributes Deposited) derive no L1-fee fields. System txs are NOT a contiguous prefix on hVM chains: a
	// BtcAttr (0x7C) can appear AFTER user txs in a block (mainnet history contains [0x7E, user, 0x7C]), so we
	// must scan for any user tx rather than test only the last element. Testing only the last tx with
	// IsZeroDAFootprintTx would wrongly early-exit on such a block and drop L1-fee fields from the preceding
	// user tx's receipt; testing only IsDepositTx (the prior behavior) would conversely fall through on an
	// all-system PoP/BtcAttr-last block and run L1-gas-param extraction that has no user tx to serve. The scan
	// is exact for both: extract+derive iff a user tx exists. Kept in lock-step with the per-receipt skip set
	// below (IsZeroDAFootprintTx).
	hasUserTx := false
	for _, tx := range txs {
		if !tx.IsZeroDAFootprintTx() {
			hasUserTx = true
			break
		}
	}
	if !hasUserTx {
		return nil
	}

	l1AttributesData := txs[0].Data()
	gasParams, err := extractL1GasParams(config, blockTime, l1AttributesData)
	if err != nil {
		return fmt.Errorf("failed to extract L1 gas params: %w", err)
	}

	var daFootprintGasScalar uint64
	isJovian := config.IsJovian(blockTime)
	if isJovian {
		scalar, err := ExtractDAFootprintGasScalar(l1AttributesData)
		if err != nil {
			return fmt.Errorf("failed to extract DA footprint gas scalar: %w", err)
		}
		daFootprintGasScalar = uint64(scalar)
	}

	for i := range rs {
		if txs[i].IsZeroDAFootprintTx() {
			continue
		}
		rs[i].L1GasPrice = gasParams.l1BaseFee
		rs[i].L1BlobBaseFee = gasParams.l1BlobBaseFee
		rcd := txs[i].RollupCostData()
		rs[i].L1Fee, rs[i].L1GasUsed = gasParams.costFunc(rcd)
		rs[i].FeeScalar = gasParams.feeScalar
		rs[i].L1BaseFeeScalar = u32ptrTou64ptr(gasParams.l1BaseFeeScalar)
		rs[i].L1BlobBaseFeeScalar = u32ptrTou64ptr(gasParams.l1BlobBaseFeeScalar)
		if gasParams.operatorFeeScalar != nil && gasParams.operatorFeeConstant != nil && (*gasParams.operatorFeeScalar != 0 || *gasParams.operatorFeeConstant != 0) {
			rs[i].OperatorFeeScalar = u32ptrTou64ptr(gasParams.operatorFeeScalar)
			rs[i].OperatorFeeConstant = gasParams.operatorFeeConstant
		}
		if isJovian {
			rs[i].DAFootprintGasScalar = &daFootprintGasScalar
			rs[i].BlobGasUsed = daFootprintGasScalar * rcd.EstimatedDASize().Uint64()
		}
	}
	return nil
}
