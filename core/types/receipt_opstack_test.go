package types

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/params"
	"github.com/stretchr/testify/require"
)

var (
	bedrockGenesisTestConfig = func() *params.ChainConfig {
		conf := *params.AllCliqueProtocolChanges // copy the config
		conf.Clique = nil
		conf.BedrockBlock = big.NewInt(0)
		conf.Optimism = &params.OptimismConfig{EIP1559Elasticity: 50, EIP1559Denominator: 10}
		return &conf
	}()
	ecotoneTestConfig = func() *params.ChainConfig {
		conf := *bedrockGenesisTestConfig // copy the config
		time := uint64(0)
		conf.EcotoneTime = &time
		return &conf
	}()
	isthmusTestConfig = func() *params.ChainConfig {
		conf := *ecotoneTestConfig // copy the config
		time := uint64(0)
		conf.FjordTime = &time
		conf.GraniteTime = &time
		conf.HoloceneTime = &time
		conf.IsthmusTime = &time
		return &conf
	}()
	jovianTestConfig = func() *params.ChainConfig {
		conf := *isthmusTestConfig // copy the config
		time := uint64(0)
		conf.JovianTime = &time
		return &conf
	}()

	daFootprintGasScalar = uint16(400)
)

func clearComputedFieldsOnOPStackReceipts(receipts []*Receipt) []*Receipt {
	receipts = clearComputedFieldsOnReceipts(receipts)
	for _, receipt := range receipts {
		receipt.L1GasPrice = nil
		receipt.L1BlobBaseFee = nil
		receipt.L1GasUsed = nil
		receipt.L1Fee = nil
		receipt.FeeScalar = nil
		receipt.L1BaseFeeScalar = nil
		receipt.L1BlobBaseFeeScalar = nil
		receipt.OperatorFeeScalar = nil
		receipt.OperatorFeeConstant = nil
		receipt.DAFootprintGasScalar = nil
	}
	return receipts
}

func getOptimismJovianTxReceipts(l1AttributesPayload []byte, l1GasPrice, l1BlobBaseFee, l1GasUsed, l1Fee *big.Int, baseFeeScalar, blobBaseFeeScalar, operatorFeeScalar, operatorFeeConstant, daFootprintGasScalar *uint64) ([]*Transaction, []*Receipt) {
	txs, receipts := getOptimismIsthmusTxReceipts(l1AttributesPayload, l1GasPrice, l1BlobBaseFee, l1GasUsed, l1Fee, baseFeeScalar, blobBaseFeeScalar, operatorFeeScalar, operatorFeeConstant)
	receipts[1].DAFootprintGasScalar = daFootprintGasScalar
	if daFootprintGasScalar != nil {
		receipts[1].BlobGasUsed = *daFootprintGasScalar * txs[1].RollupCostData().EstimatedDASize().Uint64()
	}
	return txs, receipts
}

func TestDeriveOptimismJovianTxReceipts(t *testing.T) {
	// Jovian style l1 attributes with baseFeeScalar=2, blobBaseFeeScalar=3, baseFee=1000*1e6, blobBaseFee=10*1e6, operatorFeeScalar=1439103868, operatorFeeConstant=1256417826609331460, daFootprintGasScalar=400
	payload := common.Hex2Bytes("3db6be2b000000020000000300000000000004d200000000000004d200000000000004d2000000000000000000000000000000000000000000000000000000003b9aca00000000000000000000000000000000000000000000000000000000000098968000000000000000000000000000000000000000000000000000000000000004d200000000000000000000000000000000000000000000000000000000000004d255c6fb7c116fb15b44847d040190")
	// the parameters we use below are defined in rollup_test.go
	baseFeeScalarUint64 := baseFeeScalar.Uint64()
	blobBaseFeeScalarUint64 := blobBaseFeeScalar.Uint64()
	operatorFeeScalarUint64 := operatorFeeScalar.Uint64()
	operatorFeeConstantUint64 := operatorFeeConstant.Uint64()
	daFootprintGasScalarUint64 := uint64(daFootprintGasScalar)
	txs, receipts := getOptimismJovianTxReceipts(payload, baseFee, blobBaseFee, minimumFjordGas, fjordFee, &baseFeeScalarUint64, &blobBaseFeeScalarUint64, &operatorFeeScalarUint64, &operatorFeeConstantUint64, &daFootprintGasScalarUint64)

	// Re-derive receipts.
	baseFee := big.NewInt(1000)
	derivedReceipts := clearComputedFieldsOnOPStackReceipts(receipts)
	// Should error out if we try to process this with a pre-Jovian config
	err := Receipts(derivedReceipts).DeriveFields(bedrockGenesisTestConfig, blockHash, blockNumber.Uint64(), 0, baseFee, nil, txs)
	require.Error(t, err)

	err = Receipts(derivedReceipts).DeriveFields(jovianTestConfig, blockHash, blockNumber.Uint64(), 0, baseFee, nil, txs)
	require.NoError(t, err)
	for _, r := range receipts {
		r.Bloom = CreateBloom(r)
	}
	diffReceipts(t, receipts, derivedReceipts)
}
