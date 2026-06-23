// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

// System txs (0x7C BtcAttr, 0x7D PoP) are force-included and NEVER signed. The signer special-cases Sender() to
// return their hardcoded identity, but SignatureValues must still REFUSE them (ErrTxTypeNotSupported via the
// supportsType gate at transaction_signing.go ~298). No test pinned this rejection — a mutant adding 0x7C/0x7D to
// supportsType would let a caller "sign" a system tx and would survive the suite.

import (
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

func TestSignatureValuesRejectsSystemTxs(t *testing.T) {
	signer := LatestSignerForChainID(big.NewInt(1))
	sig := make([]byte, 65) // a well-formed-length signature; rejection happens before it is decoded

	btcInner, err := MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01}, nil)
	require.NoError(t, err)
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	popTx := NewTx(&PopPayoutTx{To: &to, Gas: 50_000, Data: []byte("pop")})

	for _, tc := range []struct {
		name string
		tx   *Transaction
	}{
		{"btcattr-0x7C", NewTx(btcInner)},
		{"pop-0x7D", popTx},
	} {
		_, _, _, err := signer.SignatureValues(tc.tx, sig)
		require.ErrorIs(t, err, ErrTxTypeNotSupported, "%s must be unsignable (SignatureValues rejects it)", tc.name)
	}
}
