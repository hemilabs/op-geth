// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

import (
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

// A forced system tx (0x7C BtcAttr, 0x7D PoP) carries NO access list and a ZERO signature — these txs are never
// signed and their sender is the hardcoded identity. This pins the zero-contract of the inner
// accessList()/rawSignatureValues() stubs via the Transaction accessors.
func TestSystemTxZeroSignatureAndAccessList(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	btcInner, err := MakeBtcAttributesDepositedTx(&chainhash.Hash{0x01}, nil)
	require.NoError(t, err)
	for _, tx := range []*Transaction{
		NewTx(btcInner),
		NewTx(&PopPayoutTx{To: &to, Gas: 50_000, Data: []byte("pop")}),
	} {
		require.Nil(t, tx.AccessList(), "a system tx must carry no access list")
		v, r, s := tx.RawSignatureValues()
		require.Zero(t, v.Sign(), "system-tx signature V must be zero")
		require.Zero(t, r.Sign(), "system-tx signature R must be zero")
		require.Zero(t, s.Sign(), "system-tx signature S must be zero")
	}
}
