// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

// Sender() identity for the PoP payout (0x7D) tx, mirroring TestBtcAttrTxSenderIdentity for 0x7C. The signer returns
// the hardcoded PoPPayoutSenderAddress unconditionally for this type — the consensus "from" identity that drives
// msg.From / the nonce account. The existing PoP coverage only pins the CONSTANT literal, never that Sender() USES
// it; a "return tx.To()" mutant at transaction_signing.go ~275 would survive the constant pin but break consensus.

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

func TestPopPayoutTxSenderIdentity(t *testing.T) {
	signer := LatestSignerForChainID(big.NewInt(1))
	govAddr := common.HexToAddress("0x4200000000000000000000000000000000000042")

	// Canonical construction.
	tx := NewTx(&PopPayoutTx{To: &govAddr, Gas: 50_000, Data: []byte("pop")})
	addr, err := Sender(signer, tx)
	require.NoError(t, err)
	require.Equal(t, PoPPayoutSenderAddress, addr, "the PoP tx sender must be the hardcoded consensus identity")

	// To-INDEPENDENCE: a distinct inner To must NOT change the derived sender (it derives from the TYPE 0x7D).
	require.NotEqual(t, PoPPayoutSenderAddress, HvmStateAddress, "anti-vacuity: the distinct To must differ from the sender")
	tx2 := NewTx(&PopPayoutTx{To: &HvmStateAddress, Gas: 50_000, Data: []byte("pop")})
	addr2, err := Sender(signer, tx2)
	require.NoError(t, err)
	require.Equal(t, PoPPayoutSenderAddress, addr2, "Sender must ignore To and use the type's hardcoded identity (kills return-tx.To mutant)")

	// Caching: a second call returns the same value.
	again, err := Sender(signer, tx)
	require.NoError(t, err)
	require.Equal(t, PoPPayoutSenderAddress, again)
}
