// Copyright 2024 The go-ethereum Authors
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

package types

// Sender() identity for the BtcAttributesDeposited (0x7C) tx type. The signer returns the hardcoded
// BtcAttributesDepositedSenderAddress unconditionally for this type — this is the consensus "from" identity for
// the force-included BtcAttr tx in essentially every hVM block (it drives msg.From / the nonce account on the
// apply path). No test asserted this derivation.

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

// TestBtcAttrSenderAddressConstantPinned pins the LITERAL value of the hardcoded BtcAttr (0x7C) consensus sender.
// Every existing test references BtcAttributesDepositedSenderAddress SYMBOLICALLY, so a silent edit of the constant
// (0x8888...->0x8887...) would propagate through them and still pass. This address is the consensus "from" identity
// for the force-included BtcAttr tx in essentially every hVM block; a wrong byte is a wire/consensus breach. Mirrors
// the TestBtcAttrTxTypeConstantPinned literal-tripwire for the 0x7C wire prefix.
func TestBtcAttrSenderAddressConstantPinned(t *testing.T) {
	const want = "0x8888888888888888888888888888888888888888"
	require.Equal(t, want, BtcAttributesDepositedSender, "the BtcAttr consensus sender string constant must not drift")
	require.Equal(t, common.HexToAddress(want), BtcAttributesDepositedSenderAddress, "the derived sender address bytes must match the literal")
}

func TestBtcAttrTxSenderIdentity(t *testing.T) {
	data, err := (&BtcAttributesDepositData{CanonicalTip: tipOf(1)}).MarshalBinary()
	require.NoError(t, err)
	signer := LatestSignerForChainID(big.NewInt(1))

	// Canonical construction: To == the sender address (as MakeBtcAttributesDepositedTx builds it).
	tx := NewTx(&BtcAttributesDepositedTx{To: &BtcAttributesDepositedSenderAddress, Gas: 1_000_000, Data: data})
	addr, err := Sender(signer, tx)
	require.NoError(t, err)
	require.Equal(t, BtcAttributesDepositedSenderAddress, addr, "the BtcAttr tx sender must be the hardcoded consensus identity")

	// To-INDEPENDENCE: with a DISTINCT inner To, Sender must still resolve to the type's hardcoded address — it
	// derives from the tx TYPE (0x7C), not the To field. Kills a mutant that returned tx.To().
	require.NotEqual(t, BtcAttributesDepositedSenderAddress, HvmStateAddress, "anti-vacuity: the distinct To must differ from the sender")
	tx2 := NewTx(&BtcAttributesDepositedTx{To: &HvmStateAddress, Gas: 1_000_000, Data: data})
	addr2, err := Sender(signer, tx2)
	require.NoError(t, err)
	require.Equal(t, BtcAttributesDepositedSenderAddress, addr2, "Sender must ignore To and use the type's hardcoded identity")

	// The top-level Sender caches the resolved address; a second call returns the same value.
	again, err := Sender(signer, tx)
	require.NoError(t, err)
	require.Equal(t, BtcAttributesDepositedSenderAddress, again)
}
