// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.

package types

import (
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

// TestPopPayoutTxTypeConstantPinned pins the LITERAL 0x7D wire prefix of the PoP-payout system tx. decodeTyped
// dispatches on it and the op-stack fork must agree on the value cross-repo. Every other test references
// PopPayoutTxType symbolically; the existing distinctness sweep (TestBtcAttrTxTypeConstantPinned) only catches a
// mutation that COLLIDES with another registered prefix. A mutation to an unused byte (e.g. 0x7B/0x7F) collides with
// nothing and silently breaks dispatch + cross-repo agreement — only a literal pin catches it. Mirrors the
// 0x7C literal tripwire.
func TestPopPayoutTxTypeConstantPinned(t *testing.T) {
	require.Equal(t, byte(0x7D), byte(PopPayoutTxType), "the PoP payout consensus tx wire prefix must be exactly 0x7D")
	require.NotEqual(t, byte(BtcAttributesDepositedTxType), byte(PopPayoutTxType), "must not collide with BtcAttr 0x7C")
	require.NotEqual(t, byte(DepositTxType), byte(PopPayoutTxType), "must not collide with Deposit 0x7E")
}

// TestPopPayoutSenderAddressConstantPinned pins the LITERAL value of the hardcoded PoP-payout (0x7D) consensus
// sender, symmetric to the BtcAttr sender pin. The signer returns this address unconditionally for 0x7D; a silent
// byte change is a consensus-identity breach that every symbolic-reference test would survive.
func TestPopPayoutSenderAddressConstantPinned(t *testing.T) {
	const want = "0x8888888888888888888888888888888888888888"
	require.Equal(t, want, PoPPayoutSender, "the PoP payout consensus sender string constant must not drift")
	require.Equal(t, common.HexToAddress(want), PoPPayoutSenderAddress, "the derived PoP sender address bytes must match the literal")
}
