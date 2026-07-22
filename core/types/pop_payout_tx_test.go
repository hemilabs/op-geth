// Copyright 2021 The go-ethereum Authors
// Copyright 2023 Bloq, Inc.
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

package types

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"math/big"
	"reflect"
	"testing"

	"github.com/davecgh/go-spew/spew"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/stretchr/testify/require"
)

func TestPopPayoutTxEncodeDecode(t *testing.T) {
	govPredeployAddr := common.HexToAddress("0x4200000000000000000000000000000000000042")
	tx := PopPayoutTx{
		To:   &govPredeployAddr,
		Gas:  150_000_000,
		Data: []byte{'d', 'a', 't', 'a'},
	}

	b := new(bytes.Buffer)
	err := tx.encode(b)
	if err != nil {
		t.Fatal(err)
	}

	t.Logf("%v", spew.Sdump(b.Bytes()))

	// Golden wire bytes: the symmetric encode->decode->DeepEqual below survives a {To,Gas,Data} field reorder
	// (RLP decodes positionally), silently changing the on-the-wire layout. Pin the exact bytes to catch that.
	const goldenRLP = "df9442000000000000000000000000000000000000428408f0d1808464617461"
	if got := hex.EncodeToString(b.Bytes()); got != goldenRLP {
		t.Fatalf("PopPayoutTx RLP wire layout changed: got %s want %s (a {To,Gas,Data} reorder survives the round-trip below)", got, goldenRLP)
	}

	tx2 := &PopPayoutTx{}
	err = tx2.decode(b.Bytes())
	if err != nil {
		t.Fatal(err)
	}

	t.Logf("%v", spew.Sdump(tx2))
	if !reflect.DeepEqual(*tx2, tx) {
		t.Fatalf("not equal got %v, wanted %v", spew.Sdump(*tx2), spew.Sdump(tx))
	}
}

// The 0x7D PopPayout TX-LEVEL accessor contract the apply/fee/mempool paths rely on, mirroring
// TestBtcAttrTxAccessorContract for 0x7C: zero gas-price/value/tip/feecap/nonce, fixed To/Gas/Data pass-through,
// defensive-copied big.Int getters, zero Cost, EffectiveGasTip behavior, and the unsupported sign operation PANICS.
func TestPopPayoutTxAccessorContract(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	inner := &PopPayoutTx{To: &to, Gas: 50_000, Data: []byte{0xc9, 0x4f}}
	tx := NewTx(inner)

	// Zero economic fields.
	require.Zero(t, tx.Value().Sign(), "Value is zero")
	require.Zero(t, tx.GasPrice().Sign(), "GasPrice is zero")
	require.Zero(t, tx.GasTipCap().Sign(), "GasTipCap is zero")
	require.Zero(t, tx.GasFeeCap().Sign(), "GasFeeCap is zero")
	require.Equal(t, uint64(0), tx.Nonce(), "Nonce is zero (set during execution)")

	// Structural fields pass through.
	require.Equal(t, inner.Gas, tx.Gas())
	require.Equal(t, inner.To, tx.To())
	require.True(t, bytes.Equal(inner.Data, tx.Data()))

	// Defensive copy: the big.Int getters must not alias internal state.
	a, b := tx.GasPrice(), tx.GasPrice()
	a.SetInt64(99)
	require.Zero(t, b.Sign(), "GasPrice must return a fresh copy each call (no alias leak)")

	// Cost is zero (zero value + zero gas price).
	require.Greater(t, tx.Gas(), uint64(0), "anti-vacuity: a nonzero gas-price mutant would surface in Cost")
	require.Zero(t, tx.Cost().Sign(), "Cost is zero for a fee-free system tx")

	// EffectiveGasTip: zero with no base fee; below-base-fee error with a positive base fee.
	gt, err := tx.EffectiveGasTip(nil)
	require.NoError(t, err)
	require.Zero(t, gt.Sign())
	_, err = tx.EffectiveGasTip(big.NewInt(1000))
	require.ErrorIs(t, err, ErrGasFeeCapTooLow, "a zero fee cap is below any positive base fee")

	// The unsupported sign operation must PANIC (reachable via Signer.Hash -> inner.sigHash).
	require.Panics(t, func() { _ = LatestSignerForChainID(big.NewInt(1)).Hash(tx) },
		"signing a PoP tx must panic (it is force-included, never signed)")
}

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

// Transaction-level wire envelope for the PoP payout (0x7D) typed tx — the decodeTyped/MarshalBinary path that
// block import, p2p relay, and freezer storage use. The existing pop_payout_tx_test.go exercises ONLY the inner
// tx.encode()/tx.decode(); a field reorder of {To,Gas,Data} or a broken rlp:"nil" tag re-encodes/re-decodes
// self-consistently at the inner level and survives it, but breaks the wrapper round-trip and the golden wire bytes.
// Mirrors btc_attributes_envelope_test.go for 0x7C.
func TestPopPayoutTxEnvelopeRoundTrip(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	tx := NewTx(&PopPayoutTx{To: &to, Gas: 1_000_000, Data: []byte{0xc9, 0x4f}})

	bin, err := tx.MarshalBinary()
	require.NoError(t, err)
	require.NotEmpty(t, bin)
	require.Equal(t, byte(PopPayoutTxType), bin[0], "the typed envelope must carry the 0x7D prefix byte")

	utx := new(Transaction)
	require.NoError(t, utx.UnmarshalBinary(bin), "the 0x7D typed envelope must decode (decodeTyped case)")
	require.Equal(t, uint8(PopPayoutTxType), utx.Type())
	require.Equal(t, tx.Gas(), utx.Gas())
	require.Equal(t, tx.To(), utx.To(), "the To pointer must round-trip")
	require.True(t, bytes.Equal(tx.Data(), utx.Data()), "the data must round-trip byte-for-byte")

	// Idempotence: re-encoding the decoded tx reproduces the exact wire bytes.
	again, err := utx.MarshalBinary()
	require.NoError(t, err)
	require.True(t, bytes.Equal(bin, again), "re-marshaling a decoded 0x7D tx must reproduce the wire bytes")
}

// TestPopPayoutTxEnvelopeNilTo pins the rlp:"nil" tag on To: a nil To round-trips as nil (encoded as the 0x80 empty
// item), not a zero address.
func TestPopPayoutTxEnvelopeNilTo(t *testing.T) {
	tx := NewTx(&PopPayoutTx{To: nil, Gas: 1_000_000, Data: []byte{0xc9, 0x4f}})
	bin, err := tx.MarshalBinary()
	require.NoError(t, err)
	utx := new(Transaction)
	require.NoError(t, utx.UnmarshalBinary(bin))
	require.Nil(t, utx.To(), "a nil To must round-trip as nil (rlp:\"nil\" tag)")
	require.True(t, bytes.Equal([]byte{0xc9, 0x4f}, utx.Data()))
}

// TestPopPayoutTxEnvelopeTruncatedDecodeErrors: a malformed 0x7D envelope is REJECTED with an error, never a panic.
func TestPopPayoutTxEnvelopeTruncatedDecodeErrors(t *testing.T) {
	var err error
	require.NotPanics(t, func() {
		err = new(Transaction).UnmarshalBinary([]byte{byte(PopPayoutTxType), 0x01, 0x02, 0x03})
	}, "a truncated 0x7D envelope must not panic")
	require.Error(t, err, "a truncated 0x7D envelope must decode-error, not silently succeed")
	require.Contains(t, err.Error(), "rlp:", "the decode error must originate from the RLP decoder, not a higher-level path")
}

// TestPopPayoutTxEnvelopeRejectTrailingBytes: a well-formed 0x7D envelope with trailing bytes is rejected
// (canonical-encoding invariant; rlp.DecodeBytes rejects more-than-one-value).
func TestPopPayoutTxEnvelopeRejectTrailingBytes(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	bin, err := NewTx(&PopPayoutTx{To: &to, Gas: 1_000_000, Data: []byte{0xc9, 0x4f}}).MarshalBinary()
	require.NoError(t, err)
	require.NoError(t, new(Transaction).UnmarshalBinary(bin))

	malformed := append(append([]byte{}, bin...), 0x01, 0x02, 0x03, 0x04)
	var derr error
	require.NotPanics(t, func() { derr = new(Transaction).UnmarshalBinary(malformed) })
	require.ErrorIs(t, derr, rlp.ErrMoreThanOneValue, "a 0x7D envelope with trailing bytes must be rejected by the canonical-encoding guard")
}

// TestPopPayoutTxEnvelopeGolden freezes the EXACT wire bytes of the 0x7D envelope (Data is arbitrary bytes, so the
// golden is unconditionally stable). A field reorder in the {To,Gas,Data} RLP struct silently changes the layout and
// survives the symmetric round-trip tests; this golden catches it.
func TestPopPayoutTxEnvelopeGolden(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	bin, err := NewTx(&PopPayoutTx{To: &to, Gas: 1_000_000, Data: []byte{0xc9, 0x4f}}).MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, "7ddc944200000000000000000000000000000000000042830f424082c94f", hex.EncodeToString(bin),
		"the 0x7D typed-envelope wire layout (type || rlp[To,Gas,Data]) must be stable")

	nilBin, err := NewTx(&PopPayoutTx{To: nil, Gas: 1_000_000, Data: []byte{0xc9, 0x4f}}).MarshalBinary()
	require.NoError(t, err)
	require.Equal(t, "7dc880830f424082c94f", hex.EncodeToString(nilBin),
		"nil-To must encode the 0x80 empty item (rlp:\"nil\")")
}

// The 0x7D (PoP payout) receipt JSON (eth_getTransactionReceipt) contract: popPayoutNonce is surfaced exactly when
// set (omitempty) and round-trips through MarshalJSON/UnmarshalJSON. Mirrors TestBtcAttrReceiptJSONNonce for 0x7C —
// the PoP receipt RLP is covered but its JSON nonce path (the field RPC clients read) was not.
func TestPopPayoutReceiptJSONNonce(t *testing.T) {
	// With a nonce: the field is present and round-trips.
	b, err := json.Marshal(popPayoutReceiptWithNonce)
	require.NoError(t, err)
	require.Contains(t, string(b), "popPayoutNonce", "a set PoP nonce must appear in the receipt JSON")
	var got Receipt
	require.NoError(t, json.Unmarshal(b, &got))
	require.NotNil(t, got.PoPPayoutNonce)
	require.Equal(t, *popPayoutReceiptWithNonce.PoPPayoutNonce, *got.PoPPayoutNonce)

	// Without a nonce: omitempty drops the field and it round-trips as nil.
	b2, err := json.Marshal(popPayoutReceiptNoNonce)
	require.NoError(t, err)
	require.NotContains(t, string(b2), "popPayoutNonce", "an unset PoP nonce must be omitted (omitempty)")
	var got2 Receipt
	require.NoError(t, json.Unmarshal(b2, &got2))
	require.Nil(t, got2.PoPPayoutNonce)
}

// Sender() identity for the PoP payout (0x7D) tx, mirroring TestBtcAttrTxSenderIdentity for 0x7C. The signer returns
// the hardcoded PoPPayoutSenderAddress unconditionally for this type — the consensus "from" identity that drives
// msg.From / the nonce account. The existing PoP coverage only pins the CONSTANT literal, never that Sender() USES
// it; a "return tx.To()" mutant at transaction_signing.go ~275 would survive the constant pin but break consensus.
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
