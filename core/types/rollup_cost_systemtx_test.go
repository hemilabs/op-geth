// Copyright 2026 The go-ethereum Authors
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
	"encoding/binary"
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"
	"github.com/stretchr/testify/require"
)

// TestIsZeroDAFootprintTxMembership pins the EXACT membership of IsZeroDAFootprintTx — the single
// source-of-truth set that CalcDAFootprint (the builder, rollup_cost.go) and deriveOPStackFields (the
// receipt marshaller, receipt_opstack.go) BOTH consult to exclude non-L1-posted system txs from a block's
// DA footprint. If those two ever disagree on this set they diverge on BlobGasUsed — a consensus split. The
// expected values are enumerated by hand here, independent of the production OR-expression, so a future edit
// to the tx-type list (adding or dropping a type) is caught directly, not only via the indirect footprint
// tests. true for exactly {deposit 0x7E, PoP-payout 0x7D, BtcAttr 0x7C}; false for every standard type.
func TestIsZeroDAFootprintTxMembership(t *testing.T) {
	to := common.HexToAddress("0x4200000000000000000000000000000000000015")
	u := uint256.NewInt
	cases := []struct {
		name string
		tx   *Transaction
		want bool
	}{
		// The three zero-DA-footprint system txs (excluded from the DA footprint).
		{"deposit-0x7E", NewTx(&DepositTx{Data: []byte{0x01}}), true},
		{"pop-payout-0x7D", NewTx(&PopPayoutTx{To: &to, Gas: 21000, Data: []byte{0x11, 0x22}}), true},
		{"btc-attr-0x7C", systemTxBtcAttrTx(t), true},
		// Every standard tx type is DA-accounted (must NOT be in the set).
		{"legacy", NewTx(&LegacyTx{Nonce: 0, Gas: 21000, GasPrice: big.NewInt(1)}), false},
		{"access-list", NewTx(&AccessListTx{ChainID: big.NewInt(1), Nonce: 0, Gas: 21000, GasPrice: big.NewInt(1)}), false},
		{"dynamic-fee", NewTx(&DynamicFeeTx{ChainID: big.NewInt(1), Nonce: 0, Gas: 21000, GasTipCap: big.NewInt(1), GasFeeCap: big.NewInt(1)}), false},
		{"blob", NewTx(&BlobTx{ChainID: u(1), Nonce: 0, Gas: 21000, GasTipCap: u(1), GasFeeCap: u(1), Value: u(0), BlobFeeCap: u(1)}), false},
		{"set-code", NewTx(&SetCodeTx{ChainID: u(1), Nonce: 0, Gas: 21000, GasTipCap: u(1), GasFeeCap: u(1), Value: u(0)}), false},
	}
	for _, c := range cases {
		require.Equalf(t, c.want, c.tx.IsZeroDAFootprintTx(), "%s: IsZeroDAFootprintTx membership", c.name)
	}
}

// jovianTestChainConfig returns a config with every OP fork through Jovian active at t=0, so the L1
// attributes parser and the Jovian DA-footprint paths are all live.
func jovianTestChainConfig() *params.ChainConfig {
	zero := uint64(0)
	return &params.ChainConfig{
		Optimism:     params.OptimismTestConfig.Optimism,
		RegolithTime: &zero,
		EcotoneTime:  &zero,
		FjordTime:    &zero,
		HoloceneTime: &zero,
		IsthmusTime:  &zero,
		JovianTime:   &zero,
	}
}

// jovianL1InfoTx builds the L1-attributes deposit (tx[0]) that a post-Jovian block carries, encoding
// the DA footprint gas scalar in the trailing two bytes — mirrors the miner's jovianDepositTx helper.
func jovianL1InfoTx(scalar uint16) *Transaction {
	data := make([]byte, JovianL1AttributesLen)
	copy(data[0:4], JovianL1AttributesSelector)
	binary.BigEndian.PutUint16(data[JovianL1AttributesLen-2:], scalar)
	return NewTx(&DepositTx{Data: data})
}

func systemTxUserTx() *Transaction {
	return NewTx(&LegacyTx{Nonce: 0, Gas: 21000, GasPrice: big.NewInt(1), Data: bytes.Repeat([]byte{0xab, 0x00, 0xcd}, 64)})
}

func systemTxPopTx() *Transaction {
	to := common.HexToAddress("0x4200000000000000000000000000000000000042")
	return NewTx(&PopPayoutTx{To: &to, Gas: 21000, Data: bytes.Repeat([]byte{0x11, 0x22}, 64)})
}

func systemTxBtcAttrTx(t *testing.T) *Transaction {
	t.Helper()
	h := chainhash.Hash{0x01, 0x02, 0x03}
	btc, err := MakeBtcAttributesDepositedTx(&h, nil)
	require.NoError(t, err)
	return NewTx(btc)
}

// TestCalcDAFootprintExcludesSystemTxs verifies the Jovian DA-footprint block limit counts only user txs:
// the force-included PoP payout (0x7D) and BTC Attributes Deposited (0x7C) system txs are skipped, matching
// the block-build path which never accumulates them into header.BlobGasUsed. Guards the post-Jovian
// build-vs-import BlobGasUsed mismatch (a fleet liveness stall).
func TestCalcDAFootprintExcludesSystemTxs(t *testing.T) {
	user1 := systemTxUserTx()
	user2 := NewTx(&LegacyTx{Nonce: 7, Gas: 21000, GasPrice: big.NewInt(1), Data: bytes.Repeat([]byte{0x10, 0x20, 0x30, 0x40}, 90)})
	da1 := user1.RollupCostData().EstimatedDASize().Uint64()
	da2 := user2.RollupCostData().EstimatedDASize().Uint64()
	require.Positive(t, da1)
	require.Positive(t, da2)

	// Independent magnitude anchor for user2: recompute EstimatedDASize from FlzCompressLen and the raw
	// Fjord constants (intercept + coef*fastlz, floored to MinTransactionSize, /1e6), not via
	// RollupCostData().EstimatedDASize() (the expression CalcDAFootprint evaluates internally). Catches a
	// same-direction corruption of the per-tx formula (intercept sign, dropped floor, wrong divisor) that
	// an EstimatedDASize-derived oracle cannot. FlzCompressLen is pinned by TestFlzCompressLen.
	raw, err := user2.MarshalBinary()
	require.NoError(t, err)
	scaled := new(big.Int).Add(L1CostIntercept, new(big.Int).Mul(L1CostFastlzCoef, big.NewInt(int64(FlzCompressLen(raw)))))
	if scaled.Cmp(MinTransactionSizeScaled) < 0 {
		scaled.Set(MinTransactionSizeScaled)
	}
	require.Equal(t, new(big.Int).Div(scaled, big.NewInt(1e6)).Uint64(), da2, "independent fastlz-derived DA size must match EstimatedDASize")

	// The system txs each have a non-zero EstimatedDASize (empty RollupCostData floors to
	// MinTransactionSize=100, and 0x7C/0x7D compute a real fastlz size), so the exclusion must come from
	// the type skip, not from a zero footprint. Guards a regression that relies on ==0.
	require.Positive(t, systemTxPopTx().RollupCostData().EstimatedDASize().Uint64())
	require.Positive(t, systemTxBtcAttrTx(t).RollupCostData().EstimatedDASize().Uint64())

	// Interleaved layout [L1-info(0x7E,scalar), user1, PoP(0x7D), user2, BtcAttr(0x7C)] across several
	// on-wire scalars: only the two user txs count, the footprint accumulates both (so a `=` overwrite or
	// positional skip is observable) and is linear in the scalar decoded from tx[0] (so a hardcoded
	// multiplier or wrong-2-bytes read is observable). scalar=0 yields 0 even with positive-DA user txs
	// present, distinct from the system-only zero case below.
	for _, scalar := range []uint16{0, 1, 400, 65535} {
		got, err := CalcDAFootprint([]*Transaction{
			jovianL1InfoTx(scalar), user1, systemTxPopTx(), user2, systemTxBtcAttrTx(t),
		})
		require.NoError(t, err)
		require.Equal(t, (da1+da2)*uint64(scalar), got, "scalar=%d: footprint must be (da1+da2)*scalar with system txs skipped", scalar)
		if scalar != 0 {
			require.NotEqual(t, da2*uint64(scalar), got, "scalar=%d: an overwrite (=) bug would yield only the last user tx", scalar)
			require.NotEqual(t, da1*uint64(scalar), got, "scalar=%d: dropping an adjacent user tx would yield only the first", scalar)
		}
	}

	// An interior (non-tx[0]) deposit must also be skipped by the steady-state loop — the only case
	// exercising the loop's IsDepositTx skip somewhere other than tx[0].
	got, err := CalcDAFootprint([]*Transaction{
		jovianL1InfoTx(400), user1, NewTx(&DepositTx{Data: []byte("interior-deposit")}), user2,
	})
	require.NoError(t, err)
	require.Equal(t, (da1+da2)*400, got, "an interior deposit must be skipped too")

	// System/deposit txs only (no user tx) -> zero footprint.
	got, err = CalcDAFootprint([]*Transaction{
		jovianL1InfoTx(400), systemTxPopTx(), systemTxBtcAttrTx(t),
	})
	require.NoError(t, err)
	require.Zero(t, got, "a block with only deposit/system txs must have a zero DA footprint")
}

// TestExtractDAFootprintGasScalarGolden pins ExtractDAFootprintGasScalar directly: the length guard, the
// selector guard (otherwise untested — a mutant deleting it survives all the DA-footprint tests), and the
// big-endian uint16 read at the last two bytes (a wrong offset or little-endian read corrupts build and
// import identically, preserving build==import, so only a direct decode test catches it).
func TestExtractDAFootprintGasScalarGolden(t *testing.T) {
	valid := make([]byte, JovianL1AttributesLen)
	copy(valid[0:4], JovianL1AttributesSelector)
	binary.BigEndian.PutUint16(valid[JovianL1AttributesLen-2:], 0x0102) // distinct bytes pin offset + endianness
	got, err := ExtractDAFootprintGasScalar(valid)
	require.NoError(t, err)
	require.Equal(t, uint16(0x0102), got, "scalar is the big-endian uint16 at the trailing 2 bytes (not 0x0201, not an interior offset)")

	// Wrong selector -> error.
	badSelector := make([]byte, JovianL1AttributesLen)
	copy(badSelector[0:4], IsthmusL1AttributesSelector)
	binary.BigEndian.PutUint16(badSelector[JovianL1AttributesLen-2:], 0x0102)
	_, err = ExtractDAFootprintGasScalar(badSelector)
	require.ErrorContains(t, err, "does not have Jovian selector")

	// Too short -> error.
	_, err = ExtractDAFootprintGasScalar(make([]byte, JovianL1AttributesLen-1))
	require.ErrorContains(t, err, "too short for DA footprint gas scalar")

	// Boundary scalar values round-trip exactly.
	for _, s := range []uint16{0, 1, 0x00ff, 0xff00, 65535} {
		buf := make([]byte, JovianL1AttributesLen)
		copy(buf[0:4], JovianL1AttributesSelector)
		binary.BigEndian.PutUint16(buf[JovianL1AttributesLen-2:], s)
		got, err := ExtractDAFootprintGasScalar(buf)
		require.NoError(t, err)
		require.Equal(t, s, got)
	}
}

// TestCalcDAFootprintEqualsReceiptBlobGasSum pins the lock-step the rollup_cost.go comment demands:
// CalcDAFootprint's three-type skip-set must match the per-receipt DA derivation in receipt_opstack.go
// (deriveOPStackFields, the per-receipt skip loop in receipt_opstack.go), which independently computes BlobGasUsed = scalar*EstimatedDASize for each
// non-skipped tx. If the skip-sets drift, the block footprint and the receipt root disagree. An oracle
// independent of CalcDAFootprint's own loop (a different function computes the sum).
func TestCalcDAFootprintEqualsReceiptBlobGasSum(t *testing.T) {
	const scalar = uint16(400)
	const blockTime = uint64(0)
	config := jovianTestChainConfig()
	require.True(t, config.IsJovian(blockTime))

	// Diverse user tx encodings (DynamicFee + AccessList, not just Legacy): RollupCostData() forks
	// structurally on tx type, so a regression diverging on the typed-envelope path is caught here.
	user1 := NewTx(&DynamicFeeTx{ChainID: big.NewInt(1), Nonce: 0, GasTipCap: big.NewInt(1), GasFeeCap: big.NewInt(1), Gas: 21000, Data: bytes.Repeat([]byte{0x11, 0x22, 0x33}, 50)})
	user2 := NewTx(&AccessListTx{ChainID: big.NewInt(1), Nonce: 1, GasPrice: big.NewInt(1), Gas: 21000, Data: bytes.Repeat([]byte{0x55, 0x66}, 70)})
	// Last tx must be a non-deposit, else deriveOPStackFields early-returns without deriving fields.
	txs := []*Transaction{jovianL1InfoTx(scalar), systemTxPopTx(), systemTxBtcAttrTx(t), user1, user2}

	rs := make(Receipts, len(txs))
	for i := range rs {
		rs[i] = &Receipt{}
	}
	require.NoError(t, rs.deriveOPStackFields(config, blockTime, txs))

	var receiptSum uint64
	for i, tx := range txs {
		if tx.IsDepositTx() || tx.IsPopPayoutTx() || tx.IsBtcAttributesDepositedTx() {
			require.Zero(t, rs[i].BlobGasUsed, "deposit/system tx %d must have zero per-receipt BlobGasUsed", i)
			// The same skip leaves the L1-cost fields unset — the receipt analog of the state_transition
			// L1-fee guard. 0x7C/0x7D are charged no L1 data fee.
			require.Nil(t, rs[i].L1Fee, "deposit/system tx %d must have no L1Fee", i)
			require.Nil(t, rs[i].L1GasUsed, "deposit/system tx %d must have no L1GasUsed", i)
			require.Nil(t, rs[i].DAFootprintGasScalar, "deposit/system tx %d must have no DAFootprintGasScalar", i)
			continue
		}
		require.Positive(t, rs[i].BlobGasUsed, "user tx %d must have positive per-receipt BlobGasUsed", i)
		require.NotNil(t, rs[i].L1Fee, "user tx %d must have an L1Fee", i)
		// The per-receipt scalar must equal the on-wire scalar from tx[0] (asserted nowhere else).
		require.NotNil(t, rs[i].DAFootprintGasScalar, "user tx %d must have a DAFootprintGasScalar", i)
		require.Equal(t, uint64(scalar), *rs[i].DAFootprintGasScalar, "user tx %d DAFootprintGasScalar must equal the decoded scalar", i)
		receiptSum += rs[i].BlobGasUsed
	}

	fp, err := CalcDAFootprint(txs)
	require.NoError(t, err)
	require.Positive(t, fp)
	require.Equal(t, receiptSum, fp,
		"CalcDAFootprint must equal the sum of per-receipt BlobGasUsed — the two skip-sets must stay in lock-step")
}

// TestDeriveOPStackFieldsUserTxBeforeTrailingSystemTx pins that a user tx still gets its L1-fee receipt
// fields when a system tx (BtcAttr 0x7C / PoP 0x7D) TRAILS it. Live Hemi mainnet history contains the
// ordering [0x7E l1-info, 0x2 user, 0x7C BtcAttr] (system txs are NOT a contiguous prefix on hVM chains), so
// a last-element-only early-exit (testing txs[len-1].IsZeroDAFootprintTx) would wrongly skip the whole block
// and drop the preceding user receipt's L1-fee fields on RPC reads of that historical block. deriveOPStackFields
// runs on the read path (Receipts.DeriveFields), so this is an RPC/accounting regression, not consensus —
// but it would silently corrupt explorer/fee-accounting reads of finalized history after an upgrade.
func TestDeriveOPStackFieldsUserTxBeforeTrailingSystemTx(t *testing.T) {
	const scalar = uint16(400)
	const blockTime = uint64(0)
	config := jovianTestChainConfig()
	require.True(t, config.IsJovian(blockTime))
	user := systemTxUserTx()

	for _, tc := range []struct {
		name string
		txs  []*Transaction
	}{
		{"trailing-btcattr", []*Transaction{jovianL1InfoTx(scalar), user, systemTxBtcAttrTx(t)}},
		{"trailing-pop", []*Transaction{jovianL1InfoTx(scalar), user, systemTxPopTx()}},
		{"user-between-systems-trailing-btcattr", []*Transaction{jovianL1InfoTx(scalar), systemTxPopTx(), user, systemTxBtcAttrTx(t)}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			rs := make(Receipts, len(tc.txs))
			for i := range rs {
				rs[i] = &Receipt{}
			}
			require.NoError(t, rs.deriveOPStackFields(config, blockTime, tc.txs))
			sawUser := false
			for i, tx := range tc.txs {
				if tx.IsZeroDAFootprintTx() {
					require.Nil(t, rs[i].L1Fee, "system tx %d must have no L1Fee", i)
					continue
				}
				sawUser = true
				require.NotNil(t, rs[i].L1Fee, "user tx %d preceding a trailing system tx must still derive its L1Fee", i)
				require.NotNil(t, rs[i].DAFootprintGasScalar, "user tx %d must have a DAFootprintGasScalar", i)
				require.Equal(t, uint64(scalar), *rs[i].DAFootprintGasScalar, "user tx %d scalar must equal the decoded on-wire scalar", i)
			}
			require.True(t, sawUser, "test fixture must contain a user tx")
		})
	}

	// A genuinely all-system block (no user tx anywhere) must still early-exit and derive no L1-fee fields,
	// regardless of which system-tx type is last — the early-exit's correct purpose.
	t.Run("all-system-no-fields", func(t *testing.T) {
		txs := []*Transaction{jovianL1InfoTx(scalar), systemTxPopTx(), systemTxBtcAttrTx(t)}
		rs := make(Receipts, len(txs))
		for i := range rs {
			rs[i] = &Receipt{}
		}
		require.NoError(t, rs.deriveOPStackFields(config, blockTime, txs))
		for i := range rs {
			require.Nil(t, rs[i].L1Fee, "all-system block: tx %d must derive no L1Fee", i)
		}
	})
}

// TestCalcDAFootprintActivationLengthBoundary pins that the activation branch keys exactly on a 176-byte
// (Isthmus-length) tx[0]: a 178-byte (Jovian) tx[0] routes to the steady-state path and computes a real
// footprint, while a malformed in-between length is rejected by the scalar extractor.
func TestCalcDAFootprintActivationLengthBoundary(t *testing.T) {
	const scalar = uint16(400)
	user := systemTxUserTx()

	// 178-byte Jovian tx[0] -> steady-state path -> the trailing user tx is counted.
	got, err := CalcDAFootprint([]*Transaction{jovianL1InfoTx(scalar), user})
	require.NoError(t, err)
	require.Equal(t, user.RollupCostData().EstimatedDASize().Uint64()*uint64(scalar), got)

	// 176-byte Isthmus tx[0] -> activation path -> footprint is 0 even with a trailing system tx.
	got, err = CalcDAFootprint([]*Transaction{NewTx(&DepositTx{Data: make([]byte, IsthmusL1AttributesLen)}), systemTxBtcAttrTx(t)})
	require.NoError(t, err)
	require.Zero(t, got)

	// 177-byte tx[0] -> neither activation (176) nor a valid Jovian length (>=178) -> the scalar extractor
	// rejects it (pinning the message ensures it is not misrouted into the activation branch's error).
	_, err = CalcDAFootprint([]*Transaction{NewTx(&DepositTx{Data: make([]byte, IsthmusL1AttributesLen+1)}), user})
	require.ErrorContains(t, err, "too short for DA footprint gas scalar")
}

// TestCalcDAFootprintJovianActivationBlock covers the activation-block edge: tx[0] still carries
// Isthmus-length attributes (no DA scalar yet) and the block must contain no user txs. A trailing system
// tx (0x7C/0x7D) is legitimate — an hVM chain force-includes a 0x7C in nearly every block, so it is the
// trailing tx at the fork boundary — and must be accepted; a trailing user tx must still be rejected.
func TestCalcDAFootprintJovianActivationBlock(t *testing.T) {
	l1 := NewTx(&DepositTx{Data: make([]byte, IsthmusL1AttributesLen)})
	secondDeposit := NewTx(&DepositTx{Data: []byte("user-deposit")})

	// The activation branch inspects only the trailing tx (sufficient because deposit/system txs always
	// precede user txs in a well-formed block). Each case fixes a property of that check so a regression
	// (dropping a type from the allow-set, or an off-by-one inspecting an interior tx) fails here.
	// errContains="" means the case must succeed with a zero footprint; a non-empty value pins the exact
	// rejection path (CalcDAFootprint has three distinct error sites, so a bare require.Error would let a
	// mutant erroring via the wrong path stay green).
	for _, tc := range []struct {
		name        string
		txs         []*Transaction
		errContains string
	}{
		{"trailing-btc-attr-0x7C", []*Transaction{l1, systemTxBtcAttrTx(t)}, ""},
		{"trailing-pop-0x7D", []*Transaction{l1, systemTxPopTx()}, ""},
		{"trailing-deposit-0x7E", []*Transaction{l1, secondDeposit}, ""},
		{"multiple-trailing-system-txs", []*Transaction{l1, systemTxPopTx(), systemTxBtcAttrTx(t)}, ""},
		// Interior user tx before a trailing system tx is accepted (benign: at activation the scalar is 0
		// so the footprint is 0, and the self-build path cannot produce this ordering). Pins the
		// only-last-tx behavior.
		{"interior-user-before-trailing-system", []*Transaction{l1, systemTxUserTx(), systemTxBtcAttrTx(t)}, ""},
		{"trailing-user-tx-rejected", []*Transaction{l1, systemTxUserTx()}, "unexpected non-deposit transactions in Jovian activation block"},
		// System tx at index 1, user tx last: must be rejected — kills an off-by-one that checks txs[1].
		{"system-then-trailing-user-rejected", []*Transaction{l1, systemTxBtcAttrTx(t), systemTxUserTx()}, "unexpected non-deposit transactions in Jovian activation block"},
		// txs[0] guard (predicate 1): no test elsewhere drives this branch, so a mutant deleting it survives.
		{"empty-tx-list", []*Transaction{}, "missing deposit transaction"},
		{"non-deposit-first-tx", []*Transaction{systemTxUserTx(), systemTxBtcAttrTx(t)}, "missing deposit transaction"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := CalcDAFootprint(tc.txs)
			if tc.errContains != "" {
				require.ErrorContains(t, err, tc.errContains)
				return
			}
			require.NoError(t, err, "deposit/system txs are legitimate in the activation block")
			require.Zero(t, got, "the activation block sets no DA footprint")
		})
	}
}

// TestSystemTxPredicateConsistency pins the gas-exempt routing that keeps every hVM block from halting. The PoP
// (0x7D) and BtcAttr (0x7C) inner txs define isSystemTx()->false (annotated "Compatibility - Unused" — the comment
// is WRONG: it is load-bearing). state_transition's gas-exempt branch (entered by deposit/PoP/BtcAttr) returns
// ErrSystemTxNotSupported post-Regolith iff IsSystemTx()==true. Every hVM block force-includes a BtcAttr and many a
// PoP, and production runs Regolith, so a flip of either isSystemTx() to true would halt the fleet on essentially
// every block. No test asserts IsSystemTx() for these types. Also pin the dual the gas-exempt branch relies on:
// IsZeroDAFootprintTx()==true AND IsSystemTx()==false together; and that the DepositTx field IS honored (not a
// constant false).
func TestSystemTxPredicateConsistency(t *testing.T) {
	pop := systemTxPopTx()
	btc := systemTxBtcAttrTx(t)

	// The load-bearing routing: 0x7D/0x7C must NOT be OP system txs (else preCheck -> ErrSystemTxNotSupported).
	require.False(t, pop.IsSystemTx(), "PoP-payout (0x7D) must not be an OP system tx (would halt post-Regolith)")
	require.False(t, btc.IsSystemTx(), "BtcAttr (0x7C) must not be an OP system tx (would halt every hVM block)")

	// The gas-exempt branch consumes these three types; each must be zero-DA AND non-system simultaneously.
	depNonSys := NewTx(&DepositTx{Value: big.NewInt(0), Gas: 21000})
	for _, tc := range []struct {
		name string
		tx   *Transaction
	}{{"deposit", depNonSys}, {"pop", pop}, {"btcAttr", btc}} {
		require.Truef(t, tc.tx.IsZeroDAFootprintTx(), "%s must be zero-DA (gas-exempt system tx)", tc.name)
		require.Falsef(t, tc.tx.IsSystemTx(), "%s must NOT be an OP system tx (gas-exempt routing)", tc.name)
	}

	// The DepositTx.IsSystemTransaction field IS honored — proving IsSystemTx is genuinely wired, not constant-false.
	require.True(t, NewTx(&DepositTx{Value: big.NewInt(0), Gas: 21000, IsSystemTransaction: true}).IsSystemTx(),
		"a DepositTx with IsSystemTransaction=true must report IsSystemTx()==true")
	require.False(t, NewTx(&LegacyTx{}).IsSystemTx(), "a normal LegacyTx is not a system tx")
}
