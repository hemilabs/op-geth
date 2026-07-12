// Copyright 2024 The go-ethereum Authors
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

package txpool

import (
	"errors"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/types"
)

// These tests cover the subpool-splitting logic in TxPool.Add, which fans a batch of transactions out to
// the per-type subpools and pieces the per-subpool error slices back into the caller's order.
//
// Regression target (a chain-halting bug): the Hemi custom types (PopPayout 0x7D, BtcAttributesDeposited
// 0x7C) are short-circuited with `continue` in the split loop. If splits[i] is left at its make() zero
// value (0) for such a skipped tx, the reassembly loop misreads it as "handled by subpool 0" and consumes
// an errsets[0] entry that was never produced (the tx was never appended to txsets[0]). The underflow
// panics with "index out of range" — on the single-subpool OP-Stack config one such tx delivered over p2p
// (no recover() on the path) crashes the node. The fix marks every tx -1 before the custom-type early-out,
// so skipped txs resolve to ErrTxTypeNotSupported instead of corrupting indexing.

// addMockSubPool is a minimal SubPool used to drive TxPool.Add directly. It embeds the SubPool interface
// (left nil) so it satisfies the full interface while implementing only the two methods TxPool.Add calls,
// Filter and Add. Any other interface method being called nil-panics and fails the test loudly, the
// desired signal.
type addMockSubPool struct {
	SubPool
	accept func(tx *types.Transaction) bool
	addErr func(tx *types.Transaction) error
}

func (m *addMockSubPool) Filter(tx *types.Transaction) bool { return m.accept(tx) }

// Add honours the SubPool contract: it returns exactly one error per input tx.
func (m *addMockSubPool) Add(txs []*types.Transaction, _ bool) []error {
	errs := make([]error, len(txs))
	if m.addErr != nil {
		for i, tx := range txs {
			errs[i] = m.addErr(tx)
		}
	}
	return errs
}

func acceptTypes(accepted ...byte) func(*types.Transaction) bool {
	set := make(map[byte]bool, len(accepted))
	for _, t := range accepted {
		set[t] = true
	}
	return func(tx *types.Transaction) bool { return set[tx.Type()] }
}

func popTx() *types.Transaction    { return types.NewTx(&types.PopPayoutTx{Gas: 21000}) }
func btcTx() *types.Transaction    { return types.NewTx(&types.BtcAttributesDepositedTx{Gas: 21000}) }
func legacyTx() *types.Transaction { return types.NewTx(&types.LegacyTx{Gas: 21000}) }
func dynTx() *types.Transaction    { return types.NewTx(&types.DynamicFeeTx{Gas: 21000}) }

func isUnsupported(err error) bool { return errors.Is(err, core.ErrTxTypeNotSupported) }

// TestTxPoolAddCustomTypesNoPanic exercises the single-subpool (OP-Stack/Hemi) config — where one
// custom-type tx is the minimal crash trigger — across many batch compositions. Every batch must not
// panic and must yield ErrTxTypeNotSupported for the custom types and any other type no subpool accepts,
// preserving positional order.
func TestTxPoolAddCustomTypesNoPanic(t *testing.T) {
	// Single subpool accepting only legacy txs (the legacy-only OP-Stack pool, blobpool gated out).
	pool := &TxPool{subpools: []SubPool{
		&addMockSubPool{accept: acceptTypes(types.LegacyTxType)},
	}}

	tx := func(txs ...*types.Transaction) []*types.Transaction { return txs }
	unsup := func(b ...bool) []bool { return b }

	cases := []struct {
		name string
		txs  []*types.Transaction
		want []bool // true => expect ErrTxTypeNotSupported, false => expect nil (accepted)
	}{
		{"lone-pop", tx(popTx()), unsup(true)},                           // minimal crash trigger pre-fix
		{"lone-btc", tx(btcTx()), unsup(true)},                           // the other custom type
		{"pop-pop", tx(popTx(), popTx()), unsup(true, true)},             // all-custom batch
		{"legacy-only", tx(legacyTx()), unsup(false)},                    // normal path unaffected
		{"unsupported-noncustom", tx(dynTx()), unsup(true)},              // non-custom rejected -> -1 branch
		{"legacy-then-pop", tx(legacyTx(), popTx()), unsup(false, true)}, // custom after a real subpool-0 tx
		{"pop-then-legacy", tx(popTx(), legacyTx()), unsup(true, false)}, // custom before -> would steal errsets[0][0]
		{"legacy-pop-legacy", tx(legacyTx(), popTx(), legacyTx()), unsup(false, true, false)},
		{"btc-legacy-pop", tx(btcTx(), legacyTx(), popTx()), unsup(true, false, true)},
		{"pop-btc-dyn", tx(popTx(), btcTx(), dynTx()), unsup(true, true, true)},
		{"empty", nil, nil},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			var errs []error
			require.NotPanics(t, func() { errs = pool.Add(c.txs, false) })
			require.Len(t, errs, len(c.want))
			for i, wantUnsup := range c.want {
				require.Equalf(t, wantUnsup, isUnsupported(errs[i]),
					"position %d: got err %v, expected unsupported=%v", i, errs[i], wantUnsup)
			}
		})
	}
}

// TestTxPoolAddMultiSubpoolMappingPreserved verifies that with more than one subpool, custom-type txs
// interleaved with accepted txs do not desync the per-subpool error slices: each accepted tx receives the
// error its own subpool returned (identity-checked via distinct sentinel errors), in positional order,
// while custom txs resolve to ErrTxTypeNotSupported. Pre-fix this batch panicked (the custom txs consumed
// errsets[0] entries belonging to the legacy txs and ran the slice empty).
func TestTxPoolAddMultiSubpoolMappingPreserved(t *testing.T) {
	errLegacy := errors.New("from-legacy-subpool")
	errDyn := errors.New("from-dynamic-subpool")

	sub0 := &addMockSubPool{
		accept: acceptTypes(types.LegacyTxType),
		addErr: func(*types.Transaction) error { return errLegacy },
	}
	sub1 := &addMockSubPool{
		accept: acceptTypes(types.DynamicFeeTxType),
		addErr: func(*types.Transaction) error { return errDyn },
	}
	pool := &TxPool{subpools: []SubPool{sub0, sub1}}

	// legacy(sub0) | pop(custom) | dyn(sub1) | btc(custom) | legacy(sub0)
	batch := []*types.Transaction{legacyTx(), popTx(), dynTx(), btcTx(), legacyTx()}

	var errs []error
	require.NotPanics(t, func() { errs = pool.Add(batch, false) })
	require.Len(t, errs, 5)

	require.Same(t, errLegacy, errs[0], "legacy tx must get subpool-0's error")
	require.True(t, isUnsupported(errs[1]), "pop tx must be ErrTxTypeNotSupported")
	require.Same(t, errDyn, errs[2], "dynamic-fee tx must get subpool-1's error")
	require.True(t, isUnsupported(errs[3]), "btc tx must be ErrTxTypeNotSupported")
	require.Same(t, errLegacy, errs[4], "second legacy tx must still map to subpool-0's error")
}

// TestTxPoolAddNonCustomBatchUnchanged guards that the fix did not alter behaviour for ordinary batches
// with no custom types: every tx is routed and its subpool error returned in order, no ErrTxTypeNotSupported.
func TestTxPoolAddNonCustomBatchUnchanged(t *testing.T) {
	errLegacy := errors.New("legacy-err")
	pool := &TxPool{subpools: []SubPool{
		&addMockSubPool{accept: acceptTypes(types.LegacyTxType), addErr: func(*types.Transaction) error { return errLegacy }},
	}}
	batch := []*types.Transaction{legacyTx(), legacyTx(), legacyTx()}

	var errs []error
	require.NotPanics(t, func() { errs = pool.Add(batch, false) })
	require.Len(t, errs, 3)
	for i := range errs {
		require.Same(t, errLegacy, errs[i], "position %d", i)
		require.False(t, isUnsupported(errs[i]))
	}
}
