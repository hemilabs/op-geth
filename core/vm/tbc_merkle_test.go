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

package vm

import (
	"testing"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"
)

// makeBTCTx builds a distinct, serialize-valid transaction. Varying `seed` changes the input outpoint,
// signature script, and output script, so every tx has a unique txid (distinct merkle leaves). When
// `withWitness` is set it attaches a witness stack, so TxHash() (the txid, witness-excluded) and
// WitnessHash() differ — used to prove the gate binds the header's txid root, not the witness root.
func makeBTCTx(seed byte, withWitness bool) *wire.MsgTx {
	tx := wire.NewMsgTx(wire.TxVersion)
	in := &wire.TxIn{
		PreviousOutPoint: wire.OutPoint{Hash: chainhash.Hash{seed, seed ^ 0xff}, Index: uint32(seed)},
		SignatureScript:  []byte{0x6a, seed, seed ^ 0x5a},
		Sequence:         0xffffffff,
	}
	if withWitness {
		in.Witness = wire.TxWitness{{0x01, seed}, {0x02, seed, 0x03}}
	}
	tx.AddTxIn(in)
	tx.AddTxOut(&wire.TxOut{Value: 5_000_000_000 - int64(seed), PkScript: []byte{0x76, 0xa9, seed}})
	return tx
}

// independentMerkleRoot computes the txid merkle root without the production blockchain.CalcMerkleRoot,
// so an "accept" assertion is not circular. It re-implements Bitcoin's algorithm directly: leaves are
// txids; each level pairs adjacent nodes (duplicating the last node when the count is odd — the rule
// underlying CVE-2012-2459), double-SHA256s the 64-byte concatenation, and a single node is its own
// root. An empty list yields the zero hash (never exercised by the gate, which rejects empties first).
func independentMerkleRoot(txs []*wire.MsgTx) chainhash.Hash {
	if len(txs) == 0 {
		return chainhash.Hash{}
	}
	level := make([]chainhash.Hash, len(txs))
	for i, tx := range txs {
		level[i] = tx.TxHash()
	}
	for len(level) > 1 {
		if len(level)%2 == 1 {
			level = append(level, level[len(level)-1]) // duplicate the trailing node
		}
		next := make([]chainhash.Hash, 0, len(level)/2)
		for i := 0; i < len(level); i += 2 {
			var buf [chainhash.HashSize * 2]byte
			copy(buf[:chainhash.HashSize], level[i][:])
			copy(buf[chainhash.HashSize:], level[i+1][:])
			next = append(next, chainhash.DoubleHashH(buf[:]))
		}
		level = next
	}
	return level[0]
}

// blockWithRoot builds a MsgBlock from txs and an explicit committed merkle root, so a test can supply
// the genuine root, a corrupted one, or a deliberately wrong one independent of the body.
func blockWithRoot(root chainhash.Hash, txs ...*wire.MsgTx) *wire.MsgBlock {
	return &wire.MsgBlock{
		Header:       wire.BlockHeader{Version: 1, MerkleRoot: root},
		Transactions: txs,
	}
}

func TestCheckBTCBlockMerkleRoot(t *testing.T) {
	// A set of distinct (unique-txid) transactions reused across cases. `c` plays the coinbase (leaf 0).
	c := makeBTCTx(0, false)
	t1 := makeBTCTx(1, false)
	t2 := makeBTCTx(2, false)
	t3 := makeBTCTx(3, false)
	t4 := makeBTCTx(4, false)
	t5 := makeBTCTx(5, false)
	t6 := makeBTCTx(6, false)

	t.Run("single tx: root is the coinbase txid, accepts", func(t *testing.T) {
		txid := c.TxHash()
		// Independent cross-check: a 1-tx merkle root IS that tx's txid.
		require.Equal(t, txid, independentMerkleRoot([]*wire.MsgTx{c}))
		require.NoError(t, CheckBTCBlockMerkleRoot(blockWithRoot(txid, c)))
	})

	t.Run("even tx count accepts (independently computed root)", func(t *testing.T) {
		txs := []*wire.MsgTx{c, t1, t2, t3}
		require.NoError(t, CheckBTCBlockMerkleRoot(blockWithRoot(independentMerkleRoot(txs), txs...)))
	})

	t.Run("odd tx count accepts (trailing-node duplication path)", func(t *testing.T) {
		txs := []*wire.MsgTx{c, t1, t2}
		require.NoError(t, CheckBTCBlockMerkleRoot(blockWithRoot(independentMerkleRoot(txs), txs...)))
	})

	t.Run("multi-level odd counts accept (7 txs)", func(t *testing.T) {
		txs := []*wire.MsgTx{c, t1, t2, t3, t4, t5, t6}
		require.NoError(t, CheckBTCBlockMerkleRoot(blockWithRoot(independentMerkleRoot(txs), txs...)))
	})

	t.Run("zeroed committed root rejected", func(t *testing.T) {
		txs := []*wire.MsgTx{c, t1}
		require.ErrorIs(t, CheckBTCBlockMerkleRoot(blockWithRoot(chainhash.Hash{}, txs...)), ErrBTCBlockMerkleMismatch)
	})

	t.Run("one-bit-flipped committed root rejected", func(t *testing.T) {
		txs := []*wire.MsgTx{c, t1, t2}
		root := independentMerkleRoot(txs)
		root[0] ^= 0x01
		require.ErrorIs(t, CheckBTCBlockMerkleRoot(blockWithRoot(root, txs...)), ErrBTCBlockMerkleMismatch)
	})

	t.Run("substituted transaction rejected", func(t *testing.T) {
		// Substitution: a peer keeps a real header (its genuine committed root) but swaps a transaction in
		// the body. Changing any tx changes its txid and therefore the root, so the genuine header no longer
		// matches the body.
		genuine := []*wire.MsgTx{c, t1, t2, t3}
		realRoot := independentMerkleRoot(genuine)
		substituted := []*wire.MsgTx{c, t1, makeBTCTx(0x99, false), t3} // t2 -> substituted tx
		require.ErrorIs(t, CheckBTCBlockMerkleRoot(blockWithRoot(realRoot, substituted...)), ErrBTCBlockMerkleMismatch,
			"a body with a substituted transaction must not validate against the genuine header root")
		// Control: the genuine body validates against the same root, so the rejection above is the swap,
		// not an incidentally wrong root.
		require.NoError(t, CheckBTCBlockMerkleRoot(blockWithRoot(realRoot, genuine...)))
	})

	t.Run("appended transaction rejected", func(t *testing.T) {
		genuine := []*wire.MsgTx{c, t1}
		require.ErrorIs(t, CheckBTCBlockMerkleRoot(blockWithRoot(independentMerkleRoot(genuine), c, t1, t2)), ErrBTCBlockMerkleMismatch)
	})

	t.Run("dropped transaction rejected", func(t *testing.T) {
		genuine := []*wire.MsgTx{c, t1, t2}
		require.ErrorIs(t, CheckBTCBlockMerkleRoot(blockWithRoot(independentMerkleRoot(genuine), c, t1)), ErrBTCBlockMerkleMismatch)
	})

	t.Run("reordered transactions rejected", func(t *testing.T) {
		genuine := []*wire.MsgTx{c, t1, t2, t3}
		require.ErrorIs(t, CheckBTCBlockMerkleRoot(blockWithRoot(independentMerkleRoot(genuine), c, t2, t1, t3)), ErrBTCBlockMerkleMismatch,
			"swapping two transactions changes the root")
	})

	t.Run("witness block: header commits the TXID root; the gate uses the non-witness root", func(t *testing.T) {
		w0 := makeBTCTx(10, true)
		w1 := makeBTCTx(11, true)
		w2 := makeBTCTx(12, true)
		require.True(t, w1.HasWitness(), "test tx must carry witness data")
		txs := []*wire.MsgTx{w0, w1, w2}
		txidRoot := independentMerkleRoot(txs) // txid-based, witness excluded
		require.NoError(t, CheckBTCBlockMerkleRoot(blockWithRoot(txidRoot, txs...)),
			"a segwit block must validate against its txid merkle root")
		// The witness root differs from the txid root, so had the gate computed witness=true it would fail.
		// This pins that CheckBTCBlockMerkleRoot computes the non-witness (header-committed) root.
		witnessRoot := blockchain.CalcMerkleRoot(btcutil.NewBlock(blockWithRoot(txidRoot, txs...)).Transactions(), true)
		require.NotEqual(t, txidRoot, witnessRoot, "witness/txid roots must differ for a segwit block (else the assertion is vacuous)")
	})

	t.Run("nil block errors without panic (structural, not a mismatch)", func(t *testing.T) {
		require.NotPanics(t, func() {
			err := CheckBTCBlockMerkleRoot(nil)
			require.Error(t, err)
			require.NotErrorIs(t, err, ErrBTCBlockMerkleMismatch)
		})
	})

	t.Run("empty tx list errors without panic (structural, not a mismatch)", func(t *testing.T) {
		require.NotPanics(t, func() {
			err := CheckBTCBlockMerkleRoot(blockWithRoot(chainhash.Hash{}))
			require.Error(t, err)
			require.NotErrorIs(t, err, ErrBTCBlockMerkleMismatch)
		})
	})

	t.Run("mismatch error names both roots", func(t *testing.T) {
		txs := []*wire.MsgTx{c, t1}
		realRoot := independentMerkleRoot(txs)
		wrong := chainhash.Hash{0xab, 0xcd, 0xef}
		err := CheckBTCBlockMerkleRoot(blockWithRoot(wrong, txs...))
		require.ErrorIs(t, err, ErrBTCBlockMerkleMismatch)
		require.ErrorContains(t, err, wrong.String(), "error must name the header's committed root")
		require.ErrorContains(t, err, realRoot.String(), "error must name the computed root")
	})
}

// TestCheckBTCBlockMerkleRootMatchesProductionCalc cross-checks the independent oracle against btcd's
// blockchain.CalcMerkleRoot for a range of tx counts (including odd counts that exercise trailing-node
// duplication at several levels). If the two disagreed, the "accept" cases above would be meaningless.
func TestCheckBTCBlockMerkleRootMatchesProductionCalc(t *testing.T) {
	for n := 1; n <= 9; n++ {
		txs := make([]*wire.MsgTx, n)
		for i := range txs {
			txs[i] = makeBTCTx(byte(i), false)
		}
		prod := blockchain.CalcMerkleRoot(btcutil.NewBlock(blockWithRoot(chainhash.Hash{}, txs...)).Transactions(), false)
		require.Equal(t, prod, independentMerkleRoot(txs), "oracle must match btcd CalcMerkleRoot for n=%d", n)
	}
}

// TestCheckBTCBlockMerkleRootRejectsDuplicateTail pins the CVE-2012-2459 defense: Bitcoin's merkle
// algorithm duplicates the trailing node of an odd level, so a body that explicitly repeats its last
// transaction computes the SAME root as the genuine block — it passes the root binding, so the gate must
// additionally reject duplicate transactions (a repeated transaction is consensus-invalid and must be
// rejected).
func TestCheckBTCBlockMerkleRootRejectsDuplicateTail(t *testing.T) {
	c := makeBTCTx(0, false)
	t1 := makeBTCTx(1, false)
	t2 := makeBTCTx(2, false)

	genuine := []*wire.MsgTx{c, t1, t2}     // odd -> Bitcoin pads to [c,t1,t2,t2]
	mutated := []*wire.MsgTx{c, t1, t2, t2} // a body explicitly repeats the trailing tx

	root := independentMerkleRoot(genuine)
	require.Equal(t, root, independentMerkleRoot(mutated),
		"a duplicated-tail block collides on the root (the CVE-2012-2459 precondition)")
	// The collided root would pass the binding, so the duplicate-tx guard must catch it.
	require.ErrorIs(t, CheckBTCBlockMerkleRoot(blockWithRoot(root, mutated...)), ErrBTCBlockDuplicateTx,
		"a duplicated-tail body must be rejected even though its root collides with the genuine block")
	// The genuine (non-duplicated) body still passes against the same root.
	require.NoError(t, CheckBTCBlockMerkleRoot(blockWithRoot(root, genuine...)))
}

// TestCheckBTCBlockMerkleRootRejectsDuplicateTx covers a plain repeated transaction anywhere in the body.
func TestCheckBTCBlockMerkleRootRejectsDuplicateTx(t *testing.T) {
	c := makeBTCTx(0, false)
	t1 := makeBTCTx(1, false)
	dup := []*wire.MsgTx{c, t1, t1} // t1 repeated
	// Commit the body's own (production-computed) root so the ONLY failure is the duplicate, not a mismatch.
	root := blockchain.CalcMerkleRoot(btcutil.NewBlock(blockWithRoot(chainhash.Hash{}, dup...)).Transactions(), false)
	require.ErrorIs(t, CheckBTCBlockMerkleRoot(blockWithRoot(root, dup...)), ErrBTCBlockDuplicateTx)
}
