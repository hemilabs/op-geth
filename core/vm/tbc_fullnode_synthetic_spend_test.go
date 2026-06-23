// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

// Multi-tx / spend: this covers the precompiles that read SPEND data — btcInputByTxid (0x47),
// btcTxGetInputWitness (0x49), btcOutputByTxid (0x48) — and the spent/unspent status path, which the coinbase-only
// blocks in the sibling synthetic tests do not reach. This file mines a 2-block regtest chain where block 2 contains
// a real transaction that spends block 1's coinbase output (with an arbitrary scriptSig and a 2-element witness; the
// full node does no script validation on BlockInsert, so unsigned spends index fine), producing the input-value
// lookups, witness elements, output scripts, and spent/unspent transitions those precompiles serialize.
//
// It also covers the deep btcTxByTxid includeInputs branch (the inline per-input value lookup via the source tx),
// which the coinbase-only test could not reach.

import (
	"encoding/binary"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/txscript"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

// buildRegtestCoinbase builds a BIP34 coinbase tx paying `value` to `pkScript`.
func buildRegtestCoinbase(t *testing.T, bip34Height int32, pkScript []byte, value int64, extraNonce uint32) *wire.MsgTx {
	t.Helper()
	cb := wire.NewMsgTx(wire.TxVersion)
	sig, err := txscript.NewScriptBuilder().AddInt64(int64(bip34Height)).AddInt64(int64(extraNonce)).Script()
	require.NoError(t, err)
	cb.AddTxIn(&wire.TxIn{
		PreviousOutPoint: wire.OutPoint{Hash: chainhash.Hash{}, Index: 0xffffffff},
		SignatureScript:  sig,
		Sequence:         0xffffffff,
	})
	cb.AddTxOut(&wire.TxOut{Value: value, PkScript: pkScript})
	return cb
}

// mineRegtestBlockWithTxs assembles a regtest block over prev containing txs (txs[0] must be the coinbase), with a
// correct merkle root over all txs and a header mined to the regtest PowLimit.
func mineRegtestBlockWithTxs(t *testing.T, prev *wire.BlockHeader, txs []*wire.MsgTx, extraNonce uint32) *wire.MsgBlock {
	t.Helper()
	utxs := make([]*btcutil.Tx, len(txs))
	for i, tx := range txs {
		utxs[i] = btcutil.NewTx(tx)
	}
	merkles := blockchain.BuildMerkleTreeStore(utxs, false)
	merkleRoot := merkles[len(merkles)-1]

	hdr := wire.BlockHeader{
		Version:    4,
		PrevBlock:  prev.BlockHash(),
		MerkleRoot: *merkleRoot,
		Timestamp:  prev.Timestamp.Add(60 * time.Second),
		Bits:       syntheticRegtestPowBits,
	}
	target := blockchain.CompactToBig(hdr.Bits)
	mined := false
	for i := uint32(0); i < 1<<22; i++ {
		hdr.Nonce = extraNonce + i
		hh := hdr.BlockHash()
		if blockchain.HashToBig(&hh).Cmp(target) <= 0 {
			mined = true
			break
		}
	}
	require.True(t, mined, "must mine a regtest block within 2^22 nonces")
	return &wire.MsgBlock{Header: hdr, Transactions: txs}
}

// reversedHash returns the display-order (little-endian) byte form the precompiles take as txid input.
func reversedHash(h chainhash.Hash) []byte {
	b := make([]byte, 32)
	copy(b, h[:])
	for i, j := 0, 31; i < j; i, j = i+1, j-1 {
		b[i], b[j] = b[j], b[i]
	}
	return b
}

// TestSyntheticFullNodeSpendPrecompiles builds genesis->b1(cb1=50 BTC ->A)->b2(cb2=25 BTC ->A)->b3([cb3->D, T]) where
// T spends BOTH cb1 and cb2 (two inputs with DISTINCT values/scriptSigs/sequences/witness-element-counts) and pays B
// (out0) and A-change (out1, a DISTINCT value). The two distinct-value inputs/outputs make every per-index precompile
// query discriminating: a regression that ignores the requested input/output index and returns a fixed one is caught.
// (cb1 in b1 and cb2 in b2 are both PRIOR blocks, so T never spends within its own block — avoids same-block-spend
// indexer corner cases.)
func TestSyntheticFullNodeSpendPrecompiles(t *testing.T) {
	setupSyntheticFullNode(t)

	scriptA, addrA := regtestP2PKH(t, 0x42)
	scriptB, addrB := regtestP2PKH(t, 0x33)
	scriptD, _ := regtestP2PKH(t, 0x99) // cb3 sink — keeps A's balance equal to the change output alone
	const fund1 = int64(50 * 1e8)       // cb1
	const fund2 = int64(25 * 1e8)       // cb2 — DISTINCT from cb1 so balance proves WHICH coinbase was excluded
	const outB = int64(30 * 1e8)        // T out0 -> B
	const change = int64(40 * 1e8)      // T out1 -> A  (in 75, out 70, fee 5)

	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header

	cb1 := buildRegtestCoinbase(t, 1, scriptA, fund1, 1)
	block1 := mineRegtestBlockWithTxs(t, genesis, []*wire.MsgTx{cb1}, 1_001)
	cb1Txid := cb1.TxHash()

	cb2 := buildRegtestCoinbase(t, 2, scriptA, fund2, 2)
	block2 := mineRegtestBlockWithTxs(t, &block1.Header, []*wire.MsgTx{cb2}, 2_001)
	cb2Txid := cb2.TxHash()

	// T (in block 3) spends cb1 (input 0) and cb2 (input 1) with deliberately distinct per-input data.
	sig0, wit0, seq0 := []byte{0x51, 0x52, 0x53}, wire.TxWitness{{0xaa, 0xbb}, {0xcc}}, uint32(0xfffffffe)               // 2 witness items
	sig1, wit1, seq1 := []byte{0x61, 0x62}, wire.TxWitness{{0x11}, {0x22, 0x23}, {0x33, 0x34, 0x35}}, uint32(0xfffffffd) // 3 witness items
	spend := wire.NewMsgTx(wire.TxVersion)
	spend.AddTxIn(&wire.TxIn{PreviousOutPoint: wire.OutPoint{Hash: cb1Txid, Index: 0}, SignatureScript: sig0, Witness: wit0, Sequence: seq0})
	spend.AddTxIn(&wire.TxIn{PreviousOutPoint: wire.OutPoint{Hash: cb2Txid, Index: 0}, SignatureScript: sig1, Witness: wit1, Sequence: seq1})
	spend.AddTxOut(&wire.TxOut{Value: outB, PkScript: scriptB})   // output 0 -> B
	spend.AddTxOut(&wire.TxOut{Value: change, PkScript: scriptA}) // output 1 -> A (change)
	spendTxid := spend.TxHash()
	cb3 := buildRegtestCoinbase(t, 3, scriptD, int64(10*1e8), 3)
	block3 := mineRegtestBlockWithTxs(t, &block2.Header, []*wire.MsgTx{cb3, spend}, 3_001)

	h1, h2, h3 := block1.Header, block2.Header, block3.Header
	_, _, _, count, err := TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&h1, &h2, &h3}})
	require.NoError(t, err)
	require.Equal(t, 3, count)
	for _, b := range []*wire.MsgBlock{block1, block2, block3} {
		_, err = TBCFullNode.BlockInsert(MainCtx, b)
		require.NoError(t, err)
	}
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, block3.Header.BlockHash()))

	// btcInputByTxid framing: witnessCount(2)||value(8)||reversedPrevHash(32)||prevIdx(2)||sigLen(2)||sig||seq(4).
	// Asserted for BOTH inputs; the distinct witnessCount/value/prevHash/sig/seq per input prove index selection.
	assertInput := func(inputIdx uint16, wantWitCount int, wantValue int64, wantPrev chainhash.Hash, wantSig []byte, wantSeq uint32) {
		t.Helper()
		in := append(reversedHash(spendTxid), byte(inputIdx>>8), byte(inputIdx), 0x03, 0xE8 /*maxSigScriptSize=1000*/)
		out, err := (&btcInputByTxid{}).Run(in, common.Hash{})
		require.NoError(t, err)
		require.Equal(t, uint16(wantWitCount), binary.BigEndian.Uint16(out[0:2]), "input %d witness count", inputIdx)
		require.Equal(t, uint64(wantValue), binary.BigEndian.Uint64(out[2:10]), "input %d spent-output value", inputIdx)
		require.Equal(t, wantPrev[:], reverseBytes(out[10:42]), "input %d prev txid", inputIdx)
		// NB (documented, intentional per current ABI): btcInputByTxid emits the prevout index as a CLAMPED uint16
		// (2 bytes), whereas the deep btcTxByTxid includeInputSource branch emits the full uint32. The two precompiles
		// therefore disagree on this field's width, and an index >= 65536 (e.g. a coinbase input's 0xFFFFFFFF) would be
		// truncated to 0xFFFF here. We pin the 2-byte form as the frozen wire layout. In practice the clamp is
		// unreachable: real spends use small indices (here 0), and a coinbase input bails earlier (its null source tx
		// is unlookupable), so no fixture can drive a >= 65536 index. Widening would be an ABI change, deliberately not made.
		require.Equal(t, uint16(0), binary.BigEndian.Uint16(out[42:44]), "input %d prev index (2-byte clamped field)", inputIdx)
		sigLen := binary.BigEndian.Uint16(out[44:46])
		require.Equal(t, uint16(len(wantSig)), sigLen, "input %d sig len", inputIdx)
		require.Equal(t, wantSig, out[46:46+sigLen], "input %d scriptSig", inputIdx)
		require.Equal(t, wantSeq, binary.BigEndian.Uint32(out[46+sigLen:46+sigLen+4]), "input %d sequence", inputIdx)
		require.Len(t, out, 2+8+32+2+2+len(wantSig)+4, "input %d total frame length (no trailing junk)", inputIdx)
	}
	assertInput(0, len(wit0), fund1, cb1Txid, sig0, seq0)
	assertInput(1, len(wit1), fund2, cb2Txid, sig1, seq1) // distinct from input 0 in every field -> selection is real

	// btcTxGetInputWitness: each (input, witnessIndex) returns that exact element. Cross both inputs and indices.
	assertWitness := func(inputIdx, witIdx uint16, want []byte) {
		t.Helper()
		wi := append(reversedHash(spendTxid), byte(inputIdx>>8), byte(inputIdx), byte(witIdx>>8), byte(witIdx), 0x00, 0xFF)
		wout, err := (&btcTxGetInputWitness{}).Run(wi, common.Hash{})
		require.NoError(t, err)
		require.Equal(t, uint16(len(want)), binary.BigEndian.Uint16(wout[0:2]), "in %d wit %d len", inputIdx, witIdx)
		require.Equal(t, want, wout[2:], "in %d wit %d bytes", inputIdx, witIdx)
		require.Len(t, wout, 2+len(want), "in %d wit %d total frame length", inputIdx, witIdx)
	}
	assertWitness(0, 0, wit0[0])
	assertWitness(0, 1, wit0[1])
	assertWitness(1, 0, wit1[0])
	assertWitness(1, 2, wit1[2]) // selecting input 1 + a high witness index proves both indices are honored

	// Witness index AT the exact boundary (== len) must return (nil,nil) — pins the `>=` guard (a `>` mutation would
	// pass index-past-end but panic at index==len). Probe the boundary for both inputs (lengths 2 and 3).
	for _, bc := range []struct{ in, wi uint16 }{{0, 2}, {1, 3}} {
		probe := append(reversedHash(spendTxid), byte(bc.in>>8), byte(bc.in), byte(bc.wi>>8), byte(bc.wi), 0x00, 0xFF)
		miss, err := (&btcTxGetInputWitness{}).Run(probe, common.Hash{})
		require.NoError(t, err)
		require.Nil(t, miss, "witness index == len (input %d, idx %d) must return (nil,nil)", bc.in, bc.wi)
	}

	// btcOutputByTxid: value(8)||pkScriptLen(2)||pkScript||spent(1). Query BOTH unspent outputs (distinct value+script
	// per index proves output selection). NB the trailing byte mirrors ScriptHashAvailableToSpend (true=UNSPENT),
	// so an UNSPENT output reports 1 — inverse of the field name; we pin actual behavior.
	assertOutput := func(outIdx uint16, wantValue int64, wantScript []byte) {
		t.Helper()
		oin := append(reversedHash(spendTxid), byte(outIdx>>8), byte(outIdx), 0x01, 0x00 /*maxOutScriptSize=256*/)
		o, err := (&btcOutputByTxid{}).Run(oin, common.Hash{})
		require.NoError(t, err)
		require.Equal(t, uint64(wantValue), binary.BigEndian.Uint64(o[0:8]), "output %d value", outIdx)
		pkLen := binary.BigEndian.Uint16(o[8:10])
		require.Equal(t, wantScript, o[10:10+pkLen], "output %d pkScript", outIdx)
		require.Equal(t, byte(1), o[10+pkLen], "output %d is unspent -> available-to-spend byte 1", outIdx)
		require.Len(t, o, 8+2+len(wantScript)+1, "output %d total frame length (no trailing junk)", outIdx)
	}
	assertOutput(0, outB, scriptB)
	assertOutput(1, change, scriptA) // distinct value + script from output 0

	// DISCOVERED LIMITATION (KNOWN): btcOutputByTxid returns (nil,nil) for a SPENT output, because
	// ScriptHashAvailableToSpend maps a not-found (spent) outpoint to (false, <leveldb error>) rather than (false,nil)
	// and btcOutputByTxid bails on the error before emitting the spent byte. Both cb1 and cb2 were spent by T.
	for _, spent := range []chainhash.Hash{cb1Txid, cb2Txid} {
		c, err := (&btcOutputByTxid{}).Run(append(reversedHash(spent), 0x00, 0x00, 0x01, 0x00), common.Hash{})
		require.NoError(t, err)
		require.Nil(t, c, "btcOutputByTxid returns nil for a spent output")
	}

	// deep btcTxByTxid includeInputs (bitflag1 bit2; bitflag3 maxInputsExp=1 -> maxInputs=2): txInLen(2)||value(8)*2.
	dIn, err := (&btcTxByTxid{}).Run(append(reversedHash(spendTxid), 0x04, 0x00, 0x08, 0x00), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(2), binary.BigEndian.Uint16(dIn[0:2]), "T has two inputs")
	require.Equal(t, uint64(fund1), binary.BigEndian.Uint64(dIn[2:10]), "deep input 0 value (cb1)")
	require.Equal(t, uint64(fund2), binary.BigEndian.Uint64(dIn[10:18]), "deep input 1 value (cb2)")

	// deep btcTxByTxid includeOutputs+includeOutputSpent on the SPENT cb1 -> outLen(2)||value(8)||spent(1). This is the
	// path that DOES surface a spent output (byte 0), unlike btcOutputByTxid above.
	dCb, err := (&btcTxByTxid{}).Run(append(reversedHash(cb1Txid), 0x00, 0x24, 0x00, 0x00), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(1), binary.BigEndian.Uint16(dCb[0:2]), "cb1 has one output")
	require.Equal(t, uint64(fund1), binary.BigEndian.Uint64(dCb[2:10]), "cb1 output value")
	require.Equal(t, byte(0), dCb[10], "the SPENT cb1 output reports available-to-spend byte 0")

	// deep btcTxByTxid includeOutputs+includeOutputSpent on T (2 unspent outputs, maxOutputs=2 via bitflag3=0x01).
	dT, err := (&btcTxByTxid{}).Run(append(reversedHash(spendTxid), 0x00, 0x24, 0x01, 0x00), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(2), binary.BigEndian.Uint16(dT[0:2]), "T has two outputs")
	require.Equal(t, uint64(outB), binary.BigEndian.Uint64(dT[2:10]), "T output 0 value")
	require.Equal(t, byte(1), dT[10], "T output 0 unspent")
	require.Equal(t, uint64(change), binary.BigEndian.Uint64(dT[11:19]), "T output 1 value")
	require.Equal(t, byte(1), dT[19], "T output 1 unspent")

	// Balance cross-check: A holds ONLY the change output (both cb1 AND cb2 were spent by T; cb3 went to D). Because
	// cb1 (50), cb2 (25), and change (40) are all DISTINCT, balA==40 uniquely proves both coinbases were excluded and
	// the change was added — a regression retaining either spent coinbase would yield 90 or 65, not 40.
	balA, err := (&btcBalAddr{}).Run([]byte(addrA), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint64(change), binary.BigEndian.Uint64(balA), "A's balance must be exactly the change output (both spent coinbases excluded)")
	balB, err := (&btcBalAddr{}).Run([]byte(addrB), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint64(outB), binary.BigEndian.Uint64(balB), "B's balance = T's payment output")

	// --- btcUtxosAddrList over a MUTATED (post-spend) UTXO set: the prior coverage only queried append-only coinbase
	//     chains, so per-UTXO identity under spends was unchecked. A's UTXO set must be EXACTLY {T:1 change} (cb1,cb2
	//     spent), and B's exactly {T:0 payment} — by txid+index+value, not just count/balance. ---
	type utxo struct {
		txid chainhash.Hash
		idx  uint16
		val  uint64
	}
	listUtxos := func(addr string) []utxo {
		t.Helper()
		out, err := (&btcUtxosAddrList{}).Run(append([]byte(addr), 0x00, 0x00, 0x00, 100), common.Hash{})
		require.NoError(t, err)
		n := int(out[0])
		us := make([]utxo, 0, n)
		for i := 0; i < n; i++ {
			base := 1 + i*(32+2+8)
			var id chainhash.Hash
			copy(id[:], reverseBytes(out[base:base+32]))
			us = append(us, utxo{id, binary.BigEndian.Uint16(out[base+32 : base+34]), binary.BigEndian.Uint64(out[base+34 : base+42])})
		}
		return us
	}
	require.Equal(t, []utxo{{spendTxid, 1, uint64(change)}}, listUtxos(addrA), "A's only UTXO is T's change output (idx 1); cb1/cb2 are spent and absent")
	require.Equal(t, []utxo{{spendTxid, 0, uint64(outB)}}, listUtxos(addrB), "B's only UTXO is T's payment output (idx 0)")

	// --- CHOPPING / truncation: every prior query used a max larger than the datum, so the chop branches were dead.
	// The contract: the length WORD reports the FULL length while only the CHOPPED bytes are appended, so a caller
	// detects truncation by (declared length) > (appended bytes). Drive each chop with a max SMALLER than the datum. ---

	// btcInputByTxid input 0: sigScript len 3, maxSigScriptSize=2 -> sigLen word=3, only 2 bytes appended, seq follows.
	ci, err := (&btcInputByTxid{}).Run(append(reversedHash(spendTxid), 0x00, 0x00, 0x00, 0x02), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(len(sig0)), binary.BigEndian.Uint16(ci[44:46]), "chopped input: sigLen word must report the FULL length")
	require.Equal(t, sig0[:2], ci[46:48], "chopped input: only maxSigScriptSize bytes appended (the prefix)")
	require.Equal(t, seq0, binary.BigEndian.Uint32(ci[48:52]), "chopped input: sequence follows the CHOPPED script")
	require.Len(t, ci, 2+8+32+2+2+2+4, "chopped input: total length reflects the chopped (2-byte) script")

	// btcOutputByTxid output 0: pkScript len 25 (P2PKH), maxOutScriptSize=10 -> pkLen word=25, only 10 bytes appended.
	co, err := (&btcOutputByTxid{}).Run(append(reversedHash(spendTxid), 0x00, 0x00, 0x00, 0x0A), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(len(scriptB)), binary.BigEndian.Uint16(co[8:10]), "chopped output: pkScriptLen word must report the FULL length")
	require.Equal(t, scriptB[:10], co[10:20], "chopped output: only maxOutputScriptSize bytes appended (the prefix)")
	require.Equal(t, byte(1), co[20], "chopped output: spent byte follows the CHOPPED script")
	require.Len(t, co, 8+2+10+1, "chopped output: total length reflects the chopped (10-byte) script")

	// btcTxGetInputWitness input 0 / witness 0: element len 2, maxWitnessLength=1 -> length word=2, only 1 byte appended.
	cw, err := (&btcTxGetInputWitness{}).Run(append(reversedHash(spendTxid), 0x00, 0x00, 0x00, 0x00, 0x00, 0x01), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(len(wit0[0])), binary.BigEndian.Uint16(cw[0:2]), "chopped witness: length word must report the FULL length")
	require.Equal(t, wit0[0][:1], cw[2:], "chopped witness: only maxWitnessLength bytes appended (the prefix)")

	// --- COUNT chopping: maxInputs smaller than the actual input count. txInLen word reports the FULL count (2) while
	// only maxInputs (1) entries are emitted. bitflag1=includeInputs(0x04), bitflag3=0x00 -> maxInputsExp 0 -> maxInputs 1. ---
	cc, err := (&btcTxByTxid{}).Run(append(reversedHash(spendTxid), 0x04, 0x00, 0x00, 0x00), common.Hash{})
	require.NoError(t, err)
	require.Equal(t, uint16(2), binary.BigEndian.Uint16(cc[0:2]), "count-chop: txInLen word reports the FULL input count (2)")
	require.Len(t, cc, 2+8, "count-chop: only maxInputs(1) input entries are emitted (value only)")
	require.Equal(t, uint64(fund1), binary.BigEndian.Uint64(cc[2:10]), "count-chop: the one emitted entry is input 0")

	// --- Witness-LESS input (the coinbase cb1's input) returns (nil,nil). This pins the BEHAVIOR, not a specific guard:
	//     for an empty witness the explicit `len(Witness)==0` guard and the following `witIdx >= len(Witness)` bound
	//     both return the identical (nil,nil), so neither can be isolated by a test — deleting either still yields nil. ---
	ew, err := (&btcTxGetInputWitness{}).Run(append(reversedHash(cb1Txid), 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF), common.Hash{})
	require.NoError(t, err)
	require.Nil(t, ew, "btcTxGetInputWitness on an input with no witness must return (nil,nil)")
}

// reverseBytes returns a reversed copy of b (helper for asserting display-order hashes).
func reverseBytes(b []byte) []byte {
	out := make([]byte, len(b))
	for i, j := 0, len(b)-1; j >= 0; i, j = i+1, j-1 {
		out[i] = b[j]
	}
	return out
}
