// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

// Deep btcTxByTxid bitflag coverage. btcTxByTxid is a bitflag-driven serializer; this exercises every branch
// an hVM contract can observe (hash reversal, field widths, full-vs-stripped size order, unspendable-output
// accounting, the bit6 witness-array-size alias, count/script chopping) against a fixture tx T: two
// distinct-value inputs with distinct scriptSigs/sequences/witness counts, and three outputs including one
// OP_RETURN. A cursor decoder checks the response frame field-by-field.

import (
	"bytes"
	"encoding/binary"
	"testing"

	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/txscript"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/require"
)

// cur is a tiny big-endian cursor reader for decoding precompile response frames field-by-field.
type cur struct {
	t *testing.T
	b []byte
	i int
}

func (c *cur) u16() uint16 {
	c.t.Helper()
	v := binary.BigEndian.Uint16(c.b[c.i : c.i+2])
	c.i += 2
	return v
}
func (c *cur) u32() uint32 {
	c.t.Helper()
	v := binary.BigEndian.Uint32(c.b[c.i : c.i+4])
	c.i += 4
	return v
}
func (c *cur) u64() uint64 {
	c.t.Helper()
	v := binary.BigEndian.Uint64(c.b[c.i : c.i+8])
	c.i += 8
	return v
}
func (c *cur) take(n int) []byte { c.t.Helper(); v := c.b[c.i : c.i+n]; c.i += n; return v }
func (c *cur) end() {
	c.t.Helper()
	require.Equal(c.t, len(c.b), c.i, "no trailing bytes in the frame")
}

func TestSyntheticFullNodeDeepTxByTxidBitflags(t *testing.T) {
	setupSyntheticFullNode(t)

	scriptA, _ := regtestP2PKH(t, 0x42)
	scriptB, _ := regtestP2PKH(t, 0x33)
	scriptD, _ := regtestP2PKH(t, 0x99)
	opReturn, err := txscript.NullDataScript([]byte("hvm"))
	require.NoError(t, err)

	const fund1 = int64(50 * 1e8)
	const fund2 = int64(25 * 1e8)
	const outB = int64(30 * 1e8)
	const change = int64(40 * 1e8)

	genesis := &chaincfg.RegressionNetParams.GenesisBlock.Header
	cb1 := buildRegtestCoinbase(t, 1, scriptA, fund1, 1)
	block1 := mineRegtestBlockWithTxs(t, genesis, []*wire.MsgTx{cb1}, 60_001)
	cb1Txid := cb1.TxHash()
	cb2 := buildRegtestCoinbase(t, 2, scriptA, fund2, 2)
	block2 := mineRegtestBlockWithTxs(t, &block1.Header, []*wire.MsgTx{cb2}, 61_001)
	cb2Txid := cb2.TxHash()

	sig0, wit0, seq0 := bytes.Repeat([]byte{0x51}, 20), wire.TxWitness{{0xaa, 0xbb}, {0xcc}}, uint32(0xfffffffe) // 20-byte sig so the deep script-chop is reachable
	sig1, wit1, seq1 := []byte{0x61, 0x62}, wire.TxWitness{{0x11}, {0x22, 0x23}, {0x33, 0x34, 0x35}}, uint32(0xfffffffd)
	T := wire.NewMsgTx(wire.TxVersion)
	T.AddTxIn(&wire.TxIn{PreviousOutPoint: wire.OutPoint{Hash: cb1Txid, Index: 0}, SignatureScript: sig0, Witness: wit0, Sequence: seq0})
	T.AddTxIn(&wire.TxIn{PreviousOutPoint: wire.OutPoint{Hash: cb2Txid, Index: 0}, SignatureScript: sig1, Witness: wit1, Sequence: seq1})
	T.AddTxOut(&wire.TxOut{Value: outB, PkScript: scriptB})   // output 0: spendable -> B
	T.AddTxOut(&wire.TxOut{Value: 0, PkScript: opReturn})     // output 1: UNSPENDABLE (OP_RETURN)
	T.AddTxOut(&wire.TxOut{Value: change, PkScript: scriptA}) // output 2: spendable -> A
	tTxid := T.TxHash()
	block3 := mineRegtestBlockWithTxs(t, &block2.Header, []*wire.MsgTx{buildRegtestCoinbase(t, 3, scriptD, int64(10*1e8), 3), T}, 62_001)

	h1, h2, h3 := block1.Header, block2.Header, block3.Header
	_, _, _, _, err = TBCFullNode.BlockHeadersInsert(MainCtx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{&h1, &h2, &h3}})
	require.NoError(t, err)
	for _, b := range []*wire.MsgBlock{block1, block2, block3} {
		_, e := TBCFullNode.BlockInsert(MainCtx, b)
		require.NoError(t, e)
	}
	require.NoError(t, TBCFullNode.SyncIndexersToHash(MainCtx, block3.Header.BlockHash()))

	run := func(bf1, bf2, bf3, bf4 byte) *cur {
		t.Helper()
		out, err := (&btcTxByTxid{}).Run(append(reversedHash(tTxid), bf1, bf2, bf3, bf4), common.Hash{})
		require.NoError(t, err)
		return &cur{t: t, b: out}
	}

	// (A) Header fields: includeVersion(0x20)|includeSizes(0x10)|includeLockTime(0x08) -> version, size, strippedSize, lockTime.
	a := run(0x38, 0x00, 0x00, 0x00)
	require.Equal(t, uint32(T.Version), a.u32(), "version")
	require.Equal(t, uint32(T.SerializeSize()), a.u32(), "serialize size (with witness)")
	require.Equal(t, uint32(T.SerializeSizeStripped()), a.u32(), "stripped serialize size (no witness) — must differ from full size")
	require.NotEqual(t, T.SerializeSize(), T.SerializeSizeStripped(), "fixture must be segwit so the two size fields are distinguishable")
	require.Equal(t, T.LockTime, a.u32(), "lock time")
	a.end()

	// (B) Inputs deep: includeInputs(0x04)|includeInputSource(0x02)|includeInputScriptSig(0x01) + includeInputSeq(bf2 0x80),
	//     maxInputs=2 (bf3 0x08), maxInputScriptSigSize=32 (bf4 0x04 -> 2^(4+1) >= the 20-byte sig0, so NO chop here).
	//     Per input: value||revPrevHash||prevIdx(uint32)||sigLen||sig||seq.
	b := run(0x07, 0x80, 0x08, 0x04)
	require.Equal(t, uint16(2), b.u16(), "txInLen")
	for idx, in := range []struct {
		value int64
		prev  chainhash.Hash
		sig   []byte
		seq   uint32
	}{{fund1, cb1Txid, sig0, seq0}, {fund2, cb2Txid, sig1, seq1}} {
		require.Equal(t, uint64(in.value), b.u64(), "input %d value (via source-tx lookup)", idx)
		require.Equal(t, in.prev[:], reverseBytes(b.take(32)), "input %d reversed prev hash", idx)
		require.Equal(t, uint32(0), b.u32(), "input %d prevout index (FULL uint32 in the deep path, vs btcInputByTxid's uint16)", idx)
		sl := b.u16()
		require.Equal(t, uint16(len(in.sig)), sl, "input %d sig len", idx)
		require.Equal(t, in.sig, b.take(int(sl)), "input %d scriptSig", idx)
		require.Equal(t, in.seq, b.u32(), "input %d sequence", idx)
	}
	b.end()

	// (C) bit6 alias: includeContainingBlock(0x40)|includeInputs(0x04). bit6 ALSO enables includeWitnessArraySize, so each
	//     input emits a witness-count word. Frame: revBlockHash(32) || txInLen(2) || per input [witCount(2) || value(8)].
	c := run(0x44, 0x00, 0x08, 0x00)
	block3Hash := block3.Header.BlockHash()
	require.Equal(t, block3Hash[:], reverseBytes(c.take(32)), "containing block hash")
	require.Equal(t, uint16(2), c.u16(), "txInLen")
	require.Equal(t, uint16(len(wit0)), c.u16(), "input 0 witness-array size (bit6 alias)")
	require.Equal(t, uint64(fund1), c.u64(), "input 0 value")
	require.Equal(t, uint16(len(wit1)), c.u16(), "input 1 witness-array size")
	require.Equal(t, uint64(fund2), c.u64(), "input 1 value")
	c.end()

	// (D) Outputs with script, default (EXCLUDE unspendable): includeOutputs(0x20)|includeOutputScript(0x10), maxOutputs=2
	//     (bf3 0x01), maxOutputScriptSize=32 (bf4 0x01 -> 2^(4+1) >= 25). outLen must be 2 (the OP_RETURN is excluded).
	d := run(0x00, 0x30, 0x01, 0x01)
	require.Equal(t, uint16(2), d.u16(), "outLen excludes the unspendable OP_RETURN output")
	for idx, o := range []struct {
		value  int64
		script []byte
	}{{outB, scriptB}, {change, scriptA}} { // out0 and out2; out1 (OP_RETURN) skipped
		require.Equal(t, uint64(o.value), d.u64(), "spendable output %d value", idx)
		sl := d.u16()
		require.Equal(t, uint16(len(o.script)), sl, "spendable output %d pkScript len", idx)
		require.Equal(t, o.script, d.take(int(sl)), "spendable output %d pkScript", idx)
	}
	d.end()

	// (E) Outputs INCLUDING unspendable: add includeUnspendableOutputs(0x08), maxOutputs=4 (bf3 0x02). outLen must be 3
	//     and the OP_RETURN output (value 0) appears in its real position (index 1).
	e := run(0x00, 0x38, 0x02, 0x01)
	require.Equal(t, uint16(3), e.u16(), "outLen INCLUDES the unspendable output")
	for idx, o := range []struct {
		value  int64
		script []byte
	}{{outB, scriptB}, {0, opReturn}, {change, scriptA}} {
		require.Equal(t, uint64(o.value), e.u64(), "output %d value", idx)
		sl := e.u16()
		require.Equal(t, uint16(len(o.script)), sl, "output %d pkScript len", idx)
		require.Equal(t, o.script, e.take(int(sl)), "output %d pkScript", idx)
	}
	e.end()

	// (F) Output COUNT-chop: includeOutputs only, maxOutputs=1 (bf3 0x00). outLen reports the FULL spendable count (2)
	//     while only 1 output entry (value, no script) is emitted.
	f := run(0x00, 0x20, 0x00, 0x00)
	require.Equal(t, uint16(2), f.u16(), "outLen reports the FULL spendable count even though chopped")
	require.Equal(t, uint64(outB), f.u64(), "only the first spendable output is emitted")
	f.end()

	// (G) INPUT script-chop (deep path): includeInputs|includeInputScriptSig (bf1 0x05), maxInputs=2 (bf3 0x08),
	//     maxInputScriptSigSize=16 (bf4 0x00 -> 2^(4+0)). input 0's sig is 20 bytes -> sigLen word reports 20 (FULL)
	//     but only 16 bytes are appended; input 1's 2-byte sig is unchopped. Per input here: value(8)||sigLen(2)||sig.
	g := run(0x05, 0x00, 0x08, 0x00)
	require.Equal(t, uint16(2), g.u16(), "txInLen")
	require.Equal(t, uint64(fund1), g.u64(), "input 0 value")
	require.Equal(t, uint16(len(sig0)), g.u16(), "input 0 sigLen word reports the FULL 20-byte length")
	require.Equal(t, sig0[:16], g.take(16), "input 0 emits only maxInputScriptSigSize(16) chopped bytes")
	require.Equal(t, uint64(fund2), g.u64(), "input 1 value")
	require.Equal(t, uint16(len(sig1)), g.u16(), "input 1 sigLen word (unchopped, 2 bytes)")
	require.Equal(t, sig1, g.take(len(sig1)), "input 1 full sig (under the cap)")
	g.end()

	// (H) OUTPUT script-chop (deep path): includeOutputs|includeOutputScript (bf2 0x30), maxOutputs=2 (bf3 0x01),
	//     maxOutputScriptSize=16 (bf4 0x00). The 25-byte P2PKH pkScript -> pkScriptLen word reports 25 (FULL) but only
	//     16 bytes appended. Per output: value(8)||pkScriptLen(2)||script.
	h := run(0x00, 0x30, 0x01, 0x00)
	require.Equal(t, uint16(2), h.u16(), "outLen (spendable)")
	require.Equal(t, uint64(outB), h.u64(), "output 0 value")
	require.Equal(t, uint16(len(scriptB)), h.u16(), "output 0 pkScriptLen word reports the FULL 25-byte length")
	require.Equal(t, scriptB[:16], h.take(16), "output 0 emits only maxOutputScriptSize(16) chopped bytes")
	require.Equal(t, uint64(change), h.u64(), "output 1 (A change) value")
	require.Equal(t, uint16(len(scriptA)), h.u16(), "output 1 pkScriptLen word (FULL)")
	require.Equal(t, scriptA[:16], h.take(16), "output 1 emits only 16 chopped bytes")
	h.end()
}
