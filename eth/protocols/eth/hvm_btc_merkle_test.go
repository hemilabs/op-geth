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

package eth

// Live-node end-to-end tests for the gossip merkle-root gate. The gate binds a gossiped body to its
// header's committed merkle root before storage, so a body of substituted transactions cannot be
// admitted under a real consensus-chain header hash. These tests stand up a real in-tree TBC full
// node (localnet/regtest, where PoW is trivially easy) and drive the real handleBTCBlocks: a body
// whose transactions do not hash to the header's committed merkle root is dropped, a matching body is
// stored.

import (
	"bytes"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/enode"
	"github.com/hemilabs/heminetwork/database"
	"github.com/stretchr/testify/require"
)

// driveOneBlock serializes a full MsgBlock (header + transactions) and feeds it through the real
// handleBTCBlocks gossip handler. Sibling of driveOneHeader (hvm_btcdiff_enforce_test.go), which
// serializes a header-only (0-tx) block.
func driveOneBlock(t *testing.T, mb *wire.MsgBlock) {
	t.Helper()
	var buf bytes.Buffer
	require.NoError(t, mb.Serialize(&buf))
	bb := common.BitcoinBlock(buf.Bytes())
	pkt := &BTCBlocksPacket{}
	pkt.BTCBlocksResponse = BTCBlocksResponse{&bb}

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	_ = handleBTCBlocks(nil, fakeBTCDecoder{pkt: pkt}, peer)
}

// merkleTestBody returns a single non-empty (coinbase-shaped) transaction. Non-empty so the gate
// reaches the merkle comparison rather than the empty-body guard; the seed makes the txid unique.
func merkleTestBody(seed byte) []*wire.MsgTx {
	tx := wire.NewMsgTx(wire.TxVersion)
	tx.AddTxIn(&wire.TxIn{
		PreviousOutPoint: wire.OutPoint{Hash: chainhash.Hash{}, Index: 0xffffffff},
		SignatureScript:  []byte{seed, 0x00, seed ^ 0xff},
		Sequence:         0xffffffff,
	})
	tx.AddTxOut(&wire.TxOut{Value: 5_000_000_000, PkScript: []byte{0x51, seed}})
	return []*wire.MsgTx{tx}
}

// merkleBodyRoot is the genuine (txid, non-witness) merkle root of a body, via btcd's production calc.
func merkleBodyRoot(txs []*wire.MsgTx) chainhash.Hash {
	return blockchain.CalcMerkleRoot(btcutil.NewBlock(&wire.MsgBlock{Transactions: txs}).Transactions(), false)
}

// mineRegtestChild builds a child of `parent` carrying `txs`, commits the given merkle root (a
// parameter, so callers commit the genuine body root or a deliberately wrong one), and finds a nonce
// whose hash meets the regtest target so PoW passes (regtest PowLimit ~2^255, ~2 tries). The timestamp
// is parent+600s so the contextual difficulty/MTP check passes. The committed root does not affect
// difficulty or PoW, so the header is PoW- and difficulty-valid regardless.
func mineRegtestChild(t *testing.T, parent *wire.BlockHeader, committed chainhash.Hash, txs []*wire.MsgTx) *wire.MsgBlock {
	t.Helper()
	mb := &wire.MsgBlock{
		Header: wire.BlockHeader{
			Version:    4,
			PrevBlock:  parent.BlockHash(),
			MerkleRoot: committed,
			Timestamp:  parent.Timestamp.Add(600 * time.Second),
			Bits:       parent.Bits,
		},
		Transactions: txs,
	}
	target := blockchain.CompactToBig(mb.Header.Bits)
	for i := uint32(0); i < 1<<22; i++ {
		mb.Header.Nonce = i
		hash := mb.Header.BlockHash()
		if blockchain.HashToBig(&hash).Cmp(target) <= 0 {
			return mb
		}
	}
	t.Fatal("failed to mine a regtest child within 2^22 nonces (should take ~2)")
	return nil
}

// TestGossipMerkleRootDropEndToEnd is the live-node composition test for the merkle gate. The header's
// body does not hash to its committed merkle root, but is otherwise fully valid: correct regtest
// difficulty, good post-genesis timestamp, parent present, PoW-meeting nonce. Absent the gate it would
// pass the PoW + contextual-difficulty gates, the header would insert and the body would store unchecked
// — the substitution. The
// drop is pinned by the dedicated counter (only this gate increments hvmBTCGossipMerkleReject);
// body-absence corroborates, and header-presence proves the drop is the body-stage merkle gate, not an
// incidental header failure.
func TestGossipMerkleRootDropEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("live TBC full-node integration test; skipped in -short")
	}
	ctx := setupLocalnetFullNode(t)
	genesis := chaincfg.RegressionNetParams.GenesisBlock.Header

	body := merkleTestBody(0x11)
	// Commit a wrong root: the genuine body root with one byte flipped.
	wrong := merkleBodyRoot(body)
	wrong[0] ^= 0x01
	blk := mineRegtestChild(t, &genesis, wrong, body)
	hash := blk.Header.BlockHash()

	// Preconditions isolating the merkle drop: PoW passes, contextual difficulty passes, and the only
	// failing check is the merkle binding. CheckBTCHeaderPoW returns nil on a mined header, which the
	// gossip gate treats as do-not-drop.
	require.NoError(t, vm.CheckBTCHeaderPoW(&blk.Header), "mined header must PASS the PoW gate")
	require.NoError(t, vm.ValidateBTCHeaderContext(&blk.Header), "header must PASS the contextual-difficulty check")
	require.ErrorIs(t, vm.CheckBTCBlockMerkleRoot(blk), vm.ErrBTCBlockMerkleMismatch, "the body must FAIL the merkle gate")

	before := hvmBTCGossipMerkleReject.Snapshot().Count()
	driveOneBlock(t, blk)
	require.Equal(t, before+1, hvmBTCGossipMerkleReject.Snapshot().Count(),
		"the gossip merkle gate must increment its dedicated reject counter exactly once")

	// The body must not be stored (the substituted body is blocked).
	avail, err := vm.TBCFullNode.FullBlockAvailable(ctx, hash)
	require.NoError(t, err)
	require.False(t, avail, "a merkle-mismatched body must NOT be stored")
	_, err = vm.TBCFullNode.BlockByHash(ctx, hash)
	var bnfe database.BlockNotFoundError
	require.ErrorAs(t, err, &bnfe, "the body lookup must return BlockNotFound (body dropped)")

	// The header was inserted (it is PoW/difficulty-valid), proving the drop is the body-stage merkle
	// gate, not an incidental header-stage failure masking a bypassed gate.
	_, _, err = vm.TBCFullNode.BlockHeaderByHash(ctx, hash)
	require.NoError(t, err, "the PoW/difficulty-valid header must have been inserted; only the body is dropped")
}

// TestGossipMerkleRootAcceptEndToEnd is the control: a body that does hash to the header's committed
// merkle root passes the gate, the reject counter does not move, and the body is stored. Proves the
// gate raises no false positive on a genuine body and that the gated path reaches the body store.
func TestGossipMerkleRootAcceptEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("live TBC full-node integration test; skipped in -short")
	}
	ctx := setupLocalnetFullNode(t)
	genesis := chaincfg.RegressionNetParams.GenesisBlock.Header

	body := merkleTestBody(0x22)
	blk := mineRegtestChild(t, &genesis, merkleBodyRoot(body), body) // commit the genuine root
	hash := blk.Header.BlockHash()

	require.NoError(t, vm.CheckBTCHeaderPoW(&blk.Header))
	require.NoError(t, vm.ValidateBTCHeaderContext(&blk.Header))
	require.NoError(t, vm.CheckBTCBlockMerkleRoot(blk), "a genuine body must PASS the merkle gate")

	before := hvmBTCGossipMerkleReject.Snapshot().Count()
	driveOneBlock(t, blk)
	require.Equal(t, before, hvmBTCGossipMerkleReject.Snapshot().Count(),
		"a matching body must NOT increment the merkle reject counter")

	avail, err := vm.TBCFullNode.FullBlockAvailable(ctx, hash)
	require.NoError(t, err)
	require.True(t, avail, "a body matching its header's merkle root must be stored")

	// Read the stored body back (not just its key) and confirm it decodes to the driven block, guarding
	// against a store refactor where existence and the stored bytes could diverge.
	got, err := vm.TBCFullNode.BlockByHash(ctx, hash)
	require.NoError(t, err, "the stored body must be retrievable")
	require.Equal(t, hash, *got.Hash(), "the stored body must decode back to the driven block hash")
	require.Len(t, got.Transactions(), len(body), "the stored body must have the driven transaction set")
}

// merkleTestBodyN returns n distinct (unique-txid) transactions, for multi-transaction body shapes.
func merkleTestBodyN(base byte, n int) []*wire.MsgTx {
	txs := make([]*wire.MsgTx, n)
	for i := 0; i < n; i++ {
		txs[i] = merkleTestBody(base + byte(i))[0]
	}
	return txs
}

// merkleWitnessBody returns a 2-tx body whose first input carries witness data, so the block serializes
// with the segwit marker. The header still commits the txid (witness-excluded) root, so a correct gate
// (witness=false) accepts it, exercising the witness-aware wire round-trip (Serialize/Deserialize)
// end-to-end.
func merkleWitnessBody() []*wire.MsgTx {
	w := wire.NewMsgTx(wire.TxVersion)
	w.AddTxIn(&wire.TxIn{
		PreviousOutPoint: wire.OutPoint{Hash: chainhash.Hash{0x77}, Index: 0},
		SignatureScript:  []byte{0x01, 0x77},
		Witness:          wire.TxWitness{{0xaa, 0xbb}, {0xcc, 0xdd, 0xee}},
		Sequence:         0xffffffff,
	})
	w.AddTxOut(&wire.TxOut{Value: 1234, PkScript: []byte{0x51}})
	return []*wire.MsgTx{w, merkleTestBody(0x78)[0]}
}

// driveBlocks feeds multiple MsgBlocks in a single BtcBlocks message through the real handleBTCBlocks,
// exercising the per-entry loop and the merkle drop's `continue` semantics. Sibling of driveOneBlock.
func driveBlocks(t *testing.T, blocks ...*wire.MsgBlock) {
	t.Helper()
	resp := make(BTCBlocksResponse, 0, len(blocks))
	for _, mb := range blocks {
		var buf bytes.Buffer
		require.NoError(t, mb.Serialize(&buf))
		bb := common.BitcoinBlock(buf.Bytes())
		resp = append(resp, &bb)
	}
	pkt := &BTCBlocksPacket{}
	pkt.BTCBlocksResponse = resp

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	_ = handleBTCBlocks(nil, fakeBTCDecoder{pkt: pkt}, peer)
}

// TestGossipMerkleRootReusedGenuineHeaderSubstitutedBodyEndToEnd is the literal body-substitution scenario
// (stronger than the fabricated-header drop test): take a genuine header committing the real merkle
// root R, then gossip a msgBlock reusing that exact header (same hash) with a substituted body that
// does not hash to R. The gate must drop the substituted body; a follow-up gossip of the genuine body for
// the same hash must heal the slot, proving the substituted body is neither stored nor blocks re-fetch of the genuine body.
func TestGossipMerkleRootReusedGenuineHeaderSubstitutedBodyEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("live TBC full-node integration test; skipped in -short")
	}
	ctx := setupLocalnetFullNode(t)
	genesis := chaincfg.RegressionNetParams.GenesisBlock.Header

	genuineBody := merkleTestBody(0x33)
	genuine := mineRegtestChild(t, &genesis, merkleBodyRoot(genuineBody), genuineBody)
	hash := genuine.Header.BlockHash()

	// The substituted block reuses the genuine header (committing the real root) but swaps the body.
	substituted := &wire.MsgBlock{Header: genuine.Header, Transactions: merkleTestBody(0x44)}
	require.Equal(t, hash, substituted.Header.BlockHash(), "the substituted block must reuse the genuine header hash")
	require.NoError(t, vm.CheckBTCHeaderPoW(&substituted.Header))
	require.NoError(t, vm.ValidateBTCHeaderContext(&substituted.Header))
	require.ErrorIs(t, vm.CheckBTCBlockMerkleRoot(substituted), vm.ErrBTCBlockMerkleMismatch, "substituted body must fail the gate")
	require.NoError(t, vm.CheckBTCBlockMerkleRoot(genuine), "the genuine body must pass the gate")

	before := hvmBTCGossipMerkleReject.Snapshot().Count()
	driveOneBlock(t, substituted)
	require.Equal(t, before+1, hvmBTCGossipMerkleReject.Snapshot().Count(), "the substituted body must be rejected once")

	avail, err := vm.TBCFullNode.FullBlockAvailable(ctx, hash)
	require.NoError(t, err)
	require.False(t, avail, "a substituted body under a genuine header hash must NOT be stored")
	_, _, err = vm.TBCFullNode.BlockHeaderByHash(ctx, hash)
	require.NoError(t, err, "the genuine header itself remains present")

	// Heal: the genuine body for the same header hash is still accepted afterward (neither stored under a
	// stale entry nor blocked from re-fetch).
	driveOneBlock(t, genuine)
	avail, err = vm.TBCFullNode.FullBlockAvailable(ctx, hash)
	require.NoError(t, err)
	require.True(t, avail, "after a substitution attempt the genuine body must still heal the slot")
	got, err := vm.TBCFullNode.BlockByHash(ctx, hash)
	require.NoError(t, err)
	require.Equal(t, hash, *got.Hash())
}

// TestGossipMerkleRootMultiTxSubstitutionEndToEnd reuses a genuine multi-transaction header and swaps an
// interior transaction (changing the merkle tree, not just one leaf). Proves the gate's multi-level
// tree computation survives the wire round-trip and rejects an interior-tx substitution.
func TestGossipMerkleRootMultiTxSubstitutionEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("live TBC full-node integration test; skipped in -short")
	}
	ctx := setupLocalnetFullNode(t)
	genesis := chaincfg.RegressionNetParams.GenesisBlock.Header

	genuineBody := merkleTestBodyN(0x50, 5) // 5 txs -> a multi-level tree with odd-level duplication
	genuine := mineRegtestChild(t, &genesis, merkleBodyRoot(genuineBody), genuineBody)
	hash := genuine.Header.BlockHash()

	substitutedTxs := append([]*wire.MsgTx{}, genuineBody...)
	substitutedTxs[2] = merkleTestBody(0x99)[0] // swap an interior tx
	substituted := &wire.MsgBlock{Header: genuine.Header, Transactions: substitutedTxs}
	require.ErrorIs(t, vm.CheckBTCBlockMerkleRoot(substituted), vm.ErrBTCBlockMerkleMismatch)

	before := hvmBTCGossipMerkleReject.Snapshot().Count()
	driveOneBlock(t, substituted)
	require.Equal(t, before+1, hvmBTCGossipMerkleReject.Snapshot().Count())
	avail, err := vm.TBCFullNode.FullBlockAvailable(ctx, hash)
	require.NoError(t, err)
	require.False(t, avail, "an interior-tx-substituted multi-tx body must be dropped")
}

// TestGossipMerkleRootWitnessBodyEndToEnd drives a body carrying witness data (segwit wire encoding)
// whose header commits the txid (non-witness) root. It must be stored, pinning that the gate's
// witness=false computation matches the header through the witness-aware Serialize/Deserialize round-trip.
func TestGossipMerkleRootWitnessBodyEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("live TBC full-node integration test; skipped in -short")
	}
	ctx := setupLocalnetFullNode(t)
	genesis := chaincfg.RegressionNetParams.GenesisBlock.Header

	body := merkleWitnessBody()
	require.True(t, body[0].HasWitness(), "the body must carry witness data to exercise the segwit wire path")
	blk := mineRegtestChild(t, &genesis, merkleBodyRoot(body), body)
	hash := blk.Header.BlockHash()
	require.NoError(t, vm.CheckBTCBlockMerkleRoot(blk), "a segwit body must pass against its TXID root")

	before := hvmBTCGossipMerkleReject.Snapshot().Count()
	driveOneBlock(t, blk)
	require.Equal(t, before, hvmBTCGossipMerkleReject.Snapshot().Count(), "a genuine segwit body must not be rejected")
	avail, err := vm.TBCFullNode.FullBlockAvailable(ctx, hash)
	require.NoError(t, err)
	require.True(t, avail, "a genuine segwit body must be stored")
	got, err := vm.TBCFullNode.BlockByHash(ctx, hash)
	require.NoError(t, err)
	require.Len(t, got.Transactions(), len(body))
}

// TestGossipMerkleRootMultiBlockContinueEndToEnd pins the `continue` contract: a merkle-mismatched block
// at index 0 of a multi-block message must be dropped without aborting a valid block at index 1. The
// good block is chained off the bad block's (PoW/diff-valid) header so both headers insert. Mutating
// the gate's `continue` to `return`/`break` would drop the good body too and fail this test.
func TestGossipMerkleRootMultiBlockContinueEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("live TBC full-node integration test; skipped in -short")
	}
	ctx := setupLocalnetFullNode(t)
	genesis := chaincfg.RegressionNetParams.GenesisBlock.Header

	// Index 0: wrong-root (merkle-mismatched) but PoW/diff-valid child of genesis -> body dropped.
	badBody := merkleTestBody(0x61)
	wrong := merkleBodyRoot(badBody)
	wrong[0] ^= 0x01
	bad := mineRegtestChild(t, &genesis, wrong, badBody)
	badHash := bad.Header.BlockHash()

	// Index 1: genuine-root child of the bad header (its header is still valid and inserts) -> body stored.
	goodBody := merkleTestBody(0x62)
	good := mineRegtestChild(t, &bad.Header, merkleBodyRoot(goodBody), goodBody)
	goodHash := good.Header.BlockHash()

	before := hvmBTCGossipMerkleReject.Snapshot().Count()
	driveBlocks(t, bad, good) // bad first, good second, in one message
	require.Equal(t, before+1, hvmBTCGossipMerkleReject.Snapshot().Count(), "exactly the bad block is merkle-rejected")

	badAvail, err := vm.TBCFullNode.FullBlockAvailable(ctx, badHash)
	require.NoError(t, err)
	require.False(t, badAvail, "the index-0 mismatched body must be dropped")

	goodAvail, err := vm.TBCFullNode.FullBlockAvailable(ctx, goodHash)
	require.NoError(t, err)
	require.True(t, goodAvail, "the index-1 valid body must still be processed (continue, not return/break)")
}

// TestGossipMerkleGateRunsAfterPoWEndToEnd pins gate ordering: a block that fails PoW and has a
// mismatched body increments only the PoW reject counter, not the merkle one, proving the merkle gate
// is downstream of the cheaper header-only PoW gate and never reached for a PoW-failing header. The
// header is also absent (the PoW gate `continue`s before the header insert).
func TestGossipMerkleGateRunsAfterPoWEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("live TBC full-node integration test; skipped in -short")
	}
	ctx := setupLocalnetFullNode(t)
	genesis := chaincfg.RegressionNetParams.GenesisBlock.Header

	body := merkleTestBody(0x71)
	wrong := merkleBodyRoot(body)
	wrong[0] ^= 0x01
	// Build a header with the wrong root and a non-PoW-meeting nonce (hash > target).
	blk := &wire.MsgBlock{
		Header:       wire.BlockHeader{Version: 4, PrevBlock: genesis.BlockHash(), MerkleRoot: wrong, Timestamp: genesis.Timestamp.Add(600 * time.Second), Bits: genesis.Bits},
		Transactions: body,
	}
	target := blockchain.CompactToBig(blk.Header.Bits)
	found := false
	for i := uint32(1); i < 1<<22; i++ {
		blk.Header.Nonce = i
		h := blk.Header.BlockHash()
		if blockchain.HashToBig(&h).Cmp(target) > 0 { // hash > target -> PoW FAILS
			found = true
			break
		}
	}
	require.True(t, found, "failed to find a PoW-failing nonce")
	require.True(t, shouldDropBTCHeaderPoW(vm.CheckBTCHeaderPoW(&blk.Header)), "header must fail the PoW gate")
	require.ErrorIs(t, vm.CheckBTCBlockMerkleRoot(blk), vm.ErrBTCBlockMerkleMismatch, "body is also merkle-mismatched")

	powBefore := hvmBTCGossipPoWReject.Snapshot().Count()
	merkleBefore := hvmBTCGossipMerkleReject.Snapshot().Count()
	driveOneBlock(t, blk)
	require.Equal(t, powBefore+1, hvmBTCGossipPoWReject.Snapshot().Count(), "the PoW gate (upstream) must fire")
	require.Equal(t, merkleBefore, hvmBTCGossipMerkleReject.Snapshot().Count(), "the merkle gate (downstream) must NOT be reached for a PoW-failing header")

	_, _, err := vm.TBCFullNode.BlockHeaderByHash(ctx, blk.Header.BlockHash())
	var nfe database.NotFoundError
	require.ErrorAs(t, err, &nfe, "a PoW-dropped header is never inserted")
}
