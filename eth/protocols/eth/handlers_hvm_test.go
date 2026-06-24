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

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/metrics"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/enode"
	"github.com/hemilabs/heminetwork/database"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
	"golang.org/x/time/rate"
)

// TestBTCGossipHandlersNilTBCFullNodeIgnored is the regression for a node started without hVM
// (HvmEnabled=false), where the full TBC node is never initialized (vm.TBCFullNode is nil). Before the
// fix, a peer's GetBtcBlocksMsg/BtcBlocksMsg nil-dereferenced vm.TBCFullNode in the gossip handlers and
// crashed the process (precompiles guarded this; the handlers did not). After the fix both handler
// paths ignore the message gracefully (no panic), so one unsolicited message cannot crash-loop a
// non-hVM node.
func TestBTCGossipHandlersNilTBCFullNodeIgnored(t *testing.T) {
	orig := vm.TBCFullNode
	vm.TBCFullNode = nil
	defer func() { vm.TBCFullNode = orig }()

	// handleGetBTCBlocks path: ServiceGetBTCBlocksQuery must serve no blocks (handler replies with an
	// empty set) instead of dereferencing vm.TBCFullNode.BlockByHash. A non-empty query proves the
	// guard returns before the per-hash lookup loop.
	query := GetBTCBlocksRequest{common.HexToHash("0x01"), common.HexToHash("0x02")}
	var served []*common.BitcoinBlock
	require.NotPanics(t, func() { served = ServiceGetBTCBlocksQuery(nil, query) },
		"GetBtcBlocks service must not nil-deref vm.TBCFullNode when hVM is disabled")
	require.Nil(t, served, "with no full TBC node the query must serve no blocks")

	// handleBTCBlocks path: the nil-guard precedes message decode, so the handler ignores the gossip
	// and returns nil without touching msg/peer (passing nil for both proves it).
	var err error
	require.NotPanics(t, func() { err = handleBTCBlocks(nil, nil, nil) },
		"BtcBlocks handler must not nil-deref vm.TBCFullNode when hVM is disabled")
	require.NoError(t, err, "BtcBlocks gossip must be ignored (return nil), not error/crash, on a non-hVM node")
}

// TestHandleHvmBTCMessageGuardedRecoversPanic is the regression for the eth message-handler running on
// the per-peer goroutine with no recover() upstream (p2p/peer.go): an unrecovered fault in a Hemi BTC
// handler (the embedded Bitcoin node can fault on malformed or inconsistent peer-supplied data) would
// terminate the op-geth process. The dispatch boundary must contain a panic and
// convert it to an error (which handleMessage turns into a peer disconnect), leaving a normal handler's
// return value untouched.
func TestHandleHvmBTCMessageGuardedRecoversPanic(t *testing.T) {
	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	// A handler that panics (standing in for a fault in the embedded Bitcoin node) must be contained and
	// converted to an error, never propagated to crash the process.
	panicking := func(backend Backend, msg Decoder, peer *Peer) error { panic("simulated invalid Bitcoin data") }
	var err error
	require.NotPanics(t, func() { err = handleHvmBTCMessageGuarded(panicking, nil, nil, peer) },
		"a panic in a BTC handler must be recovered, not propagated to the peer goroutine")
	require.Error(t, err, "a recovered BTC-handler panic must surface as an error so handleMessage drops the peer")

	// A non-panicking handler must pass through its returned error unchanged (no masking).
	sentinel := errors.New("normal handler error")
	passthrough := handleHvmBTCMessageGuarded(
		func(backend Backend, msg Decoder, peer *Peer) error { return sentinel }, nil, nil, peer)
	require.ErrorIs(t, passthrough, sentinel, "the guard must not alter a normal handler's returned error")

	// And a successful handler must pass through nil.
	ok := handleHvmBTCMessageGuarded(
		func(backend Backend, msg Decoder, peer *Peer) error { return nil }, nil, nil, peer)
	require.NoError(t, ok, "the guard must not alter a normal handler's nil return")
}

// TestHandleMessageRoutesBTCCodesThroughRecover closes the gap the unit test above leaves open: it
// proves the handler.go dispatch actually routes the eth/68 BTC codes (GetBtcBlocksMsg 0x11,
// BtcBlocksMsg 0x12) through the recover boundary. It swaps in a panicking handler for each BTC code
// and drives the real handleMessage; a panic must surface as an error (peer torn down), not crash the
// process. Without the dispatch wiring in handler.go this fails even though handleHvmBTCMessageGuarded
// is correct, so it guards the glue that would otherwise re-expose the whole-process crash.
func TestHandleMessageRoutesBTCCodesThroughRecover(t *testing.T) {
	for _, code := range []uint64{GetBtcBlocksMsg, BtcBlocksMsg} {
		code := code
		t.Run(fmt.Sprintf("code_%#x", code), func(t *testing.T) {
			// Swap the eth/68 handler for this code with one that panics, restoring afterward.
			orig := eth68[code]
			eth68[code] = func(backend Backend, msg Decoder, peer *Peer) error {
				panic("simulated invalid Bitcoin data on the BTC dispatch path")
			}
			t.Cleanup(func() { eth68[code] = orig })

			app, net := p2p.MsgPipe()
			defer app.Close()
			defer net.Close()
			peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
			defer peer.Close()

			// Feed one message of this code from the remote side.
			go func() { _ = p2p.Send(app, code, []byte{}) }()

			var err error
			require.NotPanics(t, func() { err = handleMessage(nil, peer) },
				"a panicking BTC handler must be recovered by the dispatch, not crash the process")
			require.Error(t, err, "the recovered panic must surface as an error so handleMessage drops the peer")
		})
	}
}

// Live-node end-to-end tests for the gossip merkle-root gate. The gate binds a gossiped body to its
// header's committed merkle root before storage, so a body of substituted transactions cannot be
// admitted under a real consensus-chain header hash. These tests stand up a real in-tree TBC full
// node (localnet/regtest, where PoW is trivially easy) and drive the real handleBTCBlocks: a body
// whose transactions do not hash to the header's committed merkle root is dropped, a matching body is
// stored.
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

// Live-node enforce end-to-end test. Stands up a real in-tree TBC full node (localnet/regtest, where
// PoW is trivially easy so synthetic headers are valid) and drives the real handleBTCBlocks: a header
// the contextual-difficulty validator rejects is not inserted into the store, an accepted header is.
// This is the composition the unit tests cannot cover (verdict comes from the real validator + store).
// setupLocalnetFullNode brings up a real TBC full node on localnet/regtest with no peers, waits for
// genesis to be inserted, and registers teardown. It sets the package globals the enforce path +
// validator read (vm.TBCFullNode, vm.tbcChainParams, vm.MainCtx) via the production setup.
func setupLocalnetFullNode(t *testing.T) context.Context {
	t.Helper()

	cfg := tbc.NewDefaultConfig()
	cfg.Network = "localnet"
	cfg.LevelDBHome = t.TempDir()
	cfg.AutoIndex = false // required by validateTBCFullNodeConfig
	cfg.MempoolEnabled = false
	cfg.ListenAddress = "" // empty -> Run binds NO p2p/RPC listener, avoiding port use in CI/sandboxes
	cfg.Seeds = nil        // no peers: the crawler idles, DB ops are unaffected
	cfg.PeersWanted = 1
	cfg.BlockCacheSize = "0"
	cfg.BlockheaderCacheSize = "0"

	// Capture every process global SetupTBCFullNode overwrites, to restore after (other unit tests
	// assert a clean state). tbcChainParams is unexported and cannot be restored here, but is
	// harmless: ValidateBTCHeaderContext short-circuits to skip whenever TBCFullNode is nil.
	origNode, origCtx := vm.TBCFullNode, vm.MainCtx
	origCfg, origCancel := vm.TBCFullNodeConfig, vm.TBCFullNodeCtxCancel

	ctx := context.Background()
	require.NoError(t, vm.SetupTBCFullNode(ctx, cfg), "TBC full node setup")
	node := vm.TBCFullNode
	t.Cleanup(func() {
		if vm.TBCFullNodeCtxCancel != nil {
			vm.TBCFullNodeCtxCancel()
		}
		// Join the Run goroutine: Running() flips false in Run's defer just before dbClose, so waiting
		// on it releases the leveldb + crawler goroutine before the next test and t.TempDir cleanup
		// (no leaked goroutine / open DB files).
		for i := 0; node != nil && node.Running() && i < 300; i++ {
			time.Sleep(10 * time.Millisecond)
		}
		vm.TBCFullNode, vm.MainCtx = origNode, origCtx
		vm.TBCFullNodeConfig, vm.TBCFullNodeCtxCancel = origCfg, origCancel
	})

	gHash := chaincfg.RegressionNetParams.GenesisHash
	require.Eventually(t, func() bool {
		// Running() flips true only after Run's dbOpen (so s.db is set, guarding the nil-deref), and
		// genesis is inserted shortly after; gate the lookup on it.
		if !vm.TBCFullNode.Running() {
			return false
		}
		_, _, err := vm.TBCFullNode.BlockHeaderByHash(ctx, *gHash)
		return err == nil
	}, 30*time.Second, 50*time.Millisecond, "TBC full node did not insert genesis in time")
	return ctx
}

// driveOneHeader serializes a single header as a 0-tx wire.MsgBlock and feeds it through the real
// handleBTCBlocks gossip handler (bypassing RLP via the fake decoder).
func driveOneHeader(t *testing.T, h *wire.BlockHeader) {
	t.Helper()
	mb := &wire.MsgBlock{Header: *h}
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

func TestEnforceDropsRejectHeaderEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("live TBC full-node integration test; skipped in -short")
	}
	ctx := setupLocalnetFullNode(t)
	genesis := chaincfg.RegressionNetParams.GenesisBlock.Header
	gHash := genesis.BlockHash()
	ts := genesis.Timestamp.Add(600 * time.Second)

	// Reject: a header that passes proof-of-work and linkage (correct regtest powLimit bits, parent
	// present) but fails the contextual check via median-time-past — its timestamp equals genesis, so
	// it is not strictly after the MTP -> ErrTimeTooOld. The crucial choice: being PoW- and
	// sanity-valid, the header store would insert it if enforce did not
	// drop it, so its absence below is attributable to the enforce drop, not an incidental insert
	// failure. A wrong-difficulty header would fail PoW at insert anyway and could not distinguish.
	// Pick a nonce that genuinely passes PoW (Timestamp stays == genesis, so it still fails MTP). This makes
	// the drop attributable to the contextual-difficulty gate specifically: a PoW-failing nonce would be
	// dropped by the earlier PoW gate and never reach the diff gate (or its reject counter).
	rejTarget := blockchain.CompactToBig(genesis.Bits)
	reject := &wire.BlockHeader{Version: 4, PrevBlock: gHash, Bits: genesis.Bits, Timestamp: genesis.Timestamp, Nonce: 0}
	for i := uint32(1); i < 1<<20; i++ {
		reject.Nonce = i
		rh := reject.BlockHash()
		if blockchain.HashToBig(&rh).Cmp(rejTarget) <= 0 { // hash <= target -> PoW passes
			break
		}
	}
	require.NoError(t, vm.CheckBTCHeaderPoW(reject), "the reject header must pass PoW so the drop is the diff gate, not the PoW gate")
	verr := vm.ValidateBTCHeaderContext(reject)
	require.NotErrorIs(t, verr, vm.ErrBTCHeaderContextUnavailable, "present parent -> the verdict must not be skip")
	// Pin the exact rejection: on regtest (PoWNoRetargeting) difficulty passes, so Timestamp==genesis
	// fails median-time-past -> a btcd RuleError with code ErrTimeTooOld, not just some error.
	var re blockchain.RuleError
	require.ErrorAs(t, verr, &re, "the reject must be a btcd RuleError")
	require.Equal(t, blockchain.ErrTimeTooOld, re.ErrorCode, "Timestamp==genesis must reject as ErrTimeTooOld")

	rejBefore := hvmBTCDiffShadowReject.Snapshot().Count()
	driveOneHeader(t, reject)
	_, _, err := vm.TBCFullNode.BlockHeaderByHash(ctx, reject.BlockHash())
	// Pin the exact absence: the header lookup returns the TBC node's NotFoundError, not merely some
	// error, so a bypassed drop masked by an unrelated IO/decode error cannot pass.
	var nfe database.NotFoundError
	require.ErrorAs(t, err, &nfe, "ENFORCE: a reject header must be DROPPED — its lookup returns NotFound")
	// Pin that the drop is attributable to the contextual-difficulty gate specifically (its dedicated reject
	// counter ticks exactly once), not to an incidental PoW/sanity drop upstream.
	require.Equal(t, rejBefore+1, hvmBTCDiffShadowReject.Snapshot().Count(),
		"the contextual-difficulty gate must increment its reject counter exactly once for the reject header")

	// Accept: a header with the correct expected difficulty (regtest genesis bits) on the same parent.
	// The validator accepts it, so enforce must not drop it — it is inserted.
	accept := &wire.BlockHeader{Version: 4, PrevBlock: gHash, Bits: genesis.Bits, Timestamp: ts, Nonce: 2}
	require.NoError(t, vm.ValidateBTCHeaderContext(accept), "a correct-difficulty header must be accepted")

	accBefore := hvmBTCDiffShadowAccept.Snapshot().Count()
	driveOneHeader(t, accept)
	_, _, err = vm.TBCFullNode.BlockHeaderByHash(ctx, accept.BlockHash())
	require.NoError(t, err, "ENFORCE: an accepted header must NOT be dropped — it is inserted")
	require.Equal(t, accBefore+1, hvmBTCDiffShadowAccept.Snapshot().Count(),
		"the contextual-difficulty gate must increment its accept counter exactly once for the accept header")

	// Skip: a header whose parent is absent from the store must classify as skip (the sentinel), not
	// reject, so enforce never drops honest headers whose ancestry has not yet arrived (which would
	// stall IBD). Confirms the real node distinguishes skip from reject; the skip-is-not-dropped
	// policy itself is pinned by TestShouldDropBTCHeader. End-to-end the orphan also fails the
	// no-orphan insert, so store-absence cannot distinguish skip-insert from a drop — hence we assert
	// the verdict, not the store state.
	orphan := &wire.BlockHeader{Version: 4, PrevBlock: chainhash.Hash{0xab}, Bits: genesis.Bits, Timestamp: ts, Nonce: 3}
	require.ErrorIs(t, vm.ValidateBTCHeaderContext(orphan), vm.ErrBTCHeaderContextUnavailable,
		"a header with an absent parent must be a SKIP verdict (not a reject), so enforce does not drop it")
}

// TestGossipPoWDropEndToEnd is the live-node composition test for the gossip-path PoW gate:
// a header with valid Bits but no real work (whose hash does not meet its claimed target) is dropped by
// handleBTCBlocks. Mirrors the enforce test in
// reverse: the header is contextually valid (correct regtest bits, good post-genesis timestamp, parent
// present), so absent the PoW gate it would pass the contextual check and the header insert
// (which does not verify PoW) and be inserted. Its absence is
// thus attributable to the PoW drop, pinned by the dedicated counter (only this gate increments
// hvmBTCGossipPoWReject), with NotFound as corroboration.
func TestGossipPoWDropEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("live TBC full-node integration test; skipped in -short")
	}
	ctx := setupLocalnetFullNode(t)
	genesis := chaincfg.RegressionNetParams.GenesisBlock.Header
	gHash := genesis.BlockHash()
	ts := genesis.Timestamp.Add(600 * time.Second)

	// Build a header off genesis that fails PoW: correct regtest bits + a valid timestamp (so
	// contextual difficulty passes — ValidateBTCHeaderContext checks difficulty/MTP, not hash<=target),
	// then pick a Nonce whose hash exceeds the regtest target. regtest PowLimit is ~2^255, so ~half of
	// nonces fail; iterate to find one deterministically (anti-mine).
	target := blockchain.CompactToBig(genesis.Bits)
	forged := &wire.BlockHeader{Version: 4, PrevBlock: gHash, Bits: genesis.Bits, Timestamp: ts, Nonce: 0}
	found := false
	for i := uint32(1); i < 1<<20; i++ {
		forged.Nonce = i
		hash := forged.BlockHash()
		if blockchain.HashToBig(&hash).Cmp(target) > 0 { // hash > target -> PoW FAILS
			found = true
			break
		}
	}
	require.True(t, found, "failed to find a PoW-failing nonce within 2^20 (should take ~2)")

	// Preconditions: PoW genuinely fails, but the contextual validator would accept it, so the drop
	// below is attributable to the PoW gate, not an incidental contextual reject or insert failure.
	require.True(t, shouldDropBTCHeaderPoW(vm.CheckBTCHeaderPoW(forged)), "the forged header must FAIL the PoW gate")
	require.NoError(t, vm.ValidateBTCHeaderContext(forged), "the forged header must PASS the contextual check (isolating the PoW drop)")

	before := hvmBTCGossipPoWReject.Snapshot().Count()
	driveOneHeader(t, forged)
	require.Equal(t, before+1, hvmBTCGossipPoWReject.Snapshot().Count(), "the gossip PoW gate must increment its dedicated reject counter exactly once")

	_, _, err := vm.TBCFullNode.BlockHeaderByHash(ctx, forged.BlockHash())
	var nfe database.NotFoundError
	require.ErrorAs(t, err, &nfe, "a PoW-failing gossiped header must be DROPPED — its lookup returns NotFound")
}

// TestGossipHeaderOnlyMessageIsNotMerkleRejected pins that a legitimate header-only gossip message
// (a 0-tx wire.MsgBlock — the way a peer relays a bare header; a real BTC block always carries at least
// the coinbase tx) inserts its header WITHOUT being counted as a merkle reject. The body-merkle gate
// verifies a body against the header's committed root; with no body there is nothing to verify, so it
// must be skipped rather than firing the "body does not match header merkle root" reject counter/Warn.
// Mutation proof: removing the `len(msgBlock.Transactions) == 0` skip in handleBTCBlocks makes
// CheckBTCBlockMerkleRoot return "no transactions", increments hvmBTCGossipMerkleReject, and fails here.
func TestGossipHeaderOnlyMessageIsNotMerkleRejected(t *testing.T) {
	if testing.Short() {
		t.Skip("live TBC full-node integration test; skipped in -short")
	}
	ctx := setupLocalnetFullNode(t)
	genesis := chaincfg.RegressionNetParams.GenesisBlock.Header
	gHash := genesis.BlockHash()
	ts := genesis.Timestamp.Add(600 * time.Second)

	// An accept-grade header (correct regtest difficulty, post-genesis timestamp, parent present) so it
	// passes PoW + contextual checks and reaches the body-merkle gate — isolating that gate's handling
	// of the no-body case from an incidental upstream drop. regtest PowLimit is ~2^255, so ~half of
	// nonces meet the target; iterate to find a PoW-passing one deterministically (anti-mine).
	target := blockchain.CompactToBig(genesis.Bits)
	header := &wire.BlockHeader{Version: 4, PrevBlock: gHash, Bits: genesis.Bits, Timestamp: ts, Nonce: 0}
	found := false
	for i := uint32(1); i < 1<<20; i++ {
		header.Nonce = i
		hash := header.BlockHash()
		if blockchain.HashToBig(&hash).Cmp(target) <= 0 { // hash <= target -> PoW PASSES
			found = true
			break
		}
	}
	require.True(t, found, "failed to find a PoW-passing nonce within 2^20 (should take ~2)")
	require.NoError(t, vm.CheckBTCHeaderPoW(header), "the header must pass PoW so it reaches the merkle gate")
	require.NoError(t, vm.ValidateBTCHeaderContext(header), "the header must pass the contextual check")

	before := hvmBTCGossipMerkleReject.Snapshot().Count()
	driveOneHeader(t, header) // 0-tx wire.MsgBlock
	require.Equal(t, before, hvmBTCGossipMerkleReject.Snapshot().Count(),
		"a header-only (0-tx) message has no body to verify and must NOT be counted as a merkle reject")

	_, _, err := vm.TBCFullNode.BlockHeaderByHash(ctx, header.BlockHash())
	require.NoError(t, err, "the header-only message's header must still be inserted")
}

// Shadow (log-only) wiring of the contextual-difficulty validator into handleBTCBlocks. Shadow mode
// changes no behavior, so these tests pin the only new logic: verdict classification (skip stays
// distinct from reject) and that the shadow observer is benign. The end-to-end "shadow does not
// enforce" integration test needs the full TBC node harness and lives in the enforce tests.
func TestClassifyBTCDiffShadow(t *testing.T) {
	require.Equal(t, btcDiffShadowAccept, classifyBTCDiffShadow(nil),
		"nil = accept")
	require.Equal(t, btcDiffShadowSkip, classifyBTCDiffShadow(vm.ErrBTCHeaderContextUnavailable),
		"the skip sentinel = skip, not reject")
	require.Equal(t, btcDiffShadowSkip, classifyBTCDiffShadow(
		errors.Join(errors.New("wrap"), vm.ErrBTCHeaderContextUnavailable)),
		"a wrapped skip sentinel must still classify as skip (errors.Is)")
	require.Equal(t, btcDiffShadowReject, classifyBTCDiffShadow(errors.New("difficulty violation")),
		"a non-sentinel error = reject (would drop in enforce mode)")

	// The validator's actual rejection type is a btcd blockchain.RuleError (from
	// CheckBlockHeaderContext). Pin classification on the production type, not a generic error.
	ruleErr := blockchain.RuleError{ErrorCode: blockchain.ErrUnexpectedDifficulty, Description: "bad difficulty"}
	require.Equal(t, btcDiffShadowReject, classifyBTCDiffShadow(ruleErr),
		"a real btcd RuleError = reject")
	// Tripwire: a RuleError must never satisfy the skip sentinel. btcd v0.24.2's RuleError has no
	// Unwrap/Is so this holds today; a future btcd bump adding one that matched would silently
	// downgrade reject to skip, accepting an easier-than-consensus header when enforcing.
	require.False(t, errors.Is(ruleErr, vm.ErrBTCHeaderContextUnavailable),
		"a RuleError must not be classified as skip via errors.Is")

	// Precedence: the skip sentinel is checked before the default reject, so a skip sentinel
	// co-present with a RuleError classifies as skip, order-independently. The validator never
	// emits both (skip-override and RuleError branches are mutually exclusive, see
	// core/vm/tbc_difficulty.go), so this only pins the documented precedence rule.
	require.Equal(t, btcDiffShadowSkip,
		classifyBTCDiffShadow(errors.Join(ruleErr, vm.ErrBTCHeaderContextUnavailable)),
		"skip sentinel dominates a co-present RuleError (join, sentinel second)")
	require.Equal(t, btcDiffShadowSkip,
		classifyBTCDiffShadow(errors.Join(vm.ErrBTCHeaderContextUnavailable, ruleErr)),
		"skip sentinel dominates a co-present RuleError (join, sentinel first)")
	// A doubly-wrapped (%w within %w) skip sentinel must still classify as skip.
	require.Equal(t, btcDiffShadowSkip,
		classifyBTCDiffShadow(fmt.Errorf("outer: %w", fmt.Errorf("inner: %w", vm.ErrBTCHeaderContextUnavailable))),
		"doubly-wrapped skip sentinel still classifies as skip")
}

// TestEvaluateBTCDiffSkipCounterDelta pins the only reachable side effect of the shadow observer in
// unit tests: the skip-counter increment. The benign test asserts NotPanics but never checks which
// counter moved, so deleting hvmBTCDiffShadowSkip.Inc(1) or misrouting skip to reject survives it.
// A delta-based assertion kills both (counters are never-reset process-global atomic.Int64s, so
// absolute values are meaningless). Works with metrics off: this fork's metrics.Counter is a
// concrete atomic.Int64 with unconditional Inc/Snapshot and no NilCounter.
//
// Must stay non-parallel and be the sole incrementer of these counters during its run (alongside the
// concurrent test below), or the exact-delta goes flaky.
func TestEvaluateBTCDiffSkipCounterDelta(t *testing.T) {
	require.Nil(t, vm.TBCFullNode, "precondition: full node not initialized (validator returns skip)")

	accept0 := hvmBTCDiffShadowAccept.Snapshot().Count()
	skip0 := hvmBTCDiffShadowSkip.Snapshot().Count()
	reject0 := hvmBTCDiffShadowReject.Snapshot().Count()

	hdr := &wire.BlockHeader{Version: 1, Bits: 0x1d00ffff, Timestamp: time.Unix(1_600_000_000, 0)}
	verdict := evaluateBTCDiff(chainhash.Hash{0x01}, hdr)

	// The returned verdict (what the enforce caller consumes) must equal skip too, catching a mutant
	// that keeps the correct skip Inc but corrupts `return verdict`.
	require.Equal(t, btcDiffShadowSkip, verdict, "returned verdict must be skip (counter/return consistency)")
	require.Equal(t, skip0+1, hvmBTCDiffShadowSkip.Snapshot().Count(),
		"skip counter must increment by exactly 1 (kills a deleted/misrouted skip Inc)")
	require.Equal(t, accept0, hvmBTCDiffShadowAccept.Snapshot().Count(),
		"accept counter must not move on a skip verdict")
	require.Equal(t, reject0, hvmBTCDiffShadowReject.Snapshot().Count(),
		"reject counter must not move on a skip verdict")
}

// TestShadowCounterRegistration pins that each package counter var is the object registered under its
// metric name and that the three names are distinct. metrics.Register discards a duplicate-name
// registration (returns ErrDuplicateMetric, no panic), so a name typo or collision would silently
// detach a counter: Inc lands on a registered orphan, the scraped metric stays zero, no test fails.
func TestShadowCounterRegistration(t *testing.T) {
	for name, want := range map[string]*metrics.Counter{
		"eth/hvm/btcdiff/shadow/accept": hvmBTCDiffShadowAccept,
		"eth/hvm/btcdiff/shadow/skip":   hvmBTCDiffShadowSkip,
		"eth/hvm/btcdiff/shadow/reject": hvmBTCDiffShadowReject,
	} {
		got, ok := metrics.DefaultRegistry.Get(name).(*metrics.Counter)
		require.True(t, ok, "metric %q must be registered as a *Counter", name)
		require.Same(t, want, got, "package var must be the counter registered under %q", name)
	}
	// The require.Same loop above is the collision detector: on a duplicate metric name, Register
	// discards the second and Get returns the first, so Same(secondVar, firstVar) fails. These
	// NotSame checks guard a different mutation: a copy/paste aliasing two package vars to the same
	// *Counter (e.g. hvmBTCDiffShadowSkip = hvmBTCDiffShadowAccept), so two verdicts share one counter.
	require.NotSame(t, hvmBTCDiffShadowAccept, hvmBTCDiffShadowSkip, "accept and skip must be distinct counters")
	require.NotSame(t, hvmBTCDiffShadowSkip, hvmBTCDiffShadowReject, "skip and reject must be distinct counters")
	require.NotSame(t, hvmBTCDiffShadowAccept, hvmBTCDiffShadowReject, "accept and reject must be distinct counters")

	// Prefix-exclusivity: exactly the three known counters live under the namespace, with no stray or
	// typo'd sibling (e.g. ".../rejct") and nothing registered as a non-Counter type. The per-name
	// loop above only checks the three known names resolve; this enumerates the registry.
	gotUnderPrefix := map[string]bool{}
	metrics.DefaultRegistry.Each(func(name string, v interface{}) {
		if strings.HasPrefix(name, "eth/hvm/btcdiff/shadow/") {
			_, ok := v.(*metrics.Counter)
			require.True(t, ok, "metric %q under the shadow prefix must be a *Counter", name)
			gotUnderPrefix[name] = true
		}
	})
	require.Equal(t, map[string]bool{
		"eth/hvm/btcdiff/shadow/accept": true,
		"eth/hvm/btcdiff/shadow/skip":   true,
		"eth/hvm/btcdiff/shadow/reject": true,
	}, gotUnderPrefix, "exactly the three known shadow counters must exist under the prefix")
}

// TestEvaluateBTCDiffConcurrent drives the shadow observer from many goroutines at once, matching the
// live shape (handleBTCBlocks runs one goroutine per peer). This is a no-panic + exact-delta smoke
// test, not a deep race test: with vm.TBCFullNode==nil the validator short-circuits to skip before
// allocating its resolver or any header lookup, so the only concurrent work is the atomic counter Inc
// (which -race treats as synchronized and cannot flag). It does not race-validate the validator body
// (gated behind a non-nil TBCFullNode, covered by the live-TBC-node harness).
//
// Must stay non-parallel and be the sole incrementer of these counters during its run (with the delta
// test above), or the exact-delta assertion goes flaky.
func TestEvaluateBTCDiffConcurrent(t *testing.T) {
	require.Nil(t, vm.TBCFullNode, "precondition: full node not initialized (validator returns skip)")

	const n = 64
	skip0 := hvmBTCDiffShadowSkip.Snapshot().Count()
	accept0 := hvmBTCDiffShadowAccept.Snapshot().Count()
	reject0 := hvmBTCDiffShadowReject.Snapshot().Count()

	// Recover any panic into a shared slice and assert on the test goroutine after Wait(). testify
	// require.* calls t.FailNow() -> runtime.Goexit(), which Go requires run only on the test
	// goroutine, so require.* must not be used inside these spawned goroutines.
	var (
		mu     sync.Mutex
		panics []any
	)
	var wg sync.WaitGroup
	wg.Add(n)
	for i := 0; i < n; i++ {
		go func(i int) {
			defer wg.Done()
			defer func() {
				if r := recover(); r != nil {
					mu.Lock()
					panics = append(panics, r)
					mu.Unlock()
				}
			}()
			// hdr/hash are inert on the skip path (validator returns before reading them); varied
			// only so each goroutine owns its own stack-local values.
			hdr := &wire.BlockHeader{Version: 1, Bits: 0x1d00ffff, Timestamp: time.Unix(1_600_000_000+int64(i), 0)}
			evaluateBTCDiff(chainhash.Hash{byte(i)}, hdr)
		}(i)
	}
	wg.Wait()

	require.Empty(t, panics, "evaluateBTCDiff must not panic under concurrent calls: %v", panics)
	require.Equal(t, skip0+n, hvmBTCDiffShadowSkip.Snapshot().Count(),
		"N concurrent skip verdicts must produce a +N skip delta; a short delta means a call was "+
			"misrouted to accept/reject or a goroutine bailed before Inc (counts cannot tear — Inc is atomic)")
	require.Equal(t, accept0, hvmBTCDiffShadowAccept.Snapshot().Count(), "accept unchanged")
	require.Equal(t, reject0, hvmBTCDiffShadowReject.Snapshot().Count(), "reject unchanged")
}

// TestEvaluateBTCDiffBenign confirms the evaluator does not panic and, with no TBC full node set up
// (vm.TBCFullNode nil in unit tests), returns skip so the enforce caller (shouldDropBTCHeader) would
// not drop the header. Exercises the skip path end-to-end through the real validator + classifier.
func TestEvaluateBTCDiffBenign(t *testing.T) {
	require.Nil(t, vm.TBCFullNode, "precondition: full node not initialized in unit tests")
	hdr := &wire.BlockHeader{Version: 1, Bits: 0x1d00ffff, Timestamp: time.Unix(1_600_000_000, 0)}
	var verdict btcDiffShadowVerdict
	require.NotPanics(t, func() { verdict = evaluateBTCDiff(chainhash.Hash{0x01}, hdr) },
		"evaluation must never panic")
	require.Equal(t, btcDiffShadowSkip, verdict, "nil-full-node verdict must be skip, not reject")
	require.False(t, shouldDropBTCHeader(verdict), "a skip verdict must NOT drop the header")
}

// TestShouldDropBTCHeader pins the gossip-path contextual-difficulty enforce policy: only a genuine contextual-difficulty
// rejection drops a gossiped header. The load-bearing invariant is the skip case: dropping on skip
// (ancestry not yet available during IBD) would stall sync, so it is asserted explicitly.
func TestShouldDropBTCHeader(t *testing.T) {
	require.True(t, shouldDropBTCHeader(btcDiffShadowReject), "a reject MUST drop the header")
	require.False(t, shouldDropBTCHeader(btcDiffShadowSkip), "a skip MUST NOT drop (would stall IBD)")
	require.False(t, shouldDropBTCHeader(btcDiffShadowAccept), "an accept MUST NOT drop")

	// Fail open on any non-reject value: the zero-value verdict and any out-of-range int must not
	// drop, so an uninitialized verdict or a future enum addition never silently discards honest
	// headers (the safe default under enforce is insert, not drop).
	require.Equal(t, btcDiffShadowAccept, btcDiffShadowVerdict(0), "zero-value verdict must be accept (iota 0)")
	require.False(t, shouldDropBTCHeader(btcDiffShadowVerdict(0)), "zero-value verdict must not drop")
	require.False(t, shouldDropBTCHeader(btcDiffShadowVerdict(99)), "an out-of-range verdict must fail open (not drop)")

	// Enum-ordering tripwire: reject is value 2 (accept=0, skip=1, reject=2). Inserting a verdict
	// before reject shifts its value; this breaks loudly to force revisiting
	// classifyBTCDiffShadow/shouldDropBTCHeader.
	require.Equal(t, btcDiffShadowVerdict(2), btcDiffShadowReject, "verdict enum order changed — revisit the drop policy")
}

// TestShouldDropBTCHeaderPoW pins the gossip-path PoW drop policy:
// drop only on a genuine PoW RuleError, never on a valid header (nil) or the skip sentinel (params not
// yet configured). Dropping on skip would discard honest headers on a transient config gap. This gate
// is gossip-path defense-in-depth, not the consensus enforcement point.
func TestShouldDropBTCHeaderPoW(t *testing.T) {
	require.True(t, shouldDropBTCHeaderPoW(blockchain.RuleError{ErrorCode: blockchain.ErrHighHash}),
		"a genuine PoW failure (forged-Bits/zero-PoW) MUST drop")
	require.True(t, shouldDropBTCHeaderPoW(blockchain.RuleError{ErrorCode: blockchain.ErrUnexpectedDifficulty}),
		"an out-of-range target MUST drop")
	require.False(t, shouldDropBTCHeaderPoW(nil), "valid PoW (nil) MUST NOT drop")
	require.False(t, shouldDropBTCHeaderPoW(vm.ErrBTCHeaderContextUnavailable),
		"the skip sentinel (params unconfigured) MUST NOT drop (never discard honest headers on a config gap)")
	require.False(t, shouldDropBTCHeaderPoW(fmt.Errorf("ctx: %w", vm.ErrBTCHeaderContextUnavailable)),
		"a wrapped skip sentinel must still classify as skip (errors.Is), not drop")
}

// TestBTCDiffRejectLogLimiterConfig pins the reject-log throttle config via the read-only getters
// (not advancing the token bucket, which would be time-dependent). A zero/Inf rate or zero burst
// would either flood the log or suppress the throttled reject alert.
func TestBTCDiffRejectLogLimiterConfig(t *testing.T) {
	require.Equal(t, rate.Every(5*time.Second), btcDiffRejectLogLimiter.Limit(),
		"reject-log limiter must stay throttled at ~1 line / 5s")
	require.Equal(t, 4, btcDiffRejectLogLimiter.Burst(), "reject-log limiter burst must stay 4")
}

// fakeBTCDecoder copies a prepared *BTCBlocksPacket into the handler's decode target, bypassing RLP
// so a test can drive handleBTCBlocks with an arbitrary header count.
type fakeBTCDecoder struct{ pkt *BTCBlocksPacket }

func (d fakeBTCDecoder) Decode(val interface{}) error { *(val.(*BTCBlocksPacket)) = *d.pkt; return nil }
func (d fakeBTCDecoder) Time() time.Time              { return time.Time{} }

// TestHandleBTCBlocksRejectsOversizedMessage pins the per-message header cap: a BtcBlocks message
// with more than maxBtcBlocksServe entries is rejected. Reachable without a live node: a non-nil
// zero-value *tbc.Server passes the nil-guard, and the cap returns before any node method runs
// (FullBlockAvailable is inside the per-header loop). Kills a cap-removal mutant and a `>`->`>=`
// off-by-one (33 > 32 must reject).
func TestHandleBTCBlocksRejectsOversizedMessage(t *testing.T) {
	orig := vm.TBCFullNode
	vm.TBCFullNode = &tbc.Server{} // non-nil; never dereferenced before the cap return
	defer func() { vm.TBCFullNode = orig }()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	pkt := &BTCBlocksPacket{}
	pkt.BTCBlocksResponse = make(BTCBlocksResponse, maxBtcBlocksServe+1) // 33 > cap 32; cap checks len only

	err := handleBTCBlocks(nil, fakeBTCDecoder{pkt: pkt}, peer)
	require.ErrorIs(t, err, errMsgTooLarge, "an oversized BtcBlocks message must be rejected by the per-message cap")
	// Pin the exact diagnostic text (count + cap) so a %d operand swap or len/const substitution,
	// invisible to ErrorIs, is caught.
	require.EqualError(t, err, "message too long: BtcBlocks response of 33 exceeds cap 32")
}

// TestHandleBTCBlocksAcceptsAtCapBoundary pins the cap boundary: exactly maxBtcBlocksServe entries
// (an honest peer's max-size response) must not be rejected by the cap, killing a `>`->`>=` mutation.
// The entries are invalid wire bytes, so the per-header loop fails to deserialize and `continue`s
// without touching the zero-value node; the cap is the only path that returns errMsgTooLarge here.
func TestHandleBTCBlocksAcceptsAtCapBoundary(t *testing.T) {
	orig := vm.TBCFullNode
	vm.TBCFullNode = &tbc.Server{}
	defer func() { vm.TBCFullNode = orig }()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	pkt := &BTCBlocksPacket{}
	pkt.BTCBlocksResponse = make(BTCBlocksResponse, maxBtcBlocksServe) // exactly 32 (== cap, must pass)
	for i := range pkt.BTCBlocksResponse {
		bb := common.BitcoinBlock([]byte{0x00}) // invalid wire block -> loop Deserialize fails -> continue
		pkt.BTCBlocksResponse[i] = &bb
	}

	err := handleBTCBlocks(nil, fakeBTCDecoder{pkt: pkt}, peer)
	// Exactly nil: 32 is not > 32 (cap passes), each invalid entry deserialize-fails + continues
	// without touching the node, and the handler falls through to `return nil`. NoError is tighter
	// than NotErrorIs(errMsgTooLarge): it also kills a `>`->`>=` that re-wraps a different sentinel
	// and a `continue`->`return err` leak.
	require.NoError(t, err, "exactly maxBtcBlocksServe entries must pass the cap and the handler returns nil")
}

// These tests cover the production WIRING of the ancestor-fetch path (requestMissingAncestors and its
// split-out requestMissingAncestorBlocks) — the batching, the maxBtcBlocksServe chunking, and that the
// walkGate slot is released on both the normal and the recover (panic) path. The walkGate primitive itself
// is covered by hvm_ancestor_walkgate_test.go; these pin the glue a mutation there could otherwise pass.

func makeMissingHeaders(n int) []wire.BlockHeader {
	hs := make([]wire.BlockHeader, n)
	for i := range hs {
		hs[i] = wire.BlockHeader{Version: 1, Nonce: uint32(i + 1)} // distinct nonces -> distinct hashes
	}
	return hs
}

// stubAvailability points the tbcBlocksAvailableToHeader seam at a function returning the given missing set,
// and returns a restore func. It lets the walk logic run without a live TBC full node.
func stubAvailability(missing []wire.BlockHeader) func() {
	orig := tbcBlocksAvailableToHeader
	tbcBlocksAvailableToHeader = func(context.Context, *wire.BlockHeader) (bool, *[]wire.BlockHeader, *chainhash.Hash, error) {
		return false, &missing, nil, nil
	}
	return func() { tbcBlocksAvailableToHeader = orig }
}

// readBtcBlockRequests reads exactly `expect` GetBtcBlocks messages the peer sent into the pipe and returns
// the hash list from each, failing on a timeout (a leaked gate slot would stall sends, which this catches).
func readBtcBlockRequests(t *testing.T, app *p2p.MsgPipeRW, expect int) [][]common.Hash {
	t.Helper()
	type res struct {
		hashes []common.Hash
		err    error
	}
	out := make([][]common.Hash, 0, expect)
	for i := 0; i < expect; i++ {
		ch := make(chan res, 1)
		go func() {
			msg, err := app.ReadMsg()
			if err != nil {
				ch <- res{err: err}
				return
			}
			if msg.Code != GetBtcBlocksMsg {
				ch <- res{err: errUnexpectedCode(msg.Code)}
				return
			}
			var p GetBTCBlocksPacket
			if err := msg.Decode(&p); err != nil {
				ch <- res{err: err}
				return
			}
			ch <- res{hashes: []common.Hash(p.GetBTCBlocksRequest)}
		}()
		select {
		case r := <-ch:
			require.NoError(t, r.err)
			out = append(out, r.hashes)
		case <-time.After(3 * time.Second):
			t.Fatalf("timed out waiting for BTC block request %d/%d (a leaked gate slot would stall sends)", i+1, expect)
		}
	}
	return out
}

type unexpectedCodeErr uint64

func (e unexpectedCodeErr) Error() string { return "unexpected message code" }
func errUnexpectedCode(c uint64) error    { return unexpectedCodeErr(c) }

// All missing ancestors below the chunk cap go out in ONE batched request (not one message per block).
func TestRequestMissingAncestorBlocksBatchesIntoOneRequest(t *testing.T) {
	missing := makeMissingHeaders(3)
	defer stubAvailability(missing)()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	go requestMissingAncestorBlocks(peer, &wire.BlockHeader{})

	got := readBtcBlockRequests(t, app, 1)
	require.Len(t, got, 1, "all missing ancestors below the cap must batch into ONE request")
	require.Len(t, got[0], 3, "the single request must carry all 3 missing hashes")
	want := map[common.Hash]bool{}
	for _, m := range missing {
		want[common.Hash(m.BlockHash())] = true
	}
	for _, h := range got[0] {
		require.True(t, want[h], "every requested hash must be a missing ancestor")
	}
}

// More missing ancestors than maxBtcBlocksServe are split into chunks of at most maxBtcBlocksServe, with all
// hashes covered exactly once across the chunks.
func TestRequestMissingAncestorBlocksChunksAtCap(t *testing.T) {
	const n = 2*maxBtcBlocksServe + 6
	missing := makeMissingHeaders(n)
	defer stubAvailability(missing)()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	go requestMissingAncestorBlocks(peer, &wire.BlockHeader{})

	got := readBtcBlockRequests(t, app, 3)
	require.Len(t, got, 3, "n=2*cap+6 must split into 3 chunks")
	require.Len(t, got[0], maxBtcBlocksServe)
	require.Len(t, got[1], maxBtcBlocksServe)
	require.Len(t, got[2], 6)
	total := 0
	for _, c := range got {
		require.LessOrEqual(t, len(c), maxBtcBlocksServe, "no chunk may exceed the cap")
		total += len(c)
	}
	require.Equal(t, n, total, "every missing hash must be requested across the chunks")
}

// requestMissingAncestors must release its gate slot after each call; otherwise the global cap is exhausted
// after maxConcurrentAncestorWalks calls. A cap-1 fresh gate + several sequential calls all proceeding
// proves the release runs (a dropped `defer release()` would stall the 2nd call and time out the read).
func TestRequestMissingAncestorsReleasesGateSlot(t *testing.T) {
	origGate := ancestorWalkGate
	ancestorWalkGate = newWalkGate(1)
	defer func() { ancestorWalkGate = origGate }()

	origNode := vm.TBCFullNode
	vm.TBCFullNode = &tbc.Server{} // non-nil so the nil-guard passes; the stubbed seam never touches it
	defer func() { vm.TBCFullNode = origNode }()

	defer stubAvailability(makeMissingHeaders(1))()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	const calls = 5
	go func() {
		for i := 0; i < calls; i++ {
			requestMissingAncestors(peer, &wire.BlockHeader{Nonce: uint32(i + 1)}) // distinct -> in-flight dedup never blocks
		}
	}()
	got := readBtcBlockRequests(t, app, calls)
	require.Len(t, got, calls, "every call must proceed; the gate slot is released after each")
}

// The gate slot must be released even when the walk panics (defer release runs on the recover path), so a
// torn-store panic cannot permanently jam the gate.
func TestRequestMissingAncestorsReleasesGateSlotOnPanic(t *testing.T) {
	origGate := ancestorWalkGate
	ancestorWalkGate = newWalkGate(1)
	defer func() { ancestorWalkGate = origGate }()

	origNode := vm.TBCFullNode
	vm.TBCFullNode = &tbc.Server{}
	defer func() { vm.TBCFullNode = origNode }()

	origFn := tbcBlocksAvailableToHeader
	tbcBlocksAvailableToHeader = func(context.Context, *wire.BlockHeader) (bool, *[]wire.BlockHeader, *chainhash.Hash, error) {
		panic("simulated torn TBC store")
	}
	defer func() { tbcBlocksAvailableToHeader = origFn }()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	require.NotPanics(t, func() { requestMissingAncestors(peer, &wire.BlockHeader{}) },
		"a panic in the walk must be recovered, not propagated")

	rel, ok := ancestorWalkGate.tryEnter(common.Hash{0xab})
	require.True(t, ok, "the gate slot must be released even when the walk panics")
	rel()
}
