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

// Live-node enforce end-to-end test. Stands up a real in-tree TBC full node (localnet/regtest, where
// PoW is trivially easy so synthetic headers are valid) and drives the real handleBTCBlocks: a header
// the contextual-difficulty validator rejects is not inserted into the store, an accepted header is.
// This is the composition the unit tests cannot cover (verdict comes from the real validator + store).

import (
	"bytes"
	"context"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/enode"
	"github.com/hemilabs/heminetwork/database"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

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
