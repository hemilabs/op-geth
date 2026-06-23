// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Snap completion, end-to-end: the runHvmSnapWaiter HAPPY PATH — the detached goroutine that waits for the
// full TBC node to hold all Bitcoin blocks for a snap-sync candidate tip and then COMPLETES the sync (reset the
// lightweight view -> walk the full node back to genesis -> AddExternalHeaders -> updateFullTBCToLightweight ->
// SetSafe/SetFinalized -> mark finished) — had no coverage. Existing snap tests cover only the decomposed pieces
// (latch lifecycle, claim-once, abort-on-quit, noop-when-not-awaiting, the pure helpers) and the build-path prefetch
// gate is covered in core/vm; none drive the completion body, because it needs a REAL indexed full node holding real
// blocks. With the synthetic full node we can: arm the latch, feed a full node a synthetic regtest chain, pin an hVM
// base whose body is on local disk, call SnapSyncHvm, and assert the waiter reconstructs the lightweight view to the
// BTC tip and finishes.
//
// vm's synthetic full-node harness lives in a core/vm test file (not importable here), so this replicates it via the
// EXPORTED vm symbols (vm.SetupTBCFullNode + the vm.TBC* package vars). vm.tbcChainParams is unexported and set
// internally to regtest by SetupTBCFullNode; it cannot be restored from package core, but no core test reads it and
// the core/vm tests run in a separate test binary, so the residual is benign.

import (
	"bytes"
	"context"
	"math/big"
	"testing"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/txscript"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

// setupCoreSyntheticFullNode stands up a real indexed tbc.Server (localnet/regtest, no P2P, no listeners, fresh temp
// leveldb) via the production vm.SetupTBCFullNode choke point and saves/restores the exported vm globals it mutates.
// Not parallel-safe (shared package globals). Mirrors core/vm's setupSyntheticFullNode.
func setupCoreSyntheticFullNode(t *testing.T) {
	t.Helper()

	prevNode, prevCfg, prevCtx := vm.TBCFullNode, vm.TBCFullNodeConfig, vm.MainCtx
	prevCancel, prevUpstream := vm.TBCFullNodeCtxCancel, vm.TBCUpstreamTip

	ctx, cancel := context.WithCancel(context.Background())

	cfg := tbc.NewDefaultConfig()
	cfg.Network = "localnet"
	cfg.LevelDBHome = t.TempDir()
	cfg.PeersWanted = 0
	cfg.ListenAddress = ""
	cfg.PrometheusListenAddress = ""
	cfg.PprofListenAddress = ""
	cfg.AutoIndex = false
	cfg.MempoolEnabled = false
	// MaxCachedTxs stays at the NewDefaultConfig default (1e6); the UTXO indexer divides by it.

	require.NoError(t, vm.SetupTBCFullNode(ctx, cfg))

	t.Cleanup(func() {
		if vm.TBCFullNodeCtxCancel != nil {
			vm.TBCFullNodeCtxCancel()
		}
		cancel()
		deadline := time.Now().Add(5 * time.Second)
		for vm.TBCFullNode != nil && vm.TBCFullNode.Running() && time.Now().Before(deadline) {
			time.Sleep(10 * time.Millisecond)
		}
		vm.TBCFullNode, vm.TBCFullNodeConfig, vm.MainCtx = prevNode, prevCfg, prevCtx
		vm.TBCFullNodeCtxCancel, vm.TBCUpstreamTip = prevCancel, prevUpstream
	})

	require.Eventually(t, func() bool {
		if vm.TBCFullNode == nil || !vm.TBCFullNode.Running() {
			return false
		}
		_, _, err := vm.TBCFullNode.BlockHeaderBest(vm.MainCtx)
		return err == nil
	}, 30*time.Second, 10*time.Millisecond, "full node must open its DB and insert the regtest genesis")
}

// mineCoreRegtestFullBlock builds a complete synthetic regtest block (BIP34 coinbase paying value to pkScript, correct
// merkle root, header mined to the regtest PowLimit). Mirrors core/vm's mineRegtestFullBlock.
func mineCoreRegtestFullBlock(t *testing.T, prev *wire.BlockHeader, bip34Height int32, pkScript []byte, value int64, extraNonce uint32) *wire.MsgBlock {
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

	merkles := blockchain.BuildMerkleTreeStore([]*btcutil.Tx{btcutil.NewTx(cb)}, false)
	hdr := wire.BlockHeader{
		Version:    4,
		PrevBlock:  prev.BlockHash(),
		MerkleRoot: *merkles[len(merkles)-1],
		Timestamp:  prev.Timestamp.Add(60 * time.Second),
		Bits:       uint32(0x207fffff), // chaincfg.RegressionNetParams.PowLimitBits
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
	require.True(t, mined, "must mine a regtest full block within 2^22 nonces")
	return &wire.MsgBlock{Header: hdr, Transactions: []*wire.MsgTx{cb}}
}

// TestRunHvmSnapWaiterEndToEnd drives the full snap-sync completion path. It arms the snap latch, feeds the full node a
// 3-block synthetic regtest chain (headers + blocks, intentionally NOT pre-indexed so completion does the indexing),
// pins the hVM base to the L2 genesis (whose body is on disk), and calls SnapSyncHvm. The detached waiter must find
// all BTC data available on its first poll, claim completion, reset the lightweight view, bulk-load the headers up to
// the BTC tip, index the full node, set safe/finalized, and mark finished.
func TestRunHvmSnapWaiterEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real indexed TBC full node plus a lightweight node on disk")
	}

	now := uint64(time.Now().Unix())
	hvm0Time := now - 10_000 // IsHvm0(now) true
	// Order matters for teardown: set up the full node FIRST, the chain SECOND, so (t.Cleanup is LIFO) chain.Stop —
	// which joins the detached waiter via hvmSnapWg.Wait — runs BEFORE the full node is cancelled/nil'd. Otherwise a
	// require.Eventually timeout or a mid-test failure would tear down vm.TBCFullNode while the waiter still derefs it
	// (data race + nil-deref that masks the real failure).
	setupCoreSyntheticFullNode(t)
	chain, btcGenesis := newRegtestChainWithLightTBC(t, hvm0Time)

	// A deterministic regtest P2PKH script for the coinbases.
	pkh := bytes.Repeat([]byte{0x42}, 20)
	addr, err := btcutil.NewAddressPubKeyHash(pkh, &chaincfg.RegressionNetParams)
	require.NoError(t, err)
	pkScript, err := txscript.PayToAddrScript(addr)
	require.NoError(t, err)

	// Build BTC chain genesis -> b1 -> b2 -> b3, feed the full node (headers + blocks only; the completion path
	// indexes it via updateFullTBCToLightweight).
	const n = 3
	prev := btcGenesis
	blocks := make([]*wire.MsgBlock, 0, n)
	headers := make([]*wire.BlockHeader, 0, n)
	for i := 0; i < n; i++ {
		blk := mineCoreRegtestFullBlock(t, prev, int32(i+1), pkScript, int64(50*1e8), uint32(i)*100_000+1)
		blocks = append(blocks, blk)
		h := blk.Header
		headers = append(headers, &h)
		prev = &blocks[i].Header
	}
	_, _, _, count, err := vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, &wire.MsgHeaders{Headers: headers})
	require.NoError(t, err)
	require.Equal(t, n, count)
	for i, b := range blocks {
		_, err = vm.TBCFullNode.BlockInsert(vm.MainCtx, b)
		require.NoError(t, err, "block %d must insert", i+1)
	}
	btcTip := blocks[n-1].Header.BlockHash()

	// Arm the latch (the gate claimHvmSnapWaiterSlot checks) and pin an hVM base whose FULL block is on local disk:
	// the L2 genesis. The waiter probes this via GetBlockByHash and refuses to complete on a base whose body is absent.
	chain.hvmSnapMu.Lock()
	chain.awaitingHvmSnapSync = true
	chain.hvmSnapMu.Unlock()
	hvmTip := chain.Genesis().Header()
	require.NotNil(t, chain.GetBlockByHash(hvmTip.Hash()), "the pinned hVM base block must be present on disk")

	// Kick off the detached waiter. All BTC data is already available, so it completes without waiting.
	quit := make(chan struct{})
	chain.SnapSyncHvm(&btcTip, hvmTip, quit)

	require.Eventually(t, chain.HvmSnapSyncCompleted, 30*time.Second, 20*time.Millisecond,
		"the snap waiter must complete when all BTC data is available and the hVM base body is on disk")

	// --- Assert the completion's observable effects ---

	// The lightweight view was reset and bulk-loaded up to the snap BTC tip.
	_, lightTip, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, btcTip, lightTip.BlockHash(), "the lightweight canonical tip must be the snap BTC tip after completion")

	// The full node was indexed and the upstream tip recorded as the lightweight tip.
	require.NotNil(t, vm.TBCUpstreamTip, "completion must record the upstream tip")
	require.Equal(t, btcTip, vm.TBCUpstreamTip.BlockHash(), "TBCUpstreamTip must be the lightweight tip after completion")

	// The full node's UTXO/Tx indexers — completion's core consensus output — must actually have ADVANCED off genesis
	// to (lightweight tip - hVMIndexerTipLag). With a 3-block chain and lag 2 that is block 1 (height 1). Asserting
	// this (not just the header tip / upstream pointer, which are set independently of indexing progress) is what
	// catches a regression turning updateFullTBCToLightweight's SyncIndexersToHash into a successful no-op.
	require.Equal(t, 2, hVMIndexerTipLag, "this test's expected indexed tip assumes lag==2; if the consensus constant changes, revisit the n-1-lag arithmetic below")
	wantIndexed := blocks[n-1-hVMIndexerTipLag].Header.BlockHash() // btcTip walked back lag blocks = block 1
	genesisHash := btcGenesis.BlockHash()
	si := vm.TBCFullNode.Synced(vm.MainCtx)
	require.Equal(t, wantIndexed, si.Utxo.Hash, "the UTXO indexer must advance to (tip - lag), not stay at genesis")
	require.Equal(t, wantIndexed, si.Tx.Hash, "the Tx indexer must advance to (tip - lag), not stay at genesis")
	require.NotEqual(t, genesisHash, si.Utxo.Hash, "the indexers must not have stayed at the regtest genesis")

	// Safe and finalized advanced to the pinned hVM base.
	require.Equal(t, hvmTip.Hash(), chain.CurrentSafeBlock().Hash(), "completion must set safe to the hVM snap base")
	require.Equal(t, hvmTip.Hash(), chain.CurrentFinalBlock().Hash(), "completion must set finalized to the hVM snap base")

	// The latch is finished and the waiter slot released (so Stop's hvmSnapWg.Wait returns).
	require.True(t, chain.HvmSnapSyncCompleted())
	require.False(t, chain.isAwaitingHvmSnapSync(), "a finished snap sync must clear the awaiting latch")
}

// TestRunHvmSnapWaiterRefusesBodyAbsentBase exercises the snap path's primary anti-corruption gate: the waiter must
// REFUSE to complete when the pinned hVM base block's body is not on local disk (the `else if GetBlockByHash(...) == nil`
// branch in runHvmSnapWaiter). Completing on a body-absent base would persist an unreachable upstream-state-id and
// permanently fail the post-snap reconciliation walk on every restart. The happy-path test always pins a body-PRESENT
// base, so deleting the gate survives it; this drives the gate with all BTC data available but a fabricated, not-on-disk
// hVM base and asserts the waiter never completes and the latch stays armed.
func TestRunHvmSnapWaiterRefusesBodyAbsentBase(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real indexed TBC full node plus a lightweight node on disk")
	}

	now := uint64(time.Now().Unix())
	hvm0Time := now - 10_000
	setupCoreSyntheticFullNode(t) // full node first so chain.Stop joins the waiter before the node is torn down
	chain, btcGenesis := newRegtestChainWithLightTBC(t, hvm0Time)

	pkh := bytes.Repeat([]byte{0x42}, 20)
	addr, err := btcutil.NewAddressPubKeyHash(pkh, &chaincfg.RegressionNetParams)
	require.NoError(t, err)
	pkScript, err := txscript.PayToAddrScript(addr)
	require.NoError(t, err)

	// Feed a 3-block chain so ALL BTC data is available — the waiter must reach the body-absent gate, not stall on
	// missing BTC data.
	const n = 3
	prev := btcGenesis
	blocks := make([]*wire.MsgBlock, 0, n)
	headers := make([]*wire.BlockHeader, 0, n)
	for i := 0; i < n; i++ {
		blk := mineCoreRegtestFullBlock(t, prev, int32(i+1), pkScript, int64(50*1e8), uint32(i)*100_000+1)
		blocks = append(blocks, blk)
		h := blk.Header
		headers = append(headers, &h)
		prev = &blocks[i].Header
	}
	_, _, _, _, err = vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, &wire.MsgHeaders{Headers: headers})
	require.NoError(t, err)
	for _, b := range blocks {
		_, err = vm.TBCFullNode.BlockInsert(vm.MainCtx, b)
		require.NoError(t, err)
	}
	btcTip := blocks[n-1].Header.BlockHash()

	chain.hvmSnapMu.Lock()
	chain.awaitingHvmSnapSync = true
	chain.hvmSnapMu.Unlock()

	// Pin the hVM base to a FABRICATED header whose block is NOT on local disk.
	hvmTip := &types.Header{Number: big.NewInt(999_999), Time: 1, Extra: []byte("synthetic-not-on-disk")}
	require.Nil(t, chain.GetBlockByHash(hvmTip.Hash()), "the fabricated hVM base block must NOT be present on disk")

	quit := make(chan struct{})
	chain.SnapSyncHvm(&btcTip, hvmTip, quit)

	// All BTC data is available, but the base body is absent -> the gate must keep the waiter from ever completing.
	require.Never(t, chain.HvmSnapSyncCompleted, 2500*time.Millisecond, 100*time.Millisecond,
		"the waiter must refuse to complete snap sync on a base whose block body is not on disk")
	require.True(t, chain.isAwaitingHvmSnapSync(), "the latch stays armed while the body-absent base blocks completion")

	// The waiter must still HOLD its slot — not give up and release it — within this window. The give-up horizon
	// (maxHvmSnapBodyAbsentPolls polls x ~1s) is far beyond 2.5s, so a correct waiter keeps the slot the whole time.
	// This is the assertion that actually discriminates an early-give-up mutation (which awaitingHvmSnapSync, cleared
	// only by completion, does NOT reflect: give-up releases the slot but leaves the latch armed).
	chain.hvmSnapMu.Lock()
	nWaiters := len(chain.hvmSnapWaiters)
	chain.hvmSnapMu.Unlock()
	require.Equal(t, 1, nWaiters, "the body-absent waiter must keep WAITING (slot held), not give up and release within the window")
}

// TestUpdateFullTBCToLightweightMissingData drives updateFullTBCToLightweight's !available orchestration — the
// missing-full-block and missing-header arms (blockchain.go:4247-4326), home of the back-walk nil-guard and the
// best-effort header re-injection. The happy-path snap test always feeds ALL data so available==true and this
// whole block is skipped; here the lightweight view leads the full node so the deferral arms run. (TBCAttemptBlockRefetch
// returns promptly with PeersWanted=0 — pm.Random() yields ErrNoConnectedPeers immediately — so this is in-process.)
func TestUpdateFullTBCToLightweightMissingData(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real indexed TBC full node plus a lightweight node on disk")
	}
	hvm0Time := uint64(time.Now().Unix()) - 10_000
	pkh := bytes.Repeat([]byte{0x42}, 20)
	addr, err := btcutil.NewAddressPubKeyHash(pkh, &chaincfg.RegressionNetParams)
	require.NoError(t, err)
	pkScript, err := txscript.PayToAddrScript(addr)
	require.NoError(t, err)

	build5 := func(t *testing.T, genesis *wire.BlockHeader) ([]*wire.MsgBlock, []*wire.BlockHeader) {
		blocks := make([]*wire.MsgBlock, 0, 5)
		hdrs := make([]*wire.BlockHeader, 0, 5)
		prev := genesis
		for i := 0; i < 5; i++ {
			blk := mineCoreRegtestFullBlock(t, prev, int32(i+1), pkScript, int64(50*1e8), uint32(i)*100_000+1)
			blocks = append(blocks, blk)
			h := blk.Header
			hdrs = append(hdrs, &h)
			prev = &blocks[i].Header
		}
		return blocks, hdrs
	}

	// missing-FULL-BLOCK arm: full node has all 5 headers but a HOLE in the blocks (h2 withheld) on the walk-back path
	// to (lightTip - lag) = h3 -> ErrFullTBCMissingFullBTCBlock.
	t.Run("missing-full-block", func(t *testing.T) {
		setupCoreSyntheticFullNode(t)
		chain, btcGenesis := newRegtestChainWithLightTBC(t, hvm0Time)
		blocks, hdrs := build5(t, btcGenesis)
		_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: hdrs}, hVMGenesisUpstreamId[:])
		require.NoError(t, err)
		_, _, _, _, err = vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, &wire.MsgHeaders{Headers: hdrs})
		require.NoError(t, err)
		for i, b := range blocks {
			if i == 1 {
				continue // withhold h2's full block
			}
			_, err = vm.TBCFullNode.BlockInsert(vm.MainCtx, b)
			require.NoError(t, err)
		}
		require.ErrorIs(t, chain.updateFullTBCToLightweight(), consensus.ErrFullTBCMissingFullBTCBlock,
			"a hole in the full blocks on the path to (lightTip-lag) must defer with the missing-full-block sentinel")
	})

	// missing-HEADER arm: full node has only h1 (h2..h5 headers absent), so the walk-back target h3 is unknown ->
	// the back-walk (the :4276 region) runs, re-injects the absent headers, and returns ErrFullTBCMissingBTCHeader
	// without panicking.
	t.Run("missing-header", func(t *testing.T) {
		setupCoreSyntheticFullNode(t)
		chain, btcGenesis := newRegtestChainWithLightTBC(t, hvm0Time)
		blocks, hdrs := build5(t, btcGenesis)
		_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: hdrs}, hVMGenesisUpstreamId[:])
		require.NoError(t, err)
		_, _, _, _, err = vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, &wire.MsgHeaders{Headers: hdrs[:1]})
		require.NoError(t, err)
		_, err = vm.TBCFullNode.BlockInsert(vm.MainCtx, blocks[0])
		require.NoError(t, err)
		var ufErr error
		require.NotPanics(t, func() { ufErr = chain.updateFullTBCToLightweight() }, "the missing-header back-walk must not panic")
		require.ErrorIs(t, ufErr, consensus.ErrFullTBCMissingBTCHeader,
			"an absent walk-back-target header in the full node must defer with the missing-header sentinel")
	})
}

// TestRunHvmSnapWaiterBodyAbsentGivesUp drives the body-absent GIVE-UP / slot-release path (blockchain.go:2038-2047),
// the documented anti-wedge defense. The default ~100-poll horizon is far beyond any test window, so it is lowered via
// the test-only hvmSnapBodyAbsentPollsLimit. With all BTC data available but the hVM base body absent, the waiter must
// eventually GIVE UP and release its slot — while NOT completing and leaving the latch armed (only completion clears it).
// The sibling TestRunHvmSnapWaiterRefusesBodyAbsentBase asserts the opposite (slot HELD) within its short window; this
// pins that the give-up `return` actually fires and frees the slot — a deletion of it survives that sibling test.
func TestRunHvmSnapWaiterBodyAbsentGivesUp(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real indexed TBC full node plus a lightweight node on disk")
	}
	hvm0Time := uint64(time.Now().Unix()) - 10_000
	setupCoreSyntheticFullNode(t)
	chain, btcGenesis := newRegtestChainWithLightTBC(t, hvm0Time)
	chain.hvmSnapBodyAbsentPollsLimit = 2 // lower the give-up horizon to ~2 polls so the release path is reachable

	pkh := bytes.Repeat([]byte{0x42}, 20)
	addr, err := btcutil.NewAddressPubKeyHash(pkh, &chaincfg.RegressionNetParams)
	require.NoError(t, err)
	pkScript, err := txscript.PayToAddrScript(addr)
	require.NoError(t, err)
	prev := btcGenesis
	blocks := make([]*wire.MsgBlock, 0, 3)
	headers := make([]*wire.BlockHeader, 0, 3)
	for i := 0; i < 3; i++ {
		blk := mineCoreRegtestFullBlock(t, prev, int32(i+1), pkScript, int64(50*1e8), uint32(i)*100_000+1)
		blocks = append(blocks, blk)
		h := blk.Header
		headers = append(headers, &h)
		prev = &blocks[i].Header
	}
	_, _, _, _, err = vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, &wire.MsgHeaders{Headers: headers})
	require.NoError(t, err)
	for _, b := range blocks {
		_, err = vm.TBCFullNode.BlockInsert(vm.MainCtx, b)
		require.NoError(t, err)
	}
	btcTip := blocks[2].Header.BlockHash()

	chain.hvmSnapMu.Lock()
	chain.awaitingHvmSnapSync = true
	chain.hvmSnapMu.Unlock()
	hvmTip := &types.Header{Number: big.NewInt(999_999), Time: 1, Extra: []byte("synthetic-not-on-disk")}
	require.Nil(t, chain.GetBlockByHash(hvmTip.Hash()))

	chain.SnapSyncHvm(&btcTip, hvmTip, make(chan struct{}))

	// The waiter must GIVE UP (release its slot) once the lowered horizon is hit.
	require.Eventually(t, func() bool {
		chain.hvmSnapMu.Lock()
		n := len(chain.hvmSnapWaiters)
		chain.hvmSnapMu.Unlock()
		return n == 0
	}, 15*time.Second, 100*time.Millisecond, "the body-absent waiter must give up and RELEASE its slot at the poll horizon")
	require.False(t, chain.HvmSnapSyncCompleted(), "giving up must NOT complete the snap sync")
	require.True(t, chain.isAwaitingHvmSnapSync(), "give-up releases the slot but leaves the latch armed (only completion clears it)")
}
