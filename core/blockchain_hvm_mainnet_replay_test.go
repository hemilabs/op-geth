// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// One-time verification (manual, gated): replay every Bitcoin Attributes Deposited transaction ever
// committed on Hemi mainnet — reconstructed offline from every L2 block's BtcAttributesDeposited txs via
// a Hemi mainnet RPC — through the full hVM apply path applyHvmHeaderConsensusUpdate (enforce=true): the
// contextual-difficulty validator, AddExternalHeaders, the canonical-tip claim check, and the
// upstream-state-id chaining. Unlike the validator-only check in
// core/vm/btcdiff_mainnet_history_verify_test.go, this exercises the entire hVM state transition against a
// real lightweight TBC node seeded at the mainnet hVM genesis. A clean replay confirms the whole system
// accepts the entire mainnet history under contextual-difficulty enforcement — the basis for enforcing it
// from genesis rather than gating it behind a separate activation fork.
//
// Reads the reconstructed file from HEMI_MAINNET_VERIFY (or a default path); skips when absent, so it
// never runs in normal CI.

import (
	"bufio"
	"bytes"
	"context"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"testing"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"

	"github.com/hemilabs/heminetwork/service/tbc"
)

const (
	mainnetHvmGenesisHeightReplay = uint64(883092)
	mainnetHvmGenesisHeaderReplay = "0000003efaaa2ba65de684c512bb67ef115298d1d16bcb49b16c02000000000000000000ed31a56788c4488afc4ee69e0791ad6aeeb9ea05f069e0fdde6159068765ad3f4128a96726770217e7f41c86"
)

func TestHvmReplaysAllMainnetBtcAttrThroughApplyPath(t *testing.T) {
	// Manual one-time verification: provide the reconstructed NDJSON BtcAttr-header file (reconstructed
	// offline from the chain's BtcAttributesDeposited txs). Defaults to the path below; override with
	// HEMI_MAINNET_VERIFY=<path>. Skipped when the file is absent, so it never runs in normal CI.
	headersFile := os.Getenv("HEMI_MAINNET_VERIFY")
	if headersFile == "" {
		headersFile = "/tmp/btcattr_headers.ndjson"
	}
	f, err := os.Open(headersFile)
	if err != nil {
		t.Skipf("reconstructed BtcAttr file %s not present (set HEMI_MAINNET_VERIFY=<path> to override) (%v)", headersFile, err)
	}
	defer f.Close()

	// A BlockChain with hVM Phase 0 active at any positive timestamp (synthetic replay blocks use Time=2000).
	hvm0 := uint64(1000)
	cfg := *params.TestChainConfig
	cfg.Hvm0Time = &hvm0
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}
	chain, err := NewBlockChain(rawdb.NewMemoryDatabase(), gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)

	// Attach a real lightweight TBC node configured for Bitcoin mainnet at the mainnet hVM genesis. We do
	// not go through initHvmHeaderNode because its genesis-pairing guard refuses an unpinned (mainnet) pair;
	// we replicate its post-guard setup directly.
	raw, err := hex.DecodeString(mainnetHvmGenesisHeaderReplay)
	require.NoError(t, err)
	var genHdr wire.BlockHeader
	require.NoError(t, genHdr.Deserialize(bytes.NewReader(raw)))

	tbcCfg := tbc.NewDefaultConfig()
	tbcCfg.ExternalHeaderMode = true
	tbcCfg.EffectiveGenesisBlock = &genHdr
	tbcCfg.GenesisHeightOffset = mainnetHvmGenesisHeightReplay
	// Test-only speedups (none change apply semantics): put the lightweight leveldb on tmpfs to avoid disk
	// fsync/compaction stalls across the ~69k per-BtcAttr commits, and give it a large header cache so the
	// validator walks resolve from memory. The header set (~69k) fits easily.
	ldbHome := t.TempDir()
	if shm, e := os.MkdirTemp("/dev/shm", "hvmreplay"); e == nil {
		ldbHome = shm
		t.Cleanup(func() { _ = os.RemoveAll(shm) })
	}
	tbcCfg.LevelDBHome = ldbHome
	tbcCfg.BlockheaderCacheSize = "1024mb"
	tbcCfg.BlockCacheSize = "0"
	tbcCfg.AutoIndex = false
	tbcCfg.BlockSanity = true
	tbcCfg.MaxCachedTxs = 0
	tbcCfg.MempoolEnabled = false
	tbcCfg.Network = "mainnet"

	srv, err := tbc.NewServer(tbcCfg)
	require.NoError(t, err)
	require.NoError(t, srv.ExternalHeaderSetup(chain.ctx, hVMGenesisUpstreamId[:]))
	t.Cleanup(func() { _ = srv.ExternalHeaderTearDown() })
	chain.tbcHeaderNode = srv
	chain.tbcHeaderNodeConfig = tbcCfg
	chain.hvmEnabled = true

	type line struct {
		Blk  uint64   `json:"blk"`
		Tip  string   `json:"tip"`
		Hdrs []string `json:"hdrs"`
	}
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1<<20), 8<<20)
	var parent common.Hash
	n := 0
	var lastTipClaim string
	t0 := time.Now()
	for sc.Scan() {
		var l line
		require.NoError(t, json.Unmarshal(sc.Bytes(), &l))

		tipHash, err := chainhash.NewHashFromStr(l.Tip)
		require.NoErrorf(t, err, "bad tip hash at L2 block %d", l.Blk)
		hdrs := make([]wire.BlockHeader, 0, len(l.Hdrs))
		for _, hh := range l.Hdrs {
			hraw, err := hex.DecodeString(hh)
			require.NoError(t, err)
			var bh wire.BlockHeader
			require.NoErrorf(t, bh.Deserialize(bytes.NewReader(hraw)), "decode header at L2 block %d", l.Blk)
			hdrs = append(hdrs, bh)
		}
		btcAttr, err := types.MakeBtcAttributesDepositedTx(tipHash, hdrs)
		require.NoError(t, err)

		n++
		hdr := &types.Header{Number: big.NewInt(int64(n)), Time: 2000, ParentHash: parent}
		blk := types.NewBlockWithHeader(hdr).WithBody(types.Body{Transactions: types.Transactions{types.NewTx(btcAttr)}})
		// keep every block in the holding pen: the apply path looks up the parent block by the previous
		// upstream-state-id (= parent block hash) to verify the chain.
		chain.tempBlocks[blk.Hash().String()] = blk
		chain.tempHeaders[blk.Hash().String()] = blk.Header()

		if err := chain.applyHvmHeaderConsensusUpdate(blk.Header(), false, true); err != nil {
			t.Fatalf("apply FAILED at BtcAttr #%d (L2 block %d, %d headers, claimed tip %s): %v",
				n, l.Blk, len(l.Hdrs), l.Tip, err)
		}
		parent = blk.Hash()
		lastTipClaim = l.Tip
		if n%5000 == 0 {
			el := time.Since(t0).Seconds()
			fmt.Fprintf(os.Stderr, "[replay] applied %d BtcAttr txs  %.0f/s\n", n, float64(n)/el)
		}
	}
	require.NoError(t, sc.Err())

	_, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, lastTipClaim, tipAfter.BlockHash().String(),
		"after replaying all BtcAttr txs, the lightweight hVM BTC tip must equal the last committed canonical-tip claim")
	t.Logf("REPLAYED %d BtcAttr txs through applyHvmHeaderConsensusUpdate (enforce=true); all accepted; final hVM BTC tip = %s",
		n, tipAfter.BlockHash().String())
}
