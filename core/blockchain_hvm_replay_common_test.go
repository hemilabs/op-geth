// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Shared body of the apply-path differential-replay gate, parameterized by network. Both the mainnet and testnet3
// replay tests call replayBtcAttrThroughApplyPath, running real committed history end-to-end through the full apply
// path: AddExternalHeaders, cumulative-work canonical-tip selection, the per-block cbh==CanonicalTip claim check,
// the contextual-difficulty validator (enforce=true), and upstream-state-id chaining. The validator-only vm
// harnesses do NOT recompute the canonical tip, so this is the only lane covering that computation plus the
// per-block cbh==CanonicalTip identity over real history.
//
// The committed fixtures are a single LINEAR chain, so this exercises only the trivial extend-the-tip case — not
// the competing-branch / equal-work tie-break selection arm (real committed history has no forks). The
// wrong-CanonicalTip REJECT/rollback side is covered by the synthetic regtest tests
// (TestHvmApplyPathRollsBackOnWrongCanonicalTipRegtest and the curTip!=CanonicalTip self-heal tests).

import (
	"bufio"
	"bytes"
	"context"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"strconv"
	"testing"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/params"

	"github.com/hemilabs/heminetwork/service/tbc"
)

type replayParams struct {
	envPrefix        string // "HEMI_MAINNET" / "HEMI_TESTNET3" (drives _VERIFY/_EXPECT_TIP_HEIGHT/_EXPECT_TIP_HASH)
	defaultPath      string // default fixture path when _VERIFY is unset
	defaultCommitted bool   // true => the default path is a COMMITTED repo invariant whose absence FAILS (not skips)
	expectTipHash    string // pinned REAL Bitcoin tip hash of the committed default fixture (env-independent clamp)
	network          string // TBC network: "mainnet" / "testnet3"
	genesisHeight    uint64
	genesisHeader    string // 80-byte hex
	genesisHash      string // display-hex block hash of genesisHeader (genesis end of the real-chain clamp)
}

func replayBtcAttrThroughApplyPath(t *testing.T, p replayParams) {
	// Network-scoped enforcement (mirrors core/vm historyGateInput): enforce only when THIS network's VERIFY var
	// is explicitly set ("requested"). Under the global HEMI_HISTORY_GATE_REQUIRED, a non-requested network is
	// skipped, so one network's absent fixture cannot redden the other's lane, and a stale/planted default path
	// cannot be trusted as the enforced input.
	verifyEnv := p.envPrefix + "_VERIFY"
	headersFile := os.Getenv(verifyEnv)
	requested := headersFile != ""
	if headersFile == "" {
		headersFile = p.defaultPath
	}
	f, err := os.Open(headersFile)
	if err != nil {
		if requested && os.Getenv("HEMI_HISTORY_GATE_REQUIRED") != "" {
			t.Fatalf("HEMI_HISTORY_GATE_REQUIRED is set and %s=%s, but that reconstructed BtcAttr file is absent: "+
				"the apply-path differential-replay gate must not be a no-op in this CI lane (%v)", verifyEnv, headersFile, err)
		}
		if !requested && p.defaultCommitted {
			// The committed default fixture is a repo invariant: its absence must FAIL the apply-path replay,
			// never silently skip — this lane is the ONLY one that exercises the cumulative-work CanonicalTip
			// selection + per-block tip-claim, so it must stay CI-resident like the validator lane.
			t.Fatalf("the COMMITTED default fixture %s could not be opened — it is a repo invariant; the apply-path "+
				"differential-replay gate must not silently revert to skip. Either the fixture was deleted/renamed, OR "+
				"this test was run from a non-package CWD (the path is relative to ./core; `go test ./core/` sets CWD "+
				"correctly, but a `go test -c` binary run from elsewhere will not) (%v)", headersFile, err)
		}
		t.Skipf("reconstructed BtcAttr file %s not present (set %s=<path>, or HEMI_HISTORY_GATE_REQUIRED=1 to enforce) (%v)", headersFile, verifyEnv, err)
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

	// Attach a real lightweight TBC node configured for the Bitcoin network at the hVM genesis. We do not go
	// through initHvmHeaderNode (its genesis-pairing guard refuses an unpinned mainnet pair); we replicate its
	// post-guard setup directly. The genesis hex is asserted to hash to the pinned real genesis.
	raw, err := hex.DecodeString(p.genesisHeader)
	require.NoError(t, err)
	var genHdr wire.BlockHeader
	require.NoError(t, genHdr.Deserialize(bytes.NewReader(raw)))
	require.Equalf(t, p.genesisHash, genHdr.BlockHash().String(),
		"%s genesis header hex hashes wrong — the pinned genesis end of the real-chain clamp is corrupt (typo / btcd serialization drift)", p.network)

	tbcCfg := tbc.NewDefaultConfig()
	tbcCfg.ExternalHeaderMode = true
	tbcCfg.EffectiveGenesisBlock = &genHdr
	tbcCfg.GenesisHeightOffset = p.genesisHeight
	// Test-only speedups (none change apply semantics): put the lightweight leveldb on tmpfs to avoid disk
	// fsync/compaction stalls across the per-BtcAttr commits, and give it a large header cache so validator
	// walks resolve from memory.
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
	tbcCfg.Network = p.network

	srv, err := tbc.NewServer(tbcCfg)
	require.NoError(t, err)
	require.NoError(t, srv.ExternalHeaderSetup(chain.ctx, hVMGenesisUpstreamId[:]))
	t.Cleanup(func() { _ = srv.ExternalHeaderTearDown() })
	chain.tbcHeaderNode = srv
	chain.tbcHeaderNodeConfig = tbcCfg
	chain.hvmEnabled = true
	// This setup bypasses initHvmHeaderNode, which normally sets hvmDiffEnforceable. The replay runs a
	// correct-params node (mainnet/testnet3 over its real genesis), so enforcement MUST be on — otherwise the
	// difficulty-enforcement gate in applyHvmHeaderConsensusUpdate would silently turn enforceBTCDiff=true into a
	// no-op and the whole apply-path differential gate would validate nothing.
	chain.hvmDiffEnforceable.Store(true)

	type line struct {
		Blk  uint64   `json:"blk"`
		Tip  string   `json:"tip"`
		Hdrs []string `json:"hdrs"`
	}
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1<<20), 8<<20)
	var parent common.Hash
	n := 0
	sumHeaders := 0
	var lastTipClaim string
	t0 := time.Now()
	lineNo := 0
	for sc.Scan() {
		lineNo++
		raw := bytes.TrimSpace(sc.Bytes())
		if len(raw) == 0 {
			continue // tolerate a trailing/blank line (parity with the validator lanes)
		}
		var l line
		require.NoErrorf(t, json.Unmarshal(raw, &l), "bad ndjson at line %d", lineNo)

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
		sumHeaders += len(l.Hdrs)
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
			fmt.Fprintf(os.Stderr, "[replay %s] applied %d BtcAttr txs  %.0f/s\n", p.network, n, float64(n)/el)
		}
	}
	require.NoError(t, sc.Err())

	tipHeight, tipAfter, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err)
	require.Equal(t, lastTipClaim, tipAfter.BlockHash().String(),
		"after replaying all BtcAttr txs, the lightweight hVM BTC tip must equal the last committed canonical-tip claim")

	// Env-independent real-chain binding for the COMMITTED default lane. The lastTipClaim==tipAfter check above is
	// CIRCULAR (lastTipClaim is the fixture's own last line), and the EXPECT_TIP_HASH binding below is env-gated. So
	// for the committed bounded fixture (not an env override), also pin the replayed final tip to the known real
	// Bitcoin tip hash — a swapped/forged committed fixture then cannot pass even in a bare `go test ./core/` with no
	// env. The env-override (live-tip) lane ends at a DIFFERENT tip and uses EXPECT_TIP_HASH, so this binds only the default.
	if !requested && p.defaultCommitted {
		require.Equal(t, p.expectTipHash, tipAfter.BlockHash().String(),
			"committed bounded fixture must replay to its pinned REAL Bitcoin tip (env-independent real-chain clamp)")
	}

	// Anti-vacuous + coverage (mirror the vm harnesses): an empty / single-genesis-echo / truncated fixture must
	// NOT pass green. Hard-required in the enforcing CI lane (HEMI_HISTORY_GATE_REQUIRED + this network requested);
	// logged otherwise.
	enforcing := requested && os.Getenv("HEMI_HISTORY_GATE_REQUIRED") != ""
	gate := func(ok bool, format string, args ...interface{}) {
		if ok {
			return
		}
		if enforcing {
			t.Fatalf(format, args...)
		}
		t.Logf("(non-enforcing) "+format, args...)
	}
	gate(sumHeaders > 0, "vacuous: replayed %d BtcAttr txs but 0 Bitcoin headers — nothing was applied/validated", n)

	hEnv := p.envPrefix + "_EXPECT_TIP_HEIGHT"
	if pin := os.Getenv(hEnv); pin != "" {
		want, perr := strconv.ParseUint(pin, 10, 64)
		require.NoErrorf(t, perr, "%s=%q not a uint64", hEnv, pin)
		gate(tipHeight >= want, "coverage shortfall: replay reached BTC tip height %d but %s requires >= %d — fixture truncated/stale", tipHeight, hEnv, want)
	} else {
		gate(false, "%s not set: the enforcing lane must pin the expected tip height so a truncated fixture cannot pass (reached %d)", hEnv, tipHeight)
	}
	// Real-chain binding for the env-override lane: pin the expected real Bitcoin tip hash. The store tip must
	// equal it, which (genesis pinned + PrevBlock linkage) forces the replayed chain to be the real committed
	// chain, defeating the circularity of the lastTipClaim==tipAfter check above.
	sEnv := p.envPrefix + "_EXPECT_TIP_HASH"
	if want := os.Getenv(sEnv); want != "" {
		gate(tipAfter.BlockHash().String() == want,
			"real-chain binding FAILED: replay final tip %s != pinned real tip %s — fixture is not the real committed chain", tipAfter.BlockHash().String(), want)
	} else {
		gate(false, "%s not set: the enforcing lane must pin the real Bitcoin tip hash to bind the replay to the real chain (reached %s)", sEnv, tipAfter.BlockHash().String())
	}
	// Retarget-boundary coverage, ENFORCE-BAND-RELATIVE: headers in [genesis, genesis+clearance) are DEFERRED (the
	// validator cannot walk back to the retarget anchor), so a boundary inside that band triggers no recompute.
	// Merely requiring "span crosses a 2016 boundary" would pass when the only crossed boundary lies in the deferred
	// band; instead require a boundary AT/ABOVE the enforce floor, where the recompute is actually enforced.
	clearance, err := vm.BTCFloorClearanceForNetwork(p.network)
	require.NoErrorf(t, err, "floor clearance for network %s", p.network)
	enforceFrom := p.genesisHeight + clearance
	const blocksPerRetarget = 2016
	highestBoundary := (tipHeight / blocksPerRetarget) * blocksPerRetarget
	gate(highestBoundary >= enforceFrom,
		"replay span [%d,%d] reaches no ENFORCED retarget boundary: highest boundary %d < enforce floor %d (genesis+clearance) — the difficulty RECOMPUTE was deferred, never enforced; fixture must span a boundary above the floor-clearance band", p.genesisHeight, tipHeight, highestBoundary, enforceFrom)
	t.Logf("REPLAYED %s: %d BtcAttr txs (%d headers) through applyHvmHeaderConsensusUpdate (enforce=true); all accepted; final hVM BTC tip = %s @ height %d",
		p.network, n, sumHeaders, tipAfter.BlockHash().String(), tipHeight)
}
