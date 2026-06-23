// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

// The differential-replay gate (mainnet): replay every Bitcoin header ever committed to hVM consensus
// on Hemi mainnet — reconstructed offline from the BtcAttributesDeposited txs of every L2 block — through
// the EXACT contextual-difficulty + PoW validator the apply path runs, under MainNetParams, and confirm it
// would not REJECT any historical block. Zero genuine contextual/PoW RuleErrors above the floor-clearance
// band means the committed history is "clean" and difficulty validation can be enabled per node (each on its
// correct network) with no activation fork. See cmd/hvm-btcattr-reconstruct for producing the NDJSON.
//
// Classification is aligned EXACTLY to the live apply path (core/blockchain.go applyHvmHeaderConsensusUpdate
// -> ValidateBTCHeaderBatchForNetwork): a btcd RuleError / PoW failure is a real reject (the clean-history
// violation this gate checks for); ErrBTCHeaderContextUnavailable and ErrBTCBatchUnconnected are NOT rejects on the live path
// (recoverable / deferred), so they are diagnostics here, not failures — matching the testnet3 harness.
// An optional HEMI_MAINNET_EXTRA_HEADERS file supplies explorer-recovered canonical reorg-link headers as
// ancestry only, to bridge gaps the delta reconstruction is missing.
//
// CI ENFORCEMENT (two tiers):
//   1. DEFAULT (no env): replays the committed bounded fixture testdata/btcattr_mainnet_history.ndjson, a
//      repo invariant — if it is missing, historyGateInput FAILS (does not skip), so the mainnet gate can never
//      silently revert to a no-op in `go test ./...`. Proves the contextual-difficulty/PoW MATH over real
//      headers incl. a retarget recompute, but is BOUNDED (883093..887040) — not full live-tip history.
//   2. LIVE-TIP lane: set HEMI_MAINNET_VERIFY=<path> (reconstructed by cmd/hvm-btcattr-reconstruct against real
//      L2 chaindata) + HEMI_HISTORY_GATE_REQUIRED=1 (turns an absent override into a hard FAIL) +
//      HEMI_MAINNET_EXPECT_TIP_HEIGHT/HASH (anti-truncation coverage pin). Additionally covers BtcAttr
//      reconstruction faithfulness + full coverage to the pinned tip. The Makefile hvm-history-gate target runs it.
//
// Mainnet hVM genesis. The {883092, header, …188eda8} pair is the single shared source of truth in
// hvm_genesis.go (MainnetHvmGenesis{Height,Header,Hash}); core's checkpoint map and the apply-path replay test
// consume the SAME constant, and TestMainnetHvmGenesisHeaderHashesToPin welds the header bytes to the hash, so
// a re-genesis cannot re-root this gate while production uses a different pair.
//   --hvm.genesisheight=883092
//   --hvm.genesisheader=0000003efaaa2ba6...e7f41c86

import (
	"bufio"
	"bytes"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"math/big"
	"os"
	"sort"
	"strconv"
	"testing"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/core/types"
)

// assertBtcParamsPinned fails if the load-bearing btcd consensus params the gate's verdict depends on have
// drifted (e.g. a btcd bump silently changing TestNet3Params). floorClearance and the retarget/min-difficulty
// math are pure functions of these, so a drift would silently re-define what "clean" means. go.sum alone does
// not guard the values; pin them where the verdict is computed.
func assertBtcParamsPinned(t *testing.T, params *chaincfg.Params, reduceMinDiff bool) {
	t.Helper()
	if got := int64(params.TargetTimespan / params.TargetTimePerBlock); got != 2016 {
		t.Fatalf("btcd param drift: %s BlocksPerRetarget=%d, want 2016 — the difficulty verdict basis changed", params.Name, got)
	}
	if params.PowLimitBits != 0x1d00ffff {
		t.Fatalf("btcd param drift: %s PowLimitBits=%08x, want 1d00ffff", params.Name, params.PowLimitBits)
	}
	// Pin params.PowLimit (the big.Int target CEILING) too, not just PowLimitBits: the per-header
	// PoW check (checkBTCHeaderPoWWith -> blockchain.CheckProofOfWork) uses PowLimit, NOT PowLimitBits, and they
	// are independent struct fields. Real mainnet/testnet3 headers satisfy any loosened ceiling, so a btcd bump /
	// fork-local edit that raised PowLimit would keep the gate CLEAN (powRejected=0) undetected — this pin is the
	// only defense. Both MainNetParams and TestNet3Params share PowLimit = 2^224 - 1.
	wantPowLimit := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 224), big.NewInt(1))
	if params.PowLimit == nil || params.PowLimit.Cmp(wantPowLimit) != 0 {
		t.Fatalf("btcd param drift: %s PowLimit=%v, want 2^224-1 (%v) — the PoW-check ceiling changed", params.Name, params.PowLimit, wantPowLimit)
	}
	if params.RetargetAdjustmentFactor != 4 {
		t.Fatalf("btcd param drift: %s RetargetAdjustmentFactor=%d, want 4", params.Name, params.RetargetAdjustmentFactor)
	}
	if params.ReduceMinDifficulty != reduceMinDiff {
		t.Fatalf("btcd param drift: %s ReduceMinDifficulty=%v, want %v", params.Name, params.ReduceMinDifficulty, reduceMinDiff)
	}
}

func parseHeader80(h string) (*wire.BlockHeader, error) {
	raw, err := hex.DecodeString(h)
	if err != nil {
		return nil, err
	}
	var bh wire.BlockHeader
	if err := bh.Deserialize(bytes.NewReader(raw)); err != nil {
		return nil, err
	}
	return &bh, nil
}

// historyGateInput opens the reconstructed NDJSON file. It FAILS rather than skips in two cases so the gate
// cannot be a silent no-op: (1) HEMI_HISTORY_GATE_REQUIRED is set with an explicit HEMI_<NET>_VERIFY override
// (the live-tip CI lane), and (2) defaultCommitted is true and the committed default fixture is absent — a
// committed fixture is a repo invariant, not an optional dev input, so its deletion/rename must redden the
// default `go test ./...` lane (it must not silently revert to t.Skip). A lane with no committed fixture
// (defaultCommitted=false — e.g. a live-tip reconstruction written to /tmp) still skips when absent. Both
// shipped lanes, mainnet and testnet3, use defaultCommitted=true committed fixtures.
func historyGateInput(t *testing.T, envVar, defaultPath string, defaultCommitted bool) *os.File {
	t.Helper()
	path := os.Getenv(envVar)
	// "Requested" = this network's own VERIFY var is explicitly set. Enforcement is network-scoped: under the
	// global HEMI_HISTORY_GATE_REQUIRED, a network whose VERIFY var is UNSET is not part of this lane and is
	// skipped — so a single enforced `go test ./core/vm/` (both networks in one process) does not redden on the
	// other network's absent fixture. The enforcing lane MUST therefore set HEMI_<NET>_VERIFY; forgetting it
	// skips (the fixture is then absent) rather than silently passing a no-op.
	requested := path != ""
	if path == "" {
		path = defaultPath
	}
	f, err := os.Open(path)
	if err != nil {
		if requested && os.Getenv("HEMI_HISTORY_GATE_REQUIRED") != "" {
			t.Fatalf("HEMI_HISTORY_GATE_REQUIRED is set and %s=%s, but that reconstructed history file is absent: "+
				"the differential-replay gate must not be a no-op in this CI lane (%v)", envVar, path, err)
		}
		if !requested && defaultCommitted {
			t.Fatalf("the committed default fixture %s is missing — it is a repo invariant, not an optional input; "+
				"the differential-replay gate must not silently revert to skip (restore the fixture or fix the path) (%v)", path, err)
		}
		t.Skipf("reconstructed history file %s not present (set %s=<path>, or HEMI_HISTORY_GATE_REQUIRED=1 to enforce) (%v)", path, envVar, err)
	}
	return f
}

// assertCoveragePin binds the fixture to the REAL committed chain. It reads two env vars under envPrefix:
//
//	<prefix>_EXPECT_TIP_HEIGHT — the committed-connected set must reach >= this BTC height (anti-truncation).
//	<prefix>_EXPECT_TIP_HASH   — a REAL Bitcoin block hash at the tip. This is the load-bearing real-chain
//	  binding: a connected chain from the pinned genesis to a pinned real tip forces EVERY intermediate header
//	  to be the real ancestor (each hash is committed by the next header's PrevBlock), so a fabricated or
//	  EXTRA-laundered chain — which a PoW-floor-only / self-referential gate would otherwise accept — cannot
//	  reach it. Both are HARD-REQUIRED when HEMI_HISTORY_GATE_REQUIRED is set; logged otherwise.
func assertCoveragePin(t *testing.T, envPrefix string, height, committedAtL2 map[chainhash.Hash]uint64, headersByHash map[chainhash.Hash]*wire.BlockHeader) {
	t.Helper()
	// Network-scoped enforcement (see historyGateInput): enforce only when THIS network was requested.
	enforcing := os.Getenv(envPrefix+"_VERIFY") != "" && os.Getenv("HEMI_HISTORY_GATE_REQUIRED") != ""
	// Max over the COMMITTED-and-connected set only (not `height`, which includes EXTRA ancestry).
	var maxH uint64
	for h, hgt := range height {
		if _, committed := committedAtL2[h]; !committed {
			continue
		}
		if hgt > maxH {
			maxH = hgt
		}
	}

	hEnv := envPrefix + "_EXPECT_TIP_HEIGHT"
	haveHeightPin := false
	var wantHeight uint64
	if v := os.Getenv(hEnv); v != "" {
		w, err := strconv.ParseUint(v, 10, 64)
		if err != nil {
			t.Fatalf("%s=%q is not a uint64: %v", hEnv, v, err)
		}
		wantHeight, haveHeightPin = w, true
		if maxH < wantHeight {
			t.Fatalf("coverage shortfall: connected committed set reaches height %d but %s requires >= %d — fixture is truncated/stale", maxH, hEnv, wantHeight)
		}
		t.Logf("coverage OK: connected committed set reaches height %d (>= pin %s=%d)", maxH, hEnv, wantHeight)
	} else if enforcing {
		t.Fatalf("%s not set but the gate is enforced for this network: pin the expected tip height (connected committed max height=%d)", hEnv, maxH)
	} else {
		t.Logf("coverage pin %s unset; connected committed set max height=%d", hEnv, maxH)
	}

	sEnv := envPrefix + "_EXPECT_TIP_HASH"
	if v := os.Getenv(sEnv); v != "" {
		want, err := chainhash.NewHashFromStr(v)
		if err != nil {
			t.Fatalf("%s=%q is not a btc block hash: %v", sEnv, v, err)
		}
		if _, present := headersByHash[*want]; !present {
			t.Fatalf("real-chain binding FAILED: pinned tip %s (%s) is absent from the committed set — the fixture does not contain the real chain", v, sEnv)
		}
		if _, committed := committedAtL2[*want]; !committed {
			t.Fatalf("real-chain binding FAILED: pinned tip %s is present only as EXTRA ancestry, not a committed header", v)
		}
		hgt, ok := height[*want]
		if !ok {
			t.Fatalf("real-chain binding FAILED: pinned tip %s does not connect to the pinned genesis", v)
		}
		// Cross-pin consistency: the cryptographic clamp (tip HASH) and the coverage clamp (tip HEIGHT) must
		// describe the SAME endpoint. Otherwise an operator could pin a real hash at one height while pinning a
		// LARGER EXPECT_TIP_HEIGHT, leaving the (hgt, wantHeight] segment covered only by the bypassable count
		// pin and NOT bound to the real chain. Require the pinned hash to sit exactly at the pinned height.
		if haveHeightPin && hgt != wantHeight {
			t.Fatalf("pin inconsistency: %s=%s sits at height %d but %s=%d — the real-chain tip hash and the coverage height must be the SAME endpoint (pin the hash AT the height)", sEnv, v, hgt, hEnv, wantHeight)
		}
		t.Logf("real-chain binding OK: committed+connected chain reaches pinned real tip %s @ height %d", v, hgt)
	} else if enforcing {
		t.Fatalf("%s not set but the gate is enforced for this network: the enforcing lane MUST pin the expected REAL Bitcoin tip hash — without it the gate proves only the fixture's self-consistency (a fabricated/laundered chain passes), not the real committed history", sEnv)
	}
}

func TestBtcDiffValidatorAcceptsAllMainnetCommittedHistory(t *testing.T) {
	// Default to the committed bounded fixture so the gate is CI-resident (runs, not skips): real mainnet headers
	// 883093..887040 spanning the first retarget boundary (887040) above floor+clearance — proves the contextual-
	// difficulty MATH accepts real consecutive mainnet headers (incl. a retarget recompute) with zero RuleError/PoW
	// rejects. HEMI_MAINNET_VERIFY overrides the path (e.g. the Makefile gate's full live-tip reconstruction);
	// HEMI_MAINNET_EXPECT_TIP_HEIGHT + HEMI_HISTORY_GATE_REQUIRED enforce full-history coverage in that lane. The
	// bounded fixture does NOT cover BtcAttr reconstruction faithfulness (no L2 chaindata) — that needs the tool.
	f := historyGateInput(t, "HEMI_MAINNET_VERIFY", "testdata/btcattr_mainnet_history.ndjson", true /* committed repo invariant: absence FAILS, never skips */)
	defer f.Close()

	params := &chaincfg.MainNetParams
	assertBtcParamsPinned(t, params, false)
	floor := MainnetHvmGenesisHeight

	// 1. Collect every unique committed header (by hash), preserving the BtcAttr batch list and the L2 block
	//    that first committed each header (for diagnostics).
	type line struct {
		Blk  uint64   `json:"blk"`
		Tip  string   `json:"tip"`
		Hdrs []string `json:"hdrs"`
	}
	headersByHash := map[chainhash.Hash]*wire.BlockHeader{}
	committedAtL2 := map[chainhash.Hash]uint64{}
	var batches [][]*wire.BlockHeader
	nLines, nRawHdrs := 0, 0

	gen, err := parseHeader80(MainnetHvmGenesisHeader)
	if err != nil {
		t.Fatalf("decode mainnet hVM genesis header: %v", err)
	}
	if got := gen.BlockHash().String(); got != MainnetHvmGenesisHash {
		t.Fatalf("mainnet genesis header hash mismatch: hex hashes to %s, want %s — the pinned genesis end of the real-chain clamp is wrong (typo / btcd serialization drift)", got, MainnetHvmGenesisHash)
	}
	headersByHash[gen.BlockHash()] = gen

	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1024*1024), 8*1024*1024)
	lineNo := 0
	for sc.Scan() {
		lineNo++
		raw := bytes.TrimSpace(sc.Bytes())
		if len(raw) == 0 {
			continue // tolerate a trailing/blank line
		}
		var l line
		if err := json.Unmarshal(raw, &l); err != nil {
			t.Fatalf("bad ndjson at line %d: %v", lineNo, err) // locate the offending line
		}
		nLines++
		batch := make([]*wire.BlockHeader, 0, len(l.Hdrs))
		for _, hh := range l.Hdrs {
			nRawHdrs++
			bh, err := parseHeader80(hh)
			if err != nil {
				t.Fatalf("decode committed header at L2 block %d: %v", l.Blk, err)
			}
			h := bh.BlockHash()
			headersByHash[h] = bh
			if _, seen := committedAtL2[h]; !seen {
				committedAtL2[h] = l.Blk
			}
			batch = append(batch, bh)
		}
		if len(batch) > 0 {
			batches = append(batches, batch)
		}
	}
	if err := sc.Err(); err != nil {
		t.Fatalf("scanning input: %v", err)
	}

	// Optional ancestry bridge: explorer-recovered canonical reorg-link headers that entered the live hVM store
	// via full-node reorg handling (never as a BtcAttr delta), so the delta reconstruction is missing them — a
	// single missing canonical link disconnects everything downstream from the BFS. Loaded as ancestry only (not
	// counted as committed batches). One 80-byte header hex per line. Mirrors HEMI_TESTNET3_EXTRA_HEADERS.
	// Load ONLY from an explicitly-set path — never a world-writable /tmp default: a stale or planted default
	// file would otherwise be silently auto-loaded as load-bearing connectivity (bridging reconstruction gaps the
	// run never intended to bridge), masking an UNCONNECTED signal that the committed history is not yet proven
	// clean. The enforcing lane must opt in via HEMI_MAINNET_EXTRA_HEADERS.
	extraHeadersFile := os.Getenv("HEMI_MAINNET_EXTRA_HEADERS")
	nExtra := 0
	if ef, err := os.Open(extraHeadersFile); extraHeadersFile != "" && err == nil {
		t.Logf("loading EXTRA ancestry from %s (explicitly requested)", extraHeadersFile)
		esc := bufio.NewScanner(ef)
		esc.Buffer(make([]byte, 1024*1024), 8*1024*1024)
		for esc.Scan() {
			hh := string(bytes.TrimSpace(esc.Bytes()))
			if hh == "" {
				continue
			}
			bh, err := parseHeader80(hh)
			if err != nil {
				t.Fatalf("decode extra ancestry header: %v", err)
			}
			if _, dup := headersByHash[bh.BlockHash()]; !dup {
				headersByHash[bh.BlockHash()] = bh
				nExtra++
			}
		}
		ef.Close()
		t.Logf("loaded %d EXTRA explorer-recovered canonical ancestry headers", nExtra)
	}

	// 2. Assign heights by BFS from the effective genesis (handles forks: each header connects to its own
	//    parent). Any header that never connects back to genesis is reported as a diagnostic — NOT a failure
	//    (a reconstruction gap or a genuinely-orphaned committed branch; neither is a difficulty/PoW reject).
	children := map[chainhash.Hash][]chainhash.Hash{}
	for h, bh := range headersByHash {
		if h == gen.BlockHash() {
			continue
		}
		children[bh.PrevBlock] = append(children[bh.PrevBlock], h)
	}
	store := newFakeStore()
	height := map[chainhash.Hash]uint64{gen.BlockHash(): floor}
	store.put(gen, floor)
	queue := []chainhash.Hash{gen.BlockHash()}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		for _, ch := range children[cur] {
			if _, done := height[ch]; done {
				continue
			}
			height[ch] = height[cur] + 1
			store.put(headersByHash[ch], height[ch])
			queue = append(queue, ch)
		}
	}

	var unconnectedHashes []chainhash.Hash
	for h := range headersByHash {
		if _, ok := height[h]; !ok {
			unconnectedHashes = append(unconnectedHashes, h)
		}
	}
	sort.Slice(unconnectedHashes, func(i, j int) bool {
		return committedAtL2[unconnectedHashes[i]] < committedAtL2[unconnectedHashes[j]]
	})
	t.Logf("BtcAttr txs=%d  raw headers=%d  unique committed headers=%d  connected=%d  unconnected=%d (extra ancestry=%d)",
		nLines, nRawHdrs, len(headersByHash), len(height), len(unconnectedHashes), nExtra)
	for i, h := range unconnectedHashes {
		if i >= 30 {
			t.Logf("  ... and %d more unconnected headers", len(unconnectedHashes)-30)
			break
		}
		bh := headersByHash[h]
		t.Logf("  UNCONNECTED header %s (parent %s, bits %08x) first committed by L2 block %d",
			h, bh.PrevBlock, bh.Bits, committedAtL2[h])
	}

	// 3. Proof-of-work (context-free, floor-independent, enforced on the apply path): every committed header
	//    must meet its own claimed target. Real mainnet headers are really mined, so any failure is a
	//    forged/zero-PoW committed header — the only PoW dimension that bites. Must be zero for clean history.
	powRejected := 0
	var firstPoWRejects []string
	for h, bh := range headersByHash {
		if h == gen.BlockHash() {
			continue
		}
		if err := checkBTCHeaderPoWWith(bh, params); err != nil {
			powRejected++
			if len(firstPoWRejects) < 20 {
				firstPoWRejects = append(firstPoWRejects, fmt.Sprintf("%s (committed by L2 %d): %v", h, committedAtL2[h], err))
			}
		}
	}
	t.Logf("PER-HEADER PoW: rejected=%d of %d committed headers", powRejected, len(headersByHash)-1)
	for _, r := range firstPoWRejects {
		t.Errorf("MAINNET HISTORY PoW FAILURE (forged/zero-PoW committed header): %s", r)
	}

	// 4. Per-header contextual difficulty: every CONNECTED header at/above the floor-clearance band is
	//    enforced. A btcd RuleError is a genuine reject (the clean-history violation). ErrBTCHeaderContextUnavailable
	//    means the header's ancestry isn't in the store (a non-contiguous header BFS placed but whose walk
	//    crosses a gap) -> ctxSkip diagnostic, NOT a reject (the live path defers it).
	enforceFrom := floor + floorClearance(params)
	bpr := uint64(blocksPerRetarget(params))
	enforced, ctxRejected, ctxSkip, boundaryEnforced := 0, 0, 0, 0
	var firstRejects []string
	for h, bh := range headersByHash {
		hgt, ok := height[h]
		if !ok || hgt < enforceFrom {
			continue
		}
		if _, committed := committedAtL2[h]; !committed {
			continue // extra-ancestry-only header (not BtcAttr-committed): ancestry, not part of the verified set
		}
		enforced++
		err := validateBTCHeaderContextWith(ctx(), store, params, bh)
		if err != nil && errors.Is(err, ErrBTCHeaderContextUnavailable) {
			ctxSkip++
			continue
		}
		// The validator actually ran the full retarget/difficulty computation for this header (not a ctxSkip).
		// Count retarget-boundary headers (H%2016==0): these are the ones where the target is RECOMPUTED from
		// the 2016-block timespan — the security-critical case. A fixture that enforces zero boundary headers
		// has never exercised the retarget path, so "clean" would not cover difficulty CHANGES.
		if hgt%bpr == 0 {
			boundaryEnforced++
		}
		if err != nil {
			ctxRejected++
			if len(firstRejects) < 20 {
				var re blockchain.RuleError
				code := "?"
				if errors.As(err, &re) {
					code = re.ErrorCode.String()
				}
				firstRejects = append(firstRejects, fmt.Sprintf("%s @ %d : %s (%v)", h, hgt, code, err))
			}
		}
	}

	// 5. Per-batch apply-path faithfulness: replay each BtcAttr batch through the exact batch validator the
	//    apply path calls, with the real floor. Outcomes: accept / defer (BelowFloor) / skip (ContextUnavailable)
	//    / unconnected (non-contiguous) / reject (a contextual RuleError — the violation). Unconnected is split
	//    out from reject (the apply path does NOT treat it as a difficulty reject).
	batchAccept, batchDefer, batchSkip, batchUnconn, batchReject := 0, 0, 0, 0, 0
	var firstBatchRejects []string
	for _, b := range batches {
		switch err := validateBTCHeaderBatchWith(ctx(), store, params, floor, b); {
		case err == nil:
			batchAccept++
		case errors.Is(err, ErrBTCBatchBelowFloor):
			batchDefer++
		case errors.Is(err, ErrBTCHeaderContextUnavailable):
			batchSkip++
		case errors.Is(err, ErrBTCBatchUnconnected):
			batchUnconn++
		default:
			batchReject++
			if len(firstBatchRejects) < 20 {
				firstBatchRejects = append(firstBatchRejects, b[0].BlockHash().String()+" : "+err.Error())
			}
		}
	}

	t.Logf("PER-HEADER: enforced=%d ctxRejected=%d ctxSkip=%d boundaryEnforced=%d (enforce from height >= %d)", enforced, ctxRejected, ctxSkip, boundaryEnforced, enforceFrom)
	t.Logf("PER-BATCH:  accept=%d defer=%d skip=%d unconnected=%d reject=%d", batchAccept, batchDefer, batchSkip, batchUnconn, batchReject)
	for _, r := range firstRejects {
		t.Errorf("CONTEXTUAL-DIFFICULTY PER-HEADER REJECT: %s", r)
	}
	for _, r := range firstBatchRejects {
		t.Errorf("CONTEXTUAL-DIFFICULTY BATCH REJECT: %s", r)
	}

	// Clean-history verdict: the re-validation hazard is a contextual RuleError or a PoW failure (these brick /
	// split a re-validating node). Non-contiguous (unconnected) headers/batches are an ancestry artifact,
	// reported above for analysis (reconstruction gap vs genuine orphan) — NOT a difficulty/PoW violation, so
	// they do not fail the gate (matching the live apply path). Guard against a vacuous CLEAN.
	// Anti-vacuous: a clean verdict is only meaningful if at least one committed header actually COMPLETED a
	// contextual-difficulty check (enforced-ctxSkip>0) AND at least one batch was accepted — not merely that
	// the validator was invoked (enforced counts call-time, before ctxSkip classification). A reconstruction
	// where every above-band header skips on a missing retarget anchor would otherwise read CLEAN while
	// difficulty-validating nothing.
	if nRawHdrs == 0 || enforced-ctxSkip == 0 || batchAccept == 0 || boundaryEnforced == 0 {
		t.Fatalf("vacuous: rawHeaders=%d enforced=%d ctxSkip=%d batchAccept=%d boundaryEnforced=%d — too few headers actually difficulty-validated to claim clean history (boundaryEnforced=0 means the retarget path, where the target is RECOMPUTED, was never exercised; the fixture must span at least one H%%2016==0 boundary above the floor-clearance band)", nRawHdrs, enforced, ctxSkip, batchAccept, boundaryEnforced)
	}
	// Coverage pin (optional but required in the enforcing CI lane): assert the connected set reaches the
	// pinned live tip height, so a TRUNCATED/STALE fixture cannot pass as clean as the chain grows. Set
	// HEMI_MAINNET_EXPECT_TIP_HEIGHT (and HEMI_HISTORY_GATE_REQUIRED) in CI; bump the pin as history extends.
	assertCoveragePin(t, "HEMI_MAINNET", height, committedAtL2, headersByHash)
	if ctxRejected == 0 && batchReject == 0 && powRejected == 0 {
		t.Logf("CLEAN over the connected+enforced committed set: no contextual/PoW rejects across %d connected committed headers "+
			"(%d batches; %d contextually verified, %d ctxSkip). UNCONNECTED headers=%d, unconnected batches=%d are NOT difficulty-"+
			"verified here — they must be bridged via HEMI_MAINNET_EXTRA_HEADERS or analyzed (reconstruction gap vs genuine orphan) "+
			"before declaring the full history clean.", len(height)-1, len(batches), enforced-ctxSkip, ctxSkip, len(unconnectedHashes), batchUnconn)
	}
}

// TestMainnetHistoryFixtureIsContiguousAndConnectsToGenesis is an env-independent integrity guard for the
// committed fixture. It parses testdata/btcattr_mainnet_history.ndjson INDEPENDENTLY of the
// replay logic and asserts, with precise messages, that the fixture (a) connects to the real hVM genesis, (b) is
// strictly contiguous, (c) has the expected header count, and (d) ends at the pinned real-chain tip hash. So a
// corrupted / truncated / real-segment-substituted fixture fails HERE loudly, rather than silently weakening the
// gate or failing vacuously deep inside the replay. The tip pin also closes the real-for-real substitution gap in
// the default (no-env) lane, where the replay's tip-hash clamp is only enforced under HEMI_MAINNET_EXPECT_TIP_HASH.
func TestMainnetHistoryFixtureIsContiguousAndConnectsToGenesis(t *testing.T) {
	const fixturePath = "testdata/btcattr_mainnet_history.ndjson"
	const expectTipHash = "00000000000000000002358da40837b121dbf6974a73980728781562258f40d3" // real mainnet block 887040
	const expectHeaders = 3948                                                               // 883093..887040 inclusive
	const expectLines = 132                                                                  // one ndjson line per committed L2 block (BtcAttr tx)

	f, err := os.Open(fixturePath)
	if err != nil {
		t.Fatalf("committed fixture %s missing (repo invariant): %v", fixturePath, err)
	}
	defer f.Close()

	type line struct {
		Hdrs []string `json:"hdrs"`
	}
	var hdrs []*wire.BlockHeader
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1024*1024), 8*1024*1024)
	lineNo := 0
	nLines := 0
	for sc.Scan() {
		lineNo++
		raw := bytes.TrimSpace(sc.Bytes())
		if len(raw) == 0 {
			continue
		}
		nLines++
		var l line
		if err := json.Unmarshal(raw, &l); err != nil {
			t.Fatalf("fixture line %d is not valid ndjson: %v", lineNo, err)
		}
		// Per-line cap: each ndjson line is one BtcAttr payload, capped at MaximumBtcHeadersInTx by the
		// apply path; pin it here too so an over-size re-batch fails with a CLEAR message instead of the apply
		// path's opaque "invalid hvm block format". The integrity guard otherwise flattens batch structure away.
		if len(l.Hdrs) > types.MaximumBtcHeadersInTx {
			t.Fatalf("fixture line %d has %d headers, exceeds MaximumBtcHeadersInTx (%d) — the apply path would reject this batch", lineNo, len(l.Hdrs), types.MaximumBtcHeadersInTx)
		}
		for _, hh := range l.Hdrs {
			bh, err := parseHeader80(hh)
			if err != nil {
				t.Fatalf("fixture line %d: bad 80-byte header: %v", lineNo, err)
			}
			hdrs = append(hdrs, bh)
		}
	}
	if err := sc.Err(); err != nil {
		t.Fatalf("scanning fixture: %v", err)
	}

	if len(hdrs) != expectHeaders {
		t.Fatalf("fixture has %d headers, want %d (truncated/extended? if intentionally extended, re-pin expectHeaders + expectTipHash)", len(hdrs), expectHeaders)
	}
	if nLines != expectLines {
		t.Fatalf("fixture has %d ndjson lines, want %d — a re-batch redistributing the same headers across a different "+
			"number of BtcAttr lines changes the per-line canonical-tip claims the apply-path replay exercises; re-pin "+
			"expectLines deliberately if intentional", nLines, expectLines)
	}
	if got := hdrs[0].PrevBlock.String(); got != MainnetHvmGenesisHash {
		t.Fatalf("first fixture header PrevBlock %s != MainnetHvmGenesisHash %s — the fixture does not connect to the hVM genesis", got, MainnetHvmGenesisHash)
	}
	for i := 1; i < len(hdrs); i++ {
		if prev := hdrs[i-1].BlockHash(); hdrs[i].PrevBlock != prev {
			t.Fatalf("fixture chain break at index %d: PrevBlock %s != prior header hash %s", i, hdrs[i].PrevBlock, prev)
		}
	}
	if got := hdrs[len(hdrs)-1].BlockHash().String(); got != expectTipHash {
		t.Fatalf("fixture tip %s != pinned real-chain tip %s — a real segment may have been substituted (re-pin if the fixture was intentionally re-anchored)", got, expectTipHash)
	}
	// Self-validate against params drift: the fixture must still span a retarget boundary (H%2016==0) at
	// or above the CURRENT computed enforceFrom (floor+floorClearance). If MainnetHvmGenesisHeight / floorClearance
	// / blocksPerRetarget change such that the pinned range no longer covers an enforced boundary, the replay would
	// silently stop exercising the retarget recompute — catch that here deterministically (header[i] is genesis+1+i).
	enforceFrom := MainnetHvmGenesisHeight + floorClearance(&chaincfg.MainNetParams)
	bpr := uint64(blocksPerRetarget(&chaincfg.MainNetParams))
	spansBoundary := false
	for i := range hdrs {
		if h := MainnetHvmGenesisHeight + 1 + uint64(i); h >= enforceFrom && h%bpr == 0 {
			spansBoundary = true
			break
		}
	}
	if !spansBoundary {
		t.Fatalf("fixture no longer spans a retarget boundary (H%%%d==0) at/above the current enforceFrom %d — a params change shifted the enforce band out of the pinned range; re-anchor the fixture to span a boundary above the new floor+clearance", bpr, enforceFrom)
	}
}
