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

// The differential-replay gate (mainnet): replay every Bitcoin header ever committed to hVM consensus
// on Hemi mainnet — reconstructed offline from the BtcAttributesDeposited txs of every L2 block — through
// the EXACT contextual-difficulty + PoW validator the apply path runs, under MainNetParams, and confirm it
// would not REJECT any historical block. Zero genuine contextual/PoW RuleErrors above the floor-clearance
// band means the committed history is "clean" and difficulty validation can be enabled per node (each on its
// correct network) with no activation fork. See testutil/hvm-btcattr-reconstruct for producing the NDJSON.
//
// Classification is aligned EXACTLY to the live apply path (core/blockchain.go applyHvmHeaderConsensusUpdate
// -> ValidateBTCHeaderBatchForNetwork): a btcd RuleError / PoW failure is a real reject (the clean-history
// violation this gate checks for); ErrBTCHeaderContextUnavailable and ErrBTCBatchUnconnected are NOT rejects on the live path
// (recoverable / deferred), so they are diagnostics here, not failures — matching the testnet3 harness.
// An optional HEMI_MAINNET_EXTRA_HEADERS file supplies explorer-recovered canonical reorg-link headers as
// ancestry only, to bridge gaps the delta reconstruction is missing.
//
// CI ENFORCEMENT (two tiers):
//  1. DEFAULT (no env): replays the committed bounded fixture testdata/btcattr_mainnet_history.ndjson, a
//     repo invariant — if it is missing, historyGateInput FAILS (does not skip), so the mainnet gate can never
//     silently revert to a no-op in `go test ./...`. Proves the contextual-difficulty/PoW MATH over real
//     headers incl. a retarget recompute, but is BOUNDED (883093..887040) — not full live-tip history.
//  2. LIVE-TIP lane: set HEMI_MAINNET_VERIFY=<path> (reconstructed by testutil/hvm-btcattr-reconstruct against real
//     L2 chaindata) + HEMI_HISTORY_GATE_REQUIRED=1 (turns an absent override into a hard FAIL) +
//     HEMI_MAINNET_EXPECT_TIP_HEIGHT/HASH (anti-truncation coverage pin). Additionally covers BtcAttr
//     reconstruction faithfulness + full coverage to the pinned tip. See core/vm/testdata/HISTORY_GATE.md for the
//     operator runbook that runs it.
//
// Mainnet hVM genesis. The {883092, header, …188eda8} pair is the single shared source of truth in
// hvm_genesis.go (MainnetHvmGenesis{Height,Header,Hash}); core's checkpoint map and the apply-path replay test
// consume the SAME constant, and TestMainnetHvmGenesisHeaderHashesToPin welds the header bytes to the hash, so
// a re-genesis cannot re-root this gate while production uses a different pair.
//
//	--hvm.genesisheight=883092
//	--hvm.genesisheader=0000003efaaa2ba6...e7f41c86
//
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
	// rejects. HEMI_MAINNET_VERIFY overrides the path (the live-tip lane's full reconstruction from
	// testutil/hvm-btcattr-reconstruct; see testdata/HISTORY_GATE.md);
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

// Differential-replay TEETH guard. TestBtcDiffValidatorAcceptsAllMainnetCommittedHistory proves the committed mainnet
// fixture validates CLEAN under MainNetParams, with anti-vacuous guards proving the validator did real work — but
// it never proves the clean verdict is PARAMS-DISCRIMINATING. The entire enforce-gate/DEFER safety argument is that a mainnet
// header behaves DIFFERENTLY under testnet3 params (so a DEFER node must NOT enforce). This runs the IDENTICAL
// committed history under BOTH params and asserts it is clean under MainNetParams yet FLAGGED under TestNet3Params
// (whose ReduceMinDifficulty 20-minute rule mandates PowLimitBits for the many real >20-min-gap hard-difficulty
// blocks). Without this the gate could pass vacuously after a btcd/param refactor, and the DEFER rationale would be
// undemonstrated. Corpus-free: the already-committed bounded fixture, no full node.
func TestMainnetHistoryGateHasTeeth(t *testing.T) {
	const fixturePath = "testdata/btcattr_mainnet_history.ndjson"
	f, err := os.Open(fixturePath)
	if err != nil {
		t.Fatalf("committed fixture %s missing (repo invariant): %v", fixturePath, err)
	}
	defer f.Close()

	gen, err := parseHeader80(MainnetHvmGenesisHeader)
	if err != nil {
		t.Fatalf("decode mainnet hVM genesis header: %v", err)
	}
	headersByHash := map[chainhash.Hash]*wire.BlockHeader{gen.BlockHash(): gen}

	type line struct {
		Hdrs []string `json:"hdrs"`
	}
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1024*1024), 8*1024*1024)
	for sc.Scan() {
		raw := bytes.TrimSpace(sc.Bytes())
		if len(raw) == 0 {
			continue
		}
		var l line
		if err := json.Unmarshal(raw, &l); err != nil {
			t.Fatalf("bad ndjson: %v", err)
		}
		for _, hh := range l.Hdrs {
			bh, err := parseHeader80(hh)
			if err != nil {
				t.Fatalf("decode committed header: %v", err)
			}
			headersByHash[bh.BlockHash()] = bh
		}
	}
	if err := sc.Err(); err != nil {
		t.Fatalf("scanning fixture: %v", err)
	}

	// BFS heights from the genesis floor, building the in-memory ancestry store the validator resolves against.
	floor := MainnetHvmGenesisHeight
	children := map[chainhash.Hash][]chainhash.Hash{}
	for h, bh := range headersByHash {
		if h != gen.BlockHash() {
			children[bh.PrevBlock] = append(children[bh.PrevBlock], h)
		}
	}
	store := newFakeStore()
	store.put(gen, floor)
	height := map[chainhash.Hash]uint64{gen.BlockHash(): floor}
	for queue := []chainhash.Hash{gen.BlockHash()}; len(queue) > 0; {
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

	// countRejects validates every connected committed header above the floor-clearance band under `params` and
	// returns how many the validator actually completed (enforced-skip) and how many it REJECTED with a RuleError.
	countRejects := func(params *chaincfg.Params) (completed, rejected int) {
		enforceFrom := floor + floorClearance(params)
		for h, bh := range headersByHash {
			hgt, ok := height[h]
			if !ok || hgt < enforceFrom || h == gen.BlockHash() {
				continue
			}
			err := validateBTCHeaderContextWith(ctx(), store, params, bh)
			if errors.Is(err, ErrBTCHeaderContextUnavailable) {
				continue // ancestry gap -> the live path defers; not a reject
			}
			completed++
			if err != nil {
				rejected++
			}
		}
		return completed, rejected
	}

	mainCompleted, mainRejected := countRejects(&chaincfg.MainNetParams)
	if mainCompleted == 0 {
		t.Fatalf("vacuous: zero headers completed a contextual check under MainNetParams")
	}
	if mainRejected != 0 {
		t.Fatalf("the committed mainnet history must be CLEAN under MainNetParams, got %d rejects", mainRejected)
	}

	_, testnet3Rejected := countRejects(&chaincfg.TestNet3Params)
	if testnet3Rejected == 0 {
		t.Fatalf("differential-replay gate has NO TEETH: the committed mainnet history clean under MainNetParams produced ZERO rejects "+
			"under TestNet3Params — the params-discriminating property (the whole DEFER-no-enforce rationale) is "+
			"undemonstrated, or the gate would pass vacuously. (completed under mainnet=%d)", mainCompleted)
	}
	t.Logf("differential-replay teeth: committed mainnet history is CLEAN under MainNetParams (%d completed, 0 rejects) but FLAGGED "+
		"under TestNet3Params (%d rejects) — the gate discriminates params", mainCompleted, testnet3Rejected)
}

// testnet3 history gate: the testnet3 counterpart of TestBtcDiffValidatorAcceptsAllMainnetCommittedHistory.
// Replays Bitcoin headers committed to hVM consensus on the Hemi testnet3 chain through the exact
// contextual-difficulty validator (TestNet3Params, testnet3 hVM genesis height 3522419) to confirm it
// would not contextual/PoW-reject any historical block. testnet3 is the shipped default: eth/backend.go
// defaults the consensus node to testnet3 via config.TBCNetwork → ethconfig.DefaultTBCNetwork.
//
// Key difference from the mainnet harness: early testnet3 history contains a few non-contiguous committed
// headers. A non-contiguous header is one whose parent is absent from the committed set; it is an ancestry
// artifact, so the validator skips it (ErrBTCHeaderContextUnavailable) / the batch is ErrBTCBatchUnconnected.
// Those are not contextual-difficulty rejects, so this test tracks unconnected separately and the
// clean-history verdict is "zero contextual RuleError + zero PoW failure" (the only outcomes that would
// brick/split a re-validating node). Unconnected counts + the offending headers are logged for analysis
// (a genuine committed-but-orphaned-parent header is an expected testnet3 residual, not a difficulty violation).
//
// This lane replays the bounded fixture testdata/btcattr_testnet3_history.ndjson (real testnet3 headers
// 3522420..3525984, spanning a retarget boundary AND 116 diff-1 ReduceMinDifficulty headers above the floor)
// by default, FAILING (not skipping) if that fixture is missing — it is a repo invariant.
// HEMI_TESTNET3_VERIFY=<path> overrides it for the live-tip reconstruction lane (BtcAttr faithfulness +
// full coverage to the current tip).
const (
	// The live testnet3 deployment's hVM genesis (height 3522419 / hash 00000000…96c98151…), which op-geth's
	// compiled default and the pinned genesis checkpoint also use. Reference the shared exported source of truth
	// so this gate's genesis cannot diverge from the constant eth/backend_hvm_genesis_test.go cross-checks
	// against the production testnet3 default/checkpoint.
	testnet3HvmGenesisHeight = Testnet3HvmGenesisHeight
	testnet3HvmGenesisHeader = Testnet3HvmGenesisHeader
	testnet3HvmGenesisHash   = Testnet3HvmGenesisHash
	// hvm0 activation time on testnet3. BtcAttrDep txs in L2 blocks before activation are grandfathered
	// pre-activation commits that build on a different (pre-activation) BTC base and must be ignored — they
	// are not part of the canonical post-activation committed history. The reconstruction file below excludes
	// them (only L2 blocks >= the first block at/after this time).
	testnet3Hvm0ActivationTime = uint64(1733930401)
)

func TestBtcDiffValidatorAcceptsAllTestnet3CommittedHistory(t *testing.T) {
	// Primary input: the post-activation committed set (pre-activation grandfathered BtcAttrs excluded),
	// reconstructed offline from the chain's committed BtcAttributesDeposited txs by testutil/hvm-btcattr-reconstruct
	// (over a node's L2 chaindata). Defaults to the fixture path below; override with HEMI_TESTNET3_VERIFY=<path>.
	// Optional second input,
	// HEMI_TESTNET3_EXTRA_HEADERS=<path>: explorer-recovered canonical reorg-link headers missing from the
	// delta reconstruction (one 80-byte header hex per line) — ancestry only.
	// The default fixture carries real testnet3 headers 3522420..3525984 spanning the 3525984 retarget boundary
	// above floor+clearance AND 116 diff-1 (Bits==PowLimitBits) headers above the floor — the
	// ReduceMinDifficulty (20-minute) rule that is the whole reason the testnet3 lane exists and that mainnet
	// structurally cannot exercise. defaultCommitted=true: absence FAILS (repo invariant), never skips.
	// HEMI_TESTNET3_VERIFY still overrides for the live-tip lane.
	f := historyGateInput(t, "HEMI_TESTNET3_VERIFY", "testdata/btcattr_testnet3_history.ndjson", true /* committed repo invariant */)
	defer f.Close()
	// EXTRA ancestry only from an explicitly-set path — never a world-writable /tmp default, since a
	// stale/planted default would silently become load-bearing connectivity.
	extraHeadersFile := os.Getenv("HEMI_TESTNET3_EXTRA_HEADERS")

	params := &chaincfg.TestNet3Params
	assertBtcParamsPinned(t, params, true)
	floor := testnet3HvmGenesisHeight

	type line struct {
		Blk  uint64   `json:"blk"`
		Tip  string   `json:"tip"`
		Hdrs []string `json:"hdrs"`
	}
	headersByHash := map[chainhash.Hash]*wire.BlockHeader{}
	// remember the lowest L2 block each header was committed by, for diagnostics on unconnected headers.
	committedAtL2 := map[chainhash.Hash]uint64{}
	var batches [][]*wire.BlockHeader
	nLines, nRawHdrs := 0, 0

	gen, err := parseHeader80(testnet3HvmGenesisHeader)
	if err != nil {
		t.Fatalf("decode testnet3 hVM genesis header: %v", err)
	}
	if gen.BlockHash().String() != testnet3HvmGenesisHash {
		t.Fatalf("testnet3 genesis header hash mismatch: got %s, want %s — the pinned genesis end of the real-chain clamp is wrong (typo / btcd serialization drift)", gen.BlockHash(), testnet3HvmGenesisHash)
	}
	headersByHash[gen.BlockHash()] = gen

	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1024*1024), 8*1024*1024)
	lineNo := 0
	for sc.Scan() {
		lineNo++
		raw := bytes.TrimSpace(sc.Bytes())
		if len(raw) == 0 {
			continue // tolerate a trailing/blank line (parity with the mainnet lane)
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
			if prev, ok := committedAtL2[h]; !ok || l.Blk < prev {
				committedAtL2[h] = l.Blk
			}
			batch = append(batch, bh)
		}
		if len(batch) > 0 {
			batches = append(batches, batch)
		}
	}
	if err := sc.Err(); err != nil {
		t.Fatalf("scanning testnet3 committed history: %v", err)
	}

	// Extra ancestry headers (optional): testnet3's frequent reorgs mean a few canonical-tip headers entered
	// the live hVM store via full-node reorg handling, never as a BtcAttr delta, so the delta reconstruction
	// is missing them (a single missing canonical link disconnects everything downstream from the BFS). These
	// were recovered hash-verified from a testnet3 BTC explorer (only the canonical ones exist there; the
	// reorged-out orphan links do not — those stay unconnected, which is correct: they are non-canonical
	// branches the hVM committed). Loaded into headersByHash as ancestry only (not counted as committed
	// batches), so the BFS can bridge the canonical chain. File: one 80-byte header hex per line.
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
		t.Logf("loaded %d EXTRA explorer-recovered canonical ancestry headers (reorg links missing from the delta reconstruction)", nExtra)
	}

	// Assign heights by BFS from the effective genesis (handles forks). Headers that never connect back to
	// genesis are the non-contiguous set (reconstruction gap OR genuinely-orphaned committed header).
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

	// Proof-of-work: every committed header must meet its own claimed target (context-free, floor-independent,
	// enforced on the apply path). Real testnet3 headers are really mined, so any failure is a forged/zero-PoW
	// committed header (the only PoW dimension that bites). This must be zero for a clean history.
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
		t.Errorf("TESTNET3 HISTORY PoW FAILURE (forged/zero-PoW committed header): %s", r)
	}

	// Per-header contextual difficulty: every connected header at/above the floor-clearance band is enforced.
	// A btcd RuleError is a genuine contextual-difficulty reject (the clean-history violation). An unavailable
	// context here means the header's ancestry isn't in the store (a non-contiguous header that BFS placed
	// but whose walk crosses a gap) -> tracked as ctxSkip, not a reject.
	enforceFrom := floor + floorClearance(params)
	bpr := uint64(blocksPerRetarget(params))
	enforced, ctxRejected, ctxSkip, boundaryEnforced, minDiffEnforced := 0, 0, 0, 0, 0
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
		// The validator ran the full difficulty computation for this header (not a ctxSkip). Track two
		// security-critical sub-cases the verdict must actually have exercised:
		//   - boundaryEnforced: retarget-boundary headers (H%2016==0), where the target is RECOMPUTED.
		//   - minDiffEnforced: diff-1 headers (Bits==PowLimitBits) — the ReduceMinDifficulty (20-min) rule that
		//     is testnet3's ONLY difficulty difference from mainnet, and the whole reason the testnet3 lane exists.
		if hgt%bpr == 0 {
			boundaryEnforced++
		}
		// Only a NON-boundary diff-1 header exercises the 20-minute ReduceMinDifficulty branch; AT a retarget
		// boundary (H%2016==0) btcd recomputes the target and can land on PowLimitBits without ever taking the
		// min-diff path. Restrict the count to the headers that actually drive the rule this lane exists to vet.
		if bh.Bits == params.PowLimitBits && hgt%bpr != 0 {
			minDiffEnforced++
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

	// Per-batch apply-path faithfulness: replay each BtcAttr batch through the exact batch validator. Outcomes:
	// accept (nil) / defer (BelowFloor) / skip (ContextUnavailable) / unconnected (the non-contiguous case) /
	// reject (a contextual RuleError — the violation). Unconnected is split out from reject.
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

	t.Logf("PER-HEADER: enforced=%d ctxRejected=%d ctxSkip=%d boundaryEnforced=%d minDiffEnforced=%d (enforce from height >= %d)", enforced, ctxRejected, ctxSkip, boundaryEnforced, minDiffEnforced, enforceFrom)
	t.Logf("PER-BATCH:  accept=%d defer=%d skip=%d unconnected=%d reject=%d", batchAccept, batchDefer, batchSkip, batchUnconn, batchReject)
	for _, r := range firstRejects {
		t.Errorf("CONTEXTUAL-DIFFICULTY PER-HEADER REJECT: %s", r)
	}
	for _, r := range firstBatchRejects {
		t.Errorf("CONTEXTUAL-DIFFICULTY BATCH REJECT: %s", r)
	}

	// Clean-history verdict: the re-validation hazard is a contextual RuleError or a PoW failure (these brick /
	// split a re-validating node). Non-contiguous (unconnected) headers/batches are an ancestry artifact: the
	// apply path treats ErrBTCBatchUnconnected as a bad block, so any genuinely-orphaned committed batch is a
	// real residual — reported above for analysis — but it is not a difficulty/PoW violation. The test fails
	// only on a contextual/PoW reject (via the t.Errorf above); unconnected is diagnostic.
	// Guard against a vacuous CLEAN: an empty/truncated reconstruction file would leave the loops with nothing
	// to reject and print the no-rejects verdict despite verifying nothing. Require that the file parsed real
	// headers AND the enforced per-header validator actually ran on at least one of them.
	if nRawHdrs == 0 || enforced-ctxSkip == 0 || batchAccept == 0 || boundaryEnforced == 0 {
		t.Fatalf("vacuous: rawHeaders=%d enforced=%d ctxSkip=%d batchAccept=%d boundaryEnforced=%d — too few headers actually difficulty-validated to claim clean history (boundaryEnforced=0 means the retarget path, where the target is RECOMPUTED, was never exercised; the fixture must span at least one H%%2016==0 boundary above the floor-clearance band)", nRawHdrs, enforced, ctxSkip, batchAccept, boundaryEnforced)
	}
	// testnet3-specific: the ReduceMinDifficulty (20-minute diff-1) rule is the ONLY difficulty difference from
	// mainnet and the entire reason this lane exists. A verdict that enforced zero diff-1 (Bits==PowLimitBits)
	// committed headers has not actually exercised that rule, so it cannot vouch for it. Hard-require it in the
	// enforcing testnet3 lane; a window with no enforced diff-1 header must be widened.
	if os.Getenv("HEMI_TESTNET3_VERIFY") != "" && os.Getenv("HEMI_HISTORY_GATE_REQUIRED") != "" && minDiffEnforced == 0 {
		t.Fatalf("testnet3 min-difficulty rule NOT exercised: zero enforced committed headers carried Bits==PowLimitBits (diff-1) above height %d. The testnet3 gate exists specifically to vet ReduceMinDifficulty (mainnet's missing rule); choose a reconstruction window that includes real diff-1 headers above the floor-clearance band.", enforceFrom)
	}
	assertCoveragePin(t, "HEMI_TESTNET3", height, committedAtL2, headersByHash)
	if ctxRejected == 0 && batchReject == 0 && powRejected == 0 {
		t.Logf("NO CONTEXTUAL/PoW REJECTS across %d committed testnet3 headers (%d batches). "+
			"unconnected headers=%d, unconnected batches=%d (analyze: reconstruction gap vs genuine orphan).",
			len(headersByHash)-1, len(batches), len(unconnectedHashes), batchUnconn)
	}
}

// TestTestnet3HistoryFixtureIsContiguousAndConnectsToGenesis is the env-independent integrity guard for the
// committed testnet3 fixture, mirroring the mainnet guard. It parses
// testdata/btcattr_testnet3_history.ndjson directly and asserts the fixture connects to the testnet3 hVM genesis,
// is strictly contiguous, has the expected count, ends at the pinned real-chain tip, AND includes at least one
// diff-1 (Bits==PowLimitBits) header above the floor-clearance band — so the committed fixture is guaranteed to
// exercise ReduceMinDifficulty (the whole reason the testnet3 lane exists), not just the retarget math.
func TestTestnet3HistoryFixtureIsContiguousAndConnectsToGenesis(t *testing.T) {
	const fixturePath = "testdata/btcattr_testnet3_history.ndjson"
	const expectTipHash = "0000000000003b8315976d4a9412a8bc6a3a2cbdb9e748d886987b82e89aa68f" // real testnet3 block 3525984
	const expectHeaders = 3565                                                               // 3522420..3525984 inclusive
	const expectLines = 119                                                                  // one ndjson line per committed L2 block (BtcAttr tx)
	enforceFrom := testnet3HvmGenesisHeight + floorClearance(&chaincfg.TestNet3Params)

	f, err := os.Open(fixturePath)
	if err != nil {
		t.Fatalf("committed testnet3 fixture %s missing (repo invariant): %v", fixturePath, err)
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
		// Per-line cap: one BtcAttr payload per line, capped at MaximumBtcHeadersInTx (30).
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
		t.Fatalf("fixture has %d headers, want %d (truncated/extended? re-pin count+tip if intentional)", len(hdrs), expectHeaders)
	}
	if nLines != expectLines {
		t.Fatalf("fixture has %d ndjson lines, want %d — a re-batch redistributing the same headers across a different "+
			"number of BtcAttr lines changes the per-line canonical-tip claims the apply-path replay exercises; re-pin "+
			"expectLines deliberately if intentional", nLines, expectLines)
	}
	if got := hdrs[0].PrevBlock.String(); got != testnet3HvmGenesisHash {
		t.Fatalf("first fixture header PrevBlock %s != testnet3HvmGenesisHash %s — the fixture does not connect to the hVM genesis", got, testnet3HvmGenesisHash)
	}
	diff1Above := 0
	for i := 1; i < len(hdrs); i++ {
		if prev := hdrs[i-1].BlockHash(); hdrs[i].PrevBlock != prev {
			t.Fatalf("fixture chain break at index %d: PrevBlock %s != prior header hash %s", i, hdrs[i].PrevBlock, prev)
		}
	}
	// height i corresponds to genesis+1+i (header[0] is genesis+1); count diff-1 headers above the floor band.
	for i, bh := range hdrs {
		h := testnet3HvmGenesisHeight + 1 + uint64(i)
		if h >= enforceFrom && h%uint64(blocksPerRetarget(&chaincfg.TestNet3Params)) != 0 && bh.Bits == chaincfg.TestNet3Params.PowLimitBits {
			diff1Above++
		}
	}
	if diff1Above == 0 {
		t.Fatalf("testnet3 fixture has NO diff-1 (Bits==PowLimitBits) header above enforceFrom %d — it would not exercise ReduceMinDifficulty, the testnet3 lane's whole purpose; choose a window that includes 20-minute diff-1 blocks", enforceFrom)
	}
	// Exact-count pin: the committed fixture carries exactly 116 diff-1 headers above the floor. Pinning
	// the exact count (not merely >0) makes the minDiffEnforced=116 coverage claim load-bearing — a re-trim/
	// re-batch that changed the ReduceMinDifficulty coverage reddens here, forcing a deliberate re-pin.
	if diff1Above != 116 {
		t.Fatalf("testnet3 fixture diff-1 (ReduceMinDifficulty) header count above enforceFrom = %d, want the pinned 116 "+
			"(the fixture's ReduceMinDifficulty coverage changed — re-pin if the re-anchor was deliberate)", diff1Above)
	}
	if got := hdrs[len(hdrs)-1].BlockHash().String(); got != expectTipHash {
		t.Fatalf("fixture tip %s != pinned real-chain tip %s (segment substituted/extended? re-pin if intentional)", got, expectTipHash)
	}
	// Self-validate against params drift: the fixture must still span a retarget boundary at/above the
	// CURRENT computed enforceFrom, else the replay would silently stop exercising the retarget recompute.
	bpr := uint64(blocksPerRetarget(&chaincfg.TestNet3Params))
	spansBoundary := false
	for i := range hdrs {
		if h := testnet3HvmGenesisHeight + 1 + uint64(i); h >= enforceFrom && h%bpr == 0 {
			spansBoundary = true
			break
		}
	}
	if !spansBoundary {
		t.Fatalf("testnet3 fixture no longer spans a retarget boundary (H%%%d==0) at/above the current enforceFrom %d — re-anchor the fixture to span a boundary above the new floor+clearance", bpr, enforceFrom)
	}
}

// TestTestnet3HvmGenesisIsRealChainBlock pins the testnet3 hVM gate genesis to the GENUINE testnet3 block at
// height 3522419 by its decoded header FIELD LITERALS (independently verified against a testnet3 block explorer),
// mirroring TestMainnetHvmGenesisIsRealChainBlock. The header->hash weld in the gate only proves
// internal consistency (any self-consistent (header,hash) pair passes); these literals additionally catch a
// coordinated fat-finger re-anchor of testnet3HvmGenesisHeader to a DIFFERENT real-or-fake block, which would
// otherwise pass every other gate guard (the fixture + tip pin are re-derived from the genesis).
func TestTestnet3HvmGenesisIsRealChainBlock(t *testing.T) {
	gen, err := parseHeader80(testnet3HvmGenesisHeader)
	if err != nil {
		t.Fatalf("decode testnet3HvmGenesisHeader: %v", err)
	}
	if testnet3HvmGenesisHeight != 3522419 {
		t.Fatalf("testnet3HvmGenesisHeight = %d, want the real testnet3 height 3522419", testnet3HvmGenesisHeight)
	}
	if got, want := gen.PrevBlock.String(), "0000000007d9c4f552b5396a88a79f9f5e32796cfccbf05163e8ef54d6e0c3cd"; got != want {
		t.Fatalf("PrevBlock = %s, want the real h=3522419 parent %s", got, want)
	}
	if got, want := gen.MerkleRoot.String(), "629199c204bd88512bf9fea0072d358a036037a1845b42771f6fe2859407e4da"; got != want {
		t.Fatalf("MerkleRoot = %s, want the real h=3522419 merkle root %s", got, want)
	}
	if got, want := gen.Timestamp.Unix(), int64(1733872303); got != want {
		t.Fatalf("Timestamp = %d, want the real h=3522419 time %d", got, want)
	}
	if got, want := gen.Version, int32(0x3257c000); got != want {
		t.Fatalf("Version = 0x%08x, want 0x%08x", got, want)
	}
	if got, want := uint32(gen.Bits), uint32(0x19012191); got != want {
		t.Fatalf("Bits = 0x%08x, want the real h=3522419 bits 0x%08x", got, want)
	}
	if got, want := gen.Nonce, uint32(2781919586); got != want {
		t.Fatalf("Nonce = %d, want the real h=3522419 nonce %d", got, want)
	}
}
