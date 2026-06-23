// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

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

import (
	"bufio"
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"sort"
	"testing"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/core/types"
)

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
	// reconstructed offline from the chain's committed BtcAttributesDeposited txs by cmd/hvm-btcattr-reconstruct
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
		t.Fatalf("testnet3 genesis header hash mismatch: got %s want %s", gen.BlockHash(), testnet3HvmGenesisHash)
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

	t.Logf("BtcAttr txs=%d  raw headers=%d  unique committed headers=%d  connected=%d  unconnected=%d",
		nLines, nRawHdrs, len(headersByHash), len(height), len(unconnectedHashes))
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
		t.Fatalf("vacuous: rawHeaders=%d enforced=%d ctxSkip=%d batchAccept=%d boundaryEnforced=%d — too few headers actually difficulty-validated to claim clean history (boundaryEnforced=0 means the retarget path was never exercised; the fixture must span at least one H%%2016==0 boundary above the floor-clearance band)", nRawHdrs, enforced, ctxSkip, batchAccept, boundaryEnforced)
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
		t.Fatalf("first fixture header PrevBlock %s != testnet3HvmGenesisHash %s — does not connect to genesis", got, testnet3HvmGenesisHash)
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
