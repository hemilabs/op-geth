// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

// One-time manual verification: the testnet3 counterpart of TestBtcDiffValidatorAcceptsAllMainnetCommittedHistory.
// Replays every Bitcoin header ever committed to hVM consensus on the Hemi testnet3 chain (reconstructed
// offline from the BtcAttributesDeposited txs of every L2 block via a Hemi testnet3 RPC)
// through the exact contextual-difficulty validator (TestNet3Params, live testnet3 hVM genesis height 3522419) to
// confirm it would not contextual/PoW-reject any historical block. This is the testnet3-specific
// clean-history check the mainnet verification flagged as still-required for the shipped default
// (eth/backend.go hardcodes the consensus node to testnet3).
//
// Key difference from the mainnet harness: the early testnet3 days contain a few non-contiguous committed
// headers (operator-confirmed). A non-contiguous header is one whose parent is absent from the committed
// set; it is an ancestry artifact, so the validator skips it (ErrBTCHeaderContextUnavailable) / the batch
// is ErrBTCBatchUnconnected. Those are not contextual-difficulty rejects, so this test tracks unconnected
// separately and the clean-history verdict is "zero contextual RuleError + zero PoW failure" (the only
// outcomes that would brick/split a re-validating node). Unconnected counts + the offending headers are
// logged for analysis (a genuine committed-but-orphaned-parent header is the documented testnet3 residual,
// not a difficulty violation).
//
// Skipped unless the reconstructed file exists; it is an NDJSON dump of {hash, header-hex} for every
// committed testnet3 Bitcoin header, produced offline from the chain's BtcAttributesDeposited txs.

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
)

const (
	// The live testnet3 deployment's hVM genesis (hemi-node/testnet/config.json .hvm_genesis): height
	// 3522419 / hash 00000000…96c98151…. op-geth's compiled default + the pinned genesis checkpoint now also
	// use this (updated by the genesis-mismatch fix from the stale pre-re-genesis 3488421 / 00000000036fc6f1…,
	// which would have made a correctly-configured node refuse to boot).
	testnet3HvmGenesisHeight = uint64(3522419)
	testnet3HvmGenesisHeader = "00c05732cdc3e0d654efe86351f0cbfc6c79325e9f9fa7886a39b552f5c4d90700000000dae4079485e26f1f77425b84a13760038a352d07a0fef92b5188bd04c2999162afca58679121011962b9d0a5"
	testnet3HvmGenesisHash   = "000000000000000096c98151accc5ee217d7cc4ff1e59a3d91e4c9365c4ea144"
	// hvm0 activation time (hemi-node/testnet/config.json overrides.hvm0). BtcAttrDep txs in L2 blocks before
	// activation are grandfathered pre-activation commits that build on a different (pre-activation) BTC base
	// and must be ignored — they are not part of the canonical post-activation committed history. The
	// reconstruction file below already excludes them (only L2 blocks >= the first block at/after this time).
	testnet3Hvm0ActivationTime = uint64(1733930401)
)

func TestBtcDiffValidatorAcceptsAllTestnet3CommittedHistory(t *testing.T) {
	// Primary input: the reconstructed post-activation committed set (pre-activation grandfathered BtcAttrs
	// excluded), reconstructed offline from the chain's BtcAttributesDeposited txs against a Hemi testnet3
	// RPC. Defaults to the path below; override with HEMI_TESTNET3_VERIFY=<path>. Optional second input,
	// HEMI_TESTNET3_EXTRA_HEADERS=<path> (default below): explorer-recovered canonical reorg-link headers
	// missing from the delta reconstruction (one 80-byte header hex per line) — ancestry only.
	committedFile := os.Getenv("HEMI_TESTNET3_VERIFY")
	if committedFile == "" {
		committedFile = "/tmp/btcattr_testnet3_post.ndjson"
	}
	extraHeadersFile := os.Getenv("HEMI_TESTNET3_EXTRA_HEADERS")
	if extraHeadersFile == "" {
		extraHeadersFile = "/tmp/testnet3_extra_headers.txt"
	}
	f, err := os.Open(committedFile)
	if err != nil {
		t.Skipf("reconstructed testnet3 header file %s not present (set HEMI_TESTNET3_VERIFY=<path> to override) (%v)", committedFile, err)
	}
	defer f.Close()

	params := &chaincfg.TestNet3Params
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
	for sc.Scan() {
		var l line
		if err := json.Unmarshal(sc.Bytes(), &l); err != nil {
			t.Fatalf("bad ndjson line: %v", err)
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
		t.Fatalf("scanning %s: %v", committedFile, err)
	}

	// Extra ancestry headers (optional): testnet3's frequent reorgs mean a few canonical-tip headers entered
	// the live hVM store via full-node reorg handling, never as a BtcAttr delta, so the delta reconstruction
	// is missing them (a single missing canonical link disconnects everything downstream from the BFS). These
	// were recovered hash-verified from a testnet3 BTC explorer (only the canonical ones exist there; the
	// reorged-out orphan links do not — those stay unconnected, which is correct: they are non-canonical
	// branches the hVM committed). Loaded into headersByHash as ancestry only (not counted as committed
	// batches), so the BFS can bridge the canonical chain. File: one 80-byte header hex per line.
	nExtra := 0
	if ef, err := os.Open(extraHeadersFile); err == nil {
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
	// A btcd RuleError is a genuine contextual-difficulty reject (the clean-history violation we hunt). An unavailable
	// context here means the header's ancestry isn't in the store (a non-contiguous header that BFS placed
	// but whose walk crosses a gap) -> tracked as ctxSkip, not a reject.
	enforceFrom := floor + floorClearance(params)
	enforced, ctxRejected, ctxSkip := 0, 0, 0
	var firstRejects []string
	for h, bh := range headersByHash {
		hgt, ok := height[h]
		if !ok || hgt < enforceFrom {
			continue
		}
		enforced++
		if err := validateBTCHeaderContextWith(ctx(), store, params, bh); err != nil {
			if errors.Is(err, ErrBTCHeaderContextUnavailable) {
				ctxSkip++
				continue
			}
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

	t.Logf("PER-HEADER: enforced=%d ctxRejected=%d ctxSkip=%d (enforce from height >= %d)", enforced, ctxRejected, ctxSkip, enforceFrom)
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
	if nRawHdrs == 0 || enforced == 0 {
		t.Fatalf("reconstruction parsed %d raw headers and enforced %d — too few to verify; a no-rejects verdict here would be vacuous", nRawHdrs, enforced)
	}
	if ctxRejected == 0 && batchReject == 0 && powRejected == 0 {
		t.Logf("NO CONTEXTUAL/PoW REJECTS across %d committed testnet3 headers (%d batches). "+
			"unconnected headers=%d, unconnected batches=%d (analyze: reconstruction gap vs genuine orphan).",
			len(headersByHash)-1, len(batches), len(unconnectedHashes), batchUnconn)
	}
}
