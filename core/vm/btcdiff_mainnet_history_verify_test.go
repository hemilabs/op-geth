// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package vm

// One-time manual verification: replay every Bitcoin header ever committed to hVM consensus on Hemi
// mainnet (reconstructed offline from the BtcAttributesDeposited txs of every L2 block via a Hemi mainnet
// RPC) through the exact contextual-difficulty validator, to confirm it would not reject any
// historical block. If zero rejections, the chain history is "clean" and the validator can be enforced
// from genesis without a separate activation gate for this (centralized-sequencer-first) deployment.
//
// Skipped unless the reconstructed header file exists (so it never runs in normal CI); the file is an
// NDJSON dump of {hash, header-hex} for every committed Bitcoin header, produced offline from the chain.
//
// Mainnet hVM genesis (from the hemi-node mainnet config):
//   --hvm.genesisheight=883092
//   --hvm.genesisheader=0000003efaaa2ba6...e7f41c86

import (
	"bufio"
	"bytes"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"testing"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
)

const (
	mainnetHvmGenesisHeight = uint64(883092)
	mainnetHvmGenesisHeader = "0000003efaaa2ba65de684c512bb67ef115298d1d16bcb49b16c02000000000000000000ed31a56788c4488afc4ee69e0791ad6aeeb9ea05f069e0fdde6159068765ad3f4128a96726770217e7f41c86"
)

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

func TestBtcDiffValidatorAcceptsAllMainnetCommittedHistory(t *testing.T) {
	// The reconstructed NDJSON header file (reconstructed offline from the chain's BtcAttributesDeposited
	// txs against a Hemi mainnet RPC). Defaults to the path below; override with HEMI_MAINNET_VERIFY=<path>.
	headersFile := os.Getenv("HEMI_MAINNET_VERIFY")
	if headersFile == "" {
		headersFile = "/tmp/btcattr_headers.ndjson"
	}
	f, err := os.Open(headersFile)
	if err != nil {
		t.Skipf("reconstructed mainnet header file %s not present (set HEMI_MAINNET_VERIFY=<path> to override) (%v)", headersFile, err)
	}
	defer f.Close()

	params := &chaincfg.MainNetParams
	floor := mainnetHvmGenesisHeight

	// 1. Collect every unique committed header (by hash), preserving a representative BtcAttr batch list.
	type line struct {
		Blk  uint64   `json:"blk"`
		Tip  string   `json:"tip"`
		Hdrs []string `json:"hdrs"`
	}
	headersByHash := map[chainhash.Hash]*wire.BlockHeader{}
	var batches [][]*wire.BlockHeader
	nLines, nRawHdrs := 0, 0

	gen, err := parseHeader80(mainnetHvmGenesisHeader)
	if err != nil {
		t.Fatalf("decode mainnet hVM genesis header: %v", err)
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
			headersByHash[bh.BlockHash()] = bh
			batch = append(batch, bh)
		}
		if len(batch) > 0 {
			batches = append(batches, batch)
		}
	}
	if err := sc.Err(); err != nil {
		t.Fatalf("scanning %s: %v", headersFile, err)
	}

	// 2. Assign heights by BFS from the effective genesis (handles forks: each header connects to its own
	//    parent). Any header that never connects back to genesis is reported (a gap in the set).
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

	unconnected := 0
	for h := range headersByHash {
		if _, ok := height[h]; !ok {
			unconnected++
		}
	}

	t.Logf("BtcAttr txs=%d  raw headers=%d  unique committed headers=%d  connected=%d  unconnected=%d",
		nLines, nRawHdrs, len(headersByHash), len(height), unconnected)
	if unconnected > 0 {
		t.Errorf("%d committed headers do not connect to the hVM effective genesis — reconstruction gap or fork-root missing", unconnected)
	}

	// 3. Proof-of-work check: every committed header (including below the clearance band — PoW is
	//    context-free and the apply path enforces it floor-independently) must meet its own claimed
	//    target. Real Bitcoin-mainnet headers are really mined, so this must be zero failures; a non-zero
	//    count would mean the committed set contains a forged/zero-PoW header — exactly what the new PoW
	//    gate rejects, and what would make the restore-skip (enforceBTCDiff=false) divergence reachable.
	powRejected := 0
	var firstPoWRejects []string
	for h, bh := range headersByHash {
		if h == gen.BlockHash() {
			continue
		}
		if err := checkBTCHeaderPoWWith(bh, params); err != nil {
			powRejected++
			if len(firstPoWRejects) < 20 {
				firstPoWRejects = append(firstPoWRejects, fmt.Sprintf("%s @ %d : %v", h, height[h], err))
			}
		}
	}
	t.Logf("PER-HEADER PoW: rejected=%d of %d committed headers", powRejected, len(headersByHash)-1)
	for _, r := range firstPoWRejects {
		t.Errorf("MAINNET HISTORY PoW FAILURE (forged/zero-PoW committed header): %s", r)
	}

	// 4. Per-header contextual-difficulty check: every committed header at or above the floor-clearance
	//    band (floor + floorClearance) is enforced on the apply path. Run the exact validator and confirm
	//    zero rejections. Below the clearance band the apply path defers (not enforced), so those headers
	//    are only exercised as ancestry here.
	enforceFrom := floor + floorClearance(params)
	enforced, rejected := 0, 0
	var firstRejects []string
	for h, bh := range headersByHash {
		if height[h] < enforceFrom {
			continue
		}
		enforced++
		if err := validateBTCHeaderContextWith(ctx(), store, params, bh); err != nil {
			// ErrBTCHeaderContextUnavailable is an ancestry gap in our reconstruction, not a consensus
			// reject; a btcd RuleError is a genuine contextual-difficulty reject (the thing we are hunting).
			if errors.Is(err, ErrBTCHeaderContextUnavailable) {
				t.Errorf("ancestry unavailable for committed header %s @ %d (reconstruction gap): %v", h, height[h], err)
				continue
			}
			rejected++
			if len(firstRejects) < 20 {
				var re blockchain.RuleError
				code := "?"
				if errors.As(err, &re) {
					code = re.ErrorCode.String()
				}
				firstRejects = append(firstRejects, fmt.Sprintf("%s @ %d : %s (%v)", h, height[h], code, err))
			}
		}
	}

	// 5. Apply-path faithfulness: replay each BtcAttr batch through the exact batch validator the apply
	//    path calls, with the real floor. Outcomes must be accept (nil) or defer (ErrBTCBatchBelowFloor);
	//    a RuleError here is a false-reject of a historical block.
	batchAccept, batchDefer, batchReject, batchSkip := 0, 0, 0, 0
	var firstBatchRejects []string
	for _, b := range batches {
		switch err := validateBTCHeaderBatchWith(ctx(), store, params, floor, b); {
		case err == nil:
			batchAccept++
		case errors.Is(err, ErrBTCBatchBelowFloor):
			batchDefer++
		case errors.Is(err, ErrBTCHeaderContextUnavailable):
			batchSkip++
		default:
			batchReject++
			if len(firstBatchRejects) < 20 {
				firstBatchRejects = append(firstBatchRejects, b[0].BlockHash().String()+" : "+err.Error())
			}
		}
	}

	t.Logf("PER-HEADER: enforced=%d rejected=%d (enforce from height >= %d)", enforced, rejected, enforceFrom)
	t.Logf("PER-BATCH:  accept=%d defer=%d skip=%d reject=%d", batchAccept, batchDefer, batchSkip, batchReject)
	for _, r := range firstRejects {
		t.Errorf("CONTEXTUAL-DIFFICULTY PER-HEADER REJECT: %s", r)
	}
	for _, r := range firstBatchRejects {
		t.Errorf("CONTEXTUAL-DIFFICULTY BATCH REJECT: %s", r)
	}
	// Guard against a vacuous CLEAN: an empty/truncated reconstruction file (or a parse that placed nothing)
	// would leave the loops with nothing to reject and print CLEAN despite verifying nothing. Require that the
	// file parsed real headers AND the enforced per-header validator actually ran on at least one of them.
	if nRawHdrs == 0 || enforced == 0 {
		t.Fatalf("reconstruction parsed %d raw headers and enforced %d — too few to verify; a CLEAN verdict here would be vacuous", nRawHdrs, enforced)
	}
	if rejected == 0 && batchReject == 0 && batchSkip == 0 && unconnected == 0 {
		t.Logf("CLEAN: the contextual-difficulty validator accepts ALL %d committed mainnet headers; history is clean — safe to enforce from genesis.", len(headersByHash)-1)
	}
}
