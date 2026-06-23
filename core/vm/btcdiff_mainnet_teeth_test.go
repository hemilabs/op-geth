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

package vm

// Differential-replay TEETH guard. TestBtcDiffValidatorAcceptsAllMainnetCommittedHistory proves the committed mainnet
// fixture validates CLEAN under MainNetParams, with anti-vacuous guards proving the validator did real work — but
// it never proves the clean verdict is PARAMS-DISCRIMINATING. The entire enforce-gate/DEFER safety argument is that a mainnet
// header behaves DIFFERENTLY under testnet3 params (so a DEFER node must NOT enforce). This runs the IDENTICAL
// committed history under BOTH params and asserts it is clean under MainNetParams yet FLAGGED under TestNet3Params
// (whose ReduceMinDifficulty 20-minute rule mandates PowLimitBits for the many real >20-min-gap hard-difficulty
// blocks). Without this the gate could pass vacuously after a btcd/param refactor, and the DEFER rationale would be
// undemonstrated. Corpus-free: the already-committed bounded fixture, no full node.

import (
	"bufio"
	"bytes"
	"encoding/json"
	"errors"
	"os"
	"testing"

	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
)

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
