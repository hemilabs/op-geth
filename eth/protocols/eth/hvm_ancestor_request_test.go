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

import (
	"context"
	"testing"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/enode"
)

// These tests cover the production WIRING of the ancestor-fetch path (requestMissingAncestors and its
// split-out requestMissingAncestorBlocks) — the batching, the maxBtcBlocksServe chunking, and that the
// walkGate slot is released on both the normal and the recover (panic) path. The walkGate primitive itself
// is covered by hvm_ancestor_walkgate_test.go; these pin the glue a mutation there could otherwise pass.

func makeMissingHeaders(n int) []wire.BlockHeader {
	hs := make([]wire.BlockHeader, n)
	for i := range hs {
		hs[i] = wire.BlockHeader{Version: 1, Nonce: uint32(i + 1)} // distinct nonces -> distinct hashes
	}
	return hs
}

// stubAvailability points the tbcBlocksAvailableToHeader seam at a function returning the given missing set,
// and returns a restore func. It lets the walk logic run without a live TBC full node.
func stubAvailability(missing []wire.BlockHeader) func() {
	orig := tbcBlocksAvailableToHeader
	tbcBlocksAvailableToHeader = func(context.Context, *wire.BlockHeader) (bool, *[]wire.BlockHeader, *chainhash.Hash, error) {
		return false, &missing, nil, nil
	}
	return func() { tbcBlocksAvailableToHeader = orig }
}

// readBtcBlockRequests reads exactly `expect` GetBtcBlocks messages the peer sent into the pipe and returns
// the hash list from each, failing on a timeout (a leaked gate slot would stall sends, which this catches).
func readBtcBlockRequests(t *testing.T, app *p2p.MsgPipeRW, expect int) [][]common.Hash {
	t.Helper()
	type res struct {
		hashes []common.Hash
		err    error
	}
	out := make([][]common.Hash, 0, expect)
	for i := 0; i < expect; i++ {
		ch := make(chan res, 1)
		go func() {
			msg, err := app.ReadMsg()
			if err != nil {
				ch <- res{err: err}
				return
			}
			if msg.Code != GetBtcBlocksMsg {
				ch <- res{err: errUnexpectedCode(msg.Code)}
				return
			}
			var p GetBTCBlocksPacket
			if err := msg.Decode(&p); err != nil {
				ch <- res{err: err}
				return
			}
			ch <- res{hashes: []common.Hash(p.GetBTCBlocksRequest)}
		}()
		select {
		case r := <-ch:
			require.NoError(t, r.err)
			out = append(out, r.hashes)
		case <-time.After(3 * time.Second):
			t.Fatalf("timed out waiting for BTC block request %d/%d (a leaked gate slot would stall sends)", i+1, expect)
		}
	}
	return out
}

type unexpectedCodeErr uint64

func (e unexpectedCodeErr) Error() string { return "unexpected message code" }
func errUnexpectedCode(c uint64) error    { return unexpectedCodeErr(c) }

// All missing ancestors below the chunk cap go out in ONE batched request (not one message per block).
func TestRequestMissingAncestorBlocksBatchesIntoOneRequest(t *testing.T) {
	missing := makeMissingHeaders(3)
	defer stubAvailability(missing)()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	go requestMissingAncestorBlocks(peer, &wire.BlockHeader{})

	got := readBtcBlockRequests(t, app, 1)
	require.Len(t, got, 1, "all missing ancestors below the cap must batch into ONE request")
	require.Len(t, got[0], 3, "the single request must carry all 3 missing hashes")
	want := map[common.Hash]bool{}
	for _, m := range missing {
		want[common.Hash(m.BlockHash())] = true
	}
	for _, h := range got[0] {
		require.True(t, want[h], "every requested hash must be a missing ancestor")
	}
}

// More missing ancestors than maxBtcBlocksServe are split into chunks of at most maxBtcBlocksServe, with all
// hashes covered exactly once across the chunks.
func TestRequestMissingAncestorBlocksChunksAtCap(t *testing.T) {
	const n = 2*maxBtcBlocksServe + 6
	missing := makeMissingHeaders(n)
	defer stubAvailability(missing)()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	go requestMissingAncestorBlocks(peer, &wire.BlockHeader{})

	got := readBtcBlockRequests(t, app, 3)
	require.Len(t, got, 3, "n=2*cap+6 must split into 3 chunks")
	require.Len(t, got[0], maxBtcBlocksServe)
	require.Len(t, got[1], maxBtcBlocksServe)
	require.Len(t, got[2], 6)
	total := 0
	for _, c := range got {
		require.LessOrEqual(t, len(c), maxBtcBlocksServe, "no chunk may exceed the cap")
		total += len(c)
	}
	require.Equal(t, n, total, "every missing hash must be requested across the chunks")
}

// requestMissingAncestors must release its gate slot after each call; otherwise the global cap is exhausted
// after maxConcurrentAncestorWalks calls. A cap-1 fresh gate + several sequential calls all proceeding
// proves the release runs (a dropped `defer release()` would stall the 2nd call and time out the read).
func TestRequestMissingAncestorsReleasesGateSlot(t *testing.T) {
	origGate := ancestorWalkGate
	ancestorWalkGate = newWalkGate(1)
	defer func() { ancestorWalkGate = origGate }()

	origNode := vm.TBCFullNode
	vm.TBCFullNode = &tbc.Server{} // non-nil so the nil-guard passes; the stubbed seam never touches it
	defer func() { vm.TBCFullNode = origNode }()

	defer stubAvailability(makeMissingHeaders(1))()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	const calls = 5
	go func() {
		for i := 0; i < calls; i++ {
			requestMissingAncestors(peer, &wire.BlockHeader{Nonce: uint32(i + 1)}) // distinct -> in-flight dedup never blocks
		}
	}()
	got := readBtcBlockRequests(t, app, calls)
	require.Len(t, got, calls, "every call must proceed; the gate slot is released after each")
}

// The gate slot must be released even when the walk panics (defer release runs on the recover path), so a
// torn-store panic cannot permanently jam the gate.
func TestRequestMissingAncestorsReleasesGateSlotOnPanic(t *testing.T) {
	origGate := ancestorWalkGate
	ancestorWalkGate = newWalkGate(1)
	defer func() { ancestorWalkGate = origGate }()

	origNode := vm.TBCFullNode
	vm.TBCFullNode = &tbc.Server{}
	defer func() { vm.TBCFullNode = origNode }()

	origFn := tbcBlocksAvailableToHeader
	tbcBlocksAvailableToHeader = func(context.Context, *wire.BlockHeader) (bool, *[]wire.BlockHeader, *chainhash.Hash, error) {
		panic("simulated torn TBC store")
	}
	defer func() { tbcBlocksAvailableToHeader = origFn }()

	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	require.NotPanics(t, func() { requestMissingAncestors(peer, &wire.BlockHeader{}) },
		"a panic in the walk must be recovered, not propagated")

	rel, ok := ancestorWalkGate.tryEnter(common.Hash{0xab})
	require.True(t, ok, "the gate slot must be released even when the walk panics")
	rel()
}
