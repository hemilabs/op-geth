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
	"errors"
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/enode"
)

// TestBTCGossipHandlersNilTBCFullNodeIgnored is the regression for a node started without hVM
// (HvmEnabled=false), where the full TBC node is never initialized (vm.TBCFullNode is nil). Before the
// fix, a peer's GetBtcBlocksMsg/BtcBlocksMsg nil-dereferenced vm.TBCFullNode in the gossip handlers and
// crashed the process (precompiles guarded this; the handlers did not). After the fix both handler
// paths ignore the message gracefully (no panic), so one unsolicited message cannot crash-loop a
// non-hVM node.
func TestBTCGossipHandlersNilTBCFullNodeIgnored(t *testing.T) {
	orig := vm.TBCFullNode
	vm.TBCFullNode = nil
	defer func() { vm.TBCFullNode = orig }()

	// handleGetBTCBlocks path: ServiceGetBTCBlocksQuery must serve no blocks (handler replies with an
	// empty set) instead of dereferencing vm.TBCFullNode.BlockByHash. A non-empty query proves the
	// guard returns before the per-hash lookup loop.
	query := GetBTCBlocksRequest{common.HexToHash("0x01"), common.HexToHash("0x02")}
	var served []*common.BitcoinBlock
	require.NotPanics(t, func() { served = ServiceGetBTCBlocksQuery(nil, query) },
		"GetBtcBlocks service must not nil-deref vm.TBCFullNode when hVM is disabled")
	require.Nil(t, served, "with no full TBC node the query must serve no blocks")

	// handleBTCBlocks path: the nil-guard precedes message decode, so the handler ignores the gossip
	// and returns nil without touching msg/peer (passing nil for both proves it).
	var err error
	require.NotPanics(t, func() { err = handleBTCBlocks(nil, nil, nil) },
		"BtcBlocks handler must not nil-deref vm.TBCFullNode when hVM is disabled")
	require.NoError(t, err, "BtcBlocks gossip must be ignored (return nil), not error/crash, on a non-hVM node")
}

// TestHandleHvmBTCMessageGuardedRecoversPanic is the regression for the eth message-handler running on
// the per-peer goroutine with no recover() upstream (p2p/peer.go): an unrecovered fault in a Hemi BTC
// handler (the embedded Bitcoin node can fault on malformed or inconsistent peer-supplied data) would
// terminate the op-geth process. The dispatch boundary must contain a panic and
// convert it to an error (which handleMessage turns into a peer disconnect), leaving a normal handler's
// return value untouched.
func TestHandleHvmBTCMessageGuardedRecoversPanic(t *testing.T) {
	app, net := p2p.MsgPipe()
	defer app.Close()
	defer net.Close()
	peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
	defer peer.Close()

	// A handler that panics (standing in for a fault in the embedded Bitcoin node) must be contained and
	// converted to an error, never propagated to crash the process.
	panicking := func(backend Backend, msg Decoder, peer *Peer) error { panic("simulated invalid Bitcoin data") }
	var err error
	require.NotPanics(t, func() { err = handleHvmBTCMessageGuarded(panicking, nil, nil, peer) },
		"a panic in a BTC handler must be recovered, not propagated to the peer goroutine")
	require.Error(t, err, "a recovered BTC-handler panic must surface as an error so handleMessage drops the peer")

	// A non-panicking handler must pass through its returned error unchanged (no masking).
	sentinel := errors.New("normal handler error")
	passthrough := handleHvmBTCMessageGuarded(
		func(backend Backend, msg Decoder, peer *Peer) error { return sentinel }, nil, nil, peer)
	require.ErrorIs(t, passthrough, sentinel, "the guard must not alter a normal handler's returned error")

	// And a successful handler must pass through nil.
	ok := handleHvmBTCMessageGuarded(
		func(backend Backend, msg Decoder, peer *Peer) error { return nil }, nil, nil, peer)
	require.NoError(t, ok, "the guard must not alter a normal handler's nil return")
}

// TestHandleMessageRoutesBTCCodesThroughRecover closes the gap the unit test above leaves open: it
// proves the handler.go dispatch actually routes the eth/68 BTC codes (GetBtcBlocksMsg 0x11,
// BtcBlocksMsg 0x12) through the recover boundary. It swaps in a panicking handler for each BTC code
// and drives the real handleMessage; a panic must surface as an error (peer torn down), not crash the
// process. Without the dispatch wiring in handler.go this fails even though handleHvmBTCMessageGuarded
// is correct, so it guards the glue that would otherwise re-expose the whole-process crash.
func TestHandleMessageRoutesBTCCodesThroughRecover(t *testing.T) {
	for _, code := range []uint64{GetBtcBlocksMsg, BtcBlocksMsg} {
		code := code
		t.Run(fmt.Sprintf("code_%#x", code), func(t *testing.T) {
			// Swap the eth/68 handler for this code with one that panics, restoring afterward.
			orig := eth68[code]
			eth68[code] = func(backend Backend, msg Decoder, peer *Peer) error {
				panic("simulated invalid Bitcoin data on the BTC dispatch path")
			}
			t.Cleanup(func() { eth68[code] = orig })

			app, net := p2p.MsgPipe()
			defer app.Close()
			defer net.Close()
			peer := NewPeer(ETH68, p2p.NewPeer(enode.ID{}, "peer", nil), net, nil)
			defer peer.Close()

			// Feed one message of this code from the remote side.
			go func() { _ = p2p.Send(app, code, []byte{}) }()

			var err error
			require.NotPanics(t, func() { err = handleMessage(nil, peer) },
				"a panicking BTC handler must be recovered by the dispatch, not crash the process")
			require.Error(t, err, "the recovered panic must surface as an error so handleMessage drops the peer")
		})
	}
}
