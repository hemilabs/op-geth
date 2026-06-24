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

package snap

import (
	"bytes"
	"fmt"
	"math/big"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/trie"
)

// These tests cover the hardening of Syncer.OnHvmLightState against malicious or malformed hVM
// light-state responses. The handler (1) drops unsolicited packets via a request-ID presence check
// (without consuming the ID), (2) pins the response to the requested pivot, and (3) rejects malformed
// responses with an error rather than panicking, all while leaving the happy path untouched.

// hvmLightStatePeer is a minimal SyncPeer for exercising OnHvmLightState.
type hvmLightStatePeer struct{ id string }

func (p *hvmLightStatePeer) ID() string      { return p.id }
func (p *hvmLightStatePeer) Log() log.Logger { return log.New("test-peer", p.id) }
func (p *hvmLightStatePeer) RequestAccountRange(id uint64, root, origin, limit common.Hash, bytes uint64) error {
	return nil
}
func (p *hvmLightStatePeer) RequestStorageRanges(id uint64, root common.Hash, accounts []common.Hash, origin, limit []byte, bytes uint64) error {
	return nil
}
func (p *hvmLightStatePeer) RequestByteCodes(id uint64, hashes []common.Hash, bytes uint64) error {
	return nil
}
func (p *hvmLightStatePeer) RequestTrieNodes(id uint64, root common.Hash, paths []TrieNodePathSet, bytes uint64) error {
	return nil
}
func (p *hvmLightStatePeer) RequestHvmLightState(id uint64, tip common.Hash) error { return nil }

// newHvmTestSyncer builds a Syncer with a snapSyncHvm callback that records its
// invocations, returning the syncer and a pointer to the recorded calls.
func newHvmTestSyncer(t *testing.T) (*Syncer, *[]hvmSnapCall) {
	t.Helper()
	var calls []hvmSnapCall
	s := NewSyncer(rawdb.NewMemoryDatabase(), rawdb.HashScheme, func(btcTip *chainhash.Hash, hvmTip *types.Header) {
		calls = append(calls, hvmSnapCall{btcTip: btcTip, hvmTip: hvmTip})
	}, nil)
	return s, &calls
}

type hvmSnapCall struct {
	btcTip *chainhash.Hash
	hvmTip *types.Header
}

func nonZeroTip() [32]byte {
	var tip [32]byte
	for i := range tip {
		tip[i] = byte(i + 1)
	}
	return tip
}

// blockFromTxs builds a block whose header tx root matches its body, so it passes
// OnHvmLightState's body-consistency check.
func blockFromTxs(txs types.Transactions) *types.Block {
	h := &types.Header{Number: big.NewInt(1), TxHash: types.DeriveSha(txs, trie.NewStackTrie(nil))}
	return types.NewBlockWithHeader(h).WithBody(types.Body{Transactions: txs})
}

func btcAttrTx(t *testing.T, btcTip [32]byte) *types.Transaction {
	t.Helper()
	data, err := (&types.BtcAttributesDepositData{CanonicalTip: btcTip}).MarshalBinary()
	require.NoError(t, err)
	to := common.HexToAddress("0x4200000000000000000000000000000000000015")
	return types.NewTx(&types.BtcAttributesDepositedTx{To: &to, Gas: 0, Data: data})
}

// consistentBtcAttrBlock: body-consistent block carrying one valid BtcAttr tx.
func consistentBtcAttrBlock(t *testing.T, btcTip [32]byte) *types.Block {
	t.Helper()
	blk := blockFromTxs(types.Transactions{btcAttrTx(t, btcTip)})
	require.True(t, blk.Transactions()[0].IsBtcAttributesDepositedTx())
	return blk
}

// pinnedHeaders returns (reqTip, headers) such that headers[0].Hash()==reqTip, the headers chain back
// via ParentHash, and headers[len-1]==block.Header(). This is the response OnHvmLightState's pin
// accepts for a request whose recorded tip is reqTip (responder returns headers[0]=requested pivot,
// walked back to the BtcAttr block = headers[len-1] = block).
func pinnedHeaders(t *testing.T, block *types.Block, numHeaders int) (common.Hash, []*types.Header) {
	t.Helper()
	require.GreaterOrEqual(t, numHeaders, 1)
	headers := make([]*types.Header, numHeaders)
	headers[numHeaders-1] = block.Header()
	for i := numHeaders - 2; i >= 0; i-- {
		headers[i] = &types.Header{
			Number:     new(big.Int).Add(block.Number(), big.NewInt(int64(numHeaders-1-i))),
			ParentHash: headers[i+1].Hash(),
		}
	}
	return headers[0].Hash(), headers
}

// An unsolicited packet (request ID we never issued) must be dropped at the presence check, before any
// parsing — even a payload that would otherwise panic.
func TestOnHvmLightStateDropsUnsolicited(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	peer := &hvmLightStatePeer{id: "attacker"}

	var err error
	require.NotPanics(t, func() {
		err = s.OnHvmLightState(peer, 999 /* never requested */, nil, blockFromTxs(nil))
	}, "an unsolicited hVM light state packet must not panic")
	require.NoError(t, err, "unsolicited packet is silently ignored (like a stale account response), not an error")
	require.Empty(t, *calls, "snapSyncHvm must not be invoked for an unsolicited packet")
}

// Happy path: a solicited, pinned, well-formed response drives snapSyncHvm with the decoded canonical
// tip and the last header.
func TestOnHvmLightStateHappyPath(t *testing.T) {
	s, calls := newHvmTestSyncer(t)

	btcTip := nonZeroTip()
	block := consistentBtcAttrBlock(t, btcTip)
	reqTip, headers := pinnedHeaders(t, block, 2)

	require.Empty(t, s.hvmLightStateReqs)
	s.RequestHvmState(reqTip)
	require.Len(t, s.hvmLightStateReqs, 1, "RequestHvmState must record the in-flight request ID -> tip")
	var id uint64
	for k := range s.hvmLightStateReqs {
		id = k
	}

	err := s.OnHvmLightState(&hvmLightStatePeer{id: "honest"}, id, headers, block)
	require.NoError(t, err)
	require.Len(t, *calls, 1, "the happy path must drive snapSyncHvm exactly once")

	wantTip, err := chainhash.NewHash(btcTip[:])
	require.NoError(t, err)
	require.Equal(t, wantTip, (*calls)[0].btcTip, "canonical tip must be forwarded")
	require.Equal(t, headers[len(headers)-1], (*calls)[0].hvmTip, "the last header must be forwarded")
	require.Contains(t, s.hvmLightStateReqs, id, "the request ID is NOT consumed (so a later valid response can still complete the round)")
}

// A solicited, fully-validated response triggers a best-effort peer request for the BtcAttr canonical tip
// block AND every BTC header carried in the BtcAttr tx. The requests are issued from detached goroutines,
// so they only fire after the request-ID + pin validation gauntlet has accepted the response (a malicious
// unsolicited packet cannot drive them). Pins the requestBtcBlockFromPeers wiring threaded through
// NewSyncer (the merged hemi snap-sync block-fetch path).
func TestOnHvmLightStateRequestsBtcBlocksFromPeers(t *testing.T) {
	// BtcAttr carrying a canonical tip + two distinct serialized BTC headers.
	btcTip := nonZeroTip()
	hdr1 := wire.BlockHeader{Version: 1, Nonce: 111}
	hdr2 := wire.BlockHeader{Version: 1, Nonce: 222}
	var raw1, raw2 [types.BitcoinHeaderLengthBytes]byte
	var b1, b2 bytes.Buffer
	require.NoError(t, hdr1.Serialize(&b1))
	require.NoError(t, hdr2.Serialize(&b2))
	copy(raw1[:], b1.Bytes())
	copy(raw2[:], b2.Bytes())

	data, err := (&types.BtcAttributesDepositData{CanonicalTip: btcTip, Headers: [][types.BitcoinHeaderLengthBytes]byte{raw1, raw2}}).MarshalBinary()
	require.NoError(t, err)
	to := common.HexToAddress("0x4200000000000000000000000000000000000015")
	tx := types.NewTx(&types.BtcAttributesDepositedTx{To: &to, Gas: 0, Data: data})
	block := blockFromTxs(types.Transactions{tx})
	require.True(t, block.Transactions()[0].IsBtcAttributesDepositedTx())

	// Record every hash the syncer asks peers for (issued from detached goroutines).
	var mu sync.Mutex
	requested := map[common.Hash]int{}
	s := NewSyncer(rawdb.NewMemoryDatabase(), rawdb.HashScheme,
		func(*chainhash.Hash, *types.Header) {},
		func(h common.Hash) { mu.Lock(); requested[h]++; mu.Unlock() })

	reqTip, headers := pinnedHeaders(t, block, 2)
	s.RequestHvmState(reqTip)
	var id uint64
	for k := range s.hvmLightStateReqs {
		id = k
	}

	require.NoError(t, s.OnHvmLightState(&hvmLightStatePeer{id: "honest"}, id, headers, block))

	want := map[common.Hash]struct{}{
		common.Hash(btcTip):           {},
		common.Hash(hdr1.BlockHash()): {},
		common.Hash(hdr2.BlockHash()): {},
	}
	require.Eventually(t, func() bool {
		mu.Lock()
		defer mu.Unlock()
		if len(requested) != len(want) {
			return false
		}
		for h := range want {
			if requested[h] == 0 {
				return false
			}
		}
		return true
	}, 2*time.Second, 10*time.Millisecond, "must request the canonical tip + each BTC header block from peers")
}

// An unsolicited response must NOT trigger any peer BTC-block request: the request-ID presence check drops
// it before the requestBtcBlockFromPeers fan-out, so a peer cannot use light-state packets to make us spam
// block requests.
func TestOnHvmLightStateUnsolicitedDoesNotRequestBtcBlocks(t *testing.T) {
	var mu sync.Mutex
	requested := 0
	s := NewSyncer(rawdb.NewMemoryDatabase(), rawdb.HashScheme,
		func(*chainhash.Hash, *types.Header) {},
		func(common.Hash) { mu.Lock(); requested++; mu.Unlock() })

	block := consistentBtcAttrBlock(t, nonZeroTip())
	_, headers := pinnedHeaders(t, block, 2)
	require.NoError(t, s.OnHvmLightState(&hvmLightStatePeer{id: "attacker"}, 999 /* never requested */, headers, block))

	// Give any (erroneously) spawned goroutine a chance to run before asserting none did.
	require.Never(t, func() bool {
		mu.Lock()
		defer mu.Unlock()
		return requested > 0
	}, 200*time.Millisecond, 20*time.Millisecond, "an unsolicited packet must not trigger peer BTC-block requests")
}

// A solicited, fully-validated response whose BtcAttr CanonicalTip is all-zeros must be rejected BEFORE the
// BTC-block fan-out, so no (futile) all-zeros peer request is issued. Pins the zero-tip-before-fan-out
// ordering: with the fan-out placed ahead of the zero-tip reject, the recorder would fire.
func TestOnHvmLightStateZeroTipDoesNotFanOut(t *testing.T) {
	var mu sync.Mutex
	requested := 0
	s := NewSyncer(rawdb.NewMemoryDatabase(), rawdb.HashScheme,
		func(*chainhash.Hash, *types.Header) {},
		func(common.Hash) { mu.Lock(); requested++; mu.Unlock() })

	block := consistentBtcAttrBlock(t, [32]byte{}) // valid BtcAttr tx, but an all-zeros canonical tip
	reqTip, headers := pinnedHeaders(t, block, 2)
	s.RequestHvmState(reqTip)
	var id uint64
	for k := range s.hvmLightStateReqs {
		id = k
	}

	err := s.OnHvmLightState(&hvmLightStatePeer{id: "honest"}, id, headers, block)
	require.Error(t, err, "a solicited response with an all-zeros canonical tip must be rejected")
	require.Contains(t, err.Error(), "canonical tip is zero")
	require.Never(t, func() bool {
		mu.Lock()
		defer mu.Unlock()
		return requested > 0
	}, 200*time.Millisecond, 20*time.Millisecond, "a zero-tip response must be rejected before any peer BTC-block fan-out")
}

// Boundary: a response carrying EXACTLY maxHvmLightHeaders headers (the honest server's walk-back cap) must
// be ACCEPTED — only strictly more than maxHvmLightHeaders is rejected. Pairs with
// TestOnHvmLightStateTooManyHeadersRejected (max+1) to pin the receive-side bound against a `>` -> `>=`
// off-by-one that would false-reject an honest maximum-length response.
func TestOnHvmLightStateMaxHeadersAccepted(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	block := consistentBtcAttrBlock(t, nonZeroTip())
	reqTip, headers := pinnedHeaders(t, block, maxHvmLightHeaders)
	require.Len(t, headers, maxHvmLightHeaders)

	s.RequestHvmState(reqTip)
	var id uint64
	for k := range s.hvmLightStateReqs {
		id = k
	}
	err := s.OnHvmLightState(&hvmLightStatePeer{id: "honest"}, id, headers, block)
	require.NoError(t, err, "a response with exactly maxHvmLightHeaders headers must be accepted, not rejected")
	require.Len(t, *calls, 1, "a max-length valid response must drive snapSyncHvm exactly once")
}

// A solicited, pinned response whose block has no BtcAttr tx must be rejected with an error (not a
// nil-pointer panic) and must not drive sync.
func TestOnHvmLightStateNoBtcAttrTxRejected(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(7)

	block := blockFromTxs(nil) // body-consistent, but no BtcAttr tx
	reqTip, headers := pinnedHeaders(t, block, 2)
	s.hvmLightStateReqs[id] = reqTip

	var err error
	require.NotPanics(t, func() {
		err = s.OnHvmLightState(&hvmLightStatePeer{id: "peer"}, id, headers, block)
	}, "a block with no BtcAttr tx must not panic (was a nil-deref)")
	require.ErrorContains(t, err, "no Bitcoin Attributes Deposited tx",
		"must be rejected specifically by the missing-BtcAttr guard, not an earlier check")
	require.Empty(t, *calls)
	require.Contains(t, s.hvmLightStateReqs, id, "a rejected response must NOT consume the request ID")
}

// A solicited response with an empty Headers slice must be rejected (not an OOB panic) at the
// empty-headers guard, before the pin.
func TestOnHvmLightStateEmptyHeadersRejected(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(11)
	s.hvmLightStateReqs[id] = common.Hash{}

	var err error
	require.NotPanics(t, func() {
		err = s.OnHvmLightState(&hvmLightStatePeer{id: "peer"}, id, []*types.Header{}, consistentBtcAttrBlock(t, nonZeroTip()))
	}, "empty headers must not panic")
	require.ErrorContains(t, err, "no headers", "must be rejected specifically by the empty-headers guard")
	require.Empty(t, *calls)
}

// A solicited response with a nil block must be rejected (not a nil-deref panic) at the block==nil guard,
// before any field of the block is touched. RLP decoding rejects a nil block over the wire, so this guards
// the defense-in-depth check; without it the nil block flows into snapSyncHvm and is dereferenced.
func TestOnHvmLightStateNilBlockRejected(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(13)
	s.hvmLightStateReqs[id] = common.Hash{}

	var err error
	require.NotPanics(t, func() {
		err = s.OnHvmLightState(&hvmLightStatePeer{id: "peer"}, id, []*types.Header{{}}, nil)
	}, "a nil block must not panic")
	require.ErrorContains(t, err, "no block", "a nil block must be rejected at the block==nil guard")
	require.Empty(t, *calls, "snapSyncHvm must not be invoked for a nil-block response")
	require.Contains(t, s.hvmLightStateReqs, id, "a rejected response must NOT consume the request ID")
}

// A solicited response carrying more headers than the honest server would ever send (maxHvmLightHeaders)
// is rejected on the receive side, before the pin. The honest responder walks back at most maxHvmLightHeaders
// to the nearest BtcAttr block; a malicious peer could otherwise send a much longer connected chain that
// walks past the nearest BtcAttr ancestor to an older one. This is the cheap receive-side bound that backs
// up the base-body completion gate in SnapSyncHvm.
func TestOnHvmLightStateTooManyHeadersRejected(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(12)
	s.hvmLightStateReqs[id] = common.Hash{}

	// len > maxHvmLightHeaders trips the bound before any header is dereferenced (entries may be nil).
	headers := make([]*types.Header, maxHvmLightHeaders+1)
	var err error
	require.NotPanics(t, func() {
		err = s.OnHvmLightState(&hvmLightStatePeer{id: "peer"}, id, headers, consistentBtcAttrBlock(t, nonZeroTip()))
	}, "an over-long header list must not panic")
	require.ErrorContains(t, err, "too many headers", "must be rejected specifically by the receive-side header bound, not a later check")
	require.Empty(t, *calls, "snapSyncHvm must not be invoked for a rejected response")
	require.Contains(t, s.hvmLightStateReqs, id, "a rejected response must NOT consume the request ID")
}

// A solicited, pinned response with a valid BtcAttr tx but a zero canonical tip is rejected by the
// pre-existing zero-tip guard (no regression).
func TestOnHvmLightStateZeroTipRejected(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(13)

	block := consistentBtcAttrBlock(t, [32]byte{}) // valid tx, zero canonical tip
	reqTip, headers := pinnedHeaders(t, block, 1)
	s.hvmLightStateReqs[id] = reqTip

	err := s.OnHvmLightState(&hvmLightStatePeer{id: "peer"}, id, headers, block)
	require.ErrorContains(t, err, "canonical tip is zero", "must be rejected specifically by the zero-tip guard")
	require.Empty(t, *calls)
}

// Tip validation: a response for a different tip than requested (headers[0] does not hash to the
// recorded tip) must be rejected before driving sync.
func TestOnHvmLightStateWrongTipRejected(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(51)
	s.hvmLightStateReqs[id] = common.Hash{0xAA} // a fixed hash that differs from the response's headers[0]

	block := consistentBtcAttrBlock(t, nonZeroTip())
	_, headers := pinnedHeaders(t, block, 2) // internally consistent, but for a different tip

	err := s.OnHvmLightState(&hvmLightStatePeer{id: "peer"}, id, headers, block)
	require.ErrorContains(t, err, "does not match the requested tip",
		"a response whose first header is not the requested tip must be rejected by the pin")
	require.Empty(t, *calls)
	require.Contains(t, s.hvmLightStateReqs, id)
}

// Tip validation: a response whose headers do not form a connected chain must be rejected
// (headers[i].ParentHash != headers[i+1].Hash()).
func TestOnHvmLightStateBrokenChainRejected(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(53)

	block := consistentBtcAttrBlock(t, nonZeroTip())
	reqTip, headers := pinnedHeaders(t, block, 3)
	s.hvmLightStateReqs[id] = reqTip
	// Break the link between headers[0] and headers[1] without changing headers[0]'s hash, so the tip
	// check still passes but the chain check fails.
	headers[1] = &types.Header{Number: big.NewInt(999)}

	err := s.OnHvmLightState(&hvmLightStatePeer{id: "peer"}, id, headers, block)
	require.ErrorContains(t, err, "not a connected chain", "non-connected headers must be rejected by the chain check")
	require.Empty(t, *calls)
}

// Tip validation: a response whose block body does not match its header's tx root (a forged BtcAttr tx
// grafted onto a genuine header) must be rejected — this is what pins the CanonicalTip to the genuine
// chain.
func TestOnHvmLightStateBodyMismatchRejected(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(57)

	// Genuine header committing to tipA's tx, but a forged body carrying tipB's tx.
	genuine := consistentBtcAttrBlock(t, nonZeroTip())
	var tipB [32]byte
	tipB[0] = 0xBB
	forged := types.NewBlockWithHeader(genuine.Header()).WithBody(types.Body{Transactions: types.Transactions{btcAttrTx(t, tipB)}})

	reqTip, headers := pinnedHeaders(t, forged, 1) // headers[len-1] == forged.Header() == genuine.Header()
	s.hvmLightStateReqs[id] = reqTip

	err := s.OnHvmLightState(&hvmLightStatePeer{id: "peer"}, id, headers, forged)
	require.ErrorContains(t, err, "body is inconsistent with its header",
		"a block whose body does not match its header tx root must be rejected by the body-consistency check")
	require.Empty(t, *calls)
}

// A solicited response with a nil last header must be rejected, not forwarded to snapSyncHvm
// (defense-in-depth; the nil-header guard precedes the pin).
func TestOnHvmLightStateNilLastHeaderRejected(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(31)
	s.hvmLightStateReqs[id] = common.Hash{}

	var err error
	require.NotPanics(t, func() {
		err = s.OnHvmLightState(&hvmLightStatePeer{id: "peer"}, id, []*types.Header{nil}, consistentBtcAttrBlock(t, nonZeroTip()))
	})
	require.ErrorContains(t, err, "nil header", "a nil last header must be rejected by the nil-header guard")
	require.Empty(t, *calls, "a nil header must not be forwarded to snapSyncHvm")
	require.Contains(t, s.hvmLightStateReqs, id, "a rejected response must not consume the ID")
}

// A solicited, pinned response whose block carries more than one BtcAttr tx must be rejected by
// ExtractBtcAttrData's error path (no panic, no sync drive).
func TestOnHvmLightStateMultipleBtcAttrTxRejected(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(41)

	block := blockFromTxs(types.Transactions{btcAttrTx(t, nonZeroTip()), btcAttrTx(t, nonZeroTip())})
	reqTip, headers := pinnedHeaders(t, block, 1)
	s.hvmLightStateReqs[id] = reqTip

	var err error
	require.NotPanics(t, func() {
		err = s.OnHvmLightState(&hvmLightStatePeer{id: "peer"}, id, headers, block)
	})
	require.ErrorContains(t, err, "error extracting Bitcoin Attributes Deposited tx",
		"more than one BtcAttr tx must be rejected by ExtractBtcAttrData's error path, not panic")
	require.Empty(t, *calls)
}

// The request ID is not consumed by a valid response: every solicited, valid, pinned response is
// forwarded to snapSyncHvm (idempotency is SnapSyncHvm's latch, not the gate). So two valid responses
// for the same broadcast ID both drive the callback and the ID stays in place.
func TestOnHvmLightStateValidResponsesNotConsumed(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(21)

	block := consistentBtcAttrBlock(t, nonZeroTip())
	reqTip, headers := pinnedHeaders(t, block, 1)
	s.hvmLightStateReqs[id] = reqTip

	require.NoError(t, s.OnHvmLightState(&hvmLightStatePeer{id: "first"}, id, headers, block))
	require.NoError(t, s.OnHvmLightState(&hvmLightStatePeer{id: "second"}, id, headers, block))
	require.Len(t, *calls, 2, "both solicited valid responses are forwarded (dedup is SnapSyncHvm's latch, not the gate)")
	require.Contains(t, s.hvmLightStateReqs, id, "a valid response does not consume the ID")
}

// Stall regression: a peer that responds first with a rejected payload must not prevent an honest
// peer's later valid response from completing the round, because the gate never consumes the ID.
func TestOnHvmLightStateMalformedFirstValidSecond(t *testing.T) {
	s, calls := newHvmTestSyncer(t)
	const id = uint64(101)

	block := consistentBtcAttrBlock(t, nonZeroTip())
	reqTip, headers := pinnedHeaders(t, block, 2)
	s.hvmLightStateReqs[id] = reqTip

	// First responder sends a response that fails validation (wrong tip), so it is rejected.
	errFirst := s.OnHvmLightState(&hvmLightStatePeer{id: "attacker"}, id, []*types.Header{{Number: big.NewInt(5)}}, blockFromTxs(nil))
	require.Error(t, errFirst, "bad first response is rejected")
	require.Empty(t, *calls, "rejected response must not drive sync")
	require.Contains(t, s.hvmLightStateReqs, id, "a rejected response must NOT consume the broadcast request ID")

	// Honest peer then answers with the valid, pinned response for the SAME ID.
	require.NoError(t, s.OnHvmLightState(&hvmLightStatePeer{id: "honest"}, id, headers, block))
	require.Len(t, *calls, 1, "the honest valid response must still complete the round (no stall)")
	require.Contains(t, s.hvmLightStateReqs, id, "the ID is never consumed")
}

// RequestHvmState iterates the peer set, which Register/Unregister mutate under s.lock from other
// goroutines; it snapshots the peers under the lock. This test hammers RequestHvmState against
// continuous peer churn and must be clean under -race.
func TestRequestHvmStateConcurrentWithPeerChurn(t *testing.T) {
	s, _ := newHvmTestSyncer(t)

	var stop atomic.Bool
	var wg sync.WaitGroup

	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for !stop.Load() {
				s.RequestHvmState(common.Hash{})
			}
		}()
	}
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()
			p := &hvmLightStatePeer{id: fmt.Sprintf("churn-peer-%d", id)}
			for !stop.Load() {
				_ = s.Register(p)
				_ = s.Unregister(p.ID())
			}
		}(i)
	}

	time.Sleep(200 * time.Millisecond)
	stop.Store(true)
	wg.Wait()
}

// The in-flight request-ID set must stay bounded even if requests go unanswered.
func TestRequestHvmStateBounded(t *testing.T) {
	s, _ := newHvmTestSyncer(t)
	for i := 0; i < maxHvmLightStateReqs*3; i++ {
		s.RequestHvmState(common.Hash{})
		require.LessOrEqual(t, len(s.hvmLightStateReqs), maxHvmLightStateReqs, "in-flight request-ID set must stay bounded")
	}
}

// Concurrent valid responses for the same broadcast ID must be handled without a data race on the
// in-flight set. The gate does not consume the ID, so all are forwarded. Run with -race.
func TestOnHvmLightStateConcurrentValidResponses(t *testing.T) {
	var count int64
	s := NewSyncer(rawdb.NewMemoryDatabase(), rawdb.HashScheme, func(*chainhash.Hash, *types.Header) {
		atomic.AddInt64(&count, 1)
	}, nil)
	const id = uint64(77)

	btcTip := nonZeroTip()
	// numHeaders=1 -> reqTip is deterministic (= block header hash), so every goroutine building its
	// own identical block produces the same pinned response.
	reqTip, _ := pinnedHeaders(t, consistentBtcAttrBlock(t, btcTip), 1)
	s.hvmLightStateReqs[id] = reqTip

	const n = 16
	var wg sync.WaitGroup
	wg.Add(n)
	for i := 0; i < n; i++ {
		go func() {
			defer wg.Done()
			block := consistentBtcAttrBlock(t, btcTip) // each goroutine its own block
			_, headers := pinnedHeaders(t, block, 1)
			require.NoError(t, s.OnHvmLightState(&hvmLightStatePeer{id: "p"}, id, headers, block))
		}()
	}
	wg.Wait()

	require.Equal(t, int64(n), atomic.LoadInt64(&count), "every solicited valid response is forwarded (no consume-based dedup)")
	require.Contains(t, s.hvmLightStateReqs, id, "the ID is never consumed by responses")
}
