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

package downloader

import (
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/eth/protocols/snap"
	"github.com/ethereum/go-ethereum/log"
)

// These tests cover the hang-DoS fix in hVMLightStateSyncWithAllPeers: the previous uninterruptible
// busy-wait was replaced by a cancellable select loop (d.cancelCh / d.quitCh -> errCanceled) that
// polls for completion and re-issues the request. Before the fix, a peer answering with an unreachable
// canonical tip could wedge this wait forever and it could not be cancelled.

// hvmStubChain is a minimal BlockChain whose only meaningful behavior is the two hVM hooks the wait
// loop touches. Every other method is left to the embedded nil interface and panics if called, so the
// wait loop must not call them.
type hvmStubChain struct {
	BlockChain // embedded; unimplemented methods panic if invoked
	completed  atomic.Bool
}

func (c *hvmStubChain) HvmEnabled() bool           { return true }
func (c *hvmStubChain) HvmSnapSyncCompleted() bool { return c.completed.Load() }

// newHvmWaitDownloader builds the minimal Downloader needed to drive
// hVMLightStateSyncWithAllPeers in isolation (no real sync machinery).
func newHvmWaitDownloader(t *testing.T) (*Downloader, *hvmStubChain) {
	t.Helper()
	chain := &hvmStubChain{}
	d := &Downloader{
		blockchain: chain,
		SnapSyncer: snap.NewSyncer(rawdb.NewMemoryDatabase(), rawdb.HashScheme, nil, nil),
		cancelCh:   make(chan struct{}),
		quitCh:     make(chan struct{}),
	}
	return d, chain
}

// runHvmWait runs hVMLightStateSyncWithAllPeers in a goroutine and returns its error, failing on
// timeout (which means the wait was not cancellable / never returned).
func runHvmWait(t *testing.T, d *Downloader) error {
	t.Helper()
	errc := make(chan error, 1)
	go func() { errc <- d.hVMLightStateSyncWithAllPeers(common.Hash{}) }()
	select {
	case err := <-errc:
		return err
	case <-time.After(10 * time.Second):
		t.Fatal("hVMLightStateSyncWithAllPeers did not return — wait is not cancellable / wedged")
		return nil
	}
}

// Closing cancelCh must make the wait return errCanceled (mid-flight sync cancel).
func TestHVMLightStateSyncCancelledByCancelCh(t *testing.T) {
	d, _ := newHvmWaitDownloader(t)
	close(d.cancelCh)
	require.ErrorIs(t, runHvmWait(t, d), errCanceled, "cancelCh must abort the wait with errCanceled")
}

// Closing quitCh (termination) must make the wait return errCanceled.
func TestHVMLightStateSyncCancelledByQuitCh(t *testing.T) {
	d, _ := newHvmWaitDownloader(t)
	close(d.quitCh)
	require.ErrorIs(t, runHvmWait(t, d), errCanceled, "quitCh must abort the wait with errCanceled")
}

// When the blockchain reports completion, the wait must return nil (no error),
// detected on the poll tick.
func TestHVMLightStateSyncCompletes(t *testing.T) {
	d, chain := newHvmWaitDownloader(t)
	chain.completed.Store(true)
	require.NoError(t, runHvmWait(t, d), "completion must end the wait with no error")
}

// Cancellation must win even while the loop is actively waiting (not yet complete): the wait should
// return promptly after cancelCh closes, not only at a poll boundary.
func TestHVMLightStateSyncCancelWhilePending(t *testing.T) {
	d, _ := newHvmWaitDownloader(t)
	errc := make(chan error, 1)
	go func() { errc <- d.hVMLightStateSyncWithAllPeers(common.Hash{}) }()

	// Let the loop enter its select with no completion signalled.
	time.Sleep(50 * time.Millisecond)
	close(d.cancelCh)

	select {
	case err := <-errc:
		require.ErrorIs(t, err, errCanceled)
	case <-time.After(5 * time.Second):
		t.Fatal("pending wait was not cancelled")
	}
}

// countingSnapPeer is a snap.SyncPeer that counts hVM light-state requests so a test can observe
// re-broadcasts. All other methods are no-ops.
type countingSnapPeer struct {
	id          string
	hvmRequests atomic.Int64
}

func (p *countingSnapPeer) ID() string      { return p.id }
func (p *countingSnapPeer) Log() log.Logger { return log.New("test-peer", p.id) }
func (p *countingSnapPeer) RequestAccountRange(id uint64, root, origin, limit common.Hash, bytes uint64) error {
	return nil
}
func (p *countingSnapPeer) RequestStorageRanges(id uint64, root common.Hash, accounts []common.Hash, origin, limit []byte, bytes uint64) error {
	return nil
}
func (p *countingSnapPeer) RequestByteCodes(id uint64, hashes []common.Hash, bytes uint64) error {
	return nil
}
func (p *countingSnapPeer) RequestTrieNodes(id uint64, root common.Hash, paths []snap.TrieNodePathSet, bytes uint64) error {
	return nil
}
func (p *countingSnapPeer) RequestHvmLightState(id uint64, tip common.Hash) error {
	p.hvmRequests.Add(1)
	return nil
}

// While the wait is pending (no completion), it must periodically re-broadcast the hVM light-state
// request — the mechanism that defeats a malicious/unreachable first responder. Shortening
// hvmLightStateReissueInterval makes the re-issue observable: a registered peer should receive more
// than the single initial request within a few intervals.
func TestHVMLightStateSyncReissuesWhilePending(t *testing.T) {
	prev := hvmLightStateReissueInterval
	hvmLightStateReissueInterval = 20 * time.Millisecond
	defer func() { hvmLightStateReissueInterval = prev }()

	d, _ := newHvmWaitDownloader(t)
	peer := &countingSnapPeer{id: "p"}
	require.NoError(t, d.SnapSyncer.Register(peer))

	errc := make(chan error, 1)
	go func() { errc <- d.hVMLightStateSyncWithAllPeers(common.Hash{}) }()

	// Allow the initial request plus several re-issue ticks.
	time.Sleep(150 * time.Millisecond)
	close(d.cancelCh)
	require.ErrorIs(t, <-errc, errCanceled)

	// 1 initial broadcast + >=1 re-issue. (~7 expected over 150ms at 20ms.)
	require.Greater(t, peer.hvmRequests.Load(), int64(1),
		"a pending wait must re-broadcast the hVM light-state request, not just send once")
}
