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

package core

// The Bitcoin-Attributes-Deposited build cache is keyed on btcAttrCacheKey{evmTip, lightTip, fullTip}. The
// end-to-end builder (getBitcoinAttributesForNextBlock) needs a live vm.TBCFullNode and is out of unit-test
// scope, so these tests pin the liveness-relevant property of the fix directly (this is the sequencer build
// path — a cache bug halts the local sequencer; it is not a consensus-safety/split concern, since
// validators re-derive the BtcAttr independently): the cache is invalidated by a change in any of the three
// dimensions, in particular the full-node BTC view (fullTip), which the original EVM-tip-only key ignored,
// causing a stale BtcAttr to be re-served after a full-node sync/reorg and pinning the sequencer into a
// permanent self-halt.

import (
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
)

func TestBtcAttrCacheKey(t *testing.T) {
	evm := common.HexToHash("0x11")
	light := chainhash.Hash{0xaa}
	full := chainhash.Hash{0xbb}
	base := btcAttrCacheKey{evmTip: evm, lightTip: light, fullTip: full}

	// All three identical -> cache hit.
	require.Equal(t, base, btcAttrCacheKey{evmTip: evm, lightTip: light, fullTip: full},
		"identical (evmTip, lightTip, fullTip) must compare equal (cache hit)")

	// EVM tip differs -> miss (the original key already covered this).
	require.NotEqual(t, base, btcAttrCacheKey{evmTip: common.HexToHash("0x22"), lightTip: light, fullTip: full},
		"a new EVM tip must invalidate the cache")

	// Lightweight BTC view differs -> miss.
	require.NotEqual(t, base, btcAttrCacheKey{evmTip: evm, lightTip: chainhash.Hash{0xcc}, fullTip: full},
		"a lightweight-TBC view change must invalidate the cache")

	// Full-node BTC view differs -> miss. This is the case the original EVM-tip-only key missed: a
	// full-node sync/reorg changes fullTip while the EVM tip is unchanged; re-serving the stale BtcAttr here
	// is the permanent self-inflicted sequencer halt the fix removes.
	require.NotEqual(t, base, btcAttrCacheKey{evmTip: evm, lightTip: light, fullTip: chainhash.Hash{0xdd}},
		"a full-node BTC view change (sync/reorg) must invalidate the cache")
}

// TestBtcAttrCacheRoundTrip pins the inline cache check and write of getBitcoinAttributesForNextBlock via
// the cachedBtcAttrFor / storeBtcAttrCache helpers it calls (the function body itself needs a full node).
// Catches: a write that drops a key dimension, a check that matches the wrong key, and a missing
// non-nil-entry guard.
func TestBtcAttrCacheRoundTrip(t *testing.T) {
	bc := &BlockChain{}
	key := btcAttrCacheKey{
		evmTip:   common.HexToHash("0x11"),
		lightTip: chainhash.Hash{0xaa},
		fullTip:  chainhash.Hash{0xbb},
	}
	tx := &types.BtcAttributesDepositedTx{}

	// Empty cache (nil entry) -> always a miss, even for a key that happens to equal the zero key.
	require.Nil(t, bc.cachedBtcAttrFor(key), "an unwritten cache must miss")
	require.Nil(t, bc.cachedBtcAttrFor(btcAttrCacheKey{}), "the zero key must miss while the entry is nil (the guard)")

	bc.storeBtcAttrCache(key, tx)

	// Exact-key match -> the stored entry.
	require.Same(t, tx, bc.cachedBtcAttrFor(key), "an exact (evmTip, lightTip, fullTip) match must return the stored tx")

	// Any single dimension differing -> miss (so a BTC-view change forces a rebuild).
	require.Nil(t, bc.cachedBtcAttrFor(btcAttrCacheKey{evmTip: common.HexToHash("0x22"), lightTip: key.lightTip, fullTip: key.fullTip}), "a different EVM tip must miss")
	require.Nil(t, bc.cachedBtcAttrFor(btcAttrCacheKey{evmTip: key.evmTip, lightTip: chainhash.Hash{0xcc}, fullTip: key.fullTip}), "a different lightweight tip must miss")
	require.Nil(t, bc.cachedBtcAttrFor(btcAttrCacheKey{evmTip: key.evmTip, lightTip: key.lightTip, fullTip: chainhash.Hash{0xdd}}), "a different full-node tip must miss")
}
