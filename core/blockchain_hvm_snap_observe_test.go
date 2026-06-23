// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// Licensed under the GNU LGPL v3. See the go-ethereum LICENSE file.

package core

// Integration coverage for SnapSyncHvm's observe-only verdict-dispatch composition. The consensus-relevant
// part — the contextual-difficulty check (PoW + above-floor suffix split + contextual validate + verdict
// classification) — lives in observeSnapBtcDiff, which takes any vm.BTCHeaderLookup. This test drives it
// against a real regtest lightweight TBC node (the same store SnapSyncHvm reconstructs into).
//
// SnapSyncHvm's full end-to-end path needs a live, block-indexed full TBC node, so these parts are not covered
// here: the block-availability wait/refetch loop, the walk-back that builds headersToAdd, and
// updateFullTBCToLightweight. SnapSyncHvm's AddExternalHeaders-into-the-lightweight-node + canonical-tip
// section is not full-node-bound and is covered by TestHvmApplyPathRollsBackOnWrongCanonicalTipRegtest.

import (
	"testing"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/stretchr/testify/require"
)

// buildAndSeedRegtestChain mines `total` contiguous regtest headers off `genesis` and adds them to the
// lightweight node (so they are resolvable as the snap base's ancestry). The header at badIdx (if >= 0) is
// mined with badBits instead of regtestPowBits — a correct-PoW-but-wrong-difficulty header (regtest is
// PoWNoRetargeting, so the contextual rule expects regtestPowBits). Returns the header list (heights 1..N,
// since regtest genesis is height 0 / GenesisHeightOffset 0 in this harness).
func buildAndSeedRegtestChain(t *testing.T, chain *BlockChain, genesis *wire.BlockHeader, total, badIdx int, badBits uint32) []*wire.BlockHeader {
	t.Helper()
	hdrs := make([]*wire.BlockHeader, 0, total)
	prev := genesis
	for i := 0; i < total; i++ {
		var h *wire.BlockHeader
		if i == badIdx {
			h = mineRegtestChildBits(t, prev, badBits, uint32(i)*7+1)
		} else {
			h = mineRegtestChild(t, prev, uint32(i)*7+1)
		}
		hdrs = append(hdrs, h)
		prev = h
	}
	for start := 0; start < len(hdrs); start += 1000 {
		end := start + 1000
		if end > len(hdrs) {
			end = len(hdrs)
		}
		last := hdrs[end-1].BlockHash()
		_, _, _, _, err := chain.tbcHeaderNode.AddExternalHeaders(chain.ctx, &wire.MsgHeaders{Headers: hdrs[start:end]}, last[:])
		require.NoError(t, err, "seeding regtest chain chunk [%d:%d]", start, end)
	}
	return hdrs
}

// TestObserveSnapBtcDiffDispatch drives the extracted observe-only contextual-difficulty composition against a real
// regtest lightweight TBC node — the verdict-dispatch SnapSyncHvm runs on its reconstructed base. Pins: a
// clean base reports clean (no alert), a wrong-difficulty above-floor header is snapObsReject (alertable
// but the function still returns, never halts), a forged-PoW header sets powFailed, an unknown network
// skips the contextual check, and the enforce/defer split is exercised (deferred near-floor headers).
func TestObserveSnapBtcDiffDispatch(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: mines + seeds >floorClearance regtest headers into a real lightweight TBC node")
	}
	// regtest enforce floor = btcSnapEnforceFloor(0, floorClearance(regtest)). The chain must clear it so a
	// suffix is enforceable while near-floor headers are deferred.
	clearance, err := vm.BTCFloorClearanceForNetwork("localnet")
	require.NoError(t, err)
	enforceFloor := btcSnapEnforceFloor(0, clearance)
	total := int(enforceFloor) + 16 // a handful of enforceable headers above the floor + the deferred band below

	t.Run("clean base -> snapObsClean, no alert, enforce/defer split", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		hdrs := buildAndSeedRegtestChain(t, chain, genesis, total, -1, 0)

		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, hdrs)
		require.False(t, obs.powFailed, "a fully-mined base must not flag PoW")
		require.NoError(t, obs.clearanceErr)
		require.NoError(t, obs.firstHeightErr)
		require.False(t, obs.firstHeightMismatch, "headers[0] is genesis+1 (height 1 == offset 0 + 1)")
		require.True(t, obs.contextualRan, "an above-floor suffix must be enforced")
		require.Equal(t, snapObsClean, obs.ctxObservation, "a correct-difficulty regtest base is contextually clean")
		require.Greater(t, obs.enforcedCount, 0, "some headers are above the enforce floor")
		require.Greater(t, obs.deferredCount, 0, "the near-floor band is deferred, not checked")
		require.Equal(t, len(hdrs), obs.enforcedCount+obs.deferredCount, "every header is either enforced or deferred")
	})

	t.Run("all headers below enforce floor -> benign empty suffix, NOT a skip", func(t *testing.T) {
		// A short base entirely within the deferred near-floor band: enforceable suffix is empty, so contextualRan
		// is false WITHOUT any skip error (clearanceErr/firstHeightErr nil). The migration observe switch's
		// benign-empty arm keys on exactly this shape, distinct from a genuine skipped check. If
		// clearanceErr/firstHeightErr were set here the migration would misroute to the misleading SKIPPED warn.
		belowFloor := int(enforceFloor) - 1
		if belowFloor < 1 {
			t.Skip("enforce floor too low on this network to construct an all-below-floor base")
		}
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		hdrs := buildAndSeedRegtestChain(t, chain, genesis, belowFloor, -1, 0)
		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, hdrs)
		require.NoError(t, obs.clearanceErr, "an all-below-floor base is NOT a skipped check (clearance resolved)")
		require.NoError(t, obs.firstHeightErr, "the first header is resolvable")
		require.False(t, obs.contextualRan, "no above-floor suffix -> the contextual validator does not run")
		require.Equal(t, 0, obs.enforcedCount, "nothing is enforceable below the floor")
		require.Equal(t, len(hdrs), obs.deferredCount, "every header is deferred (the benign empty-suffix case)")
	})

	t.Run("walk not starting at genesis+1 -> firstHeightMismatch (the TRUE direction)", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		hdrs := buildAndSeedRegtestChain(t, chain, genesis, total, -1, 0)
		// Drop headers[0] so the slice now starts at the height-2 header (still resolvable in the lightweight node,
		// so firstHeightErr stays nil). firstHeight (2) != genesisOffset(0)+1, so the genesis+1 tripwire must fire.
		// This exercises the TRUE direction of the walk-start tripwire on both the snap and migration bulk-load paths.
		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, hdrs[1:])
		require.NoError(t, obs.firstHeightErr, "the first header (height 2) is resolvable, so the height read must succeed")
		require.True(t, obs.firstHeightMismatch, "a walk starting at height 2 (not genesisOffset+1==1) must set firstHeightMismatch")
		require.Equal(t, uint64(2), obs.firstHeight, "the observed first height is 2")
	})

	t.Run("wrong-difficulty header above floor -> snapObsReject (alertable, NEVER halts)", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		// A wrong (slightly harder) difficulty header well above the enforce floor: PoW still passes (target
		// barely below PowLimit -> minable), but Bits != regtestPowBits -> ErrUnexpectedDifficulty.
		badIdx := int(enforceFloor) + 4
		hdrs := buildAndSeedRegtestChain(t, chain, genesis, total, badIdx, 0x207ffffe)

		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, hdrs)
		require.False(t, obs.powFailed, "the wrong-difficulty header is still validly mined (PoW must pass) — isolates the contextual reject")
		require.True(t, obs.contextualRan)
		require.Equal(t, snapObsReject, obs.ctxObservation, "a wrong-difficulty above-floor header must be the alertable reject verdict")
		// The point of observe-only: it RETURNS (no panic / no halt). Reaching here is the assertion.
	})

	t.Run("PoW-failing header -> powFailed set (does not halt)", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		// An unmined header (correct Bits, but a nonce whose hash exceeds the target). Passed as a one-element
		// base; headers[0] is not in the lookup so the contextual check is skipped via firstHeightErr, which
		// isolates the PoW arm (the PoW check runs over the passed list, before the lookup).
		target := blockchain.CompactToBig(regtestPowBits)
		forged := &wire.BlockHeader{Version: 4, PrevBlock: genesis.BlockHash(), Bits: regtestPowBits, Nonce: 0}
		found := false
		for i := uint32(1); i < 1<<20; i++ {
			forged.Nonce = i
			hash := forged.BlockHash()
			if blockchain.HashToBig(&hash).Cmp(target) > 0 {
				found = true
				break
			}
		}
		require.True(t, found, "must find a PoW-failing nonce")

		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "localnet", 0, []*wire.BlockHeader{forged})
		require.True(t, obs.powFailed, "an unmined header must flag the PoW observation")
		require.Error(t, obs.powErr)
		// Pin the firstHeightErr SKIP arm distinctly from the PoW arm: the forged header is not in the lookup,
		// so the contextual stage is skipped via firstHeightErr (NOT clearanceErr — localnet resolves params).
		require.Error(t, obs.firstHeightErr, "an absent first header must skip the contextual check via firstHeightErr")
		require.False(t, obs.contextualRan, "the contextual validator must not run when the first header is unresolvable")
		require.NoError(t, obs.clearanceErr, "localnet has params, so the SKIP here is firstHeightErr, not clearanceErr")
	})

	t.Run("unknown network -> contextual check skipped (clearanceErr), no PoW alert", func(t *testing.T) {
		chain, genesis := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
		h := mineRegtestChild(t, genesis, 1)
		obs := observeSnapBtcDiff(chain.ctx, chain.tbcHeaderNode, "nonsense-network", 0, []*wire.BlockHeader{h})
		require.False(t, obs.powFailed, "PoW over an unknown network returns the skip sentinel, not a failure")
		require.Error(t, obs.clearanceErr, "an unknown network has no chaincfg params -> contextual observation skipped")
		require.False(t, obs.contextualRan)
	})
}
