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

// Direct tests of the initHvmHeaderNode wrapper policy (the verdict->action mapping), the
// classifier's multi-checkpoint loop, and the checkpoint map's well-formedness.
// TestClassifyHvmGenesisPairing pins the pure classifier verdict; these pin what the wrapper does with it:
// Canonical->proceed, localnet-Custom->warn+proceed (in-process), and Mismatch / non-localnet-Custom->
// refuse-to-start (subprocess, because log.Crit calls os.Exit).

import (
	"context"
	"math/big"
	"os"
	"os/exec"
	"strings"
	"testing"

	"github.com/btcsuite/btcd/wire"
	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"

	"github.com/hemilabs/heminetwork/service/tbc"
)

// newHvmInitTestChain builds a real BlockChain with hVM Phase 0 enabled but WITHOUT attaching the lightweight
// TBC node, so a test can drive initHvmHeaderNode with an arbitrary (network, genesis, offset) config.
func newHvmInitTestChain(t *testing.T) *BlockChain {
	t.Helper()
	hvm0Time := btcDiffTestHvm0Time
	cfg := *params.TestChainConfig
	cfg.Hvm0Time = &hvm0Time
	gspec := &Genesis{Config: &cfg, BaseFee: big.NewInt(params.InitialBaseFee), Alloc: types.GenesisAlloc{}}
	chain, err := NewBlockChain(rawdb.NewMemoryDatabase(), gspec, nil, ethash.NewFaker(), DefaultConfig(), nil, nil, context.Background())
	require.NoError(t, err)
	t.Cleanup(chain.Stop)
	return chain
}

// hvmInitLightTBCConfig builds an ExternalHeaderMode TBC config mirroring eth/backend.go for an arbitrary
// network / effective-genesis / offset, so the genesis-pairing guard's policy arms can be exercised
// independently of the canonical harness.
func hvmInitLightTBCConfig(t *testing.T, network string, genesis *wire.BlockHeader, offset uint64) *tbc.Config {
	t.Helper()
	tbcCfg := tbc.NewDefaultConfig()
	tbcCfg.ExternalHeaderMode = true
	tbcCfg.EffectiveGenesisBlock = genesis
	tbcCfg.GenesisHeightOffset = offset
	tbcCfg.LevelDBHome = t.TempDir()
	tbcCfg.BlockheaderCacheSize = "0"
	tbcCfg.BlockCacheSize = "0"
	tbcCfg.AutoIndex = false
	tbcCfg.BlockSanity = true
	tbcCfg.MaxCachedTxs = 0
	tbcCfg.MempoolEnabled = false
	tbcCfg.Network = network
	return tbcCfg
}

// TestInitHvmHeaderNodeLocalnetCustomProceeds pins the localnet-Custom warn-and-proceed carve-out — the
// only reachable non-exit wrapper arm, and the most dangerous to get wrong. A Custom pairing (uncheckpointed
// network) is refused on every network except localnet, where it warns and proceeds. Without this,
// inverting `if config.Network != "localnet"` to `== "localnet"` (or deleting the carve-out) would brick
// localnet dev nodes while letting every real non-canonical network boot — a fail-open — and the suite
// would stay green.
func TestInitHvmHeaderNodeLocalnetCustomProceeds(t *testing.T) {
	chain := newHvmInitTestChain(t)
	// localnet has no checkpoint -> a self-consistent custom pair classifies Custom.
	cfg := hvmInitLightTBCConfig(t, "localnet", mustEffectiveGenesisHeader(t), 0)
	require.Equal(t, hvmGenesisPairingCustom,
		classifyHvmGenesisPairing(cfg.Network, cfg.GenesisHeightOffset, cfg.EffectiveGenesisBlock.BlockHash().String()),
		"precondition: a localnet custom pair must classify Custom")

	chain.initHvmHeaderNode(cfg) // must warn and proceed, not os.Exit
	t.Cleanup(func() { _ = chain.tbcHeaderNode.ExternalHeaderTearDown() })

	require.True(t, chain.hvmEnabled, "localnet-Custom must warn-and-proceed (hVM enabled), not refuse")
	require.NotNil(t, chain.tbcHeaderNode, "the lightweight node must have been built")
	_, _, err := chain.tbcHeaderNode.BlockHeaderBest(chain.ctx)
	require.NoError(t, err, "the node must be queryable after proceeding")
}

// hvmInitCritChildEnv selects which refuse-to-start config the subprocess child builds.
const hvmInitCritChildEnv = "HVM_INIT_CRIT_CHILD_MODE"

// TestInitHvmHeaderNodeRefusesDesyncedChild is the subprocess child for TestInitHvmHeaderNodeRefuses. It is
// a no-op unless invoked with hvmInitCritChildEnv set; the parent re-execs the test binary with that env var so
// it can observe the os.Exit(1) from log.Crit (which cannot be caught in-process).
func TestInitHvmHeaderNodeRefusesDesyncedChild(t *testing.T) {
	mode := os.Getenv(hvmInitCritChildEnv)
	if mode == "" {
		t.Skip("child-only: driven by TestInitHvmHeaderNodeRefuses via subprocess re-exec")
	}
	// The root logger defaults to DiscardHandler in a bare test binary, so log.Crit would emit nothing
	// before os.Exit(1). Route it to stderr so the parent can assert on the genesis-pairing guard's refuse
	// message (not just the exit code), distinguishing it from any other log.Crit site that also exits non-zero.
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	chain := newHvmInitTestChain(t)
	var cfg *tbc.Config
	switch mode {
	case "mismatch":
		// testnet3, canonical header, wrong offset -> half-match -> Mismatch -> refuse (any network).
		cfg = hvmInitLightTBCConfig(t, "testnet3", mustEffectiveGenesisHeader(t), 999999)
	case "custom-mainnet":
		// mainnet (uncheckpointed) with the exact canonical pair -> Custom -> non-localnet -> refuse.
		cfg = hvmInitLightTBCConfig(t, "mainnet", mustEffectiveGenesisHeader(t), canonicalHvmGenesisHeight)
	case "custom-testnet3":
		// testnet3 (checkpointed/enforced) with a non-canonical pair: perturb the canonical header so its
		// hash misses, and use offset 0 so the height misses too -> the pair touches neither checkpoint field
		// -> Custom -> non-localnet -> refuse. Proves the Custom-refuse arm fires on the production network
		// (testnet3), not only the never-deployed mainnet. The correct code crits at the pairing guard before
		// tbc setup, so the perturbed header's broken PoW is never reached.
		h := mustEffectiveGenesisHeader(t)
		h.Nonce++
		cfg = hvmInitLightTBCConfig(t, "testnet3", h, 0)
	case "chaincfg-unknown":
		// chaincfg<->genesis lockstep: a network with a pinned checkpoint (so the pairing guard classifies it
		// Canonical and passes) but no btcd chaincfg params must refuse at startup, not boot and then
		// per-block ErrCorrupt-wedge. Inject a checkpoint for a chaincfg-unknown network so the pairing guard
		// passes, reaching the lockstep crit. (This subprocess has a fresh package var; the injection is local.)
		const noChaincfgNet = "zzz-no-chaincfg-params"
		hh := mustEffectiveGenesisHeader(t)
		hvmGenesisCheckpoints[noChaincfgNet] = []btcGenesisCheckpoint{{height: canonicalHvmGenesisHeight, hash: hh.BlockHash().String()}}
		require.Equal(t, hvmGenesisPairingCanonical,
			classifyHvmGenesisPairing(noChaincfgNet, canonicalHvmGenesisHeight, hh.BlockHash().String()),
			"precondition: the injected checkpoint must make this network classify Canonical so the pairing guard passes to the lockstep check")
		cfg = hvmInitLightTBCConfig(t, noChaincfgNet, hh, canonicalHvmGenesisHeight)
	default:
		t.Fatalf("unknown child mode %q", mode)
	}
	chain.initHvmHeaderNode(cfg)
	// initHvmHeaderNode must log.Crit -> os.Exit(1) before returning. Reaching here means the refuse arm
	// did not fire; exit 0 so the parent's non-zero-exit assertion fails loudly.
	t.Fatalf("initHvmHeaderNode returned for mode %q; expected refuse-to-start (log.Crit)", mode)
}

// TestInitHvmHeaderNodeRefuses drives the two refuse-to-start wrapper arms (Mismatch on any network;
// non-localnet Custom) via subprocess re-exec, asserting both a non-zero exit and a pairing-guard-specific
// stderr substring — a bare exit!=0 is vacuity-prone (initHvmHeaderNode has other log.Crit sites that also
// exit non-zero for the wrong reason). Mutants killed: downgrading either log.Crit to log.Warn (node boots
// on a desynced/non-canonical pair), swapping the Mismatch/Custom bodies, or inverting the
// EffectiveGenesisBlock!=nil guard — none observable in-process, all survive the classifier-only test.
func TestInitHvmHeaderNodeRefuses(t *testing.T) {
	cases := []struct {
		mode       string
		wantSub    string // a substring UNIQUE to the intended refuse arm's crit message
		wantNotSub string // the OTHER refuse arm's unique substring — must be ABSENT (proves the right arm)
	}{
		{"mismatch", "DESYNCED", "NOT a pinned canonical"},
		{"custom-mainnet", "NOT a pinned canonical", "DESYNCED"},
		{"custom-testnet3", "NOT a pinned canonical", "DESYNCED"},
		{"chaincfg-unknown", "no btcd chaincfg params", "DESYNCED"},
	}
	for i, tc := range cases {
		// The refuse arms are the pairing guard's core protection (verdict->refuse). Keep the first on the
		// fast lane: under -short, run only the Mismatch case and skip the rest. The child crits before
		// tbc.NewServer, so it opens no leveldb — each spawn is ~0.05s, cheaper than the ungated
		// localnet-proceed test which builds a real node.
		if testing.Short() && i > 0 {
			continue
		}
		t.Run(tc.mode, func(t *testing.T) {
			cmd := exec.Command(os.Args[0], "-test.run=^TestInitHvmHeaderNodeRefusesDesyncedChild$", "-test.v")
			cmd.Env = append(os.Environ(), hvmInitCritChildEnv+"="+tc.mode)
			out, err := cmd.CombinedOutput()

			var ee *exec.ExitError
			require.ErrorAs(t, err, &ee, "child must exit non-zero (refuse-to-start), got output:\n%s", string(out))
			require.False(t, ee.Success(), "child must report failure")
			require.Contains(t, string(out), tc.wantSub,
				"child stderr must carry the pairing guard's refuse reason for mode %q", tc.mode)
			require.NotContains(t, string(out), tc.wantNotSub,
				"the OTHER refuse arm must not have fired for mode %q (arms must be discriminable)", tc.mode)
			// Negative control: a generic crash would not carry the pairing guard's refuse vocabulary.
			require.Contains(t, string(out), "Refusing to start",
				"the exit must be the pairing guard's refuse-to-start, not another log.Crit site")
			// Kills the log.Crit -> log.Warn downgrade mutant. A downgrade keeps the same message text (so
			// "Refusing to start"/"DESYNCED" still appear, now from the warn) and lets execution fall through
			// to the child's post-call t.Fatalf ("initHvmHeaderNode returned for mode"), which also exits
			// non-zero — so without this assertion the test passes though the node did not refuse. A genuine
			// log.Crit os.Exits before that marker, so the marker must be absent.
			require.NotContains(t, string(out), "initHvmHeaderNode returned for mode",
				"the pairing guard must REFUSE (os.Exit via log.Crit) before returning; the returned-marker means a refuse "+
					"arm was downgraded to log.Warn for mode %q", tc.mode)
			// Also kills the downgrade mutant for the chaincfg-lockstep 'chaincfg-unknown' arm: there the
			// witness network is rejected by both layers, so a Crit->Warn downgrade of the lockstep guard lets
			// execution fall through to tbc.NewServer, which crit-exits on the same unknown network — masking
			// the downgrade from the exit-code + "returned for mode" marker checks above (the marker is never
			// printed because tbc.NewServer crits first). A genuine refusal (pairing guard or lockstep crit)
			// happens before tbc.NewServer, so its "unable to create new TBC server" message must be absent;
			// if present, a refuse arm was downgraded and execution reached tbc.NewServer.
			require.NotContains(t, string(out), "unable to create new TBC server",
				"a refuse arm must os.Exit BEFORE tbc.NewServer for mode %q; the TBC-create crit means it was "+
					"downgraded to log.Warn and fell through", tc.mode)
		})
	}
}

// TestClassifyHvmGenesisPairingMultiCheckpoint exercises the classifier's loop over a network with more
// than one checkpoint — invisible in production today (every network has exactly one), but the ordering and
// the Mismatch accumulator are real code. Injects a synthetic 2-entry network with defer-restore.
func TestClassifyHvmGenesisPairingMultiCheckpoint(t *testing.T) {
	// This test mutates the package global hvmGenesisCheckpoints (with defer-restore). Safe only because Go
	// runs a package's tests sequentially and no pairing-guard test calls t.Parallel(). Do not add
	// t.Parallel() here or to any test that reads hvmGenesisCheckpoints, or this becomes a data race.
	const net = "hvminitmultitest"
	require.NotContains(t, hvmGenesisCheckpoints, net, "precondition: synthetic test network must not pre-exist")
	hashA := strings.Repeat("a", 64)
	hashB := strings.Repeat("b", 64)

	t.Run("canonical-at-index1-wins-over-latched-mismatch", func(t *testing.T) {
		// index0 half-matches the candidate (same height 200, different hash) -> mismatch=true; index1 fully
		// matches (200, B) -> must return Canonical immediately. A mutant that moves the
		// `if mismatch { return Mismatch }` check inside the loop, or defers the Canonical return behind a
		// flag, would wrongly return Mismatch here.
		hvmGenesisCheckpoints[net] = []btcGenesisCheckpoint{{height: 200, hash: hashA}, {height: 200, hash: hashB}}
		defer delete(hvmGenesisCheckpoints, net)
		require.Equal(t, hvmGenesisPairingCanonical, classifyHvmGenesisPairing(net, 200, hashB))
	})

	t.Run("latched-mismatch-survives-a-full-miss", func(t *testing.T) {
		// index0 half-matches (height 200) -> mismatch=true; index1 fully misses (999, different hash) ->
		// contributes nothing. After the loop the latched mismatch must yield Mismatch. A mutant turning the
		// latch `if hEq != sEq { mismatch = true }` into `mismatch = (hEq != sEq)` would reset it to false at
		// index1 and wrongly return Custom.
		hvmGenesisCheckpoints[net] = []btcGenesisCheckpoint{{height: 200, hash: hashA}, {height: 999, hash: hashB}}
		defer delete(hvmGenesisCheckpoints, net)
		require.Equal(t, hvmGenesisPairingMismatch, classifyHvmGenesisPairing(net, 200, "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"))
	})
}

// TestHvmGenesisCheckpointsWellFormed is the map-domain meta-test: a forward tripwire so a future mainnet
// checkpoint (or a typo'd key / malformed hash / duplicate entry) cannot slip in unnoticed. The
// checkpoint-inspection test only inspects testnet3[0]; the classifier test only checks NotEmpty/Empty;
// nothing else iterates the whole map.
func TestHvmGenesisCheckpointsWellFormed(t *testing.T) {
	allowed := map[string]bool{"testnet3": true, "upgradetest": true}
	require.Len(t, hvmGenesisCheckpoints, len(allowed), "only testnet3 and upgradetest are pinned today")
	for net, cps := range hvmGenesisCheckpoints {
		require.Truef(t, allowed[net], "unexpected checkpoint network key %q (a typo like 'mainet', or a premature mainnet add that needs its own lockstep test?)", net)
		require.Lenf(t, cps, 1, "network %q: exactly one checkpoint expected today", net)
		for _, cp := range cps {
			require.Greaterf(t, cp.height, uint64(0), "network %q: checkpoint height must be > 0", net)
			require.Regexpf(t, "^[0-9a-f]{64}$", cp.hash, "network %q: checkpoint hash must be 64-char lowercase hex with no 0x prefix", net)
		}
	}
	require.NotContains(t, hvmGenesisCheckpoints, "mainnet", "a mainnet checkpoint needs its own ethconfig.Defaults lockstep test (see eth/backend_hvm_genesis_test.go)")
	require.NotContains(t, hvmGenesisCheckpoints, "localnet", "localnet is intentionally unpinned (Custom -> warn)")
}

// TestHvmGenesisCheckpointChaincfgLockstep pins the cross-package weld between the genesis-pairing map
// (core: hvmGenesisCheckpoints, network -> checkpoint) and the validator-params map (core/vm:
// paramsForNetwork, network -> btcd chaincfg.Params). Every network with a pinned checkpoint must also
// resolve to chaincfg params, else a node boots past the genesis-pairing guard (Canonical) but cannot
// parameterize contextual-difficulty validation -> every block maps to ErrCorruptHVMHeaderOnlyModeState -> a per-block restore
// wedge. This is the CI tripwire for that drift (the same invariant initHvmHeaderNode also enforces at
// startup via the chaincfg-lockstep runtime crit, exercised by the "chaincfg-unknown" subprocess case
// above). vm.SupportsBTCNetwork resolves iff the network has chaincfg params, so it is the probe.
func TestHvmGenesisCheckpointChaincfgLockstep(t *testing.T) {
	require.NotEmpty(t, hvmGenesisCheckpoints)
	for net := range hvmGenesisCheckpoints {
		require.Truef(t, vm.SupportsBTCNetwork(net),
			"checkpointed network %q must have btcd chaincfg params (chaincfg<->genesis lockstep)", net)
	}
	// The production consensus node's hardcoded network (eth/backend.go buildHvmHeaderNodeConfig) must be
	// both checkpointed and chaincfg-resolvable. Pinned so a future change to either map for testnet3 is
	// caught. (upgradetest is the TBC alias, covered by the loop above.)
	require.True(t, vm.SupportsBTCNetwork("testnet3"), "the shipped consensus network (testnet3) must resolve to chaincfg params")
	require.Contains(t, hvmGenesisCheckpoints, "testnet3", "the shipped consensus network (testnet3) must be checkpointed")
	// The dev network localnet, which the pairing guard lets boot Custom, must also be chaincfg-resolvable
	// (else a localnet dev node would boot then wedge).
	require.True(t, vm.SupportsBTCNetwork("localnet"), "localnet must resolve to chaincfg params even though it is intentionally uncheckpointed")
	// Negative control: a network with neither checkpoint nor chaincfg params is what the lockstep forbids
	// (and what the chaincfg-lockstep startup crit relies on rejecting).
	require.False(t, vm.SupportsBTCNetwork("zzz-no-chaincfg-params"), "an unknown network must fail the chaincfg probe")
}
