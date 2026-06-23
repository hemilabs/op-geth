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
	"path/filepath"
	"strings"
	"testing"

	"github.com/btcsuite/btcd/chaincfg"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/eth/ethconfig"
	"github.com/hemilabs/heminetwork/cmd/btctool/bdf"
	"github.com/mitchellh/go-homedir"
)

// TestEthconfigHvmDefaultsMatchCanonicalCheckpoint guards lockstep between the compiled hVM
// effective-genesis default (ethconfig.Defaults.HvmGenesisHeader/HvmGenesisHeight) and the pinned
// consensus checkpoint (core.hvmGenesisCheckpoints). The in-core binding test
// (TestHvmGenesisCheckpointMatchesCanonicalHeader) only asserts the checkpoint equals a test-local hex
// copy, so re-pinning ethconfig.Defaults without updating the checkpoint stays green yet bricks every
// enforced node at startup (initHvmHeaderNode classifies the default as Mismatch/Custom and log.Crit's).
// This lives in package eth, the only place importing both ethconfig and core; ethconfig imports core,
// so the comparison cannot be made from inside core. It reproduces the production decode path from
// eth/backend.go: bdf.Hex2Header over the default header, GenesisHeightOffset = HvmGenesisHeight, network
// testnet3. On failure, update core.hvmGenesisCheckpoints to match ethconfig.Defaults before shipping.
func TestEthconfigHvmDefaultsMatchCanonicalCheckpoint(t *testing.T) {
	// The consensus header node's network DEFAULTS to testnet3 in eth/backend.go (buildHvmHeaderNodeConfig sets
	// tbcCfg.Network = config.TBCNetwork, falling back to ethconfig.DefaultTBCNetwork when unset). Keep this
	// identical to that default; if a non-testnet3 network ships its own default genesis, extend this test to
	// cover every reachable (network, default) pair.
	const productionNetwork = "testnet3"

	hdr, err := bdf.Hex2Header(ethconfig.Defaults.HvmGenesisHeader)
	if err != nil {
		t.Fatalf("ethconfig.Defaults.HvmGenesisHeader does not decode via the production bdf.Hex2Header path: %v", err)
	}
	gotHash := hdr.BlockHash().String()

	// Absolute anchors. IsCanonicalHvmGenesisPairing only checks the default is internally consistent with
	// the checkpoint, so a coordinated re-pin (both ethconfig.Defaults and the checkpoint moved to a new
	// pair) would still pass it. Pin the known-good values here; also self-contained for a path-scoped CI
	// lane that runs `go test ./eth/...` without ./core/... (where the in-core binding test does not run).
	const knownGoodHash = "000000000000000096c98151accc5ee217d7cc4ff1e59a3d91e4c9365c4ea144"
	const knownGoodHeight = uint64(3522419)
	if gotHash != knownGoodHash {
		t.Fatalf("ethconfig.Defaults.HvmGenesisHeader decodes to %s, want the known-good testnet3 hVM "+
			"effective-genesis hash %s — a coordinated re-pin to a different header must be deliberate.", gotHash, knownGoodHash)
	}
	if ethconfig.Defaults.HvmGenesisHeight != knownGoodHeight {
		t.Fatalf("ethconfig.Defaults.HvmGenesisHeight = %d, want %d.", ethconfig.Defaults.HvmGenesisHeight, knownGoodHeight)
	}

	// Retarget-residue anchor: the height's residue mod BlocksPerRetarget is consensus-load-bearing (it
	// fixes where the (parentHeight+1) % BlocksPerRetarget retarget boundary lands), so a re-pin to a
	// height with a different residue mod BlocksPerRetarget mis-aligns every boundary network-wide
	// even if the (height,header) pair is internally consistent. Derive the divisor from chaincfg, not 2016.
	p := chaincfg.TestNet3Params
	blocksPerRetarget := uint64(p.TargetTimespan / p.TargetTimePerBlock)
	const knownGoodResidue = uint64(467) // 3522419 % 2016
	if got := ethconfig.Defaults.HvmGenesisHeight % blocksPerRetarget; got != knownGoodResidue {
		t.Fatalf("ethconfig.Defaults.HvmGenesisHeight %% BlocksPerRetarget(%d) = %d, want %d; a height re-pin "+
			"that changes this residue mis-aligns the contextual-difficulty retarget boundary on every node.",
			blocksPerRetarget, got, knownGoodResidue)
	}

	if !core.IsCanonicalHvmGenesisPairing(productionNetwork, ethconfig.Defaults.HvmGenesisHeight, gotHash) {
		t.Fatalf("hVM genesis DRIFT: ethconfig.Defaults (height=%d, header-hash=%s) is NOT a pinned canonical "+
			"checkpoint for network %q in core.hvmGenesisCheckpoints. Re-pinning the default without updating the "+
			"checkpoint bricks every enforced node at startup (initHvmHeaderNode crits) while the in-core binding "+
			"test stays green. Update core.hvmGenesisCheckpoints[%q] to {height: %d, hash: %q}.",
			ethconfig.Defaults.HvmGenesisHeight, gotHash, productionNetwork,
			productionNetwork, ethconfig.Defaults.HvmGenesisHeight, gotHash)
	}

	// upgradetest runs in lockstep with testnet3 (same compiled default); guard it too so a default change
	// that updates only the testnet3 checkpoint cannot silently brick upgradetest.
	if !core.IsCanonicalHvmGenesisPairing("upgradetest", ethconfig.Defaults.HvmGenesisHeight, gotHash) {
		t.Fatalf("hVM genesis DRIFT: ethconfig.Defaults (height=%d, header-hash=%s) is NOT canonical for "+
			"network \"upgradetest\"; it must track testnet3 in core.hvmGenesisCheckpoints.",
			ethconfig.Defaults.HvmGenesisHeight, gotHash)
	}
}

// TestProductionHvmHeaderConfigIsCanonical drives the production config assembly (the exact
// buildHvmHeaderNodeConfig that New calls) and asserts the resulting (Network, GenesisHeightOffset,
// EffectiveGenesisBlock) triple is a canonical genesis pairing. The defaults test above only checks
// ethconfig.Defaults against the checkpoint using a test-local "testnet3" literal; it does not read the
// network default backend.go actually resolves (config.TBCNetwork → ethconfig.DefaultTBCNetwork). Without
// this, a backend-only refactor (changing the default network, breaking the --tbc.network plumbing, or
// breaking the field mapping) would refuse to start every node at boot (initHvmHeaderNode's genesis-pairing
// guard) while the suite stayed green.
func TestProductionHvmHeaderConfigIsCanonical(t *testing.T) {
	cfg := ethconfig.Defaults // copy
	tbcCfg := buildHvmHeaderNodeConfig(&cfg)

	if tbcCfg.EffectiveGenesisBlock == nil {
		t.Fatal("buildHvmHeaderNodeConfig produced a nil EffectiveGenesisBlock")
	}
	gotHash := tbcCfg.EffectiveGenesisBlock.BlockHash().String()
	if !core.IsCanonicalHvmGenesisPairing(tbcCfg.Network, tbcCfg.GenesisHeightOffset, gotHash) {
		t.Fatalf("the production hVM header-node config is NOT a canonical genesis pairing: network=%q, "+
			"offset=%d, genesis-hash=%s. initHvmHeaderNode would refuse to start the fleet. Either restore "+
			"a canonical (network, offset, header) triple in buildHvmHeaderNodeConfig, or add the canonical "+
			"checkpoint for this network to core.hvmGenesisCheckpoints.",
			tbcCfg.Network, tbcCfg.GenesisHeightOffset, gotHash)
	}
	if !tbcCfg.ExternalHeaderMode {
		t.Error("the hVM header node must be configured in ExternalHeaderMode")
	}
}

// TestBuildHvmHeaderNodeConfigNetwork pins how buildHvmHeaderNodeConfig derives the lightweight header node's
// Bitcoin Network: it flows config.TBCNetwork through verbatim, and falls back to the shared
// ethconfig.DefaultTBCNetwork ONLY when config.TBCNetwork is empty (a programmatic config). This is the field
// that keeps the lightweight and full nodes on the same network, guarding against a network mislabel. Pure
// unit test: no running node, no test fixtures.
func TestBuildHvmHeaderNodeConfigNetwork(t *testing.T) {
	cases := []struct {
		name string
		tbc  string
		want string
	}{
		{"mainnet flows through", "mainnet", "mainnet"},
		{"testnet3 flows through", "testnet3", "testnet3"},
		{"empty falls back to the shared default", "", ethconfig.DefaultTBCNetwork},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			cfg := ethconfig.Defaults // a valid config with a decodable default genesis header
			cfg.TBCNetwork = tc.tbc
			got := buildHvmHeaderNodeConfig(&cfg)
			if got.Network != tc.want {
				t.Fatalf("buildHvmHeaderNodeConfig with TBCNetwork=%q -> Network %q, want %q", tc.tbc, got.Network, tc.want)
			}
			if !got.ExternalHeaderMode {
				t.Fatalf("the lightweight header node config must have ExternalHeaderMode set")
			}
			if got.GenesisHeightOffset != cfg.HvmGenesisHeight {
				t.Fatalf("GenesisHeightOffset %d != HvmGenesisHeight %d", got.GenesisHeightOffset, cfg.HvmGenesisHeight)
			}
		})
	}
}

// TestDifferentialReplayGateTestnet3GenesisMatchesProductionDefault cross-checks the shared testnet3 hVM genesis constants the
// vm-package differential-replay gate uses (vm.Testnet3HvmGenesis*) against the production testnet3 default
// (ethconfig.Defaults, which TestEthconfigHvmDefaultsMatchCanonicalCheckpoint welds to core.hvmGenesisCheckpoints).
// Mainnet uses one symbol (vm.MainnetHvmGenesis*) so its gate cannot diverge; testnet3 has several independent
// literal copies, so a re-genesis that updated production but not the gate would leave the gate silently proving
// difficulty math over a defunct chain. Binding gate genesis to production makes that drift fail CI. The vm package
// cannot import ethconfig/core; this lives in package eth, which imports both.
func TestDifferentialReplayGateTestnet3GenesisMatchesProductionDefault(t *testing.T) {
	if vm.Testnet3HvmGenesisHeight != ethconfig.Defaults.HvmGenesisHeight {
		t.Fatalf("gate testnet3 genesis height %d != ethconfig.Defaults.HvmGenesisHeight %d — the gate genesis has "+
			"drifted from the production testnet3 default (re-genesis not propagated to vm.Testnet3HvmGenesis*)",
			vm.Testnet3HvmGenesisHeight, ethconfig.Defaults.HvmGenesisHeight)
	}
	if vm.Testnet3HvmGenesisHeader != ethconfig.Defaults.HvmGenesisHeader {
		t.Fatalf("gate testnet3 genesis header != ethconfig.Defaults.HvmGenesisHeader — gate/production drift")
	}
	// Weld the shared hash to the header so all three values stay internally consistent.
	gen, err := bdf.Hex2Header(vm.Testnet3HvmGenesisHeader)
	if err != nil {
		t.Fatalf("decode vm.Testnet3HvmGenesisHeader: %v", err)
	}
	if got := gen.BlockHash().String(); got != vm.Testnet3HvmGenesisHash {
		t.Fatalf("vm.Testnet3HvmGenesisHeader hashes to %s but vm.Testnet3HvmGenesisHash pins %s", got, vm.Testnet3HvmGenesisHash)
	}
}

// TestBuildHvmHeaderNodeConfigExpandsDataDir pins that buildHvmHeaderNodeConfig expands a leading "~" in
// HvmHeaderDataDir to an absolute path for LevelDBHome. This is load-bearing: op-geth's OWN filepath.Join
// consumers (the network-scoped reset and the migration's detect/delete/rename) operate on this string
// directly, so an un-expanded literal "~/.tbcdheaders/..." would point at a directory that never exists — the
// migration would silently no-op and the scoped reset would target the wrong path. The production DEFAULT is the
// literal "~/.tbcdheaders", and every migration test feeds an absolute t.TempDir() that BYPASSES this branch, so
// a revert to the un-expanded assignment (tbcCfg.LevelDBHome = config.HvmHeaderDataDir) would pass the whole
// suite while silently breaking migration on the default home. Pure unit test: no running node, no test fixtures.
func TestBuildHvmHeaderNodeConfigExpandsDataDir(t *testing.T) {
	home, err := homedir.Dir()
	if err != nil {
		t.Skipf("cannot resolve home directory in this environment: %v", err)
	}

	cases := []string{
		ethconfig.Defaults.HvmHeaderDataDir, // the production default ("~/.tbcdheaders") — the path that actually ships
		"~/.tbcdheaders",
		"~/some/nested/headers",
	}
	for _, in := range cases {
		t.Run(in, func(t *testing.T) {
			if !strings.HasPrefix(in, "~") {
				t.Fatalf("test input %q must start with ~ to exercise the expansion branch", in)
			}
			cfg := ethconfig.Defaults // valid config with a decodable default genesis header
			cfg.HvmHeaderDataDir = in
			got := buildHvmHeaderNodeConfig(&cfg)

			if strings.HasPrefix(got.LevelDBHome, "~") {
				t.Fatalf("LevelDBHome %q still has a leading ~ — HvmHeaderDataDir was NOT expanded (a revert to the "+
					"un-expanded assignment would silently no-op the migration and mis-target the scoped reset)", got.LevelDBHome)
			}
			if !filepath.IsAbs(got.LevelDBHome) {
				t.Fatalf("LevelDBHome %q is not absolute after expansion", got.LevelDBHome)
			}
			if !strings.HasPrefix(got.LevelDBHome, home) {
				t.Fatalf("LevelDBHome %q must expand under the home directory %q", got.LevelDBHome, home)
			}
			want, eerr := homedir.Expand(in)
			if eerr != nil {
				t.Fatalf("homedir.Expand(%q): %v", in, eerr)
			}
			if got.LevelDBHome != want {
				t.Fatalf("LevelDBHome = %q, want homedir.Expand(%q) = %q", got.LevelDBHome, in, want)
			}
		})
	}
}
