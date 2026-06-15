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
	"testing"

	"github.com/btcsuite/btcd/chaincfg"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/eth/ethconfig"
	"github.com/hemilabs/heminetwork/cmd/btctool/bdf"
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
	// The consensus header node's network is hardcoded in eth/backend.go. Keep this identical to that
	// constant; if backend.go starts deriving the network per chain, extend this test to cover every
	// reachable (network, default) pair.
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
// network literal backend.go actually hardcodes. Without this, a backend-only refactor (changing the
// network literal, wiring --tbc.network through, or breaking the field mapping) would refuse to start
// every node at boot (initHvmHeaderNode's genesis-pairing guard) while the suite stayed green.
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
