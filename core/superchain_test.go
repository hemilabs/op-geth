package core

import (
	"fmt"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/superchain"
	"github.com/ethereum/go-ethereum/triedb"
)

func TestOPStackGenesis(t *testing.T) {
	for id, cfg := range superchain.Chains {
		t.Run(fmt.Sprintf("chain-%s", cfg.Name), func(t *testing.T) {
			t.Parallel()
			_, err := LoadOPStackGenesis(id)
			if err != nil {
				t.Error(err)
			}
		})
	}
}

func TestRegistryChainConfigOverride(t *testing.T) {
	tests := []struct {
		name                 string
		overrides            *ChainOverrides
		setDenominator       *uint64
		expectedDenominator  uint64
		expectedRegolithTime *uint64
	}{
		{
			name:                 "ApplySuperchainUpgrades",
			overrides:            &ChainOverrides{ApplySuperchainUpgrades: true},
			setDenominator:       uint64ptr(50),
			expectedDenominator:  250,
			expectedRegolithTime: uint64ptr(0),
		},
		{
			name:                 "OverrideOptimismCanyon_denom_nil",
			overrides:            &ChainOverrides{OverrideOptimismCanyon: uint64ptr(1)},
			setDenominator:       nil,
			expectedDenominator:  250,
			expectedRegolithTime: nil,
		},
		{
			name:                 "OverrideOptimismCanyon_denom_0",
			overrides:            &ChainOverrides{OverrideOptimismCanyon: uint64ptr(1)},
			setDenominator:       uint64ptr(0),
			expectedDenominator:  250,
			expectedRegolithTime: nil,
		},
		{
			name:                 "OverrideOptimismCanyon_ignore_override",
			overrides:            &ChainOverrides{OverrideOptimismCanyon: uint64ptr(1)},
			setDenominator:       uint64ptr(100),
			expectedDenominator:  100,
			expectedRegolithTime: nil,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			db := rawdb.NewMemoryDatabase()
			genesis, err := LoadOPStackGenesis(10)
			if err != nil {
				t.Fatal(err)
			}
			if genesis.Config.RegolithTime == nil {
				t.Fatal("expected non-nil regolith time")
			}
			genesis.Config.RegolithTime = nil

			// initialize the DB
			tdb := triedb.NewDatabase(db, newDbConfig(rawdb.PathScheme))
			genesis.MustCommit(db, tdb)
			bl := genesis.ToBlock()
			rawdb.WriteCanonicalHash(db, bl.Hash(), 0)
			rawdb.WriteBlock(db, bl)

			if genesis.Config.Optimism == nil {
				t.Fatal("expected non nil Optimism config")
			}
			genesis.Config.Optimism.EIP1559DenominatorCanyon = tt.setDenominator
			// create chain config, even with incomplete genesis input: the chain config should be corrected
			chainConfig, _, _, err := SetupGenesisBlockWithOverride(db, tdb, genesis, tt.overrides)
			if err != nil {
				t.Fatal(err)
			}

			// check if we have a corrected chain config
			if tt.expectedRegolithTime == nil {
				if chainConfig.RegolithTime != nil {
					t.Fatal("expected regolith time to be nil")
				}
			} else if *chainConfig.RegolithTime != *tt.expectedRegolithTime {
				t.Fatalf("expected regolith time to be %d, but got %d", *tt.expectedRegolithTime, *chainConfig.RegolithTime)
			}

			if *chainConfig.Optimism.EIP1559DenominatorCanyon != tt.expectedDenominator {
				t.Fatalf("expected EIP1559DenominatorCanyon to be %d, but got %d", tt.expectedDenominator, *chainConfig.Optimism.EIP1559DenominatorCanyon)
			}
		})
	}
}

func TestOPMainnetGenesisDB(t *testing.T) {
	db := rawdb.NewMemoryDatabase()
	genesis, err := LoadOPStackGenesis(10)
	if err != nil {
		t.Fatal(err)
	}
	tdb := triedb.NewDatabase(db, newDbConfig(rawdb.PathScheme))
	genesis.MustCommit(db, tdb)
	bl := genesis.ToBlock()
	expected := common.HexToHash("0x7ca38a1916c42007829c55e69d3e9a73265554b586a499015373241b8a3fa48b")
	if blockHash := bl.Hash(); blockHash != expected {
		t.Fatalf("block hash mismatch: %s <> %s", blockHash, expected)
	}
	// This is written separately to the DB by Commit() and is thus tested explicitly here
	canonicalHash := rawdb.ReadCanonicalHash(db, 0)
	if canonicalHash != expected {
		t.Fatalf("canonical hash mismatch: %s <> %s", canonicalHash, expected)
	}
}

// TestOverrideHemiHvm0 pins ChainOverrides.OverrideHemiHvm0 propagation through SetupGenesisBlockWithOverride
// (genesis.go apply() ~392): a set override lands on the final chainConfig.Hvm0Time, and a nil override leaves it
// unchanged. Every sibling override (Canyon, etc.) is covered by TestRegistryChainConfigOverride; OverrideHemiHvm0
// alone was not — it is the CLI-wired (eth/backend.go, ethconfig) mechanism to activate hVM at genesis. Corpus-free
// (in-memory DB + the committed superchain-configs fixture).
func TestOverrideHemiHvm0(t *testing.T) {
	for _, tt := range []struct {
		name     string
		override *uint64
	}{
		{"set", uint64ptr(1234567)},
		{"nil-preserves", nil},
	} {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			db := rawdb.NewMemoryDatabase()
			genesis, err := LoadOPStackGenesis(10)
			if err != nil {
				t.Fatal(err)
			}
			if genesis.Config.Hvm0Time != nil {
				t.Fatal("precondition: baseline OP-stack genesis must have no hVM activation")
			}
			tdb := triedb.NewDatabase(db, newDbConfig(rawdb.PathScheme))
			genesis.MustCommit(db, tdb)
			bl := genesis.ToBlock()
			rawdb.WriteCanonicalHash(db, bl.Hash(), 0)
			rawdb.WriteBlock(db, bl)

			chainConfig, _, _, err := SetupGenesisBlockWithOverride(db, tdb, genesis, &ChainOverrides{OverrideHemiHvm0: tt.override})
			if err != nil {
				t.Fatal(err)
			}
			if tt.override == nil {
				if chainConfig.Hvm0Time != nil {
					t.Fatalf("a nil OverrideHemiHvm0 must leave Hvm0Time unchanged, got %d", *chainConfig.Hvm0Time)
				}
				return
			}
			if chainConfig.Hvm0Time == nil {
				t.Fatal("OverrideHemiHvm0 must propagate to Hvm0Time, got nil")
			}
			if *chainConfig.Hvm0Time != *tt.override {
				t.Fatalf("expected Hvm0Time %d, got %d", *tt.override, *chainConfig.Hvm0Time)
			}
		})
	}
}
