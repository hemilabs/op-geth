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

import (
	"bytes"
	"context"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/log"
	"github.com/hemilabs/heminetwork/database"
	"github.com/hemilabs/heminetwork/database/tbcd/level"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/stretchr/testify/require"
)

// fakeBtcLookup is a minimal in-memory btcHeaderByHashLookup for testing the full-node walk geometry.
type fakeBtcLookup struct {
	byHash map[chainhash.Hash]*wire.BlockHeader
	height map[chainhash.Hash]uint64
}

func (f *fakeBtcLookup) BlockHeaderByHash(_ context.Context, h chainhash.Hash) (*wire.BlockHeader, uint64, error) {
	hdr, ok := f.byHash[h]
	if !ok {
		return nil, 0, errors.New("not found")
	}
	return hdr, f.height[h], nil
}

// makeFakeBtcChain builds n+1 hash-linked wire.BlockHeaders rooted at a genesis at genesisHeight (distinct
// hashes via Nonce; no PoW needed — the walk only follows PrevBlock hash-links). Returns the lookup and the
// header slice (index 0 = genesis).
func makeFakeBtcChain(n int, genesisHeight uint64) (*fakeBtcLookup, []*wire.BlockHeader) {
	f := &fakeBtcLookup{byHash: map[chainhash.Hash]*wire.BlockHeader{}, height: map[chainhash.Hash]uint64{}}
	hdrs := make([]*wire.BlockHeader, n+1)
	hdrs[0] = &wire.BlockHeader{Version: 1, Bits: 0x207fffff, Nonce: 0}
	for i := 1; i <= n; i++ {
		hdrs[i] = &wire.BlockHeader{Version: 1, PrevBlock: hdrs[i-1].BlockHash(), Bits: 0x207fffff, Nonce: uint32(i)}
	}
	for i, h := range hdrs {
		hh := h.BlockHash()
		f.byHash[hh] = h
		f.height[hh] = genesisHeight + uint64(i)
	}
	return f, hdrs
}

// TestGatherHeadersBackToGenesis pins the full-node walk geometry: ascending order, genesis exclusion, the
// missing-ancestor defer, the empty (T==genesis) case, and the height-floor brick guard.
func TestGatherHeadersBackToGenesis(t *testing.T) {
	const gh = uint64(883092)
	f, hdrs := makeFakeBtcChain(3, gh) // genesis + 3 headers (heights gh..gh+3)
	gHash := hdrs[0].BlockHash()

	// (a) walk from tip hdrs[3] back to genesis -> 3 headers ASCENDING, genesis excluded.
	got, ok := gatherHeadersBackToGenesis(context.Background(), f, hdrs[3].BlockHash(), gHash, gh)
	require.True(t, ok)
	require.Len(t, got, 3)
	require.Equal(t, hdrs[1].BlockHash(), got[0].BlockHash(), "ascending: first returned is genesis+1")
	require.Equal(t, hdrs[2].BlockHash(), got[1].BlockHash())
	require.Equal(t, hdrs[3].BlockHash(), got[2].BlockHash(), "ascending: last returned is the tip")

	// (b) T == genesis -> 0 headers, ok=true (the fresh store is already at genesis).
	got, ok = gatherHeadersBackToGenesis(context.Background(), f, gHash, gHash, gh)
	require.True(t, ok)
	require.Len(t, got, 0)

	// (c) a missing mid-walk ancestor -> defer (ok=false).
	delete(f.byHash, hdrs[1].BlockHash())
	_, ok = gatherHeadersBackToGenesis(context.Background(), f, hdrs[3].BlockHash(), gHash, gh)
	require.False(t, ok, "a missing ancestor must defer")

	// (d) height floor: walk a real chain but pass a WRONG genesis hash; the walk reaches genesisHeight without
	// matching -> defer (never descends below the floor / to real Bitcoin genesis).
	f2, hdrs2 := makeFakeBtcChain(3, gh)
	var wrongGenesis chainhash.Hash
	wrongGenesis[0] = 0xff
	_, ok = gatherHeadersBackToGenesis(context.Background(), f2, hdrs2[3].BlockHash(), wrongGenesis, gh)
	require.False(t, ok, "a tip that does not descend from the effective genesis must defer at the height floor")

	// (e) Floor boundary: pin the `<=` (not `<`) in the height-floor guard. Hand-link a chain where a
	// non-genesis header `a` sits exactly AT genesisHeight and the genuine genesis `gen` is one BELOW the floor.
	// With `<=`, reaching `a` at height==floor without a genesis-hash match DEFERS; a `<` would descend past the
	// floor to `gen`, match, and wrongly accept. The makeFakeBtcChain cases above never place a header exactly at
	// the floor, so this is the only case that exercises the boundary.
	f3 := &fakeBtcLookup{byHash: map[chainhash.Hash]*wire.BlockHeader{}, height: map[chainhash.Hash]uint64{}}
	gen := &wire.BlockHeader{Version: 1, Bits: 0x207fffff, Nonce: 1}
	a := &wire.BlockHeader{Version: 1, Bits: 0x207fffff, Nonce: 2, PrevBlock: gen.BlockHash()}
	b := &wire.BlockHeader{Version: 1, Bits: 0x207fffff, Nonce: 3, PrevBlock: a.BlockHash()}
	f3.byHash[gen.BlockHash()], f3.height[gen.BlockHash()] = gen, gh-1 // genuine genesis is BELOW the floor
	f3.byHash[a.BlockHash()], f3.height[a.BlockHash()] = a, gh         // a non-genesis header sits AT the floor
	f3.byHash[b.BlockHash()], f3.height[b.BlockHash()] = b, gh+1
	_, ok = gatherHeadersBackToGenesis(context.Background(), f3, b.BlockHash(), gen.BlockHash(), gh)
	require.False(t, ok,
		"a header at exactly the effective-genesis height that is NOT the genesis must DEFER at the floor (`<=`), "+
			"not descend below it to a misplaced genesis (`<`)")
}

// TestCanonicalBTCNetwork pins the alias canonicalization: only upgradetest rewrites to testnet3
// (mirroring TBC's on-disk path); everything else is identity. This is load-bearing for the network-scoped
// reset and the migration detection — a wrong mapping would target the wrong on-disk dir.
func TestCanonicalBTCNetwork(t *testing.T) {
	cases := map[string]string{
		"upgradetest": "testnet3",
		"testnet3":    "testnet3",
		"mainnet":     "mainnet",
		"localnet":    "localnet",
		"":            "",
	}
	for in, want := range cases {
		require.Equalf(t, want, canonicalBTCNetwork(in), "canonicalBTCNetwork(%q)", in)
	}
}

// TestIsLegacyDeferredPairing pins the enforce-gate key: difficulty enforcement is disabled ONLY for
// a node running testnet3 params over the Bitcoin-mainnet pair (height 883092) — the legacy mislabel / defer
// fallback. A genuine testnet3 node, a migrated mainnet node, localnet and upgradetest are all enforceable.
func TestIsLegacyDeferredPairing(t *testing.T) {
	cases := []struct {
		network  string
		height   uint64
		deferred bool
		why      string
	}{
		{"testnet3", vm.MainnetHvmGenesisHeight, true, "legacy mainnet-as-testnet3 (DEFER state) must NOT enforce"},
		{"upgradetest", vm.MainnetHvmGenesisHeight, false, "upgradetest+mainnet-pair is NOT a valid defer state — the genesis guard crits it (Custom); matched on the RAW network only"},
		{"testnet3", 3522419, false, "genuine testnet3 (height 3522419) enforces"},
		{"mainnet", vm.MainnetHvmGenesisHeight, false, "migrated mainnet node enforces"},
		{"localnet", 0, false, "localnet enforces (its own custom pair)"},
	}
	for _, c := range cases {
		require.Equalf(t, c.deferred, isLegacyDeferredPairing(c.network, c.height), c.why)
	}
}

// TestHvmHeaderStoreDirCanonicalizes pins that the on-disk path uses the canonical network: upgradetest
// resolves to the testnet3 dir, mainnet/testnet3 are identity.
func TestHvmHeaderStoreDirCanonicalizes(t *testing.T) {
	home := "/data/hdr"
	require.Equal(t, filepath.Join(home, "testnet3"), hvmHeaderStoreDir(home, "upgradetest"))
	require.Equal(t, filepath.Join(home, "testnet3"), hvmHeaderStoreDir(home, "testnet3"))
	require.Equal(t, filepath.Join(home, "mainnet"), hvmHeaderStoreDir(home, "mainnet"))
}

// TestRemoveHvmHeaderNetworkDirIsScoped is the load-bearing test for the network-scoped delete: it removes ONLY
// the target network's store and never a sibling (the migrated mainnet store or the retired backup), AND it
// honors canonicalization (an upgradetest reset deletes <home>/testnet3/, not a nonexistent <home>/upgradetest/).
func TestRemoveHvmHeaderNetworkDirIsScoped(t *testing.T) {
	home := t.TempDir()
	for _, d := range []string{"mainnet", "testnet3", "testnet3.migrated-deadbeef"} {
		require.NoError(t, os.MkdirAll(filepath.Join(home, d), 0o755))
		require.NoError(t, os.WriteFile(filepath.Join(home, d, "marker"), []byte("x"), 0o644))
	}

	// Deleting mainnet must leave the legacy store and the rollback backup intact.
	require.NoError(t, removeHvmHeaderNetworkDir(home, "mainnet"))
	require.NoDirExists(t, filepath.Join(home, "mainnet"))
	require.DirExists(t, filepath.Join(home, "testnet3"))
	require.DirExists(t, filepath.Join(home, "testnet3.migrated-deadbeef"))

	// An upgradetest-configured reset canonicalizes to testnet3 and deletes the real store (not a phantom dir).
	require.NoError(t, removeHvmHeaderNetworkDir(home, "upgradetest"))
	require.NoDirExists(t, filepath.Join(home, "testnet3"))
	require.DirExists(t, filepath.Join(home, "testnet3.migrated-deadbeef"), "the backup must survive a sibling delete")
}

// TestDeferHvmMigrationMutatesNetwork pins the defer override: the single config.Network field flips to
// testnet3 (driving the path, the genesis guard, and the enforcement params together) and the node is reported
// not-handled (false) so the caller boots normally on the legacy store.
func TestDeferHvmMigrationMutatesNetwork(t *testing.T) {
	bc := &BlockChain{}
	cfg := &tbc.Config{Network: "mainnet", GenesisHeightOffset: vm.MainnetHvmGenesisHeight}
	handled := bc.deferHvmMigration(cfg, "test")
	require.False(t, handled, "defer must report not-handled (caller falls through to normal boot)")
	require.Equal(t, "testnet3", cfg.Network, "defer flips Network to testnet3 (the legacy store label)")
	require.True(t, isLegacyDeferredPairing(cfg.Network, cfg.GenesisHeightOffset),
		"after the defer flip the (network,height) pair is the legacy DEFER pairing -> not enforceable")
}

// TestHvmMigrationNeeded_FalseTriggerGuards pins the detection precondition that does NOT need a chain or
// TBC infra: a migration is triggered ONLY for a mainnet-configured node with a populated legacy testnet3
// store and no mainnet store. A genuine non-mainnet node must NEVER trigger (it would rename a live store).
func TestHvmMigrationNeeded_FalseTriggerGuards(t *testing.T) {
	mkStore := func(home, net string) {
		require.NoError(t, os.MkdirAll(hvmHeaderStoreDir(home, net), 0o755))
		require.NoError(t, os.WriteFile(filepath.Join(hvmHeaderStoreDir(home, net), "x"), []byte("x"), 0o644))
	}
	bc := &BlockChain{}

	// genuine testnet3 node with a populated testnet3 store: NOT migrated (the store is its live store).
	h1 := t.TempDir()
	mkStore(h1, "testnet3")
	require.False(t, bc.hvmMigrationNeeded(&tbc.Config{Network: "testnet3", LevelDBHome: h1}),
		"a genuine testnet3 node must never be migrated")

	// upgradetest canonicalizes to testnet3: also never migrated.
	require.False(t, bc.hvmMigrationNeeded(&tbc.Config{Network: "upgradetest", LevelDBHome: h1}),
		"upgradetest (canonical testnet3) must never be migrated")

	// mainnet-configured but NO legacy testnet3 store (a fresh mainnet node): nothing to migrate.
	h2 := t.TempDir()
	require.False(t, bc.hvmMigrationNeeded(&tbc.Config{Network: "mainnet", LevelDBHome: h2}),
		"no legacy store -> no migration")

	// mainnet-configured WITH a populated legacy testnet3 store and NO mainnet store: migration needed.
	h3 := t.TempDir()
	mkStore(h3, "testnet3")
	require.True(t, bc.hvmMigrationNeeded(&tbc.Config{Network: "mainnet", LevelDBHome: h3}),
		"mainnet node + legacy testnet3 store + no mainnet store -> migrate")
	// NOTE: these paths return on the fast (network!=mainnet / no-mainnet-store) checks BEFORE the
	// store-classification + retire branch; the destructive retire is covered by TestHvmMigrationNeededDispatch
	// and the NON-mainnet no-retire guarantee by TestHvmMigrationNeeded_NonMainnetNeverRetires below.
	require.True(t, dirHasEntries(hvmHeaderStoreDir(h1, "testnet3")), "genuine testnet3 store untouched by the fast-path predicate")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(h3, "testnet3")), "the legacy store untouched by the fast-path predicate")
}

// TestHvmMigrationNeeded_NonMainnetNeverRetires makes the "no live store retired" guarantee LOAD-BEARING: even
// with a VALID sibling mainnet store present (which WOULD trigger the retire branch on a mainnet node), a
// genuine testnet3 node must return early on the network check and NEVER retire its live testnet3 store. This
// kills a mutant that drops the canonicalBTCNetwork(config.Network)=="mainnet" guard (which would brick a
// genuine testnet3 node by renaming its live store out from under it).
func TestHvmMigrationNeeded_NonMainnetNeverRetires(t *testing.T) {
	ctx := context.Background()
	home := t.TempDir()
	seedTbcHeaderStore(t, ctx, home, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, false)
	seedTbcHeaderStore(t, ctx, home, "mainnet", vm.MainnetHvmGenesisHeader, vm.MainnetHvmGenesisHeight, true)
	bc := &BlockChain{ctx: ctx}

	require.False(t, bc.hvmMigrationNeeded(&tbc.Config{Network: "testnet3", LevelDBHome: home}),
		"a genuine testnet3 node never needs migration")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")),
		"a testnet3 node must NEVER retire its live store, even with a sibling mainnet store present")
	// And no backup was created (no rename happened).
	ents, _ := os.ReadDir(home)
	for _, e := range ents {
		require.NotContains(t, e.Name(), "testnet3.migrated-", "no retirement may occur on a non-mainnet node")
	}
}

// seedTbcHeaderStore stands up a real lightweight tbc.Server for (network, genesis) under home, optionally sets
// a non-genesis upstream-state-id, then tears it down (releasing the exclusive lock so the guard-free probe can
// re-open it). Shared by the seeded migration tests.
func seedTbcHeaderStore(t *testing.T, ctx context.Context, home, network, genHdrHex string, height uint64, setStateId bool) {
	t.Helper()
	raw, err := hex.DecodeString(genHdrHex)
	require.NoError(t, err)
	var gen wire.BlockHeader
	require.NoError(t, gen.Deserialize(bytes.NewReader(raw)))
	cfg := tbc.NewDefaultConfig()
	cfg.ExternalHeaderMode = true
	cfg.EffectiveGenesisBlock = &gen
	cfg.GenesisHeightOffset = height
	cfg.LevelDBHome = home
	cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
	cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
	cfg.Network = network
	srv, e := tbc.NewServer(cfg)
	require.NoError(t, e)
	require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
	if setStateId {
		var s [32]byte
		s[0] = 0x77
		require.NoError(t, srv.SetUpstreamStateId(ctx, s))
	}
	require.NoError(t, srv.ExternalHeaderTearDown())
}

// TestUpstreamContractGuards pins the heminetwork behaviors the migration relies on, so a future dependency
// bump that changes them reddens CI instead of silently bricking the fleet.
func TestUpstreamContractGuards(t *testing.T) {
	// (1) REAL version-ceiling guard (a bare require.Equal(4,...) would be a tautology). A freshly-created
	// store is written at heminetwork's CURRENT ldbVersion, and readLegacyStoreTS rejects any version >
	// ldbMaxSupportedVersion — so if a heminetwork bump moves the on-disk version past that ceiling, reading a
	// FRESH store errors here, forcing the lockstep update.
	{
		ctx := context.Background()
		home := t.TempDir()
		seedTbcHeaderStore(t, ctx, home, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, false)
		_, verr := readLegacyStoreTS(ctx, home, "testnet3")
		require.NoError(t, verr, "a fresh store must read cleanly; an error here means heminetwork bumped ldbVersion past ldbMaxSupportedVersion (%d) — update it in lockstep", ldbMaxSupportedVersion)
	}

	// (2) errors.As must match a wrapped database.NotFoundError — the torn-store (errLegacyStoreEmpty) detection
	// in readLegacyStoreTS depends on it.
	var nf database.NotFoundError
	require.True(t, errors.As(database.ErrNotFound, &nf), "errors.As(&database.NotFoundError) must match — torn-store detection relies on it")
	require.True(t, errors.Is(fmt.Errorf("wrap: %w", errLegacyStoreEmpty), errLegacyStoreEmpty), "errLegacyStoreEmpty survives wrapping")

	// (3) AddExternalHeaders with NO headers must error — the empty-fill (T==genesis) path special-cases this and
	// would otherwise crash the migration if upstream silently accepted an empty set.
	ctx := context.Background()
	raw, err := hex.DecodeString(testnet3HvmGenesisHeaderReplay)
	require.NoError(t, err)
	var gen wire.BlockHeader
	require.NoError(t, gen.Deserialize(bytes.NewReader(raw)))
	cfg := tbc.NewDefaultConfig()
	cfg.ExternalHeaderMode = true
	cfg.EffectiveGenesisBlock = &gen
	cfg.GenesisHeightOffset = testnet3HvmGenesisHeightReplay
	cfg.LevelDBHome = t.TempDir()
	cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
	cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
	cfg.Network = "testnet3"
	srv, e := tbc.NewServer(cfg)
	require.NoError(t, e)
	require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
	_, _, _, _, addErr := srv.AddExternalHeaders(ctx, &wire.MsgHeaders{}, make([]byte, 32))
	require.Error(t, addErr, "AddExternalHeaders([]) must error — the empty-fill path relies on this")
	require.Contains(t, addErr.Error(), "no headers",
		"the error must be the EMPTY-SET error specifically (assert the reason, not just any error)")
	require.NoError(t, srv.ExternalHeaderTearDown())
}

// TestClassifyMigratedMainnetStore pins the destructive-delete polarity of the keep-vs-re-migrate decision
// (a flipped branch would silently DELETE a healthy mainnet store or KEEP a torn one and crit-loop the boot).
func TestClassifyMigratedMainnetStore(t *testing.T) {
	require.Equal(t, mainnetStoreReMigrate, classifyMigratedMainnetStore(nil, fmt.Errorf("wrap: %w", errLegacyStoreEmpty)),
		"empty/torn store -> RE-MIGRATE")
	require.Equal(t, mainnetStoreKeepUnreadable, classifyMigratedMainnetStore(nil, errors.New("lock held")),
		"unreadable (lock/corruption) -> CONSERVATIVE KEEP, do NOT retire the fallback")
	require.Equal(t, mainnetStoreReMigrate, classifyMigratedMainnetStore(&legacyStoreTS{atGenesis: true}, nil),
		"fresh at-genesis store -> RE-MIGRATE")
	require.Equal(t, mainnetStoreValidMigrated, classifyMigratedMainnetStore(&legacyStoreTS{atGenesis: false}, nil),
		"readable non-genesis store -> VALID MIGRATED (kept; fallback may be retired), even if a reorg made the state-id non-canonical")
}

// TestDirHasEntries pins the store-presence predicate (gates whether migration triggers and whether the
// legacy source is deleted): missing / empty / populated dir / a plain file.
func TestDirHasEntries(t *testing.T) {
	h := t.TempDir()
	require.False(t, dirHasEntries(filepath.Join(h, "missing")), "missing path")
	empty := filepath.Join(h, "empty")
	require.NoError(t, os.MkdirAll(empty, 0o755))
	require.False(t, dirHasEntries(empty), "empty dir")
	require.NoError(t, os.WriteFile(filepath.Join(empty, "x"), []byte("y"), 0o644))
	require.True(t, dirHasEntries(empty), "populated dir")
	f := filepath.Join(h, "afile")
	require.NoError(t, os.WriteFile(f, []byte("y"), 0o644))
	require.False(t, dirHasEntries(f), "a plain file is not a populated store dir")
}

// TestRetireLegacyTestnet3Store pins the rollback-backup retirement: it must NEVER destroy the only
// rollback copy. Three branches: fresh rename, non-empty backup -> drop source, EMPTY backup -> keep BOTH.
func TestRetireLegacyTestnet3Store(t *testing.T) {
	var s [32]byte
	s[0], s[1] = 0xde, 0xad
	backup := fmt.Sprintf("testnet3.migrated-%x", s[:])
	bc := &BlockChain{}
	mk := func(home, sub string) {
		require.NoError(t, os.MkdirAll(filepath.Join(home, sub), 0o755))
		require.NoError(t, os.WriteFile(filepath.Join(home, sub, "m"), []byte("x"), 0o644))
	}

	// (a) no pre-existing backup -> rename testnet3/ -> testnet3.migrated-<S>/, and the CONTENTS move with it
	// (a rename-dropping mutant, e.g. RemoveAll+MkdirAll, would leave an empty backup and fail FileExists).
	h1 := t.TempDir()
	mk(h1, "testnet3")
	bc.retireLegacyTestnet3Store(h1, s)
	require.NoDirExists(t, filepath.Join(h1, "testnet3"))
	require.DirExists(t, filepath.Join(h1, backup))
	require.FileExists(t, filepath.Join(h1, backup, "m"), "rename must PRESERVE the backup contents (rollback copy)")

	// (b) a NON-EMPTY backup already exists -> remove the source, keep the backup AND its original content intact.
	h2 := t.TempDir()
	mk(h2, "testnet3")
	// A distinct source-only marker: after retirement it must be DISCARDED (RemoveAll), not merged into the backup.
	require.NoError(t, os.WriteFile(filepath.Join(h2, "testnet3", "sourceonly"), []byte("src"), 0o644))
	require.NoError(t, os.MkdirAll(filepath.Join(h2, backup), 0o755))
	require.NoError(t, os.WriteFile(filepath.Join(h2, backup, "orig"), []byte("keep"), 0o644))
	bc.retireLegacyTestnet3Store(h2, s)
	require.NoDirExists(t, filepath.Join(h2, "testnet3"))
	b, err := os.ReadFile(filepath.Join(h2, backup, "orig"))
	require.NoError(t, err)
	require.Equal(t, "keep", string(b), "the pre-existing backup content must be untouched")
	// The source's distinctive content must NOT leak into the backup (kills a merge-instead-of-remove mutant).
	require.NoFileExists(t, filepath.Join(h2, backup, "sourceonly"), "the source content must be DISCARDED, not merged into the existing backup")
	require.NoFileExists(t, filepath.Join(h2, backup, "m"), "no source file may be merged into the pre-existing backup")

	// (c) an EMPTY backup exists -> keep BOTH (never delete the only rollback copy for an empty backup)
	h3 := t.TempDir()
	mk(h3, "testnet3")
	require.NoError(t, os.MkdirAll(filepath.Join(h3, backup), 0o755)) // empty backup dir
	bc.retireLegacyTestnet3Store(h3, s)
	require.DirExists(t, filepath.Join(h3, "testnet3"), "an empty backup must NOT cause source deletion")
	require.FileExists(t, filepath.Join(h3, "testnet3", "m"), "the source content must survive intact")
	require.DirExists(t, filepath.Join(h3, backup))
}

// openStoreGuardFree opens the store at <home>/<canonicalNet> with the SAME guard-free settings readLegacyStoreTS
// uses (SetUpgradeOpen, so the on-disk format is untouched and the upgrade ladder is skipped). The caller MUST
// Close the returned handle before any re-open of the same dir (the goleveldb lock is exclusive). Used by tests
// to inject corruption (a bogus version key, a deleted state-id) that a real tbc.Server would never write.
func openStoreGuardFree(t *testing.T, ctx context.Context, home, network string) interface {
	MetadataGet(context.Context, []byte) ([]byte, error)
	MetadataPut(context.Context, []byte, []byte) error
	MetadataDel(context.Context, []byte) error
	Close() error
} {
	t.Helper()
	cfg, err := level.NewConfig(canonicalBTCNetwork(network), home, "0", "0")
	require.NoError(t, err)
	cfg.SetUpgradeOpen(true)
	db, err := level.New(ctx, cfg)
	require.NoError(t, err)
	return db
}

// TestReadLegacyStoreTS_VersionCeiling drives the forward/backward-incompatibility guard against a REAL store
// whose on-disk version key has been corrupted out from under the binary. TestUpstreamContractGuards only covers a
// FRESH store (version == ldbVersion) reading cleanly, so a flipped comparison or a dropped bound passes there.
// Here both the FUTURE (> ceiling) and the SUB-FLOOR (< min) branches are forced and asserted, with an in-range
// control proving the guard is not over-broad.
func TestReadLegacyStoreTS_VersionCeiling(t *testing.T) {
	ctx := context.Background()
	writeVersion := func(home string, version uint64) {
		db := openStoreGuardFree(t, ctx, home, "testnet3")
		vb := make([]byte, 8)
		binary.BigEndian.PutUint64(vb, version)
		require.NoError(t, db.MetadataPut(ctx, []byte("version"), vb))
		require.NoError(t, db.Close()) // release the exclusive lock before readLegacyStoreTS re-opens
	}

	// FUTURE version (ceiling): a store written by a newer binary must be rejected, not misdecoded.
	homeF := t.TempDir()
	seedTbcHeaderStore(t, ctx, homeF, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, true)
	writeVersion(homeF, uint64(ldbMaxSupportedVersion)+1)
	_, errF := readLegacyStoreTS(ctx, homeF, "testnet3")
	require.Error(t, errF, "a FUTURE-version store must be rejected")
	require.Contains(t, errF.Error(), "FUTURE version", "the FUTURE-version branch must fire (not a generic read error)")
	// Lock release on the ERROR path: the deferred Close must fire before return, so the dir is re-openable.
	require.NoError(t, openStoreGuardFree(t, ctx, homeF, "testnet3").Close(),
		"the guard-free read must release the exclusive lock even on the FUTURE-version error path")

	// SUB-FLOOR version: a torn/zeroed version key must fail closed, not slip past a ceiling-only check.
	homeZ := t.TempDir()
	seedTbcHeaderStore(t, ctx, homeZ, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, true)
	writeVersion(homeZ, 0)
	_, errZ := readLegacyStoreTS(ctx, homeZ, "testnet3")
	require.Error(t, errZ, "a sub-floor (0) version must be rejected")
	require.Contains(t, errZ.Error(), "invalid version", "the sub-floor branch must fire")
	require.NoError(t, openStoreGuardFree(t, ctx, homeZ, "testnet3").Close(),
		"the guard-free read must release the exclusive lock even on the sub-floor-version error path")

	// TRUNCATED/SHORT version key: a 1-7 byte version value makes heminetwork's db.Version do
	// binary.BigEndian.Uint64 on a <8-byte slice -> PANIC, BEFORE the value guards above can run. readLegacyStoreTS
	// must RECOVER it into the conservative version-read error (fail closed), not crash the node boot.
	homeT := t.TempDir()
	seedTbcHeaderStore(t, ctx, homeT, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, true)
	{
		dbT := openStoreGuardFree(t, ctx, homeT, "testnet3")
		require.NoError(t, dbT.MetadataPut(ctx, []byte("version"), []byte{0x00, 0x00, 0x03})) // 3 bytes -> Uint64 would panic
		require.NoError(t, dbT.Close())
	}
	var errT error
	require.NotPanics(t, func() { _, errT = readLegacyStoreTS(ctx, homeT, "testnet3") },
		"a torn/short version key must be RECOVERED into a graceful error, not panic/crash the node boot")
	require.Error(t, errT, "a torn/short version key must fail closed")
	require.Contains(t, errT.Error(), "torn/short", "the recovered error must identify the torn version key")
	// NB: unlike the value-out-of-range cases above, the lock is NOT re-openable here — heminetwork's level.New panics
	// PART-WAY through open (after acquiring the leveldb lock, at the Uint64 version decode) and the deferred db.Close
	// never registers, so the lock leaks for the process lifetime. That is a heminetwork-internal limitation;
	// readLegacyStoreTS still converts a boot CRASH into a graceful fail-closed error (the store is corrupt either way).

	// CONTROL (ceiling): an in-range version at the CEILING still reads — proves the guard is bounded above.
	homeOK := t.TempDir()
	seedTbcHeaderStore(t, ctx, homeOK, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, true)
	writeVersion(homeOK, uint64(ldbMaxSupportedVersion))
	_, errOK := readLegacyStoreTS(ctx, homeOK, "testnet3")
	require.NoError(t, errOK, "an in-range version (== ceiling) must still read; the guard must not be over-broad above")

	// CONTROL (floor): an in-range version at the FLOOR (== ldbMinSupportedVersion) must STILL read. A v1
	// store is a legitimate on-disk format (heminetwork New() accepts versions 1..ldbVersion under SetUpgradeOpen),
	// so this pins the lower bound symmetrically: silently RAISING ldbMinSupportedVersion would turn this red.
	homeMin := t.TempDir()
	seedTbcHeaderStore(t, ctx, homeMin, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, true)
	writeVersion(homeMin, uint64(ldbMinSupportedVersion))
	_, errMin := readLegacyStoreTS(ctx, homeMin, "testnet3")
	require.NoError(t, errMin, "the floor version (== ldbMinSupportedVersion) must still read; the guard must not exclude the lowest supported on-disk version")
}

// TestReadLegacyStoreTS_TornStoreEmpty drives the two production torn-store paths against REAL stores (not just the
// abstract errors.As contract in TestUpstreamContractGuards): a store with NO best header, and a store with a best
// header but NO upstream-state-id (the fill commits headers and the state-id in separate transactions, state-id
// last, so a crash between them leaves exactly this shape). Both MUST classify as errLegacyStoreEmpty so the
// keep-vs-re-migrate dispatch RE-MIGRATEs them rather than keeping a store that would crit-loop the normal boot.
func TestReadLegacyStoreTS_TornStoreEmpty(t *testing.T) {
	ctx := context.Background()

	// (a) NO best header: open a fresh store directly (level.New writes the version key) but never run
	// ExternalHeaderSetup, so no genesis/best header is recorded. BlockHeaderBest -> NotFound -> errLegacyStoreEmpty.
	homeNoHdr := t.TempDir()
	require.NoError(t, openStoreGuardFree(t, ctx, homeNoHdr, "testnet3").Close()) // create+version, then release lock
	_, errNoHdr := readLegacyStoreTS(ctx, homeNoHdr, "testnet3")
	require.ErrorIs(t, errNoHdr, errLegacyStoreEmpty, "a store with no best header is torn -> errLegacyStoreEmpty (RE-MIGRATE)")
	require.NoError(t, openStoreGuardFree(t, ctx, homeNoHdr, "testnet3").Close(),
		"the guard-free read must release the lock even on the no-best-header torn-store error path")

	// (b) MISSING upstream-state-id: seed a real store (genesis best header + genesis state-id), then delete only the
	// state-id key. BlockHeaderBest succeeds, MetadataGet(upstreamstateid) -> NotFound -> errLegacyStoreEmpty.
	homeNoSid := t.TempDir()
	seedTbcHeaderStore(t, ctx, homeNoSid, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, true)
	dbDel := openStoreGuardFree(t, ctx, homeNoSid, "testnet3")
	require.NoError(t, dbDel.MetadataDel(ctx, upstreamStateIdMetaKey))
	require.NoError(t, dbDel.Close())
	_, errNoSid := readLegacyStoreTS(ctx, homeNoSid, "testnet3")
	require.ErrorIs(t, errNoSid, errLegacyStoreEmpty, "a best header with no upstream-state-id is torn -> errLegacyStoreEmpty (RE-MIGRATE)")
	require.NoError(t, openStoreGuardFree(t, ctx, homeNoSid, "testnet3").Close(),
		"the guard-free read must release the lock even on the no-state-id torn-store error path")
}

// TestRetireLegacyTestnet3Store_RenameFailureLeavesSource pins the NON-FATAL failure contract of the retirement: if
// the rename cannot complete (here forced via a read-only parent dir -> EACCES), the legacy source MUST survive
// intact (it is the only rollback copy) and the function must not panic or destroy data — it just warns and retries
// next boot. Complements TestRetireLegacyTestnet3Store, which covers only the SUCCESS branches.
func TestRetireLegacyTestnet3Store_RenameFailureLeavesSource(t *testing.T) {
	if os.Geteuid() == 0 {
		t.Skip("running as root bypasses directory permission bits; cannot force an EACCES rename")
	}
	var s [32]byte
	s[0], s[1] = 0xbe, 0xef
	home := t.TempDir()
	src := filepath.Join(home, "testnet3")
	require.NoError(t, os.MkdirAll(src, 0o755))
	require.NoError(t, os.WriteFile(filepath.Join(src, "m"), []byte("rollback-copy"), 0o644))

	// Make the parent read+execute only: creating the dst entry (the rename target) fails with EACCES, while
	// os.Stat(dst) still resolves to not-exist (so the dst-already-exists branch is not taken).
	require.NoError(t, os.Chmod(home, 0o500))
	t.Cleanup(func() { _ = os.Chmod(home, 0o755) }) // restore so t.TempDir cleanup can remove it

	bc := &BlockChain{}
	bc.retireLegacyTestnet3Store(home, s) // must be non-fatal

	require.NoError(t, os.Chmod(home, 0o755)) // restore to assert contents
	require.DirExists(t, src, "a failed rename must LEAVE the legacy source intact (it is the only rollback copy)")
	b, err := os.ReadFile(filepath.Join(src, "m"))
	require.NoError(t, err)
	require.Equal(t, "rollback-copy", string(b), "the source content must survive a failed retirement untouched")
	require.NoDirExists(t, filepath.Join(home, fmt.Sprintf("testnet3.migrated-%x", s[:])), "no partial backup should be left")
}

// TestLegacyStateIdIsCanonical pins the pre-rebuild PROCEED guard on a real in-memory chain: a canonical block
// at/below the bodied tip is canonical; an unknown EVM block is not.
func TestLegacyStateIdIsCanonical(t *testing.T) {
	genDb, _, bc, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
	require.NoError(t, err)
	defer bc.Stop()

	h3 := bc.GetCanonicalHash(3)
	require.NotEqual(t, common.Hash{}, h3)
	require.True(t, bc.legacyStateIdIsCanonical([32]byte(h3)), "a canonical block below the bodied tip is canonical")
	require.True(t, bc.legacyStateIdIsCanonical([32]byte(bc.CurrentBlock().Hash())), "the bodied tip itself is canonical")

	var unknown [32]byte
	unknown[0] = 0xab
	require.False(t, bc.legacyStateIdIsCanonical(unknown), "an unknown EVM block is not a canonical ancestor")

	// Known-but-non-canonical: a state-id whose block is on disk (GetHeaderByHash != nil) and at/below
	// the bodied tip but on an ORPHANED fork (reorged out) must be rejected. This pins the
	// `GetCanonicalHash(n) == h.Hash()` conjunct, which the canonical/unknown/above-tip cases all survive. Capture
	// the ORIGINAL canonical block 3, then force a reorg with a LONGER competing full-block fork off block 2; the
	// original block 3 then stays on disk (GetHeaderByHash != nil) but is no longer canonical. Full-block fork
	// matches the full chain (a header-only insert over a full chain nil-derefs the state-commit path). No corpus.
	orig3 := bc.GetCanonicalHash(3)
	require.NotEqual(t, common.Hash{}, orig3)
	forkBlocks := makeBlockChain(bc.chainConfig, bc.GetBlockByNumber(2), 6, ethash.NewFaker(), genDb, 99 /* longer fork -> reorg */)
	_, err = bc.InsertChain(forkBlocks)
	require.NoError(t, err)
	require.Greater(t, bc.CurrentBlock().Number.Uint64(), uint64(5), "sanity: the longer fork reorged the canonical chain")
	require.NotEqual(t, orig3, bc.GetCanonicalHash(3), "sanity: the original block 3 was reorged out (now non-canonical)")
	require.NotNil(t, bc.GetHeaderByHash(orig3), "sanity: the orphaned original block 3 is still on disk")
	require.False(t, bc.legacyStateIdIsCanonical([32]byte(orig3)),
		"a known but non-canonical (orphaned-by-reorg) state-id must NOT be canonical-for-proceed")
}

// TestReadLegacyStoreTS_Seeded exercises the guard-free read against a REAL leveldb store seeded by a real
// lightweight tbc.Server, and directly validates the lock-safety the read depends on: the server is fully torn
// down (releasing the exclusive goleveldb lock) BEFORE readLegacyStoreTS re-opens the same dir. Covers the happy
// read (tipHash byte order, state-id round-trip) and the atGenesis classification.
func TestReadLegacyStoreTS_Seeded(t *testing.T) {
	ctx := context.Background()
	raw, err := hex.DecodeString(testnet3HvmGenesisHeaderReplay)
	require.NoError(t, err)
	var genHdr wire.BlockHeader
	require.NoError(t, genHdr.Deserialize(bytes.NewReader(raw)))

	newSrv := func(home string) *tbc.Server {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = &genHdr
		cfg.GenesisHeightOffset = testnet3HvmGenesisHeightReplay
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize = "0"
		cfg.BlockCacheSize = "0"
		cfg.AutoIndex = false
		cfg.BlockSanity = false
		cfg.MaxCachedTxs = 0
		cfg.MempoolEnabled = false
		cfg.Network = "testnet3"
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		return srv
	}

	// Case A: a fresh store (genesis only, default state-id) reads back as atGenesis with tip==genesis.
	homeA := t.TempDir()
	srvA := newSrv(homeA)
	require.NoError(t, srvA.ExternalHeaderTearDown()) // release the exclusive lock before the guard-free re-open
	tsA, err := readLegacyStoreTS(ctx, homeA, "testnet3")
	require.NoError(t, err)
	require.True(t, tsA.atGenesis, "a fresh store carries the genesis upstream-state-id")
	require.Equal(t, testnet3HvmGenesisHashReplay, tsA.tipHash.String(), "tipHash round-trips in correct byte order")
	require.Equal(t, testnet3HvmGenesisHeightReplay, tsA.tipHeight)

	// Case B: a custom upstream-state-id S reads back exactly, atGenesis=false — and the read succeeds AFTER a
	// real tear-down, proving the exclusive lock is released and re-acquirable.
	homeB := t.TempDir()
	srvB := newSrv(homeB)
	var S [32]byte
	S[0], S[31] = 0xab, 0xcd
	require.NoError(t, srvB.SetUpstreamStateId(ctx, S))
	require.NoError(t, srvB.ExternalHeaderTearDown())
	tsB, err := readLegacyStoreTS(ctx, homeB, "testnet3")
	require.NoError(t, err)
	require.False(t, tsB.atGenesis, "a custom non-genesis state-id is not atGenesis")
	require.Equal(t, S, tsB.stateId, "the 32-byte upstream-state-id round-trips exactly")
	require.Equal(t, testnet3HvmGenesisHeightReplay, tsB.tipHeight, "tip height is read correctly (no headers added -> genesis height)")
	require.Equal(t, testnet3HvmGenesisHashReplay, tsB.tipHash.String(), "tip hash byte order preserved")

	// Case C (fixture realism): a NON-genesis tip via a real linked child header. This exercises the
	// read path at a real tip+1 (tipHeight, tipHash) that the genesis-only fixtures cannot — a tipHeight or
	// byte-order bug for a progressed store would surface here.
	homeC := t.TempDir()
	srvC := newSrv(homeC)
	child := &wire.BlockHeader{
		Version:    genHdr.Version,
		PrevBlock:  genHdr.BlockHash(),
		MerkleRoot: genHdr.MerkleRoot,
		Timestamp:  genHdr.Timestamp.Add(10 * time.Minute),
		Bits:       genHdr.Bits,
		Nonce:      1,
	}
	var SC [32]byte
	SC[0] = 0x42
	_, _, _, _, addErr := srvC.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{child}}, SC[:])
	require.NoError(t, addErr, "adding a linked child header should succeed (BlockSanity off)")
	require.NoError(t, srvC.ExternalHeaderTearDown())
	tsC, err := readLegacyStoreTS(ctx, homeC, "testnet3")
	require.NoError(t, err)
	require.Equal(t, testnet3HvmGenesisHeightReplay+1, tsC.tipHeight, "tip advanced to genesis+1")
	require.Equal(t, child.BlockHash().String(), tsC.tipHash.String(), "tipHash is the child header (correct byte order at a non-genesis tip)")
	require.Equal(t, SC, tsC.stateId, "state-id from AddExternalHeaders round-trips")
	require.False(t, tsC.atGenesis)
}

// TestLegacyStateIdIsCanonicalBoundedByBodiedHead kills the CurrentBlock()->CurrentHeader() mutant: on a
// HEADER-ONLY chain (CurrentHeader leads the bodied head, which stays at genesis), a state-id above the bodied
// head must be rejected (the catch-up needs bodies). If the bound were CurrentHeader this would wrongly pass.
func TestLegacyStateIdIsCanonicalBoundedByBodiedHead(t *testing.T) {
	_, _, bc, err := newCanonical(ethash.NewFaker(), 5, false /* header-only */, rawdb.HashScheme)
	require.NoError(t, err)
	defer bc.Stop()
	require.Greater(t, bc.CurrentHeader().Number.Uint64(), bc.CurrentBlock().Number.Uint64(),
		"sanity: header chain must lead the bodied head for this test to be meaningful")

	h3 := bc.GetCanonicalHash(3)
	require.NotEqual(t, common.Hash{}, h3)
	require.False(t, bc.legacyStateIdIsCanonical([32]byte(h3)),
		"a state-id above the BODIED head must NOT be canonical-for-proceed (bound is CurrentBlock, not CurrentHeader)")
}

// TestCatchUpMigratedStoreToTipBounds pins the infra-free guard branches of the catch-up (no tbc node needed —
// they return before the apply loop): no-op at the bodied tip, unknown state-id error, and the from>tip error
// on a header-only chain (also kills the CurrentBlock->CurrentHeader tip mutant in the catch-up).
func TestCatchUpMigratedStoreToTipBounds(t *testing.T) {
	// Header-only chain: bodied tip stays at genesis, header chain at 5.
	_, _, bc, err := newCanonical(ethash.NewFaker(), 5, false, rawdb.HashScheme)
	require.NoError(t, err)
	defer bc.Stop()

	// no-op: stateId == the bodied tip (genesis here) -> nil, never touches the (nil) tbc node.
	require.NoError(t, bc.catchUpMigratedStoreToTip([32]byte(bc.CurrentBlock().Hash())), "stateId at the bodied tip is a no-op")

	// unknown state-id -> error (not a known EVM block). Assert the SPECIFIC branch (a bare
	// require.Error survives a mutant that routes this input into the canonical-ancestor message instead).
	var unknown [32]byte
	unknown[0] = 0x99
	errU := bc.catchUpMigratedStoreToTip(unknown)
	require.Error(t, errU, "unknown state-id must error")
	require.Contains(t, errU.Error(), "not a known EVM block",
		"unknown state-id must fire the nil-from branch, not the canonical-ancestor branch")

	// a header above the bodied tip -> from.Number > tip(CurrentBlock).Number -> error (no apply attempted).
	h3 := bc.GetCanonicalHash(3)
	errH := bc.catchUpMigratedStoreToTip([32]byte(h3))
	require.Error(t, errH, "a state-id above the bodied head must error before applying")
	require.Contains(t, errH.Error(), "not a canonical ancestor",
		"a state-id above the bodied tip must fire the from>tip branch, distinct from the unknown-block branch")
}

// TestCatchUpMigratedStoreRejectsNonCanonicalAncestor pins the catch-up's defensive canonical-ancestor re-check:
// a state-id whose block is on disk and at/below the BODIED tip but ORPHANED by a reorg must fail
// with "not a canonical ancestor" BEFORE the apply loop (so no tbc node is needed). The from>tip bounds test
// covers a state-id ABOVE the tip; this covers the distinct at/below-tip-but-non-canonical case, pinning the
// GetCanonicalHash(fromN)==from.Hash() term. Corpus-free.
func TestCatchUpMigratedStoreRejectsNonCanonicalAncestor(t *testing.T) {
	genDb, _, bc, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
	require.NoError(t, err)
	defer bc.Stop()

	orig3 := bc.GetCanonicalHash(3)
	require.NotEqual(t, common.Hash{}, orig3)
	// Longer fork off block 2 -> reorg; the original block 3 stays on disk but is no longer canonical and is now
	// well below the (advanced) bodied tip, so it passes the from<=tip bound and reaches the canonical re-check.
	forkBlocks := makeBlockChain(bc.chainConfig, bc.GetBlockByNumber(2), 6, ethash.NewFaker(), genDb, 99)
	_, err = bc.InsertChain(forkBlocks)
	require.NoError(t, err)
	require.NotEqual(t, orig3, bc.GetCanonicalHash(3), "sanity: original block 3 reorged out")
	require.NotNil(t, bc.GetHeaderByHash(orig3), "sanity: orphaned block 3 still on disk")
	require.Less(t, uint64(3), bc.CurrentBlock().Number.Uint64(), "sanity: orphan is below the bodied tip")

	err = bc.catchUpMigratedStoreToTip([32]byte(orig3))
	require.Error(t, err, "a non-canonical ancestor at/below the bodied tip must error")
	require.Contains(t, err.Error(), "not a canonical ancestor",
		"the canonical re-check (not the from>tip bound) must fire for an at/below-tip orphan")
}

// TestHvmMigrationNeededDispatch exercises the keep-vs-re-migrate dispatch against REAL seeded mainnet stores (kills the
// existingMainnetStoreState dispatch mutants): a valid (non-genesis) mainnet store + a legacy testnet3 store ->
// NOT needed AND the orphan testnet3 is retired; a fresh at-genesis mainnet store + testnet3 -> migration needed.
func TestHvmMigrationNeededDispatch(t *testing.T) {
	ctx := context.Background()
	decode := func(hexHdr string) *wire.BlockHeader {
		raw, err := hex.DecodeString(hexHdr)
		require.NoError(t, err)
		var h wire.BlockHeader
		require.NoError(t, h.Deserialize(bytes.NewReader(raw)))
		return &h
	}
	mainnetGen := decode(vm.MainnetHvmGenesisHeader)
	testnet3Gen := decode(testnet3HvmGenesisHeaderReplay)

	// seedStore stands up a REAL lightweight tbc.Server for (network, genesis), optionally sets a non-genesis
	// state-id, then tears down (releasing the exclusive lock) so the guard-free probe can re-open it.
	seedStore := func(home, network string, gen *wire.BlockHeader, height uint64, setStateId bool) {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = gen
		cfg.GenesisHeightOffset = height
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
		cfg.Network = network
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		if setStateId {
			var s [32]byte
			s[0] = 0x77
			require.NoError(t, srv.SetUpstreamStateId(ctx, s)) // non-genesis -> ValidMigrated
		}
		require.NoError(t, srv.ExternalHeaderTearDown()) // release the lock before the guard-free probe
	}
	seedMainnet := func(home string, setStateId bool) {
		seedStore(home, "mainnet", mainnetGen, vm.MainnetHvmGenesisHeight, setStateId)
	}
	mkLegacy := func(home string) { // a REAL seeded testnet3 store so retireOrphanedLegacyStore can read+rename it
		seedStore(home, "testnet3", testnet3Gen, testnet3HvmGenesisHeightReplay, false)
	}
	bc := &BlockChain{ctx: ctx}

	// (a) valid migrated mainnet store + legacy testnet3 -> NOT needed; the orphan testnet3 is retired.
	hA := t.TempDir()
	seedMainnet(hA, true)
	mkLegacy(hA)
	require.False(t, bc.hvmMigrationNeeded(&tbc.Config{Network: "mainnet", LevelDBHome: hA}),
		"a valid migrated mainnet store -> no migration needed")
	require.False(t, dirHasEntries(hvmHeaderStoreDir(hA, "testnet3")),
		"the orphaned legacy testnet3 store must be retired once mainnet is definitively migrated")
	// It must be RENAMED to a backup (rollback-safe), NOT deleted: a testnet3.migrated-* dir must now exist.
	ents, err := os.ReadDir(hA)
	require.NoError(t, err)
	var hasBackup bool
	for _, e := range ents {
		if e.IsDir() && len(e.Name()) > len("testnet3.migrated-") && e.Name()[:len("testnet3.migrated-")] == "testnet3.migrated-" {
			hasBackup = true
		}
	}
	require.True(t, hasBackup, "the retired legacy store must be RENAMED to a testnet3.migrated-<S> backup, not deleted")

	// (b) fresh at-genesis mainnet store + legacy testnet3 -> migration needed (incomplete store).
	hB := t.TempDir()
	seedMainnet(hB, false) // genesis state-id only -> atGenesis -> ReMigrate
	mkLegacy(hB)
	require.True(t, bc.hvmMigrationNeeded(&tbc.Config{Network: "mainnet", LevelDBHome: hB}),
		"a fresh at-genesis mainnet store is incomplete -> migration needed")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(hB, "testnet3")),
		"the legacy testnet3 store must NOT be retired when re-migration is needed")

	// (c) UNREADABLE mainnet store + legacy testnet3 -> NOT needed (conservative KEEP), and crucially the legacy
	// store is NOT retired and the mainnet store is NOT wiped: a mutant routing the mainnetStoreKeepUnreadable
	// dispatch arm to ReMigrate would destructively wipe a store the binary cannot
	// even read. Corrupt the mainnet store's version key to a FUTURE version so
	// readLegacyStoreTS("mainnet") returns a non-empty, non-NotFound error -> KeepUnreadable. No corpus needed.
	hC := t.TempDir()
	seedMainnet(hC, true) // a valid migrated store...
	mkLegacy(hC)
	dbC := openStoreGuardFree(t, ctx, hC, "mainnet") // ...whose version we now corrupt to "future"
	vb := make([]byte, 8)
	binary.BigEndian.PutUint64(vb, uint64(ldbMaxSupportedVersion)+1)
	require.NoError(t, dbC.MetadataPut(ctx, []byte("version"), vb))
	require.NoError(t, dbC.Close()) // release the lock before hvmMigrationNeeded re-opens it
	require.False(t, bc.hvmMigrationNeeded(&tbc.Config{Network: "mainnet", LevelDBHome: hC}),
		"an UNREADABLE mainnet store must conservatively KEEP (return false), never re-migrate")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(hC, "mainnet")),
		"the unreadable mainnet store must NOT be wiped (a destructive re-migrate would be catastrophic)")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(hC, "testnet3")),
		"the legacy fallback must NOT be retired while the mainnet store is unreadable")

	// (d) TORN mainnet store (best header present, upstream-state-id deleted -> errLegacyStoreEmpty) + legacy
	// testnet3 -> RE-MIGRATE (the crash window where the fill committed headers but crashed
	// before the state-id). Distinct from (c)'s unreadable-KEEP: a torn store MUST re-migrate, and the legacy
	// fallback must be preserved so the re-migration can read T/S from it. Corpus-free.
	hD := t.TempDir()
	seedMainnet(hD, true) // a valid mainnet store...
	mkLegacy(hD)
	dbD := openStoreGuardFree(t, ctx, hD, "mainnet")
	require.NoError(t, dbD.MetadataDel(ctx, upstreamStateIdMetaKey)) // ...torn: delete the state-id
	require.NoError(t, dbD.Close())
	require.True(t, bc.hvmMigrationNeeded(&tbc.Config{Network: "mainnet", LevelDBHome: hD}),
		"a TORN mainnet store (no state-id) must RE-MIGRATE, not be kept")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(hD, "testnet3")),
		"the legacy fallback must be preserved when the mainnet store is torn (re-migration reads T/S from it)")
}

// TestGatherHeadersBackToGenesis_CycleTerminates pins the cycle guard: the full node is NOT trusted,
// so a PrevBlock cycle ABOVE the genesis-height floor (a corrupt index / malicious peer) must DEFER, never
// loop forever. A genuine hash-cycle is cryptographically unconstructable, so the fake lookup LIES (maps keys
// to headers regardless of their real hash) to simulate a torn index. Run under a hard timeout so that if a
// future edit removes the strict-descent guard, this test FAILS (timeout) instead of hanging the suite.
func TestGatherHeadersBackToGenesis_CycleTerminates(t *testing.T) {
	const gh = uint64(883092)
	f := &fakeBtcLookup{byHash: map[chainhash.Hash]*wire.BlockHeader{}, height: map[chainhash.Hash]uint64{}}
	hA := &wire.BlockHeader{Version: 1, Bits: 0x207fffff, Nonce: 1}
	hB := &wire.BlockHeader{Version: 1, Bits: 0x207fffff, Nonce: 2}
	var keyA, keyB chainhash.Hash
	keyA[0], keyB[0] = 0xaa, 0xbb
	hA.PrevBlock = keyB // A -> B
	hB.PrevBlock = keyA // B -> A : a 2-cycle, both at the SAME (non-decreasing) height above the floor
	f.byHash[keyA], f.height[keyA] = hA, gh+1000
	f.byHash[keyB], f.height[keyB] = hB, gh+1000
	var genesis chainhash.Hash
	genesis[0] = 0xff // distinct from the cycle, never reached

	done := make(chan bool, 1)
	go func() {
		_, ok := gatherHeadersBackToGenesis(context.Background(), f, keyA, genesis, gh)
		done <- ok
	}()
	select {
	case ok := <-done:
		require.False(t, ok, "a PrevBlock cycle must DEFER (ok=false), not be accepted")
	case <-time.After(5 * time.Second):
		t.Fatal("gatherHeadersBackToGenesis did NOT terminate on a PrevBlock cycle — the strict-descent guard is missing")
	}
}

// TestMaybeMigrate_DefersWhenFullNodeAbsent drives the actual orchestration entry point maybeMigrateHvmHeaderNode
// end-to-end through the migrate-evaluation and the full-node-readiness DEFER (vm.TBCFullNode is nil in unit
// tests). It pins: a mainnet-configured node with a legacy testnet3 store but no ready full node DEFERS
// (returns not-handled, mutates config.Network back to testnet3) and touches NO directory (the legacy store is
// untouched, no mainnet store is created). This is the executable coverage of the orchestration entry;
// a regression that proceeded to a destructive rebuild without a ready full node would fail here.
func TestMaybeMigrate_DefersWhenFullNodeAbsent(t *testing.T) {
	ctx := context.Background()
	home := t.TempDir()
	seedTbcHeaderStore(t, ctx, home, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, true)

	raw, err := hex.DecodeString(vm.MainnetHvmGenesisHeader)
	require.NoError(t, err)
	var mainnetGen wire.BlockHeader
	require.NoError(t, mainnetGen.Deserialize(bytes.NewReader(raw)))
	cfg := &tbc.Config{
		Network:               "mainnet",
		LevelDBHome:           home,
		EffectiveGenesisBlock: &mainnetGen, // satisfies the genesis weld so we reach the full-node guard
		GenesisHeightOffset:   vm.MainnetHvmGenesisHeight,
	}
	bc := &BlockChain{ctx: ctx}

	// Meter/gauge baselines: assert the exact deltas the defer path must produce.
	trigBefore := hvmMigrationTriggeredMeter.Snapshot().Count()
	deferBefore := hvmMigrationDeferredMeter.Snapshot().Count()
	compBefore := hvmMigrationCompletedMeter.Snapshot().Count()
	failBefore := hvmMigrationFailedMeter.Snapshot().Count()

	// vm.TBCFullNode is nil in a unit test -> the full-node-is-mainnet guard DEFERS.
	handled := bc.maybeMigrateHvmHeaderNode(cfg)
	require.False(t, handled, "with no ready full node the orchestration must DEFER (not-handled), not migrate")
	require.Equal(t, "testnet3", cfg.Network, "defer must flip config.Network back to testnet3")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be untouched on defer")
	require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "no mainnet store may be created on defer")

	// The rebuild window was never entered: the in-progress field/gauge must be clean.
	require.False(t, bc.hvmMigrationInProgress, "a DEFER must leave bc.hvmMigrationInProgress false (the rebuild window was never entered)")
	require.Equal(t, int64(0), hvmMigrationInProgressGauge.Snapshot().Value(), "the in-progress gauge must be 0 after a defer")

	// Exact meter deltas: triggered +1, deferred +1, completed/failed unchanged.
	require.Equal(t, trigBefore+1, hvmMigrationTriggeredMeter.Snapshot().Count(), "defer must still count as triggered")
	require.Equal(t, deferBefore+1, hvmMigrationDeferredMeter.Snapshot().Count(), "defer must mark the deferred meter exactly once")
	require.Equal(t, compBefore, hvmMigrationCompletedMeter.Snapshot().Count(), "a defer must NOT mark completed")
	require.Equal(t, failBefore, hvmMigrationFailedMeter.Snapshot().Count(), "a defer is not a failure")
}

// TestMigrate_SuccessRebuildsAndRetires drives the FULL success orchestration end-to-end — the path that needs a
// ready full node. It is built entirely from synthetic headers + an in-memory EVM chain, with NO real
// mainnet/testnet header corpus: observeSnapBtcDiff is advisory/never-halting, so easy-difficulty synthetic
// children that fail real mainnet PoW do not block the rebuild. This is the only test that exercises the fill, the
// tip==T / state-id==S verify, the retire, and the completed meter, so mutants like swapping want/got in the tip
// check, or feeding the wrong state-id to AddExternalHeaders, are caught only here.
func TestMigrate_SuccessRebuildsAndRetires(t *testing.T) {
	ctx := context.Background()

	// The REAL mainnet effective genesis (height 883092) — the rebuild welds against it and the walk
	// terminates on its hash.
	raw, err := hex.DecodeString(vm.MainnetHvmGenesisHeader)
	require.NoError(t, err)
	var mainnetGen wire.BlockHeader
	require.NoError(t, mainnetGen.Deserialize(bytes.NewReader(raw)))

	// Synthetic children hash-linked from the real genesis (heights 883093..883092+N). Easy to build; their real
	// mainnet PoW is irrelevant (observe-only).
	const N = 4
	children := make([]*wire.BlockHeader, N)
	prev := &mainnetGen
	for i := 0; i < N; i++ {
		h := &wire.BlockHeader{
			Version:    prev.Version,
			PrevBlock:  prev.BlockHash(),
			MerkleRoot: mainnetGen.MerkleRoot,
			Timestamp:  prev.Timestamp.Add(time.Duration(i+1) * 10 * time.Minute),
			Bits:       mainnetGen.Bits,
			Nonce:      uint32(i + 1),
		}
		children[i] = h
		prev = h
	}
	tipHash := prev.BlockHash()

	// newSrv builds a real lightweight tbc.Server at <home>/<network> rooted at the mainnet genesis and filled
	// with the synthetic children to committed tip T, with the given upstream-state-id.
	newSrv := func(home, network string, stateId [32]byte) *tbc.Server {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = &mainnetGen
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
		cfg.Network = network
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		_, _, _, _, addErr := srv.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: children}, stateId[:])
		require.NoError(t, addErr)
		return srv
	}

	// In-memory EVM chain so the legacy state-id S = bodied tip is canonical -> the pre-rebuild guard passes and
	// the catch-up is a clean no-op.
	_, _, bc, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
	require.NoError(t, err)
	defer bc.Stop()
	S := [32]byte(bc.CurrentBlock().Hash())

	home := t.TempDir()

	// The full node (mainnet, kept OPEN during the migration so the walk can read it) holds genesis..T.
	var fullSid [32]byte
	fullSid[0] = 0x01
	fullSrv := newSrv(t.TempDir(), "mainnet", fullSid)
	defer func() { _ = fullSrv.ExternalHeaderTearDown() }()
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	vm.TBCFullNode = fullSrv
	vm.TBCFullNodeConfig = &tbc.Config{Network: "mainnet"}
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	// The legacy testnet3-LABELED store (the v1 mislabel): the mainnet pair, committed to T, state-id S. Torn
	// down so the guard-free read can re-open it.
	legacySrv := newSrv(home, "testnet3", S)
	require.NoError(t, legacySrv.ExternalHeaderTearDown())

	cfg := &tbc.Config{
		Network:               "mainnet",
		LevelDBHome:           home,
		EffectiveGenesisBlock: &mainnetGen,
		GenesisHeightOffset:   vm.MainnetHvmGenesisHeight,
		ExternalHeaderMode:    true,
	}

	compBefore := hvmMigrationCompletedMeter.Snapshot().Count()
	powBefore := hvmMigrationPoWRejectMeter.Snapshot().Count()
	handled := bc.maybeMigrateHvmHeaderNode(cfg)
	// Release the migrated mainnet node's goleveldb lock/fds before t.TempDir cleanup (bc.Stop does not tear down
	// bc.tbcHeaderNode). Registered right after the call so it runs even if an assertion fails.
	t.Cleanup(func() {
		if bc.tbcHeaderNode != nil {
			_ = bc.tbcHeaderNode.ExternalHeaderTearDown()
		}
	})
	require.True(t, handled, "a ready full node + a progressed legacy store must MIGRATE (handled=true)")
	require.Equal(t, "mainnet", cfg.Network, "a successful migration must NOT flip the network back to testnet3")
	require.NotNil(t, bc.tbcHeaderNode, "the migrated mainnet header node must be initialized")
	require.True(t, bc.hvmDiffEnforceable.Load(), "a migrated mainnet node must be difficulty-enforceable")
	require.False(t, bc.hvmMigrationInProgress, "the in-progress flag must be cleared after a successful migration")

	// Post-state: the rebuilt store is at T with upstream-state-id S.
	postH, postTip, err := bc.tbcHeaderNode.BlockHeaderBest(ctx)
	require.NoError(t, err)
	require.Equal(t, tipHash.String(), postTip.BlockHash().String(), "rebuilt store canonical tip must equal the legacy committed tip T")
	require.Equal(t, vm.MainnetHvmGenesisHeight+uint64(N), postH, "rebuilt store tip height must be genesis+N")
	postId, err := bc.tbcHeaderNode.UpstreamStateId(ctx)
	require.NoError(t, err)
	require.Equal(t, S, *postId, "rebuilt store upstream-state-id must equal the legacy state-id S")

	// Retire: mainnet store present, legacy store renamed to a backup (not deleted).
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "the migrated mainnet store must exist")
	require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy testnet3 store must be retired")
	require.DirExists(t, filepath.Join(home, fmt.Sprintf("testnet3.migrated-%x", S[:])),
		"the legacy store must be RENAMED to a testnet3.migrated-<S> backup, not deleted")

	require.Equal(t, compBefore+1, hvmMigrationCompletedMeter.Snapshot().Count(), "a successful migration marks the completed meter exactly once")

	// Observe-only PoW backstop: the synthetic easy-difficulty children deterministically FAIL real
	// mainnet PoW, so the observe-only check must have marked the alert meter — and crucially the migration still
	// SUCCEEDED (asserted above), proving the check is advisory and never halts the rebuild.
	require.Equal(t, powBefore+1, hvmMigrationPoWRejectMeter.Snapshot().Count(),
		"the observe-only PoW check must alert on the synthetic children yet NOT halt the migration")
}

// hvmWeldCritChildEnv selects which mismatched genesis config the genesis-weld subprocess child builds.
const hvmWeldCritChildEnv = "HVM_WELD_CRIT_CHILD_MODE"

// TestMigrateWeldCritChild is the subprocess child for TestMigrateWeldCrit. The genesis weld is the FIRST
// statement of migrateHvmHeaderNode and crits (os.Exit, via migrationCrit) before reading the legacy store, the
// full node, or touching any dir — so a bare *BlockChain and a mismatched config suffice; no store/full-node/
// header corpus is needed. log.Crit cannot be caught in-process, hence the re-exec.
func TestMigrateWeldCritChild(t *testing.T) {
	mode := os.Getenv(hvmWeldCritChildEnv)
	if mode == "" {
		t.Skip("child-only: driven by TestMigrateWeldCrit via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	decode := func(hexHdr string) *wire.BlockHeader {
		raw, err := hex.DecodeString(hexHdr)
		require.NoError(t, err)
		var h wire.BlockHeader
		require.NoError(t, h.Deserialize(bytes.NewReader(raw)))
		return &h
	}
	bc := &BlockChain{ctx: context.Background()}
	cfg := &tbc.Config{Network: "mainnet", LevelDBHome: t.TempDir()}
	switch mode {
	case "nil-genesis":
		cfg.EffectiveGenesisBlock = nil
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
	case "wrong-header":
		// A different real header (testnet3 genesis) at the mainnet height: hash misses the canonical -> weld crit.
		cfg.EffectiveGenesisBlock = decode(testnet3HvmGenesisHeaderReplay)
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
	case "wrong-height":
		// The CORRECT mainnet header but the wrong height -> kills the drop-the-height-clause mutant specifically.
		cfg.EffectiveGenesisBlock = decode(vm.MainnetHvmGenesisHeader)
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight + 1
	default:
		t.Fatalf("unknown child mode %q", mode)
	}
	bc.migrateHvmHeaderNode(cfg)
	// The weld must migrationCrit -> os.Exit(1) before returning. Reaching here means it did not refuse; the
	// parent's "returned for mode" absence check catches a Crit->Warn downgrade.
	t.Fatalf("migrateHvmHeaderNode returned for mode %q; expected the genesis weld to refuse-to-start (migrationCrit)", mode)
}

// TestMigrateWeldCrit drives the genesis-weld refuse-to-start via subprocess re-exec. The weld guards a
// DESTRUCTIVE rebuild against a wrong genesis, so its failing side — nil genesis, wrong header, and wrong HEIGHT —
// must refuse to start. Asserts non-zero exit, the weld's specific crit reason, and the ABSENCE of the
// returned-marker (which kills a migrationCrit->log.Warn downgrade). No store/full-node/header corpus needed.
func TestMigrateWeldCrit(t *testing.T) {
	for i, tc := range []struct{ mode, wantSub string }{
		{"nil-genesis", "does not match the canonical"},
		{"wrong-header", "does not match the canonical"},
		{"wrong-height", "does not match the canonical"},
	} {
		if testing.Short() && i > 0 {
			continue // each spawn is cheap (crits before any leveldb open), but keep -short to one case
		}
		t.Run(tc.mode, func(t *testing.T) {
			cmd := exec.Command(os.Args[0], "-test.run=^TestMigrateWeldCritChild$", "-test.v")
			cmd.Env = append(os.Environ(), hvmWeldCritChildEnv+"="+tc.mode)
			out, err := cmd.CombinedOutput()

			var ee *exec.ExitError
			require.ErrorAs(t, err, &ee, "child must exit non-zero (weld refuse-to-start), output:\n%s", string(out))
			require.False(t, ee.Success(), "child must report failure")
			require.Contains(t, string(out), tc.wantSub,
				"child stderr must carry the genesis weld's refuse reason for mode %q", tc.mode)
			require.NotContains(t, string(out), "migrateHvmHeaderNode returned for mode",
				"the weld must os.Exit (migrationCrit) before returning; the returned-marker means a downgrade to log.Warn for mode %q", tc.mode)
		})
	}
}

// TestMigrate_DefersWhenStateIdNonCanonical exercises the pre-rebuild canonical-S deferral DISPATCH inside
// migrateHvmHeaderNode: a readable, progressed legacy store whose recorded EVM state-id is NOT a
// canonical ancestor of the current tip (a deep reorg across an unclean shutdown) must DEFER — leaving the legacy
// store untouched and creating no mainnet store — rather than rebuild into a state the catch-up would crit-loop
// on. The predicate (legacyStateIdIsCanonical) is unit-tested; this pins that the migrate routine actually
// branches to deferHvmMigration on it. Corpus-free (mirrors the success-path fixture with a non-canonical S).
func TestMigrate_DefersWhenStateIdNonCanonical(t *testing.T) {
	ctx := context.Background()
	raw, err := hex.DecodeString(vm.MainnetHvmGenesisHeader)
	require.NoError(t, err)
	var mainnetGen wire.BlockHeader
	require.NoError(t, mainnetGen.Deserialize(bytes.NewReader(raw)))
	child := &wire.BlockHeader{
		Version: mainnetGen.Version, PrevBlock: mainnetGen.BlockHash(), MerkleRoot: mainnetGen.MerkleRoot,
		Timestamp: mainnetGen.Timestamp.Add(10 * time.Minute), Bits: mainnetGen.Bits, Nonce: 1,
	}
	newSrv := func(home, network string, stateId [32]byte) *tbc.Server {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = &mainnetGen
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
		cfg.Network = network
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		_, _, _, _, addErr := srv.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{child}}, stateId[:])
		require.NoError(t, addErr)
		return srv
	}

	_, _, bc, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
	require.NoError(t, err)
	defer bc.Stop()

	// A non-genesis state-id that is NOT any EVM block -> legacyStateIdIsCanonical == false.
	var badS [32]byte
	badS[0], badS[31] = 0xde, 0xad
	require.False(t, bc.legacyStateIdIsCanonical(badS), "precondition: badS must be non-canonical")

	home := t.TempDir()
	full := newSrv(t.TempDir(), "mainnet", [32]byte{0x01})
	defer func() { _ = full.ExternalHeaderTearDown() }()
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	vm.TBCFullNode = full
	vm.TBCFullNodeConfig = &tbc.Config{Network: "mainnet"}
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	legacy := newSrv(home, "testnet3", badS)
	require.NoError(t, legacy.ExternalHeaderTearDown())

	cfg := &tbc.Config{
		Network: "mainnet", LevelDBHome: home,
		EffectiveGenesisBlock: &mainnetGen, GenesisHeightOffset: vm.MainnetHvmGenesisHeight, ExternalHeaderMode: true,
	}
	handled := bc.maybeMigrateHvmHeaderNode(cfg)
	require.False(t, handled, "a non-canonical legacy state-id must DEFER, not rebuild")
	require.Equal(t, "testnet3", cfg.Network, "the deferral dispatch must flip the network back to testnet3")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be untouched on this deferral")
	require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "no mainnet store may be created on this deferral")

	// lock-release-on-defer: the guard-free read must have FULLY closed the legacy store before
	// deferring, so the normal fall-through boot (initHvmHeaderNode -> ExternalHeaderSetup re-opens the same dir)
	// can re-acquire the exclusive goleveldb lock. Re-open it here; a leaked handle would make this fail ErrLocked.
	reopened := openStoreGuardFree(t, ctx, home, "testnet3")
	require.NoError(t, reopened.Close(), "the legacy store must be re-openable after a defer (the guard-free read released its lock)")
}

// TestMarkHvmMigrationFailed positively asserts the "failed" event side effect: markHvmMigrationFailed
// marks the failed meter and clears the in-progress gauge. The failed meter is otherwise only marked on a path
// that immediately os.Exits (migrationCrit), so isolating the side effect in markHvmMigrationFailed makes it
// checkable in-process. Kills a mutant that drops either the meter mark or the gauge clear.
func TestMarkHvmMigrationFailed(t *testing.T) {
	failBefore := hvmMigrationFailedMeter.Snapshot().Count()
	hvmMigrationInProgressGauge.Update(1) // simulate being mid-rebuild
	markHvmMigrationFailed()
	require.Equal(t, failBefore+1, hvmMigrationFailedMeter.Snapshot().Count(), "the failed meter must be marked")
	require.Equal(t, int64(0), hvmMigrationInProgressGauge.Snapshot().Value(), "the in-progress gauge must be cleared")
}

// hvmInWindowCritChildEnv gates the in-window-crit subprocess child.
const hvmInWindowCritChildEnv = "HVM_INWINDOW_CRIT_CHILD"

// TestHvmInWindowCritChild is the subprocess child for TestHvmMigrationAwareCritRoutes: with
// bc.hvmMigrationInProgress=true, hvmMigrationAwareCrit must route through migrationCrit (which marks the failed
// meter + clears the gauge) and then os.Exit via log.Crit. Driven by re-exec because log.Crit cannot be caught
// in-process. No header/store/full-node corpus needed (hvmMigrationAwareCrit only reads the bool field).
func TestHvmInWindowCritChild(t *testing.T) {
	if os.Getenv(hvmInWindowCritChildEnv) == "" {
		t.Skip("child-only: driven by TestHvmMigrationAwareCritRoutes via subprocess re-exec")
	}
	log.SetDefault(log.NewLogger(log.NewTerminalHandler(os.Stderr, false)))
	bc := &BlockChain{ctx: context.Background()}
	bc.hvmMigrationInProgress = true
	bc.hvmMigrationAwareCrit("forced in-window crit for the routing test")
	t.Fatalf("hvmMigrationAwareCrit returned with hvmMigrationInProgress=true; expected migrationCrit -> os.Exit")
}

// TestHvmMigrationAwareCritRoutes drives the in-window crit routing: the
// `if bc.hvmMigrationInProgress { migrationCrit() }` branch (the weld crit fires before the flag is set, and the
// success/defer paths trigger no crit, so only a forced in-window state reaches it). The subprocess proves the
// in-window crit reaches os.Exit with the right message and does NOT fall through to the returned-marker (which
// would mean the branch was downgraded/deleted to a non-exiting path). The failed-meter side effect of this path
// is covered in-process by TestMarkHvmMigrationFailed.
func TestHvmMigrationAwareCritRoutes(t *testing.T) {
	cmd := exec.Command(os.Args[0], "-test.run=^TestHvmInWindowCritChild$", "-test.v")
	cmd.Env = append(os.Environ(), hvmInWindowCritChildEnv+"=1")
	out, err := cmd.CombinedOutput()

	var ee *exec.ExitError
	require.ErrorAs(t, err, &ee, "an in-window crit must os.Exit non-zero, output:\n%s", string(out))
	require.False(t, ee.Success(), "child must report failure")
	require.Contains(t, string(out), "forced in-window crit for the routing test", "the crit message must reach stderr")
	require.NotContains(t, string(out), "hvmMigrationAwareCrit returned",
		"the in-window branch must os.Exit (via migrationCrit/log.Crit) before returning; the returned-marker means the routing branch was downgraded")
}

// TestResetHvmHeaderNodeToGenesisIsScoped pins the scoped-delete behavior at its PRODUCTION call site:
// resetHvmHeaderNodeToGenesis must delete ONLY this node's own <home>/<canonicalNet> store, never sibling dirs
// (a migrated mainnet store or a testnet3.migrated-<S> rollback backup) that a parent-wipe would destroy.
// TestRemoveHvmHeaderNetworkDirIsScoped covers the scoped-delete primitive directly; this covers the reset
// wrapper, which every steady-state recovery path routes through. Corpus-free (regtest light node).
func TestResetHvmHeaderNodeToGenesisIsScoped(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a real lightweight TBC node")
	}
	chain, _ := newRegtestChainWithLightTBC(t, btcDiffTestHvm0Time)
	home := chain.tbcHeaderNodeConfig.LevelDBHome
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "localnet")), "sanity: the live localnet store exists before reset")

	// Plant sibling dirs a parent-wipe would clobber.
	for _, d := range []string{"mainnet", "testnet3.migrated-deadbeef"} {
		require.NoError(t, os.MkdirAll(filepath.Join(home, d), 0o755))
		require.NoError(t, os.WriteFile(filepath.Join(home, d, "marker"), []byte("x"), 0o644))
	}

	chain.resetHvmHeaderNodeToGenesis()

	// Siblings must survive; only this node's own store is reset (and re-initialized at genesis).
	require.DirExists(t, filepath.Join(home, "mainnet"), "a sibling mainnet store must survive a scoped reset")
	require.FileExists(t, filepath.Join(home, "mainnet", "marker"), "the sibling store's contents must be intact")
	require.DirExists(t, filepath.Join(home, "testnet3.migrated-deadbeef"), "the rollback backup must survive a scoped reset")
	require.FileExists(t, filepath.Join(home, "testnet3.migrated-deadbeef", "marker"))
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "localnet")), "the node's own store is re-initialized at genesis after reset")
}

// TestEnterHvmMigrationRebuildWindow positively asserts the "in-progress" SET event: the production set path
// (gauge->1, bc.hvmMigrationInProgress->true). The success test only asserts the CLEARED state post-completion, so
// without this a mutant deleting either set survives. Pairs with TestMarkHvmMigrationFailed (the clear path).
func TestEnterHvmMigrationRebuildWindow(t *testing.T) {
	t.Cleanup(func() { hvmMigrationInProgressGauge.Update(0) }) // do not leak the gauge to later tests
	bc := &BlockChain{ctx: context.Background()}
	require.False(t, bc.hvmMigrationInProgress, "precondition: flag starts false")
	bc.enterHvmMigrationRebuildWindow()
	require.Equal(t, int64(1), hvmMigrationInProgressGauge.Snapshot().Value(), "the in-progress gauge must be set to 1")
	require.True(t, bc.hvmMigrationInProgress, "the in-window crit routing flag must be armed")
}

// TestMigrate_SuccessEmptyFill drives the EMPTY-FILL migrate branch end-to-end: when the legacy
// committed BTC tip T IS the mainnet effective genesis (no committed BTC headers past genesis — the early-hVM
// state where the EVM state-id advanced while the BTC tip stayed at genesis), the gather returns zero headers and
// the fill must SKIP AddExternalHeaders (which errors on an empty set) and set only the upstream-state-id. Mirrors
// TestMigrate_SuccessRebuildsAndRetires with no synthetic children. Corpus-free.
func TestMigrate_SuccessEmptyFill(t *testing.T) {
	ctx := context.Background()
	raw, err := hex.DecodeString(vm.MainnetHvmGenesisHeader)
	require.NoError(t, err)
	var mainnetGen wire.BlockHeader
	require.NoError(t, mainnetGen.Deserialize(bytes.NewReader(raw)))

	// A store at the mainnet genesis ONLY (no children), with the given non-genesis state-id.
	newGenesisOnlySrv := func(home, network string, stateId [32]byte) *tbc.Server {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = &mainnetGen
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
		cfg.Network = network
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		require.NoError(t, srv.SetUpstreamStateId(ctx, stateId)) // non-genesis state-id, tip stays at genesis
		return srv
	}

	_, _, bc, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
	require.NoError(t, err)
	defer bc.Stop()
	S := [32]byte(bc.CurrentBlock().Hash()) // canonical -> catch-up no-op

	home := t.TempDir()
	full := newGenesisOnlySrv(t.TempDir(), "mainnet", [32]byte{0x01})
	defer func() { _ = full.ExternalHeaderTearDown() }()
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	vm.TBCFullNode = full
	vm.TBCFullNodeConfig = &tbc.Config{Network: "mainnet"}
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	legacy := newGenesisOnlySrv(home, "testnet3", S)
	require.NoError(t, legacy.ExternalHeaderTearDown())

	cfg := &tbc.Config{
		Network: "mainnet", LevelDBHome: home,
		EffectiveGenesisBlock: &mainnetGen, GenesisHeightOffset: vm.MainnetHvmGenesisHeight, ExternalHeaderMode: true,
	}
	compBefore := hvmMigrationCompletedMeter.Snapshot().Count()
	handled := bc.maybeMigrateHvmHeaderNode(cfg)
	t.Cleanup(func() {
		if bc.tbcHeaderNode != nil {
			_ = bc.tbcHeaderNode.ExternalHeaderTearDown()
		}
	})
	require.True(t, handled, "an empty-fill migration (T==genesis) must still MIGRATE")
	require.Equal(t, "mainnet", cfg.Network)

	// The rebuilt store sits at the genesis (empty fill) with the state-id set.
	postH, postTip, err := bc.tbcHeaderNode.BlockHeaderBest(ctx)
	require.NoError(t, err)
	require.Equal(t, vm.MainnetHvmGenesisHeight, postH, "empty-fill: the rebuilt tip stays at the mainnet genesis height")
	require.Equal(t, mainnetGen.BlockHash().String(), postTip.BlockHash().String(), "empty-fill: tip == mainnet genesis")
	postId, err := bc.tbcHeaderNode.UpstreamStateId(ctx)
	require.NoError(t, err)
	require.Equal(t, S, *postId, "empty-fill: the upstream-state-id is still set to S")

	require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be retired even on an empty fill")
	require.DirExists(t, filepath.Join(home, fmt.Sprintf("testnet3.migrated-%x", S[:])), "the legacy store must be renamed to the backup")
	require.Equal(t, compBefore+1, hvmMigrationCompletedMeter.Snapshot().Count(), "empty-fill still marks completed")
}

// TestReadLegacyStoreTS_WrongLengthStateId covers the len(sBytes)!=32 corruption branch in readLegacyStoreTS: a
// torn/partial upstream-state-id of the wrong length must error with "unexpected length" and — crucially — NOT be
// classified errLegacyStoreEmpty, so classifyMigratedMainnetStore routes it to the conservative KEEP
// (mainnetStoreKeepUnreadable), never the destructive ReMigrate.
func TestReadLegacyStoreTS_WrongLengthStateId(t *testing.T) {
	ctx := context.Background()
	for _, n := range []int{16, 33} {
		home := t.TempDir()
		seedTbcHeaderStore(t, ctx, home, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, true)
		db := openStoreGuardFree(t, ctx, home, "testnet3")
		require.NoError(t, db.MetadataPut(ctx, upstreamStateIdMetaKey, make([]byte, n)))
		require.NoError(t, db.Close()) // release the lock before readLegacyStoreTS re-opens

		_, err := readLegacyStoreTS(ctx, home, "testnet3")
		require.Error(t, err, "a %d-byte state-id must error", n)
		require.Contains(t, err.Error(), "unexpected length")
		require.False(t, errors.Is(err, errLegacyStoreEmpty),
			"a wrong-length state-id is corruption (KeepUnreadable), not a torn empty store (ReMigrate)")
		require.Equal(t, mainnetStoreKeepUnreadable, classifyMigratedMainnetStore(nil, err),
			"the dispatch must conservatively KEEP a wrong-length store, never re-migrate/destroy it")
	}
}

// TestReadLegacyStoreTS_OpenFailureNeutral covers the level.New open-failure wrap: an unopenable store path must
// error with the NEUTRAL message naming the dir (it must not claim "lock held"), and must NOT classify as
// errLegacyStoreEmpty (an open failure is KeepUnreadable, not ReMigrate). Pointed at a path that is a regular FILE
// so level.New cannot open a leveldb directory there.
func TestReadLegacyStoreTS_OpenFailureNeutral(t *testing.T) {
	ctx := context.Background()
	home := t.TempDir()
	// hvmHeaderStoreDir(home,"mainnet") == home/mainnet; make it a FILE so level.New fails to open a dir there.
	require.NoError(t, os.WriteFile(hvmHeaderStoreDir(home, "mainnet"), []byte("not a leveldb dir"), 0o644))

	_, err := readLegacyStoreTS(ctx, home, "mainnet")
	require.Error(t, err, "an unopenable store path must error")
	require.Contains(t, err.Error(), hvmHeaderStoreDir(home, "mainnet"), "the neutral open-failure message must name the dir")
	require.False(t, errors.Is(err, errLegacyStoreEmpty), "an open failure is KeepUnreadable, not a torn empty store")
	require.Equal(t, mainnetStoreKeepUnreadable, classifyMigratedMainnetStore(nil, err))
}

// TestHvmMigrationNeeded_OrphanedUnreadableLegacyIsLeft covers branch 2 of retireOrphanedLegacyStore: when a
// VALID migrated mainnet store coexists with an UNREADABLE orphaned testnet3 store (crash-before-rename), the
// orphan's state-id cannot be read to name the backup, so it must be LEFT untouched — never renamed with a
// zero/garbage state-id (which would mis-name the only recoverable copy). Branch 1 (readable -> rename) is
// covered by TestHvmMigrationNeededDispatch case (a); this pins the conservative leave-it branch.
func TestHvmMigrationNeeded_OrphanedUnreadableLegacyIsLeft(t *testing.T) {
	ctx := context.Background()
	home := t.TempDir()
	// A valid migrated mainnet store (non-genesis state-id) -> dispatch enters retireOrphanedLegacyStore.
	seedTbcHeaderStore(t, ctx, home, "mainnet", vm.MainnetHvmGenesisHeader, vm.MainnetHvmGenesisHeight, true)
	// An orphaned legacy testnet3 store, made UNREADABLE by corrupting its version to a FUTURE value.
	seedTbcHeaderStore(t, ctx, home, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, false)
	db := openStoreGuardFree(t, ctx, home, "testnet3")
	vb := make([]byte, 8)
	binary.BigEndian.PutUint64(vb, uint64(ldbMaxSupportedVersion)+1)
	require.NoError(t, db.MetadataPut(ctx, []byte("version"), vb))
	require.NoError(t, db.Close())

	bc := &BlockChain{ctx: ctx}
	require.False(t, bc.hvmMigrationNeeded(&tbc.Config{Network: "mainnet", LevelDBHome: home}),
		"a valid migrated mainnet store -> no migration needed")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")),
		"an UNREADABLE orphaned legacy store must be LEFT (its state-id could not be read to name the backup)")
	ents, err := os.ReadDir(home)
	require.NoError(t, err)
	for _, e := range ents {
		require.NotContains(t, e.Name(), "testnet3.migrated-",
			"no backup may be created for an unreadable orphan (would mis-name the only recoverable copy)")
	}
}

// TestMigrate_SuccessMarksBtcDiffRejectMeter pins the migrate fill's observe-only CONTEXTUAL branch: an above-floor
// bulk-load header with a wrong difficulty must mark hvmMigrationBtcDiffRejectMeter yet NOT halt the rebuild
// (advisory only — the migration's sole forged-full-node detection surface). TestMigrate_SuccessRebuildsAndRetires
// covers the PoW-reject meter being advisory-but-non-halting; this covers the distinct contextual BtcDiffReject
// branch, killing a mutant that turns that observe into a halt or drops the meter mark. Synthetic children are
// sized just past the enforce floor so the contextual suffix is non-empty.
func TestMigrate_SuccessMarksBtcDiffRejectMeter(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: builds a synthetic chain past the mainnet enforce floor")
	}
	ctx := context.Background()
	raw, err := hex.DecodeString(vm.MainnetHvmGenesisHeader)
	require.NoError(t, err)
	var mainnetGen wire.BlockHeader
	require.NoError(t, mainnetGen.Deserialize(bytes.NewReader(raw)))

	clearance, err := vm.BTCFloorClearanceForNetwork("mainnet")
	require.NoError(t, err)
	enforceFloor := btcSnapEnforceFloor(vm.MainnetHvmGenesisHeight, clearance)
	// N children (heights genesis+1..genesis+N); the LAST few sit above the enforce floor so the contextual
	// observe runs on them. badIdx is the last child, given a wrong (non-inherited, non-boundary) difficulty.
	n := int(enforceFloor-vm.MainnetHvmGenesisHeight) + 4
	require.Greater(t, vm.MainnetHvmGenesisHeight+uint64(n), enforceFloor, "the top children must clear the enforce floor")

	children := make([]*wire.BlockHeader, n)
	prev := &mainnetGen
	for i := 0; i < n; i++ {
		bits := mainnetGen.Bits
		if i == n-1 {
			bits = 0x1d00fffe // one notch off the inherited difficulty at a non-boundary height -> ErrUnexpectedDifficulty
		}
		h := &wire.BlockHeader{Version: prev.Version, PrevBlock: prev.BlockHash(), MerkleRoot: mainnetGen.MerkleRoot,
			Timestamp: prev.Timestamp.Add(time.Duration(i+1) * 10 * time.Minute), Bits: bits, Nonce: uint32(i + 1)}
		children[i] = h
		prev = h
	}
	require.NotEqual(t, uint64(0), (vm.MainnetHvmGenesisHeight+uint64(n))%2016, "the wrong-diff child must NOT land on a retarget boundary (so the expected diff is the inherited value)")

	newSrv := func(home, network string, stateId [32]byte) *tbc.Server {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = &mainnetGen
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
		cfg.Network = network
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		_, _, _, _, addErr := srv.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: children}, stateId[:])
		require.NoError(t, addErr)
		return srv
	}

	_, _, bc, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
	require.NoError(t, err)
	defer bc.Stop()
	S := [32]byte(bc.CurrentBlock().Hash()) // canonical -> catch-up no-op; isolates the observe assertion

	home := t.TempDir()
	full := newSrv(t.TempDir(), "mainnet", [32]byte{0x01})
	defer func() { _ = full.ExternalHeaderTearDown() }()
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	vm.TBCFullNode, vm.TBCFullNodeConfig = full, &tbc.Config{Network: "mainnet"}
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	legacy := newSrv(home, "testnet3", S)
	require.NoError(t, legacy.ExternalHeaderTearDown())

	cfg := &tbc.Config{Network: "mainnet", LevelDBHome: home, EffectiveGenesisBlock: &mainnetGen, GenesisHeightOffset: vm.MainnetHvmGenesisHeight, ExternalHeaderMode: true}
	rejectBefore := hvmMigrationBtcDiffRejectMeter.Snapshot().Count()
	compBefore := hvmMigrationCompletedMeter.Snapshot().Count()
	handled := bc.maybeMigrateHvmHeaderNode(cfg)
	t.Cleanup(func() {
		if bc.tbcHeaderNode != nil {
			_ = bc.tbcHeaderNode.ExternalHeaderTearDown()
		}
	})
	require.True(t, handled, "the contextual observe is advisory: the migration must still succeed")
	require.Equal(t, rejectBefore+1, hvmMigrationBtcDiffRejectMeter.Snapshot().Count(),
		"the wrong-difficulty bulk-load header must mark the contextual BtcDiffReject meter exactly once")
	require.Equal(t, compBefore+1, hvmMigrationCompletedMeter.Snapshot().Count(), "the migration still completes")
}

// TestReadLegacyStoreTS_DoesNotMutateOnDiskVersion pins the downgrade-safety invariant: the guard-free read
// uses SetUpgradeOpen(true) precisely so it does NOT run heminetwork's in-place v2/v3/v4 upgrade ladder (which would
// REWRITE the store and bump its version, bricking the case where an OLD binary reads the legacy store after a
// deferred boot). Write a deliberately-LOW (but valid) on-disk version, run the guard-free read, and assert the
// version is UNCHANGED — if SetUpgradeOpen were dropped/defaulted-false the upgrade ladder would bump it, and this
// test would catch the silent forward-only mutation.
func TestReadLegacyStoreTS_DoesNotMutateOnDiskVersion(t *testing.T) {
	ctx := context.Background()
	home := t.TempDir()
	seedTbcHeaderStore(t, ctx, home, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, true)

	// Force the on-disk version to the FLOOR (a legitimate older on-disk format). An upgrade ladder, if it ran,
	// would bump this; SetUpgradeOpen must leave it exactly as written.
	low := make([]byte, 8)
	binary.BigEndian.PutUint64(low, uint64(ldbMinSupportedVersion))
	dbw := openStoreGuardFree(t, ctx, home, "testnet3")
	require.NoError(t, dbw.MetadataPut(ctx, []byte("version"), low))
	require.NoError(t, dbw.Close())

	readVersion := func() []byte {
		db := openStoreGuardFree(t, ctx, home, "testnet3")
		v, err := db.MetadataGet(ctx, []byte("version"))
		require.NoError(t, err)
		require.NoError(t, db.Close())
		return v
	}
	before := readVersion()
	require.Equal(t, low, before, "precondition: the on-disk version was set to the floor")

	// The guard-free read must succeed AND leave the on-disk format untouched.
	_, err := readLegacyStoreTS(ctx, home, "testnet3")
	require.NoError(t, err, "a floor-version store must read cleanly under the guard-free path")

	after := readVersion()
	require.True(t, bytes.Equal(before, after),
		"readLegacyStoreTS must NOT mutate the on-disk version (SetUpgradeOpen suppresses the upgrade ladder; downgrade safety)")
	require.Equal(t, uint64(ldbMinSupportedVersion), binary.BigEndian.Uint64(after), "the version must remain at the floor it was written to")
}

// TestMigrate_MeterLifecycleConservation pins the meter LIFECYCLE invariant across a multi-call orchestration
// sequence: every triggered migration ends in exactly one terminal (deferred | completed | failed), so
// triggered == deferred + completed + failed. Each terminal is otherwise tested only as an isolated +1 delta; no
// test asserts the conservation, nor that the SUCCESS arm leaves deferred/failed at 0. It also pins the
// in-progress GAUGE (not just the bool) returns to 0 on the success exit — the deferred Update(0) clear has no
// other positive teeth, so a mutant deleting it would leave a stuck "migration hung" gauge undetected.
func TestMigrate_MeterLifecycleConservation(t *testing.T) {
	if testing.Short() {
		t.Skip("heavy: builds a real lightweight TBC node + EVM chain for the success arm")
	}
	ctx := context.Background()
	raw, err := hex.DecodeString(vm.MainnetHvmGenesisHeader)
	require.NoError(t, err)
	var mainnetGen wire.BlockHeader
	require.NoError(t, mainnetGen.Deserialize(bytes.NewReader(raw)))
	child := &wire.BlockHeader{
		Version: mainnetGen.Version, PrevBlock: mainnetGen.BlockHash(), MerkleRoot: mainnetGen.MerkleRoot,
		Timestamp: mainnetGen.Timestamp.Add(10 * time.Minute), Bits: mainnetGen.Bits, Nonce: 1,
	}
	newSrv := func(home, network string, stateId [32]byte) *tbc.Server {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = &mainnetGen
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
		cfg.Network = network
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		_, _, _, _, addErr := srv.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{child}}, stateId[:])
		require.NoError(t, addErr)
		return srv
	}

	trigB := hvmMigrationTriggeredMeter.Snapshot().Count()
	defB := hvmMigrationDeferredMeter.Snapshot().Count()
	compB := hvmMigrationCompletedMeter.Snapshot().Count()
	failB := hvmMigrationFailedMeter.Snapshot().Count()

	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	// --- DEFER arm: a populated legacy store + an ABSENT full node -> triggered+1, deferred+1. ---
	vm.TBCFullNode, vm.TBCFullNodeConfig = nil, nil
	homeD := t.TempDir()
	seedTbcHeaderStore(t, ctx, homeD, "testnet3", testnet3HvmGenesisHeaderReplay, testnet3HvmGenesisHeightReplay, true)
	bcD := &BlockChain{ctx: ctx}
	require.False(t, bcD.maybeMigrateHvmHeaderNode(mainnetMigrateConfig(&mainnetGen, homeD)), "no full node -> defer")

	// --- SUCCESS arm: a ready full node + a progressed legacy store -> triggered+1, completed+1. ---
	_, _, bcS, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
	require.NoError(t, err)
	defer bcS.Stop()
	S := [32]byte(bcS.CurrentBlock().Hash())
	full := newSrv(t.TempDir(), "mainnet", [32]byte{0x01})
	defer func() { _ = full.ExternalHeaderTearDown() }()
	vm.TBCFullNode, vm.TBCFullNodeConfig = full, &tbc.Config{Network: "mainnet"}
	homeS := t.TempDir()
	legacy := newSrv(homeS, "testnet3", S)
	require.NoError(t, legacy.ExternalHeaderTearDown())
	require.True(t, bcS.maybeMigrateHvmHeaderNode(mainnetMigrateConfig(&mainnetGen, homeS)), "ready full node -> migrate")
	t.Cleanup(func() {
		if bcS.tbcHeaderNode != nil {
			_ = bcS.tbcHeaderNode.ExternalHeaderTearDown()
		}
	})

	// GAUGE teeth: the in-progress gauge (not just the bool) must return to 0 on the success exit.
	require.Equal(t, int64(0), hvmMigrationInProgressGauge.Snapshot().Value(), "the in-progress gauge must return to 0 after a successful migration")
	require.False(t, bcS.hvmMigrationInProgress, "the in-progress bool must be cleared (consistent with the gauge)")

	// CONSERVATION: triggered == deferred + completed + failed across the two terminals.
	trig := hvmMigrationTriggeredMeter.Snapshot().Count() - trigB
	def := hvmMigrationDeferredMeter.Snapshot().Count() - defB
	comp := hvmMigrationCompletedMeter.Snapshot().Count() - compB
	fail := hvmMigrationFailedMeter.Snapshot().Count() - failB
	require.Equal(t, int64(2), trig, "two orchestration calls triggered")
	require.Equal(t, int64(1), def, "exactly one deferred terminal")
	require.Equal(t, int64(1), comp, "exactly one completed terminal")
	require.Equal(t, int64(0), fail, "no crit/failed terminal on these paths")
	require.Equal(t, trig, def+comp+fail, "conservation: every triggered migration ends in exactly one terminal state")
}

// TestMaybeMigrate_NonTriggeringDoesNotMarkTriggered is the negative control for the migration-triggered meter:
// a non-triggering config (testnet3, which canonicalBTCNetwork maps to non-mainnet) must return false from
// maybeMigrateHvmHeaderNode BEFORE the hvmMigrationTriggeredMeter.Mark(1), leaving the meter UNCHANGED. The other
// migration tests only drive TRIGGERING (mainnet) configs, so an always-increment mutant (Mark moved before the
// hvmMigrationNeeded guard) survives them. No legacy store needed; returns at the network guard.
func TestMaybeMigrate_NonTriggeringDoesNotMarkTriggered(t *testing.T) {
	ctx := context.Background()
	cfg := &tbc.Config{Network: "testnet3", LevelDBHome: t.TempDir()}
	bc := &BlockChain{ctx: ctx}

	trigBefore := hvmMigrationTriggeredMeter.Snapshot().Count()
	handled := bc.maybeMigrateHvmHeaderNode(cfg)
	require.False(t, handled, "a non-triggering (testnet3) config must not be handled by migration")
	require.Equal(t, trigBefore, hvmMigrationTriggeredMeter.Snapshot().Count(),
		"the triggered meter must NOT increment for a non-triggering config (negative control)")
}

// DEFER-branch coverage for migrateHvmHeaderNode. The routine has several "leave everything untouched and boot on
// the legacy store" exits not reached by the other migrate tests:
//
//   - the full-node identity guard (absent / wrong-network embedded full node);
//   - the legacy-store-at-genesis exit (the recorded EVM state-id is still the genesis marker);
//   - the gather-not-ready exit (the mainnet full node lacks the committed tip T or its ancestry).
//
// Each must report not-handled, flip config.Network back to testnet3 (so the caller boots on the legacy store
// unenforced), and touch NO dirs. A lightweight tbc.Server stands in for the full node — no real Bitcoin full node
// or chaindata involved.
func decodeMainnetGenesisHeader(t *testing.T) *wire.BlockHeader {
	t.Helper()
	raw, err := hex.DecodeString(vm.MainnetHvmGenesisHeader)
	require.NoError(t, err)
	var h wire.BlockHeader
	require.NoError(t, h.Deserialize(bytes.NewReader(raw)))
	return &h
}

// mainnetMigrateConfig is the config a migrating mainnet node carries: the canonical mainnet effective-genesis pair
// (so the genesis weld passes) plus the legacy store's home.
func mainnetMigrateConfig(gen *wire.BlockHeader, home string) *tbc.Config {
	return &tbc.Config{
		Network: "mainnet", LevelDBHome: home,
		EffectiveGenesisBlock: gen, GenesisHeightOffset: vm.MainnetHvmGenesisHeight, ExternalHeaderMode: true,
	}
}

// TestMigrate_DefersWhenFullNodeAbsentOrWrongNetwork pins the full-node identity guard: the routine must DEFER
// (never walk the wrong index / nil-deref) when the embedded full node is absent, or present but configured for a
// non-mainnet network. Both arms defer BEFORE reading the legacy store, so no store or chain is needed.
func TestMigrate_DefersWhenFullNodeAbsentOrWrongNetwork(t *testing.T) {
	gen := decodeMainnetGenesisHeader(t)
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	t.Run("absent", func(t *testing.T) {
		vm.TBCFullNode, vm.TBCFullNodeConfig = nil, nil
		bc := &BlockChain{ctx: context.Background()}
		cfg := mainnetMigrateConfig(gen, t.TempDir())
		require.False(t, bc.migrateHvmHeaderNode(cfg), "an absent full node must DEFER, not migrate")
		require.Equal(t, "testnet3", cfg.Network, "defer flips Network back to testnet3")
	})

	t.Run("wrong-network", func(t *testing.T) {
		// A non-nil full node configured for testnet3 (not mainnet) must defer on the third guard clause; the
		// dummy server is never dereferenced — the routine returns at the guard before any gather.
		vm.TBCFullNode = &tbc.Server{}
		vm.TBCFullNodeConfig = &tbc.Config{Network: "testnet3"}
		bc := &BlockChain{ctx: context.Background()}
		cfg := mainnetMigrateConfig(gen, t.TempDir())
		require.False(t, bc.migrateHvmHeaderNode(cfg), "a non-mainnet full node must DEFER")
		require.Equal(t, "testnet3", cfg.Network, "defer flips Network back to testnet3")
	})
}

// TestMigrate_DefersWhenLegacyStoreAtGenesis pins the at-genesis exit: a legacy store whose recorded EVM
// upstream-state-id is still the genesis marker (atGenesis) has no committed state to migrate, so the routine must
// DEFER to a normal boot, leaving the legacy store untouched and creating no mainnet store.
func TestMigrate_DefersWhenLegacyStoreAtGenesis(t *testing.T) {
	if testing.Short() {
		t.Skip("seeds a real lightweight legacy store")
	}
	ctx := context.Background()
	gen := decodeMainnetGenesisHeader(t)
	home := t.TempDir()

	// A legacy testnet3-labeled store seated at the mainnet genesis with the DEFAULT (genesis) state-id -> atGenesis.
	seedTbcHeaderStore(t, ctx, home, "testnet3", vm.MainnetHvmGenesisHeader, vm.MainnetHvmGenesisHeight, false /* keep genesis state-id */)

	// Make the full-node guard PASS (so the routine reaches the atGenesis check); the atGenesis defer happens
	// before any gather, so the dummy server is never dereferenced.
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	vm.TBCFullNode, vm.TBCFullNodeConfig = &tbc.Server{}, &tbc.Config{Network: "mainnet"}
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	bc := &BlockChain{ctx: ctx}
	cfg := mainnetMigrateConfig(gen, home)
	require.False(t, bc.migrateHvmHeaderNode(cfg), "an at-genesis legacy store has nothing to migrate -> DEFER")
	require.Equal(t, "testnet3", cfg.Network, "the at-genesis defer must flip Network back to testnet3")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be untouched on the at-genesis defer")
	require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "no mainnet store may be created on the at-genesis defer")

	// Lock release: the guard-free read must have closed the legacy store so the normal boot can re-open it.
	reopened := openStoreGuardFree(t, ctx, home, "testnet3")
	require.NoError(t, reopened.Close(), "the legacy store must be re-openable after the at-genesis defer (the read released its lock)")
}

// TestMigrate_DefersWhenFullNodeNotReady pins the gather-not-ready exit: a readable, progressed legacy store
// (committed tip T = a child header, canonical EVM state-id) but a mainnet full node that does NOT hold T's
// ancestry must DEFER without touching any dir. The pure gather geometry is covered by TestGatherHeadersBackToGenesis;
// this pins that the routine maps a gather miss to deferHvmMigration. The full node is a lightweight genesis-only
// store (no real chaindata).
func TestMigrate_DefersWhenFullNodeNotReady(t *testing.T) {
	if testing.Short() {
		t.Skip("builds a chain + two real lightweight stores")
	}
	ctx := context.Background()
	gen := decodeMainnetGenesisHeader(t)
	child := &wire.BlockHeader{
		Version: gen.Version, PrevBlock: gen.BlockHash(), MerkleRoot: gen.MerkleRoot,
		Timestamp: gen.Timestamp.Add(10 * time.Minute), Bits: gen.Bits, Nonce: 1,
	}

	newSrv := func(home, network string, withChild bool, stateId [32]byte) *tbc.Server {
		cfg := tbc.NewDefaultConfig()
		cfg.ExternalHeaderMode = true
		cfg.EffectiveGenesisBlock = gen
		cfg.GenesisHeightOffset = vm.MainnetHvmGenesisHeight
		cfg.LevelDBHome = home
		cfg.BlockheaderCacheSize, cfg.BlockCacheSize = "0", "0"
		cfg.AutoIndex, cfg.BlockSanity, cfg.MaxCachedTxs, cfg.MempoolEnabled = false, false, 0, false
		cfg.Network = network
		srv, e := tbc.NewServer(cfg)
		require.NoError(t, e)
		require.NoError(t, srv.ExternalHeaderSetup(ctx, hVMGenesisUpstreamId[:]))
		if withChild {
			_, _, _, _, addErr := srv.AddExternalHeaders(ctx, &wire.MsgHeaders{Headers: []*wire.BlockHeader{child}}, stateId[:])
			require.NoError(t, addErr)
		} else {
			require.NoError(t, srv.SetUpstreamStateId(ctx, stateId))
		}
		return srv
	}

	_, _, bc, err := newCanonical(ethash.NewFaker(), 5, true, rawdb.HashScheme)
	require.NoError(t, err)
	defer bc.Stop()
	S := [32]byte(bc.CurrentBlock().Hash()) // canonical -> passes legacyStateIdIsCanonical, reaches the gather

	// The mainnet full node holds ONLY the genesis (no child) -> the gather from T (=child) misses -> not ready.
	full := newSrv(t.TempDir(), "mainnet", false, [32]byte{0x01})
	defer func() { _ = full.ExternalHeaderTearDown() }()
	prevFN, prevCfg := vm.TBCFullNode, vm.TBCFullNodeConfig
	vm.TBCFullNode, vm.TBCFullNodeConfig = full, &tbc.Config{Network: "mainnet"}
	defer func() { vm.TBCFullNode, vm.TBCFullNodeConfig = prevFN, prevCfg }()

	// The legacy store HAS progressed to T=child with a canonical state-id S.
	home := t.TempDir()
	legacy := newSrv(home, "testnet3", true, S)
	require.NoError(t, legacy.ExternalHeaderTearDown())

	cfg := mainnetMigrateConfig(gen, home)
	require.False(t, bc.migrateHvmHeaderNode(cfg), "a full node missing T's ancestry must DEFER")
	require.Equal(t, "testnet3", cfg.Network, "the gather-not-ready defer must flip Network back to testnet3")
	require.True(t, dirHasEntries(hvmHeaderStoreDir(home, "testnet3")), "the legacy store must be untouched on the gather-not-ready defer")
	require.False(t, dirHasEntries(hvmHeaderStoreDir(home, "mainnet")), "no mainnet store may be created on the gather-not-ready defer")

	reopened := openStoreGuardFree(t, ctx, home, "testnet3")
	require.NoError(t, reopened.Close(), "the legacy store must be re-openable after a gather-not-ready defer")
}

// ---------------------------------------------------------------------------
// (a) FuzzClassifyHvmGenesisPairing — never panics; result is exactly one of 3
//     enum values; for a checkpointed network an exact match is Canonical and a
//     single-field match is Mismatch.
// ---------------------------------------------------------------------------

func FuzzClassifyHvmGenesisPairing(f *testing.F) {
	// Seeds: real checkpointed nets, the empty/whitespace net, a malformed hash.
	f.Add("mainnet", vm.MainnetHvmGenesisHeight, vm.MainnetHvmGenesisHash)
	f.Add("testnet3", uint64(3522419), "000000000000000096c98151accc5ee217d7cc4ff1e59a3d91e4c9365c4ea144")
	f.Add("upgradetest", uint64(3522419), "000000000000000096c98151accc5ee217d7cc4ff1e59a3d91e4c9365c4ea144")
	f.Add("", uint64(0), "")
	f.Add("   ", uint64(883092), "zzzz")
	f.Add("mainnet", vm.MainnetHvmGenesisHeight, "deadbeef") // height matches, hash diverges
	f.Add("mainnet", uint64(1), vm.MainnetHvmGenesisHash)    // hash matches, height diverges
	f.Add("localnet", uint64(0), "")

	f.Fuzz(func(t *testing.T, network string, height uint64, hash string) {
		got := classifyHvmGenesisPairing(network, height, hash)

		// INVARIANT 1: exactly one of the three enum values.
		switch got {
		case hvmGenesisPairingCanonical, hvmGenesisPairingCustom, hvmGenesisPairingMismatch:
			// ok
		default:
			t.Fatalf("classifyHvmGenesisPairing returned out-of-range value %d for (%q,%d,%q)", got, network, height, hash)
		}

		// INVARIANT 2: for a checkpointed network, exact match => Canonical, single-field match => Mismatch.
		cps := hvmGenesisCheckpoints[network]
		anyExact, anyHeightOnly, anyHashOnly := false, false, false
		for _, cp := range cps {
			hEq, sEq := cp.height == height, cp.hash == hash
			switch {
			case hEq && sEq:
				anyExact = true
			case hEq && !sEq:
				anyHeightOnly = true
			case !hEq && sEq:
				anyHashOnly = true
			}
		}
		if anyExact && got != hvmGenesisPairingCanonical {
			t.Fatalf("exact checkpoint match must be Canonical, got %d for (%q,%d,%q)", got, network, height, hash)
		}
		// A single-field match with NO exact match must be Mismatch.
		if !anyExact && (anyHeightOnly || anyHashOnly) && got != hvmGenesisPairingMismatch {
			t.Fatalf("single-field checkpoint match (no exact) must be Mismatch, got %d for (%q,%d,%q)", got, network, height, hash)
		}
		// No checkpoint touched at all => Custom.
		if !anyExact && !anyHeightOnly && !anyHashOnly && got != hvmGenesisPairingCustom {
			t.Fatalf("no-checkpoint-touch must be Custom, got %d for (%q,%d,%q)", got, network, height, hash)
		}

		// INVARIANT 3: IsCanonicalHvmGenesisPairing agrees with the classifier.
		if IsCanonicalHvmGenesisPairing(network, height, hash) != (got == hvmGenesisPairingCanonical) {
			t.Fatalf("IsCanonicalHvmGenesisPairing disagrees with classifier for (%q,%d,%q)", network, height, hash)
		}
	})
}

// ---------------------------------------------------------------------------
// (b) FuzzCanonicalBTCNetwork — idempotent; only "upgradetest" changes.
// ---------------------------------------------------------------------------

func FuzzCanonicalBTCNetwork(f *testing.F) {
	f.Add("mainnet")
	f.Add("testnet3")
	f.Add("upgradetest")
	f.Add("localnet")
	f.Add("")
	f.Add("UpgradeTest") // case sensitivity probe
	f.Add(" upgradetest ")

	f.Fuzz(func(t *testing.T, network string) {
		c := canonicalBTCNetwork(network)

		// INVARIANT 1: idempotent.
		if cc := canonicalBTCNetwork(c); cc != c {
			t.Fatalf("canonicalBTCNetwork not idempotent: canonical(%q)=%q, canonical(canonical)=%q", network, c, cc)
		}

		// INVARIANT 2: only "upgradetest" changes; everything else is identity.
		if network == "upgradetest" {
			if c != "testnet3" {
				t.Fatalf("upgradetest must canonicalize to testnet3, got %q", c)
			}
		} else if c != network {
			t.Fatalf("canonicalBTCNetwork(%q) changed a non-upgradetest network to %q", network, c)
		}
	})
}

// ---------------------------------------------------------------------------
// (c) Property test for gatherHeadersBackToGenesis over randomly-linked fake
//     chains (incl. cycles): termination + ascending + genesis-exclusion.
//     The seed corpus drives both adversarial topologies and a randomized loop.
// ---------------------------------------------------------------------------

// adversarialLookup serves arbitrary, possibly-malicious header graphs (cycles,
// dead ends, non-descending heights) to stress gatherHeadersBackToGenesis.
type adversarialLookup struct {
	byHash map[chainhash.Hash]*wire.BlockHeader
	height map[chainhash.Hash]uint64
}

func (a *adversarialLookup) BlockHeaderByHash(_ context.Context, h chainhash.Hash) (*wire.BlockHeader, uint64, error) {
	hdr, ok := a.byHash[h]
	if !ok {
		return nil, 0, errNotFoundFuzz
	}
	return hdr, a.height[h], nil
}

var errNotFoundFuzz = &notFoundErr{}

type notFoundErr struct{}

func (e *notFoundErr) Error() string { return "not found" }

// buildGraphFromSeed deterministically builds a header graph from a byte seed by
// linking each header's PrevBlock to an arbitrary other header (possibly itself,
// possibly forming cycles), with arbitrary (possibly non-descending) heights.
func buildGraphFromSeed(seed []byte, n int, genesisHeight uint64) (*adversarialLookup, []chainhash.Hash, chainhash.Hash) {
	if n < 1 {
		n = 1
	}
	if n > 64 {
		n = 64
	}
	lk := &adversarialLookup{byHash: map[chainhash.Hash]*wire.BlockHeader{}, height: map[chainhash.Hash]uint64{}}
	hdrs := make([]*wire.BlockHeader, n)
	hashes := make([]chainhash.Hash, n)
	for i := 0; i < n; i++ {
		hdrs[i] = &wire.BlockHeader{Version: 1, Bits: 0x207fffff, Nonce: uint32(i)*7919 + 1}
	}
	// Link PrevBlock by seed bytes (allows cycles, self-loops, forward links).
	for i := 0; i < n; i++ {
		var sel byte
		if len(seed) > 0 {
			sel = seed[i%len(seed)]
		}
		target := int(sel) % n
		hdrs[i].PrevBlock = hdrs[target].BlockHash()
	}
	for i := 0; i < n; i++ {
		hh := hdrs[i].BlockHash()
		hashes[i] = hh
		lk.byHash[hh] = hdrs[i]
		// Arbitrary heights from the seed — may be non-descending along PrevBlock links.
		var hsel byte
		if len(seed) > 1 {
			hsel = seed[(i*3+1)%len(seed)]
		}
		lk.height[hh] = genesisHeight + uint64(hsel)
	}
	// Pick an arbitrary genesis hash NOT in the graph (so the only termination is
	// via the height-floor / cycle guards), or in-graph if seed says so.
	genesis := chainhash.Hash{0xde, 0xad}
	if len(seed) > 2 && seed[2]&1 == 1 && n > 0 {
		genesis = hashes[int(seed[0])%n]
	}
	return lk, hashes, genesis
}

func FuzzGatherHeadersBackToGenesis(f *testing.F) {
	f.Add([]byte{1, 2, 3, 4}, 8)
	f.Add([]byte{0, 0, 0, 0}, 4) // all link to header 0 -> potential self/cycle
	f.Add([]byte{255, 1, 1}, 16) // genesis-in-graph probe
	f.Add([]byte{}, 1)           // single node, links to self -> cycle
	f.Add([]byte{7, 7, 7, 7, 7}, 32)

	const gh = uint64(883092)

	f.Fuzz(func(t *testing.T, seed []byte, n int) {
		lk, hashes, genesis := buildGraphFromSeed(seed, n, gh)

		// Pick a tip from the seed.
		tip := genesis
		if len(hashes) > 0 {
			idx := 0
			if len(seed) > 0 {
				idx = int(seed[len(seed)-1]) % len(hashes)
			}
			tip = hashes[idx]
		}

		// INVARIANT (termination): this call MUST return. The test harness itself
		// catches a hang via the test timeout; we rely on the cycle/height guards.
		got, ok := gatherHeadersBackToGenesis(context.Background(), lk, tip, genesis, gh)

		if !ok {
			// Defer path: ok=false MUST come with an empty slice. Callers treat ok=false as defer and
			// must never consume a partial slice; returning partial headers here would pass silently.
			if len(got) != 0 {
				t.Fatalf("ok=false (defer) must return an empty slice, got %d headers", len(got))
			}
			return
		}

		// INVARIANT (genesis-exclusion): genesis hash never appears in the result.
		for i, h := range got {
			hh := h.BlockHash()
			if hh == genesis {
				t.Fatalf("genesis hash present in gathered result at index %d", i)
			}
		}

		// INVARIANT (ascending by height): each successive header strictly ascends.
		for i := 1; i < len(got); i++ {
			prevH := lk.height[got[i-1].BlockHash()]
			curH := lk.height[got[i].BlockHash()]
			if curH <= prevH {
				t.Fatalf("gathered headers not strictly ascending: idx %d height %d <= idx %d height %d", i, curH, i-1, prevH)
			}
		}

		// INVARIANT (all above floor): every gathered header is strictly above genesisHeight.
		for i, h := range got {
			if lk.height[h.BlockHash()] <= gh {
				t.Fatalf("gathered header at idx %d has height %d <= genesisHeight %d", i, lk.height[h.BlockHash()], gh)
			}
		}
	})
}

// Sanity: decode helper used by seeds (keeps imports honest if seeds change).
var _ = hex.DecodeString

// Integration matrix for the legacy "mainnet-as-testnet3" hVM migration. These exercise the I/O paths the unit
// tests cannot (the guard-free LevelDB read, the full-node canonical walk, the bulk fill, the rename retirement,
// the crash windows). They need real infrastructure — a mainnet TBC full node holding the committed Bitcoin chain,
// a populated legacy <home>/testnet3/ header store, and an EVM chain at a known tip — gated behind HVM_MIGRATION_IT=1
// plus the fixtures HVM_MIGRATION_FULLNODE_DATADIR and HVM_MIGRATION_LEGACY_HOME. The pure decision logic is
// covered by the unit tests in blockchain_hvm_migration_test.go.
//
// These bodies have no assertions yet, so requireMigrationInfra SKIPs unconditionally — even with HVM_MIGRATION_IT
// set — to prevent an empty body reporting a vacuous PASS that masks the missing end-to-end verification. Each test
// must replace this call with a real body (and its own infra checks) before it can run; the per-test comments state
// the convergence that body must assert.
func requireMigrationInfra(t *testing.T) {
	t.Helper()
	if os.Getenv("HVM_MIGRATION_IT") == "" {
		t.Skip("integration matrix opt-in: set HVM_MIGRATION_IT=1 (note: these tests have no body yet)")
	}
	t.Skip("this test has no body yet and must NOT report a vacuous PASS. " +
		"Implement the documented assertions (a seeded legacy leveldb store makes most of these buildable without a P2P full node) before relying on it.")
}

// Full-sync legacy node: testnet3/ store at the EVM tip, full node holds T's ancestry -> migrate.
// Assert: <home>/mainnet/ tip == T, upstream-state-id == S, hvmDiffEnforceable == true, and <home>/testnet3/
// renamed to <home>/testnet3.migrated-<S>/.
func TestHvmMigration_FullSyncLegacy_Migrates(t *testing.T) { requireMigrationInfra(t) }

// Snap-synced legacy node (no pre-pivot EVM history): migrate via the guard-free T read + full-node fill, then
// the S_old-anchored forward catch-up. Assert it does NOT call performFullHvmHeaderStateRestore (which would
// crit on the missing deep bodies) and converges to tip == T.
func TestHvmMigration_SnapLegacy_MigratesWithoutGenesisRestore(t *testing.T) {
	requireMigrationInfra(t)
}

// Lagged legacy store (S_old < EVM tip after an unclean shutdown): after the fill, the forward catch-up walks
// [S_old+1 .. tip]. Assert the migrated store's state-id == current EVM tip (not the stale S_old).
func TestHvmMigration_LaggedLegacyStore_CatchesUpToTip(t *testing.T) { requireMigrationInfra(t) }

// Full node behind (does not yet hold T or its ancestry): DEFER. Assert no dir is touched, the node boots on
// the legacy testnet3/ store with hvmDiffEnforceable == false, and a re-run migrates once the full node catches up.
func TestHvmMigration_FullNodeBehind_DefersThenMigrates(t *testing.T) { requireMigrationInfra(t) }

// Genuine testnet3 / upgradetest / localnet node: NOT migrated, no crit, normal boot.
func TestHvmMigration_GenuineNonMainnet_NotMigrated(t *testing.T) { requireMigrationInfra(t) }

// Crash-safety windows: kill after each of {mainnet/ removed; init-before-fill; mid-fill torn;
// fill+state-id committed before rename; after rename} and assert the per-window convergence direction
// (re-migrate vs idempotent-rename vs steady-state) via the upstream-state-id witness.
func TestHvmMigration_CrashWindows_Converge(t *testing.T) { requireMigrationInfra(t) }

// A deferred node must BOOT (not crit) despite the guard-free read having opened the legacy store: the read
// fully closes before init re-opens the same dir (LOCK SAFETY).
func TestHvmMigration_DeferredNode_BootsNoLockCrit(t *testing.T) { requireMigrationInfra(t) }
