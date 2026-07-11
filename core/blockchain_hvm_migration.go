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

// Automatic, opaque migration of a legacy "mainnet-as-testnet3" hVM header store to a correct per-network
// mainnet store. It runs at the TOP of SetupHvmHeaderNode, before initHvmHeaderNode opens any dir:
//
//   - DETECT: only when the node is now configured for mainnet (canonicalBTCNetwork=="mainnet") and a
//     legacy <home>/testnet3/ store with progressed state exists and <home>/mainnet/ is absent or invalid.
//   - MIGRATE-OR-DEFER: read the legacy store's committed BTC tip T and upstream-state-id S guard-free
//     (a direct LevelDB open, fully closed before returning), then confirm the mainnet full node holds T and
//     its full ancestry to the mainnet effective genesis. If not ready, DEFER: mutate config.Network back to
//     "testnet3" and fall through to a normal boot on the untouched legacy store (retry next start).
//   - REBUILD: scoped-delete any stale <home>/mainnet/, init a fresh mainnet node at the mainnet
//     genesis, bulk-add the full node's canonical headers [genesis+1 .. T] with upstream-state-id S (the
//     last-write crash-safety witness), verify tip==T && state-id==S, forward-catch-up S->EVM-tip if the
//     legacy store lagged, then rename <home>/testnet3/ -> <home>/testnet3.migrated-<S>/.
//
// Behavior notes:
//   - updateFullTBCToLightweight() is intentionally NOT called here; the full-node indexer sync is deferred
//     to the first normal import (mirrors performFullHvmHeaderStateRestore, which also does not drive it).
//   - Older testnet3.migrated-* backups are never reaped; they accumulate only across repeated
//     migrate/rollback cycles, which are rare.
//   - The forward catch-up's final state-id is not re-verified against the EVM tip; a catch-up shortfall is
//     logged (NON-fatal) and reconciled by normal import.

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"slices"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/database"
	"github.com/hemilabs/heminetwork/database/tbcd/level"
	"github.com/hemilabs/heminetwork/service/tbc"
	"github.com/syndtr/goleveldb/leveldb"
	"github.com/syndtr/goleveldb/leveldb/opt"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/log"
)

// upstreamStateIdMetaKey mirrors the heminetwork tbc package's internal upstream-state-id metadata key. The
// guard-free read bypasses tbc.Server, so it must reference the raw LevelDB key directly.
var upstreamStateIdMetaKey = []byte("upstreamstateid")

// ldbMaxSupportedVersion mirrors heminetwork database/tbcd/level ldbVersion (currently 4): the highest on-disk
// store version this binary can decode. The guard-free read (which suppresses the upgrade ladder) re-imposes
// this ceiling so a newer-format store is rejected rather than misdecoded. Bump in lockstep with heminetwork.
const ldbMaxSupportedVersion = 4

// ldbMinSupportedVersion is the lowest valid heminetwork on-disk store version (versions are 1-based; v1 is the
// first format). The guard-free read (SetUpgradeOpen) bypasses heminetwork New()'s own "invalid version" lower
// bound, so a torn/zeroed/garbage version key could read back as 0 (or other sub-floor value) and slip past a
// ceiling-only check; re-impose the floor too so a corrupt version fails closed symmetrically.
const ldbMinSupportedVersion = 1

// errLegacyStoreEmpty marks a store that opened but has NO best header (empty / torn — e.g. a crash during
// ExternalHeaderSetup). It is distinct from a lock/open failure: an empty mainnet store must RE-MIGRATE, while
// an unreadable (locked) store is kept conservatively. readLegacyStoreTS returns it wrapped; callers errors.Is.
var errLegacyStoreEmpty = errors.New("hVM header store opened but is empty/torn (no best header)")

// legacyStoreTS is the (T, S) read guard-free from the OLD testnet3 store: T is the committed Bitcoin
// tip at the EVM tip the store last recorded; S is that EVM tip hash (the upstream-state-id).
type legacyStoreTS struct {
	tipHeight uint64
	tipHash   chainhash.Hash
	stateId   [32]byte
	atGenesis bool // true if the store is still at its effective-genesis state-id (nothing to migrate)
}

// hvmHeaderStoreDir returns the on-disk store path TBC uses for a (home, network): <home>/<canonicalNet>.
func hvmHeaderStoreDir(levelDBHome, network string) string {
	return filepath.Join(levelDBHome, canonicalBTCNetwork(network))
}

// legacyStoreVersionKeyTorn reports whether the store's metadata "version" key exists but is shorter than 8 bytes.
// heminetwork's level.New / db.Version decode that key with binary.BigEndian.Uint64, which PANICS on a <8-byte
// value AFTER level.New has opened and locked the metadata leveldb; because the panic unwinds before level.New
// returns the handle, that goleveldb directory lock leaks for the process lifetime. readLegacyStoreTS probes this
// first and rejects a torn key BEFORE level.New, so the leak never happens for this corruption. We open the
// metadata leveldb READ-ONLY (a handle we own and immediately close) to read the key. ANY open/read failure
// returns false: those are not the torn-Uint64 panic (level.New handles them with a clean error) and we must not
// false-defer a healthy store that merely needs journal recovery (which a read-only open refuses). The directory
// and key names mirror heminetwork's database/level.MetadataDB ("metadata") and tbcd/level versionKey ("version").
func legacyStoreVersionKeyTorn(levelDBHome, network string) bool {
	mdb, err := leveldb.OpenFile(filepath.Join(hvmHeaderStoreDir(levelDBHome, network), "metadata"), &opt.Options{ReadOnly: true})
	if err != nil {
		return false
	}
	defer mdb.Close()
	v, err := mdb.Get([]byte("version"), nil)
	if err != nil {
		return false
	}
	return len(v) < 8
}

// markHvmMigrationFailed records the "failed" event: mark the failed meter and clear the in-progress gauge.
// Split out of migrationCrit so the side effect can be exercised WITHOUT log.Crit's os.Exit (the failed meter
// is otherwise only ever marked on a path that immediately terminates the process).
func markHvmMigrationFailed() {
	hvmMigrationFailedMeter.Mark(1)
	hvmMigrationInProgressGauge.Update(0)
}

// enterHvmMigrationRebuildWindow records the "in-progress" event: set the in-progress gauge to 1 and arm the
// in-window crit routing (bc.hvmMigrationInProgress) so a fatal init/apply crit during the committed rebuild
// routes through migrationCrit. Mirrors markHvmMigrationFailed; the caller (migrateHvmHeaderNode) installs the
// deferred clears for both.
func (bc *BlockChain) enterHvmMigrationRebuildWindow() {
	hvmMigrationInProgressGauge.Update(1)
	bc.hvmMigrationInProgress = true
}

// migrationCrit marks the failed meter ("failed" event) immediately before a fatal migration log.Crit, so
// at least one scrape/flush can capture the failure before the process exits. It also clears the in-progress
// gauge: log.Crit calls os.Exit, so the migrateHvmHeaderNode deferred Update(0) would never run,
// leaving the gauge stuck at 1.
func migrationCrit(msg string, ctx ...interface{}) {
	markHvmMigrationFailed()
	log.Crit(msg, ctx...)
}

// removeHvmHeaderNetworkDir is the shared network-scoped delete primitive: it removes ONLY
// <home>/<canonicalNet>, never the parent home, and never another network's sibling store.
func removeHvmHeaderNetworkDir(levelDBHome, network string) error {
	return os.RemoveAll(hvmHeaderStoreDir(levelDBHome, network))
}

// dirHasEntries reports whether a directory exists and is non-empty.
func dirHasEntries(dir string) bool {
	ents, err := os.ReadDir(dir)
	return err == nil && len(ents) > 0
}

// maybeMigrateHvmHeaderNode is the top-of-SetupHvmHeaderNode entry point. It returns true ("handled") only
// when it fully rebuilt and initialized bc.tbcHeaderNode for a migrated mainnet store — in which case the
// caller must NOT run the normal init/restore flow. It returns false when no migration is needed (normal
// boot) OR when it DEFERRED (having mutated config.Network back to "testnet3" so the caller boots normally on
// the untouched legacy store).
func (bc *BlockChain) maybeMigrateHvmHeaderNode(config *tbc.Config) (handled bool) {
	if !bc.hvmMigrationNeeded(config) {
		return false
	}
	hvmMigrationTriggeredMeter.Mark(1)
	log.Info("hVM header store migration: legacy testnet3 store detected on a mainnet-configured node; evaluating migrate-or-defer",
		"levelDBHome", config.LevelDBHome)
	return bc.migrateHvmHeaderNode(config)
}

// hvmMigrationNeeded implements migration detection.
func (bc *BlockChain) hvmMigrationNeeded(config *tbc.Config) bool {
	// Only the mainnet fleet migrates. Genuine testnet/upgradetest/localnet are excluded.
	if canonicalBTCNetwork(config.Network) != "mainnet" {
		return false
	}
	home := config.LevelDBHome
	// A legacy testnet3 store must exist with progressed (non-empty) state.
	if !dirHasEntries(hvmHeaderStoreDir(home, "testnet3")) {
		return false
	}
	// Classify an existing mainnet store. Only a DEFINITIVELY-migrated store (readable, non-genesis) lets us
	// retire the legacy fallback; an absent / torn / at-genesis store re-migrates; an UNREADABLE store is kept
	// conservatively BUT the legacy fallback is NOT retired (retiring the testnet3 fallback for a
	// store we cannot even open would destroy the only recoverable copy and the normal boot would then crit on
	// the unreadable mainnet store with nothing to fall back to).
	if dirHasEntries(hvmHeaderStoreDir(home, "mainnet")) {
		switch bc.existingMainnetStoreState(config) {
		case mainnetStoreValidMigrated:
			log.Info("hVM header store migration: a valid mainnet store already exists; normal boot will catch it up to tip")
			// Opportunistic retirement: a crash-before-rename leaves the legacy testnet3/ store
			// orphaned next to the valid mainnet store; this branch returns before migrateHvmHeaderNode so the
			// retirement step would otherwise never re-run. Safe to retire ONLY because the mainnet store is definitively migrated.
			bc.retireOrphanedLegacyStore(config)
			return false
		case mainnetStoreKeepUnreadable:
			// Conservatively keep the unreadable store AND keep the legacy fallback intact.
			return false
		case mainnetStoreReMigrate:
			// fall through to re-migrate
		default:
			// Fail-CLOSED: a future mainnetStoreState value must NOT silently fall through to the
			// destructive re-migrate below. Keep the existing store (non-destructive) until the new case is wired.
			log.Warn("hVM header store migration: unclassified mainnet store state; NOT re-migrating (fail-closed)")
			return false
		}
	}
	return true
}

// retireOrphanedLegacyStore retires a lingering <home>/testnet3/ that survived a crash-before-rename on an
// already-migrated node. Best-effort and non-fatal. Names the backup by the LEGACY testnet3 store's OWN
// upstream-state-id (re-read guard-free, closed before the rename) for parity with the retirement backup naming.
func (bc *BlockChain) retireOrphanedLegacyStore(config *tbc.Config) {
	home := config.LevelDBHome
	if !dirHasEntries(hvmHeaderStoreDir(home, "testnet3")) {
		return
	}
	// Name the backup by the LEGACY store's OWN state-id, matching the retirement path's
	// testnet3.migrated-<S> naming — not the mainnet store's (advanced) state-id, which would diverge from
	// retirement and make the backup harder to identify when rolling back by renaming it to testnet3/.
	ts, err := readLegacyStoreTS(bc.ctx, home, "testnet3")
	if err != nil {
		log.Warn("hVM header store migration: orphaned testnet3 store present but could not read its state-id to name the backup; leaving it", "err", err)
		return
	}
	log.Info("hVM header store migration: retiring an orphaned legacy testnet3 store left by a crash-before-rename")
	bc.retireLegacyTestnet3Store(home, ts.stateId)
}

// mainnetStoreState is the classification of an existing <home>/mainnet/ store.
type mainnetStoreState int

const (
	mainnetStoreReMigrate      mainnetStoreState = iota // torn / at-genesis: delete + rebuild
	mainnetStoreKeepUnreadable                          // could not open/read: keep conservatively, do NOT retire the fallback
	mainnetStoreValidMigrated                           // readable, non-genesis state-id: a completed migration
)

// existingMainnetStoreState reads the existing <home>/mainnet/ store and classifies it (with logging). It does
// NOT require the state-id be currently CANONICAL: a post-migration EVM reorg makes a valid store's state-id
// non-canonical, and the normal SetupHvmHeaderNode restore/reorg path reconciles that — re-migrating on a
// transient non-canonical state-id would destroy the valid store and rebuild from the staler legacy state-id.
func (bc *BlockChain) existingMainnetStoreState(config *tbc.Config) mainnetStoreState {
	ts, err := readLegacyStoreTS(bc.ctx, config.LevelDBHome, "mainnet")
	state := classifyMigratedMainnetStore(ts, err)
	switch state {
	case mainnetStoreReMigrate:
		if err != nil {
			log.Warn("hVM header store migration: existing mainnet store is empty/torn; re-migrating", "err", err)
		} else {
			log.Warn("hVM header store migration: existing mainnet store is at genesis (incomplete); re-migrating")
		}
	case mainnetStoreKeepUnreadable:
		log.Warn("hVM header store migration: existing mainnet store could not be probed; NOT re-migrating and KEEPING the legacy fallback (normal boot will open it and surface the cause)", "err", err)
	}
	return state
}

// classifyMigratedMainnetStore is the PURE classification of an existing <home>/mainnet/ store from a guard-free
// (ts, err) read. The branch polarity is destructive-delete sensitive: a flipped branch would silently DELETE a
// healthy store, KEEP a torn one and crit-loop the boot, or retire the fallback for an unreadable store.
//
//	(nil, errLegacyStoreEmpty)  -> ReMigrate     : empty/torn (e.g. crash during rebuild) must re-migrate, else the
//	                                               normal boot crit-loops on a headerless / state-id-less store.
//	(nil, any other error)      -> KeepUnreadable: lock / corruption / future version — conservative keep; the
//	                                               legacy fallback is NOT retired (it may be the only recoverable copy).
//	(atGenesis=true,  nil)      -> ReMigrate     : a fresh/empty store is not a completed migration.
//	(atGenesis=false, nil)      -> ValidMigrated : readable, non-genesis state-id = a completed migration.
func classifyMigratedMainnetStore(ts *legacyStoreTS, err error) mainnetStoreState {
	if err != nil {
		if errors.Is(err, errLegacyStoreEmpty) {
			return mainnetStoreReMigrate
		}
		return mainnetStoreKeepUnreadable
	}
	if ts.atGenesis {
		return mainnetStoreReMigrate
	}
	return mainnetStoreValidMigrated
}

// readLegacyStoreTS performs the guard-free read: open the store at <home>/<canonicalNet> DIRECTLY
// (bypassing tbc.Server, whose ExternalHeaderSetup re-validates the genesis pair and whose db handle is
// private), read its committed BTC tip and upstream-state-id, and FULLY CLOSE before returning. level.New
// takes an EXCLUSIVE goleveldb directory lock and is not read-only, so the handle must never outlive this
// function — otherwise the defer-fallthrough init or the rename of the SAME dir would ErrLocked-crit the
// node (LOCK SAFETY). The deferred Close fires at THIS function's return, before any caller re-opens.
func readLegacyStoreTS(ctx context.Context, levelDBHome, network string) (result *legacyStoreTS, retErr error) {
	// heminetwork's level.New (during the guard-free open) and db.Version read the on-disk version key with
	// binary.BigEndian.Uint64 and NO length check, so a TORN/SHORT (1-7 byte) version key PANICS. Recover any panic in
	// this function into the conservative version-read error (callers defer/keep-the-store on a read error) rather than
	// crashing the node boot. The panic is in level.New itself, before the version-value guards below, so a
	// function-level recover — not one around db.Version — is required.
	//
	// LIMITATION (heminetwork-internal, mainnet-path only): when level.New panics PART-WAY through open it has
	// ALREADY taken the goleveldb directory lock but never returns, so the `defer db.Close()` below never registers
	// and the lock leaks for the process lifetime. The panic is converted to a clean error here, but the normal boot
	// fall-through then re-opens the SAME dir and ErrLocked-crits — so a torn-version store does NOT "boot
	// unenforced"; the operator must remove or restore that store. This is unreachable on testnet3 nodes (migration
	// is gated on canonicalBTCNetwork=="mainnet", so a genuine testnet3 node never calls readLegacyStoreTS) and the
	// store is corrupt either way; a clean fix would pre-validate the version-key length with a lock-free raw read
	// BEFORE level.New.
	defer func() {
		if r := recover(); r != nil {
			result, retErr = nil, fmt.Errorf("read hVM header store at %s: version key is torn/short (read panicked): %v",
				hvmHeaderStoreDir(levelDBHome, network), r)
		}
	}()
	cfg, err := level.NewConfig(canonicalBTCNetwork(network), levelDBHome, "0", "0")
	if err != nil {
		return nil, fmt.Errorf("legacy store config: %w", err)
	}
	// Suppress the in-place schema upgrade: level.New otherwise runs v2/v3/v4 migrations that REWRITE the store,
	// after which an older binary could no longer read the upgraded legacy store following a deferred boot.
	// SetUpgradeOpen makes New return right after reading the version, skipping the rewrite ladder so the store's
	// block/header DATA stays byte-for-byte intact; the two values needed (best header, upstream-state-id) are read
	// without an upgrade.
	//
	// This is "no rewrite ladder", not "zero bytes written": against a VERSION-LESS legacy store, level.New still
	// stamps a single version key on open even under SetUpgradeOpen — a metadata-only write that does not touch
	// block/header data. testnet3 nodes never reach that case (their legacy stores already carry a version); it
	// would only matter on the mainnet-path open that testnet3 nodes do not perform.
	cfg.SetUpgradeOpen(true)
	// Reject a torn (<8-byte) on-disk version key BEFORE level.New: it decodes the version with
	// binary.BigEndian.Uint64 and PANICS on a short value after taking the metadata leveldb's directory lock,
	// leaking that lock for the process lifetime (see legacyStoreVersionKeyTorn). The function-level recover above
	// remains a backstop for any other panic, but this avoids the leak for the common torn-version corruption.
	if legacyStoreVersionKeyTorn(levelDBHome, network) {
		return nil, fmt.Errorf("open hVM header store at %s: on-disk version key is torn/short (corrupt store)",
			hvmHeaderStoreDir(levelDBHome, network))
	}
	db, err := level.New(ctx, cfg)
	if err != nil {
		// Neutral message: do NOT assert "lock held" — the open can fail for corruption, a future
		// on-disk version, or I/O too. Name the exact dir so the operator can act.
		return nil, fmt.Errorf("open hVM header store at %s: %w", hvmHeaderStoreDir(levelDBHome, network), err)
	}
	defer db.Close() // closes before return — never held across the defer/rebuild/rename re-opens of the same dir

	// Forward-incompatibility guard: SetUpgradeOpen suppresses the upgrade ladder, which also
	// suppresses the normal open's rejection of a NEWER/unknown on-disk version. Reading a future-format store
	// with this binary's decoder could misdecode the tip / state-id. Re-impose the version ceiling so a
	// future-version store returns an error (the callers treat that conservatively: the mainnet probe keeps the
	// store, the legacy read defers) instead of silently misreading.
	// A short/torn version key would panic inside db.Version too, but the pre-open legacyStoreVersionKeyTorn probe
	// already rejected that case before level.New; the function-level recover at the top remains a backstop.
	if v, verr := db.Version(ctx); verr != nil {
		return nil, fmt.Errorf("read hVM header store version at %s: %w", hvmHeaderStoreDir(levelDBHome, network), verr)
	} else if v > ldbMaxSupportedVersion {
		return nil, fmt.Errorf("hVM header store at %s is an unsupported FUTURE version %d (this binary supports up to %d) — "+
			"upgrade the binary; do NOT downgrade onto an upgraded store", hvmHeaderStoreDir(levelDBHome, network), v, ldbMaxSupportedVersion)
	} else if v < ldbMinSupportedVersion {
		return nil, fmt.Errorf("hVM header store at %s reports an invalid version %d (below the minimum supported %d) — "+
			"the version key is torn/corrupt; the store cannot be trusted", hvmHeaderStoreDir(levelDBHome, network), v, ldbMinSupportedVersion)
	}

	best, err := db.BlockHeaderBest(ctx)
	if err != nil {
		// Distinguish a definitively EMPTY/TORN store (no best header — e.g. a crash during rebuild ExternalHeaderSetup
		// left a headerless mainnet/) from a lock/open failure. The empty case must RE-MIGRATE, not
		// be conservatively kept; callers branch on errLegacyStoreEmpty.
		var nf database.NotFoundError
		if errors.As(err, &nf) {
			return nil, fmt.Errorf("%w: %v", errLegacyStoreEmpty, err)
		}
		return nil, fmt.Errorf("read legacy committed BTC tip: %w", err)
	}
	out := &legacyStoreTS{tipHeight: best.Height, tipHash: best.Hash}

	sBytes, err := db.MetadataGet(ctx, upstreamStateIdMetaKey)
	if err != nil {
		// A MISSING upstream-state-id is also a torn store: the fill commits the headers and the
		// state-id in SEPARATE leveldb transactions, state-id LAST, so a crash between them leaves a best header
		// present but NO state-id. That store MUST re-migrate — booting the normal flow on it crit-loops at the
		// UpstreamStateId read. Classify it as errLegacyStoreEmpty like the no-best-header case.
		var nf database.NotFoundError
		if errors.As(err, &nf) {
			return nil, fmt.Errorf("%w: %v", errLegacyStoreEmpty, err)
		}
		return nil, fmt.Errorf("read legacy upstream-state-id: %w", err)
	}
	if len(sBytes) != len(out.stateId) {
		return nil, fmt.Errorf("legacy upstream-state-id has unexpected length %d", len(sBytes))
	}
	copy(out.stateId[:], sBytes)
	out.atGenesis = bytes.Equal(out.stateId[:], hVMGenesisUpstreamId[:])
	return out, nil
}

// migrateHvmHeaderNode implements the rebuild (gather, fill, verify, catch-up, retire). Returns true if it fully
// migrated and initialized bc.tbcHeaderNode; false if it DEFERRED (config.Network mutated to "testnet3", caller
// boots on the legacy store).
func (bc *BlockChain) migrateHvmHeaderNode(config *tbc.Config) (migrated bool) {
	home := config.LevelDBHome

	// Genesis weld: the rebuilt store's effective genesis comes from the operator flags
	// (config.EffectiveGenesisBlock/GenesisHeightOffset), while the full-node walk target + height floor use the
	// hardcoded shared constant. They MUST be the same pair or the walk and the store genesis diverge. Assert it
	// BEFORE any destructive op, with a clear message (the initHvmHeaderNode guard would otherwise crit only
	// after removeHvmHeaderNetworkDir). On a correctly-configured mainnet node these are identical by the
	// dual-pin; a mismatch means --hvm.genesisheader/height was dropped or wrong.
	if config.EffectiveGenesisBlock == nil ||
		config.EffectiveGenesisBlock.BlockHash().String() != vm.MainnetHvmGenesisHash ||
		config.GenesisHeightOffset != vm.MainnetHvmGenesisHeight {
		got := "<nil>"
		if config.EffectiveGenesisBlock != nil {
			got = config.EffectiveGenesisBlock.BlockHash().String()
		}
		migrationCrit("hVM header store migration: the configured mainnet effective-genesis pair does not match the canonical "+
			"mainnet pair the migration rebuilds against — set --hvm.genesisheight to the height below and "+
			"--hvm.genesisheader to the 80-byte header hex below (the flag takes the HEADER bytes, not the hash)",
			"wantHeight", vm.MainnetHvmGenesisHeight, "wantHeader", vm.MainnetHvmGenesisHeader, "wantHash", vm.MainnetHvmGenesisHash,
			"gotHeight", config.GenesisHeightOffset, "gotHash", got)
	}

	// Full-node identity guard: the gather walk treats vm.TBCFullNode as the MAINNET chain. If the
	// full node is absent or configured for a different network (e.g. a leftover testnet3 index), DEFER rather
	// than walk the wrong index — the node boots on the untouched legacy store and retries once the operator
	// fixes the full-node network.
	if vm.TBCFullNode == nil || vm.TBCFullNodeConfig == nil || canonicalBTCNetwork(vm.TBCFullNodeConfig.Network) != "mainnet" {
		return bc.deferHvmMigration(config, "embedded full node is absent or not configured for mainnet")
	}

	// Guard-free read of T (committed BTC tip) and S (EVM-tip upstream-state-id) from the legacy store.
	ts, err := readLegacyStoreTS(bc.ctx, home, "testnet3")
	if err != nil {
		// A TORN/empty legacy store: name the corruption and the remedy — deferring "retry next
		// start" is a false promise (the store will not heal), and the normal fall-through boot would crit-loop
		// on it. The operator must remove or restore the dir; we defer (untouched) so they can intervene.
		if errors.Is(err, errLegacyStoreEmpty) {
			log.Error("hVM header store migration: the legacy testnet3 store is TORN/EMPTY (no best header or no "+
				"upstream-state-id) — migration cannot proceed. Remove or restore it from backup; the node will run "+
				"unenforced until then", "dir", hvmHeaderStoreDir(home, "testnet3"), "err", err)
			return bc.deferHvmMigration(config, "legacy testnet3 store is torn/empty (remove or restore it)")
		}
		// Otherwise unreadable (lock contention / corruption / future version). Do NOT touch any dir — defer.
		log.Error("hVM header store migration: could not read the legacy testnet3 store; deferring", "dir", hvmHeaderStoreDir(home, "testnet3"), "err", err)
		return bc.deferHvmMigration(config, "legacy store unreadable (see err)")
	}
	if ts.atGenesis {
		// The legacy store never progressed past genesis — nothing to migrate. Defer to a normal boot, which
		// will build state on the (still testnet3-labeled) store; a fresh mainnet node would be equivalent but
		// deferring avoids touching dirs on an ambiguous state.
		log.Info("hVM header store migration: legacy store is at genesis (no committed state); deferring to normal boot")
		return bc.deferHvmMigration(config, "legacy store at genesis")
	}
	log.Info("hVM header store migration: legacy store committed BTC tip and EVM state-id read",
		"btcTipHeight", ts.tipHeight, "btcTip", ts.tipHash.String(), "evmStateId", fmt.Sprintf("%x", ts.stateId[:]))

	// Pre-rebuild canonical-S guard: the recorded EVM state-id S MUST be a canonical ancestor of
	// the current tip before we destructively rebuild and then catch up from it. If a deep reorg across an
	// unclean shutdown orphaned S (or left it above the current tip), a forward catch-up cannot anchor on it;
	// DEFER (legacy store untouched, node boots on it, the normal reorg path reconciles) rather than rebuild
	// into a state the catch-up would crit-loop on.
	if !bc.legacyStateIdIsCanonical(ts.stateId) {
		return bc.deferHvmMigration(config, "legacy EVM state-id is not a canonical ancestor of the current tip (deep reorg across an unclean shutdown?)")
	}

	// Readiness check: gather the canonical headers [genesis+1 .. T] from the mainnet full node, walking back from
	// T to the mainnet effective genesis. A walk failure means the full node lacks T or its ancestry (fresh /
	// behind node) — DEFER without touching any dir (retry next boot).
	headers, ok := bc.gatherMainnetHeadersFromFullNode(ts.tipHash)
	if !ok {
		return bc.deferHvmMigration(config, "mainnet full node not ready (missing T or ancestry to genesis)")
	}
	log.Info("hVM header store migration: mainnet full node holds the full committed chain; proceeding to rebuild",
		"headers", len(headers))

	// In-progress signal: from here on the rebuild is committed and can take minutes (bulk-load + catch-up).
	// Mark the gauge so the node does not look hung, and arm the in-window crit routing: a fatal init/apply crit
	// on the freshly-emptied mainnet store would otherwise os.Exit without marking the "failed" meter or clearing
	// the gauge. Both side effects are set by enterHvmMigrationRebuildWindow; the defers clear them.
	bc.enterHvmMigrationRebuildWindow()
	defer hvmMigrationInProgressGauge.Update(0)
	defer func() { bc.hvmMigrationInProgress = false }()

	// Scoped-reset any stale/partial <home>/mainnet/, then init a fresh mainnet node at the mainnet genesis.
	if err := removeHvmHeaderNetworkDir(home, "mainnet"); err != nil {
		migrationCrit("hVM header store migration: unable to remove stale mainnet store before rebuild", "err", err)
	}
	bc.initHvmHeaderNode(config) // config.Network == "mainnet"; sets bc.tbcHeaderNode + hvmDiffEnforceable

	// Fill [genesis+1 .. T] with upstream-state-id S (the LAST commit, so a torn fill leaves state-id != S
	// and is caught by the store classification next boot). EMPTY-FILL case: when T IS the mainnet effective
	// genesis (no committed BTC headers past genesis yet — the normal early-hVM state where the EVM state-id
	// advanced while the BTC tip stayed at genesis), the fresh node is ALREADY at T, and AddExternalHeaders
	// errors on an empty set ("called with no headers"), so it must be SKIPPED — only the state-id is set.
	if len(headers) == 0 {
		if err := bc.tbcHeaderNode.SetUpstreamStateId(bc.ctx, ts.stateId); err != nil {
			migrationCrit("hVM header store migration: unable to set upstream-state-id on the genesis-tip mainnet store", "err", err)
		}
	} else {
		// Observe-only PoW + contextual-difficulty check BEFORE the bulk add, mirroring
		// the snap path (observeSnapBtcDiff): AddExternalHeaders trusts headers blindly, so without this the
		// one-time mainnet bulk-load has NO detection surface for a forged / corrupt / PoW-invalid full node.
		// NEVER halts (a near-floor honest node would otherwise brick) — it only marks alert meters + logs so a
		// bad full-node base is investigable. The cumulative-work tip select + the post-fill tip/state-id verify crit remain the backstop.
		obs := observeSnapBtcDiff(bc.ctx, vm.TBCFullNode, config.Network, config.GenesisHeightOffset, headers)
		if obs.powFailed {
			hvmMigrationPoWRejectMeter.Mark(1)
			log.Error("hVM header store migration observe-only check: a full-node header in the bulk-load failed "+
				"proof-of-work; proceeding under the canonical-tip + cumulative-work backstops — investigate", "err", obs.powErr)
		}
		if obs.firstHeightMismatch {
			// Tripwire (mirrors the snap path): the first gathered header should be genesis+1. A
			// mismatch means the walk did not start where expected — surface it rather than silently accepting.
			log.Warn("hVM header store migration observe-only check: first bulk-load header height is not effective-genesis+1; "+
				"unexpected walk start — investigate", "firstHeight", obs.firstHeight, "expected", config.GenesisHeightOffset+1)
		}
		switch {
		case obs.ctxObservation == snapObsReject:
			hvmMigrationBtcDiffRejectMeter.Mark(1)
			log.Error("hVM header store migration observe-only check: a full-node header in the bulk-load failed "+
				"contextual difficulty validation; proceeding under the canonical-tip + cumulative-work backstops — investigate", "err", obs.ctxErr)
		case obs.ctxObservation == snapObsIncomplete:
			// Surface the INCOMPLETE verdict (a connectivity gap / transient full-node read while
			// resolving ancestry).
			log.Warn("hVM header store migration observe-only check: contextual difficulty observation INCOMPLETE "+
				"(connectivity/transient read while resolving the bulk-load ancestry); proceeding under the backstops", "err", obs.ctxErr)
		case !obs.contextualRan && (obs.clearanceErr != nil || obs.firstHeightErr != nil):
			// GENUINE skip: the contextual observation could not run because the base could not be
			// parameterized (unknown network: no chaincfg params) or its first header height could not be read.
			// Surface it rather than silently reading as "clean" — this is the only detection surface for the
			// one-time bulk-load, so a skipped check must be visible.
			log.Warn("hVM header store migration observe-only check: contextual difficulty observation was SKIPPED "+
				"(the bulk-load base could not be difficulty-observed: unknown network params or a full-node read "+
				"error); proceeding under the backstops",
				"clearanceErr", obs.clearanceErr, "firstHeightErr", obs.firstHeightErr)
		case !obs.contextualRan:
			// BENIGN empty enforceable suffix: every gathered header sits at/below the enforce floor
			// (the early-mainnet case where the committed BTC tip is within ~clearance blocks of effective genesis),
			// so there is NO above-floor suffix to contextually verify. This is normal, not a skipped/failed check —
			// log Info (not WARN) with the floor so it is not confused with a genuine SKIPPED/INCOMPLETE result.
			log.Info("hVM header store migration observe-only check: no enforceable (above-floor) headers in the "+
				"bulk-load near the effective genesis; nothing to contextually verify (normal for an early-mainnet tip)",
				"enforceFloor", obs.enforceFloor, "deferredCount", obs.deferredCount, "enforcedCount", obs.enforcedCount)
		}
		msgHeaders := &wire.MsgHeaders{Headers: headers}
		if _, _, _, _, err := bc.tbcHeaderNode.AddExternalHeaders(bc.ctx, msgHeaders, ts.stateId[:]); err != nil {
			migrationCrit("hVM header store migration: AddExternalHeaders failed while filling the mainnet store", "err", err)
		}
	}

	// Verify fail-closed — rebuilt canonical tip == T AND upstream-state-id == S. Read the actual store
	// tip (not the AddExternalHeaders return, which is absent on the empty-fill path).
	postHeight, postTip, err := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
	if err != nil {
		migrationCrit("hVM header store migration: unable to read best header after fill", "err", err)
	}
	postTipHash := postTip.BlockHash()
	if !bytes.Equal(postTipHash[:], ts.tipHash[:]) {
		migrationCrit("hVM header store migration: rebuilt canonical tip does not match the legacy committed tip",
			"want", ts.tipHash.String(), "got", postTipHash.String(), "wantHeight", ts.tipHeight, "gotHeight", postHeight)
	}
	postId, err := bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
	if err != nil {
		migrationCrit("hVM header store migration: unable to read upstream-state-id after fill", "err", err)
	}
	if !bytes.Equal(postId[:], ts.stateId[:]) {
		migrationCrit("hVM header store migration: post-fill upstream-state-id mismatch",
			"want", fmt.Sprintf("%x", ts.stateId[:]), "got", fmt.Sprintf("%x", postId[:]))
	}
	log.Info("hVM header store migration: mainnet store filled and verified", "btcTip", ts.tipHash.String(), "btcTipHeight", ts.tipHeight)

	// Forward catch-up [S+1 .. currentTip] if the legacy store lagged the EVM tip (unclean shutdown). NON-
	// FATAL: the store is already valid at the canonical state-id S, so a catch-up error is logged
	// and we proceed — the node boots slightly behind and catches up via normal import — rather than crit-looping.
	catchUp := "ok"
	if err := bc.catchUpMigratedStoreToTip(ts.stateId); err != nil {
		catchUp = "deferred-to-normal-import"
		log.Warn("hVM header store migration: forward catch-up to the EVM tip did not complete; the migrated store "+
			"is valid at the legacy state-id and will catch up via normal import", "err", err)
	}

	// Rollback-safe retirement of the legacy store. Non-fatal: the migrated store is already valid; a
	// rename failure leaves testnet3/ present, and the orphaned-store retirement idempotently re-attempts the rename next boot.
	bc.retireLegacyTestnet3Store(home, ts.stateId)

	hvmMigrationCompletedMeter.Mark(1)
	// Success summary — includes the catch-up outcome so a still-lagging store is not read as fully current.
	log.Info(fmt.Sprintf("hVM header store migrated testnet3->mainnet to BTC tip %s @ %d at EVM state-id %x (catchUp=%s)",
		ts.tipHash.String(), ts.tipHeight, ts.stateId[:], catchUp))
	return true
}

// The gather walk's full-node read surface is the shared vm.BTCHeaderLookup (the same minimal BlockHeaderByHash
// interface the contextual-difficulty validator uses), satisfied by *tbc.Server / vm.TBCFullNode and by the test
// fakes. The *tbc.Server contract is compile-guarded in package vm (var _ headerLookup = (*tbc.Server)(nil)).

// gatherMainnetHeadersFromFullNode walks the mainnet full node from the committed tip T back to the mainnet
// effective genesis, returning the canonical headers [genesis+1 .. T] in ascending order (the order
// AddExternalHeaders expects). Returns ok=false if any link is missing (full node not ready / behind) — the
// readiness check for migrate-or-defer. Modeled on the snap-completion walk (runHvmSnapWaiter).
func (bc *BlockChain) gatherMainnetHeadersFromFullNode(tip chainhash.Hash) (headers []*wire.BlockHeader, ok bool) {
	genesis, err := chainhash.NewHashFromStr(vm.MainnetHvmGenesisHash)
	if err != nil {
		migrationCrit("hVM header store migration: invalid mainnet genesis hash constant", "err", err)
	}
	return gatherHeadersBackToGenesis(bc.ctx, vm.TBCFullNode, tip, *genesis, vm.MainnetHvmGenesisHeight)
}

// gatherHeadersBackToGenesis is the pure walk: from tip back to genesisHash by PrevBlock hash-link, collecting
// (genesis EXCLUDED) and reversing to ascending order. Returns ok=false (defer) if a link is missing OR the walk
// reaches genesisHeight without matching genesisHash (T is not a descendant of the effective genesis — a wrong/
// forged full node), which also bounds the walk so it never descends to real Bitcoin genesis.
func gatherHeadersBackToGenesis(ctx context.Context, lookup vm.BTCHeaderLookup, tip, genesisHash chainhash.Hash, genesisHeight uint64) (headers []*wire.BlockHeader, ok bool) {
	cursor, cursorHeight, err := lookup.BlockHeaderByHash(ctx, tip)
	if err != nil {
		log.Warn("hVM header store migration: full node does not have the legacy committed BTC tip yet; deferring", "tip", tip.String(), "err", err)
		return nil, false
	}
	cursorHash := cursor.BlockHash()
	for !bytes.Equal(cursorHash[:], genesisHash[:]) {
		// Height floor: the committed tip MUST descend from the mainnet effective genesis. If the
		// walk reaches the genesis height (or below) without matching the genesis HASH, T is not a descendant of
		// {883092,…eda8} (a wrong/forged full node) — defer rather than walk to real Bitcoin genesis (~883k
		// headers buffered in memory). bytes-equal against the genesis hash above is the normal loop exit.
		if cursorHeight <= genesisHeight {
			log.Warn("hVM header store migration: committed BTC tip does not descend from the mainnet effective genesis; deferring",
				"reachedHeight", cursorHeight, "reached", cursorHash.String())
			return nil, false
		}
		headers = append(headers, cursor)
		prevHeight := cursorHeight
		prev := cursor.PrevBlock
		cursor, cursorHeight, err = lookup.BlockHeaderByHash(ctx, prev)
		if err != nil {
			log.Warn("hVM header store migration: full node is missing an ancestor header on the walk to the mainnet genesis; deferring",
				"missing", prev.String(), "err", err)
			return nil, false
		}
		cursorHash = cursor.BlockHash()
		// CYCLE / corrupt-index guard: an honest PrevBlock walk strictly DECREASES height by one
		// each step. The full node is NOT trusted (a torn leveldb index or a malicious/buggy peer could serve a
		// header whose PrevBlock forms a cycle ABOVE the genesis-height floor), so without this the loop would
		// spin forever appending headers and OOM-brick the boot. A non-decreasing height => cycle/corruption =>
		// DEFER (boot on the untouched legacy store; the operator repairs the full-node index).
		if cursorHeight >= prevHeight {
			log.Warn("hVM header store migration: full-node header walk did not strictly descend in height (PrevBlock cycle / corrupt index?); deferring",
				"fromHeight", prevHeight, "toHeight", cursorHeight, "header", cursorHash.String())
			return nil, false
		}
	}
	slices.Reverse(headers)
	return headers, true
}

// legacyStateIdIsCanonical reports whether the legacy store's recorded EVM state-id S resolves to a block that
// is a canonical ancestor of (or equal to) the BODIED tip (CurrentBlock). Used as the pre-rebuild PROCEED guard
// (a non-canonical S means the forward catch-up cannot anchor on it -> DEFER). NOTE: this is distinct from
// existingMainnetStoreState, which deliberately does NOT require canonicality (it must tolerate a post-migration
// reorg on an already-migrated store); only this pre-rebuild guard requires it.
func (bc *BlockChain) legacyStateIdIsCanonical(stateId [32]byte) bool {
	h := bc.GetHeaderByHash(common.BytesToHash(stateId[:]))
	if h == nil {
		return false
	}
	n := h.Number.Uint64()
	// Bounded by the BODIED head (CurrentBlock): this is the migrate-PROCEED guard, and the
	// subsequent catch-up applies [S+1 .. CurrentBlock] (which needs bodies). Requiring S <= CurrentBlock
	// guarantees the catch-up can actually reach the bodied head and the migrated store lands AT the bodied tip
	// — never ABOVE it (which would force a full restore-from-genesis on first import). If S is above the bodied
	// head (rare: bodies lost between boots), DEFER this boot; bodies catch up and a later boot migrates.
	return n <= bc.CurrentBlock().Number.Uint64() && bc.GetCanonicalHash(n) == h.Hash()
}

// catchUpMigratedStoreToTip advances the freshly-filled mainnet store from the legacy state-id S forward to the
// current EVM tip, applying only [S+1 .. tip]. It re-applies ALREADY-COMMITTED canonical history with
// enforcement OFF (the third applyHvmHeaderConsensusUpdate arg) — mirroring performFullHvmHeaderStateRestore —
// so a recoverable difficulty/format result on a historical block cannot crash recovery, and it walks forward
// by canonical NUMBER (only [S+1 .. tip], never below S), so a snap node's missing deep bodies are never
// touched. Returns an error (caller logs, non-fatally) rather than crit. No-op when S is already the tip.
func (bc *BlockChain) catchUpMigratedStoreToTip(stateId [32]byte) error {
	from := bc.GetHeaderByHash(common.BytesToHash(stateId[:]))
	if from == nil {
		return fmt.Errorf("legacy state-id %x is not a known EVM block; cannot forward-catch-up", stateId[:])
	}
	// Target the BODIED head (CurrentBlock): applyHvmHeaderConsensusUpdate consumes the block
	// BODY (the BtcAttr tx), so walking to CurrentHeader (which can lead the bodied head on a snap / unclean-
	// shutdown node) would abort at the first body-less header and abandon the appliable [S+1..CurrentBlock]
	// span. This mirrors performFullHvmHeaderStateRestore, which also targets CurrentBlock.
	tip := bc.CurrentBlock()
	fromN, tipN := from.Number.Uint64(), tip.Number.Uint64()
	if from.Hash() == tip.Hash() {
		return nil // already at the bodied tip
	}
	// Defensive: S must be canonical and at/below the bodied tip (the pre-rebuild guard already checked this;
	// re-check here so a race/reorg between the checks cannot drive the walk off the canonical chain).
	if fromN > tipN || bc.GetCanonicalHash(fromN) != from.Hash() {
		return fmt.Errorf("legacy state-id is not a canonical ancestor of the bodied tip (from %d, tip %d)", fromN, tipN)
	}
	log.Info("hVM header store migration: forward catch-up of the migrated store", "from", fromN, "to", tipN)
	for n := fromN + 1; n <= tipN; n++ {
		h := bc.GetHeaderByNumber(n)
		if h == nil {
			return fmt.Errorf("missing canonical header at %d during forward catch-up", n)
		}
		if err := bc.applyHvmHeaderConsensusUpdate(h, false, false); err != nil {
			return fmt.Errorf("apply hVM update at %d during forward catch-up: %w", n, err)
		}
		if n%1000 == 0 { // in-progress signal: a long catch-up must not look hung
			log.Info("hVM header store migration: forward catch-up progress", "applied", n, "to", tipN)
		}
	}
	return nil
}

// retireLegacyTestnet3Store renames <home>/testnet3/ to <home>/testnet3.migrated-<S>/. Rollback-safe: the
// operator can rename it back before downgrading to a pre-migration binary. Non-fatal.
func (bc *BlockChain) retireLegacyTestnet3Store(levelDBHome string, stateId [32]byte) {
	src := hvmHeaderStoreDir(levelDBHome, "testnet3")
	dst := filepath.Join(levelDBHome, fmt.Sprintf("testnet3.migrated-%x", stateId[:]))
	if _, err := os.Stat(dst); err == nil {
		// A backup for this S already exists. Only remove the source if that backup is a NON-EMPTY store:
		// never delete the legacy source to satisfy an empty/partial backup dir, which would
		// destroy the only rollback copy. If the existing backup is empty, leave both for the operator.
		if !dirHasEntries(dst) {
			log.Warn("hVM header store migration: existing migrated-backup is empty; leaving BOTH the source and the backup for the operator", "backup", dst)
			return
		}
		log.Info("hVM header store migration: a valid migrated-backup already exists; leaving it and removing the source",
			"backup", dst)
		if err := os.RemoveAll(src); err != nil {
			log.Warn("hVM header store migration: could not remove the legacy source after an existing backup was found", "err", err)
		}
		return
	}
	if err := os.Rename(src, dst); err != nil {
		log.Warn("hVM header store migration: could not retire the legacy testnet3 store (will retry next boot); the migrated mainnet store is already valid",
			"src", src, "dst", dst, "err", err)
		return
	}
	log.Info("hVM header store migration: legacy testnet3 store retired", "backup", dst)
}

// deferHvmMigration implements the defer override: mutate config.Network to "testnet3" (the single field
// that drives the store path, the genesis-pairing guard, AND every enforcement-params read) on the in-flight
// config the caller will pass to initHvmHeaderNode, leaving the legacy {883092,…eda8} pair intact. The dual-pin
// makes the guard pass; hvmDiffEnforceable stays false (isLegacyDeferredPairing). Returns false ("not handled")
// so the caller falls through to a normal boot on the untouched legacy store.
func (bc *BlockChain) deferHvmMigration(config *tbc.Config, reason string) bool {
	hvmMigrationDeferredMeter.Mark(1)
	log.Warn("hVM header store migration DEFERRED — node boots on the legacy testnet3 store, unenforced; retrying next start",
		"reason", reason)
	config.Network = "testnet3"
	return false
}
