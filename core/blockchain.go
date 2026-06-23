// Copyright 2014 The go-ethereum Authors
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

// Package core implements the Ethereum consensus protocol.
package core

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"runtime"
	"slices"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/database"
	"github.com/hemilabs/heminetwork/hemi"
	"github.com/hemilabs/heminetwork/service/deucalion"
	"github.com/hemilabs/heminetwork/service/tbc"
	"golang.org/x/net/context"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/lru"
	"github.com/ethereum/go-ethereum/common/mclock"
	"github.com/ethereum/go-ethereum/common/prque"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/consensus/misc/eip4844"
	"github.com/ethereum/go-ethereum/core/history"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/state/snapshot"
	"github.com/ethereum/go-ethereum/core/stateless"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/event"
	"github.com/ethereum/go-ethereum/internal/syncx"
	"github.com/ethereum/go-ethereum/internal/version"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/metrics"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/triedb"
	"github.com/ethereum/go-ethereum/triedb/hashdb"
	"github.com/ethereum/go-ethereum/triedb/pathdb"
)

var (
	headBlockGauge          = metrics.NewRegisteredGauge("chain/head/block", nil)
	headHeaderGauge         = metrics.NewRegisteredGauge("chain/head/header", nil)
	headFastBlockGauge      = metrics.NewRegisteredGauge("chain/head/receipt", nil)
	headFinalizedBlockGauge = metrics.NewRegisteredGauge("chain/head/finalized", nil)
	headSafeBlockGauge      = metrics.NewRegisteredGauge("chain/head/safe", nil)

	chainInfoGauge   = metrics.NewRegisteredGaugeInfo("chain/info", nil)
	chainMgaspsMeter = metrics.NewRegisteredResettingTimer("chain/mgasps", nil)

	// hVM Bitcoin Attributes Deposited tx generation on the sequencer build path. A persistent
	// failure here means the hVM Bitcoin view stops advancing while the L2 keeps producing blocks;
	// the function does not crash the sequencer on failure, so these meters are the alertable signal in its
	// place. hvmBtcAttrFailMeter gives a genuine-failure rate; hvmBtcAttrFailingGauge holds the last
	// status (1 = last attempt did not advance the hVM Bitcoin view, whether a genuine failure or
	// pending work blocked this round; 0 = succeeded or had nothing to do), so a stuck condition is
	// alertable as "gauge==1 for N min".
	hvmBtcAttrFailMeter    = metrics.NewRegisteredMeter("chain/hvm/btcattr/fail", nil)
	hvmBtcAttrFailingGauge = metrics.NewRegisteredGauge("chain/hvm/btcattr/failing", nil)

	// hvmFullTBCBehindGauge holds the last status of the embedded full TBC Bitcoin node's indexer
	// advance: 1 = it could not be moved to the target BTC tip because the required headers/blocks
	// are not yet P2P-synced (the deferrable condition), 0 = caught up. That condition is a non-fatal
	// log.Warn on the head-set/reorg path rather than a crash, so this gauge is the alertable signal
	// in its place — alert on "gauge==1 for N min".
	//
	// Caveat (best-effort, not authoritative): the gauge reflects only the last full-node-advance
	// attempt, updated inside updateFullTBCToLightweight (reached on a new head / block import). It is
	// in-memory (resets to 0 on restart) and is not refreshed during a same-head forkchoiceUpdated
	// pause, so during a quiet period it can read stale in either direction. Corroborate with the
	// missing-BTC-blocks RPC (GetMissingBtcBlocks). Consensus-safe regardless (see isHvmFullNodeBehind).
	hvmFullTBCBehindGauge = metrics.NewRegisteredGauge("chain/hvm/fulltbc/behind", nil)

	// hvmSnapAwaitingGauge is 1 while the apply-path hVM consensus gate is paused for an in-flight hVM snap
	// sync (updateHvmHeaderConsensus skipped in ProcessBlock), 0 once snap completes. The pause is otherwise
	// silent on the per-block hot path, so this is the alertable signal — alert on "gauge==1 while the head
	// keeps advancing for N min" to catch a stuck snap-await. In-memory (resets to 0 on restart).
	hvmSnapAwaitingGauge = metrics.NewRegisteredGauge("chain/hvm/snap/awaiting", nil)

	// hvmSnapBtcDiffRejectMeter counts contextual-difficulty failures observed while
	// validating a snap-sync-reconstructed BTC base (SnapSyncHvm). Snap-sync is observe-only for this check
	// (it does not halt — see SnapSyncHvm), so a non-zero rate is the alertable signal that this node's
	// full TBC node served a base that fails contextual validation, worth investigation even though the load
	// still proceeds under the canonical-tip + cumulative-work backstops. The proof-of-work failure class
	// has its own meter (hvmSnapPoWRejectMeter) so the two are not conflated.
	hvmSnapBtcDiffRejectMeter = metrics.NewRegisteredMeter("chain/hvm/snap/btcdiff_reject", nil)

	// hvmSnapPoWRejectMeter counts proof-of-work failures (hash > target) observed on a snap-sync base
	// — a distinct failure class from the contextual-difficulty meter above (a header can fail one without
	// the other). Also observe-only (snap never halts on it).
	hvmSnapPoWRejectMeter = metrics.NewRegisteredMeter("chain/hvm/snap/pow_reject", nil)

	// hVM header-store migration meters: triggered when a legacy testnet3 store is detected on a
	// mainnet-configured node, deferred when the full node is not yet ready (no dir touched), completed on a
	// verified rebuild + retirement.
	hvmMigrationTriggeredMeter = metrics.NewRegisteredMeter("chain/hvm/migration/triggered", nil)
	hvmMigrationDeferredMeter  = metrics.NewRegisteredMeter("chain/hvm/migration/deferred", nil)
	hvmMigrationCompletedMeter = metrics.NewRegisteredMeter("chain/hvm/migration/completed", nil)
	// Observe-only alert meters for the one-time migration bulk-load (mirrors the snap-path pow_reject /
	// btcdiff_reject; never halts — the full node served a base that fails PoW / contextual difficulty).
	hvmMigrationPoWRejectMeter     = metrics.NewRegisteredMeter("chain/hvm/migration/pow_reject", nil)
	hvmMigrationBtcDiffRejectMeter = metrics.NewRegisteredMeter("chain/hvm/migration/btcdiff_reject", nil)
	// hvmMigrationFailedMeter is marked immediately before each fatal migration log.Crit so a failed migration
	// leaves a scrapeable signal (the "failed" event), since log.Crit then exits the process.
	hvmMigrationFailedMeter = metrics.NewRegisteredMeter("chain/hvm/migration/failed", nil)
	// hvmMigrationInProgressGauge is 1 while a rebuild is running (set after the readiness check, cleared on
	// return) so a multi-minute bulk-load/catch-up is observable rather than looking hung.
	hvmMigrationInProgressGauge = metrics.NewRegisteredGauge("chain/hvm/migration/in_progress", nil)

	// hvmBtcAttrDiffTruncMeter counts contextual-difficulty truncations on the sequencer
	// build path (getBitcoinAttributesForNextBlock dropped candidate BTC headers that the apply path
	// would reject). It distinguishes a contextually-invalid header fed by the full node from a benign
	// "next full block not yet downloaded" stall — both otherwise surface only as the shared stuck gauge.
	// A sustained non-zero rate means the full node is serving contextually-invalid BTC headers.
	hvmBtcAttrDiffTruncMeter = metrics.NewRegisteredMeter("chain/hvm/btcattr/diff_trunc", nil)

	// hvmReapplyRestoreMeter counts node-local lightweight-view rebuilds (performFullHvmHeaderStateRestore)
	// triggered when re-applying already-committed history (head-set / canonical / post-invalid-block
	// revert / parent-move) hit a recoverable hVM error (isHvmReapplyRecoverableError: grandfathered-rule
	// reject or torn lightweight store) instead of escalating to a fleet-halt log.Crit. A non-zero value
	// signals that committed history is being re-judged against a stricter rule, or that the lightweight
	// store was torn — the recovery is safe (rebuild replays with enforcement off) but the cause warrants
	// investigation. See isHvmReapplyRecoverableError and recoverReapplyHvmState.
	hvmReapplyRestoreMeter = metrics.NewRegisteredMeter("chain/hvm/reapply/restore", nil)

	accountReadTimer   = metrics.NewRegisteredResettingTimer("chain/account/reads", nil)
	accountHashTimer   = metrics.NewRegisteredResettingTimer("chain/account/hashes", nil)
	accountUpdateTimer = metrics.NewRegisteredResettingTimer("chain/account/updates", nil)
	accountCommitTimer = metrics.NewRegisteredResettingTimer("chain/account/commits", nil)

	storageReadTimer   = metrics.NewRegisteredResettingTimer("chain/storage/reads", nil)
	storageUpdateTimer = metrics.NewRegisteredResettingTimer("chain/storage/updates", nil)
	storageCommitTimer = metrics.NewRegisteredResettingTimer("chain/storage/commits", nil)

	accountCacheHitMeter  = metrics.NewRegisteredMeter("chain/account/reads/cache/process/hit", nil)
	accountCacheMissMeter = metrics.NewRegisteredMeter("chain/account/reads/cache/process/miss", nil)
	storageCacheHitMeter  = metrics.NewRegisteredMeter("chain/storage/reads/cache/process/hit", nil)
	storageCacheMissMeter = metrics.NewRegisteredMeter("chain/storage/reads/cache/process/miss", nil)

	accountCacheHitPrefetchMeter  = metrics.NewRegisteredMeter("chain/account/reads/cache/prefetch/hit", nil)
	accountCacheMissPrefetchMeter = metrics.NewRegisteredMeter("chain/account/reads/cache/prefetch/miss", nil)
	storageCacheHitPrefetchMeter  = metrics.NewRegisteredMeter("chain/storage/reads/cache/prefetch/hit", nil)
	storageCacheMissPrefetchMeter = metrics.NewRegisteredMeter("chain/storage/reads/cache/prefetch/miss", nil)

	accountReadSingleTimer = metrics.NewRegisteredResettingTimer("chain/account/single/reads", nil)
	storageReadSingleTimer = metrics.NewRegisteredResettingTimer("chain/storage/single/reads", nil)

	snapshotCommitTimer = metrics.NewRegisteredResettingTimer("chain/snapshot/commits", nil)
	triedbCommitTimer   = metrics.NewRegisteredResettingTimer("chain/triedb/commits", nil)

	blockInsertTimer          = metrics.NewRegisteredResettingTimer("chain/inserts", nil)
	blockValidationTimer      = metrics.NewRegisteredResettingTimer("chain/validation", nil)
	blockCrossValidationTimer = metrics.NewRegisteredResettingTimer("chain/crossvalidation", nil)
	blockExecutionTimer       = metrics.NewRegisteredResettingTimer("chain/execution", nil)
	blockWriteTimer           = metrics.NewRegisteredResettingTimer("chain/write", nil)

	blockReorgMeter     = metrics.NewRegisteredMeter("chain/reorg/executes", nil)
	blockReorgAddMeter  = metrics.NewRegisteredMeter("chain/reorg/add", nil)
	blockReorgDropMeter = metrics.NewRegisteredMeter("chain/reorg/drop", nil)

	blockPrefetchExecuteTimer    = metrics.NewRegisteredResettingTimer("chain/prefetch/executes", nil)
	blockPrefetchInterruptMeter  = metrics.NewRegisteredMeter("chain/prefetch/interrupts", nil)
	blockPrefetchTxsInvalidMeter = metrics.NewRegisteredMeter("chain/prefetch/txs/invalid", nil)
	blockPrefetchTxsValidMeter   = metrics.NewRegisteredMeter("chain/prefetch/txs/valid", nil)

	errInsertionInterrupted = errors.New("insertion is interrupted")
	errChainStopped         = errors.New("blockchain is stopped")
	errInvalidOldChain      = errors.New("invalid old chain")
	errInvalidNewChain      = errors.New("invalid new chain")

	// The upstream ID used when TBC is in its genesis configuration for Hemi
	hVMGenesisUpstreamId = [32]byte{
		0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
		0x48, 0x56, 0x4D, 0x47, 0x45, 0x4E, 0x45, 0x53, 0x49, 0x53, // HVMGENESIS
		0x48, 0x56, 0x4D, 0x47, 0x45, 0x4E, 0x45, 0x53, 0x49, 0x53, // HVMGENESIS
		0x06, 0x05, 0x04, 0x03, 0x02, 0x01}

	// Temporary dummy ID used when TBC is testing application of headers that will go into a new block
	hVMDummyUpstreamId = [32]byte{
		0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C,
		0x44, 0x55, 0x4D, 0x4D, 0x59, 0x42, 0x4C, 0x4F, 0x43, 0x4B, // DUMMYBLOCK
		0x44, 0x55, 0x4D, 0x4D, 0x59, 0x42, 0x4C, 0x4F, 0x43, 0x4B, // DUMMYBLOCK
		0x0C, 0x0B, 0x0A, 0x09, 0x08, 0x07}

	emptyArray = [32]byte{}

	// deucalion interval between progression check
	progressionInterval = 7 * time.Second
	maxBlockAge         = 33 * time.Second

	// Special error thrown when blockchain state manipulation functions find that the external header mode TBC
	// instance is in an impossible state implying data corruption or incrrect application of previous state trnsitions.
	ErrExternalHeaderTBCInvalidState = errors.New("external header TBC instance is in an invalid state")
)
var (
	forkReadyInterval = 3 * time.Minute
)

const (
	bodyCacheLimit     = 256
	blockCacheLimit    = 256
	receiptsCacheLimit = 32
	txLookupCacheLimit = 1024

	// BlockChainVersion ensures that an incompatible database forces a resync from scratch.
	//
	// Changelog:
	//
	// - Version 4
	//   The following incompatible database changes were added:
	//   * the `BlockNumber`, `TxHash`, `TxIndex`, `BlockHash` and `Index` fields of log are deleted
	//   * the `Bloom` field of receipt is deleted
	//   * the `BlockIndex` and `TxIndex` fields of txlookup are deleted
	//
	// - Version 5
	//  The following incompatible database changes were added:
	//    * the `TxHash`, `GasCost`, and `ContractAddress` fields are no longer stored for a receipt
	//    * the `TxHash`, `GasCost`, and `ContractAddress` fields are computed by looking up the
	//      receipts' corresponding block
	//
	// - Version 6
	//  The following incompatible database changes were added:
	//    * Transaction lookup information stores the corresponding block number instead of block hash
	//
	// - Version 7
	//  The following incompatible database changes were added:
	//    * Use freezer as the ancient database to maintain all ancient data
	//
	// - Version 8
	//  The following incompatible database changes were added:
	//    * New scheme for contract code in order to separate the codes and trie nodes

	// Number of blocks behind the lightweight TBC canonical tip that the full TBC node is indexed to.
	// For example when a Bitcoin Attributes Deposited transaction adds headers 101 through 103, indexer
	// would move from 98 to 101.
	// TODO: Make this configurable as part of chain parameters?
	hVMIndexerTipLag = 2

	// Chosen as reasonable testnet3 difficulty above which block production should not be easy enough for
	// large reorgs to normally occur.
	// 0x1a03fffc = difficulty of 4194304
	testnet3LowDiffThresholdForTipLag = 436469756
	//
	// - Version 9
	//  The following incompatible database changes were added:
	//  * Total difficulty has been removed from both the key-value store and the ancient store.
	//  * The metadata structure of freezer is changed by adding 'flushOffset'
	BlockChainVersion uint64 = 9

	maxFutureBlocks = 256
)

// BlockChainConfig contains the configuration of the BlockChain object.
type BlockChainConfig struct {
	// Trie database related options
	TrieCleanLimit       int           // Memory allowance (MB) to use for caching trie nodes in memory
	TrieDirtyLimit       int           // Memory limit (MB) at which to start flushing dirty trie nodes to disk
	TrieTimeLimit        time.Duration // Time limit after which to flush the current in-memory trie to disk
	TrieNoAsyncFlush     bool          // Whether the asynchronous buffer flushing is disallowed
	TrieJournalDirectory string        // Directory path to the journal used for persisting trie data across node restarts

	Preimages   bool   // Whether to store preimage of trie key to the disk
	StateScheme string // Scheme used to store ethereum states and merkle tree nodes on top
	ArchiveMode bool   // Whether to enable the archive mode

	// Number of blocks from the chain head for which state histories are retained.
	// If set to 0, all state histories across the entire chain will be retained;
	StateHistory uint64

	// State snapshot related options
	SnapshotLimit   int  // Memory allowance (MB) to use for caching snapshot entries in memory
	SnapshotNoBuild bool // Whether the background generation is allowed
	SnapshotWait    bool // Wait for snapshot construction on startup. TODO(karalabe): This is a dirty hack for testing, nuke it

	// This defines the cutoff block for history expiry.
	// Blocks before this number may be unavailable in the chain database.
	ChainHistoryMode history.HistoryMode

	// Misc options
	NoPrefetch bool            // Whether to disable heuristic state prefetching when processing blocks
	Overrides  *ChainOverrides // Optional chain config overrides
	VmConfig   vm.Config       // Config options for the EVM Interpreter

	// TxLookupLimit specifies the maximum number of blocks from head for which
	// transaction hashes will be indexed.
	//
	// If the value is zero, all transactions of the entire chain will be indexed.
	// If the value is -1, indexing is disabled.
	TxLookupLimit int64

	// StateSizeTracking indicates whether the state size tracking is enabled.
	StateSizeTracking bool
}

// DefaultConfig returns the default config.
// Note the returned object is safe to modify!
func DefaultConfig() *BlockChainConfig {
	return &BlockChainConfig{
		TrieCleanLimit:   256,
		TrieDirtyLimit:   256,
		TrieTimeLimit:    5 * time.Minute,
		StateScheme:      rawdb.HashScheme,
		SnapshotLimit:    256,
		SnapshotWait:     true,
		ChainHistoryMode: history.KeepAll,
		// Transaction indexing is disabled by default.
		// This is appropriate for most unit tests.
		TxLookupLimit: -1,
	}
}

// WithArchive enables/disables archive mode on the config.
func (cfg BlockChainConfig) WithArchive(on bool) *BlockChainConfig {
	cfg.ArchiveMode = on
	return &cfg
}

// WithStateScheme sets the state storage scheme on the config.
func (cfg BlockChainConfig) WithStateScheme(scheme string) *BlockChainConfig {
	cfg.StateScheme = scheme
	return &cfg
}

// WithNoAsyncFlush enables/disables asynchronous buffer flushing mode on the config.
func (cfg BlockChainConfig) WithNoAsyncFlush(on bool) *BlockChainConfig {
	cfg.TrieNoAsyncFlush = on
	return &cfg
}

// triedbConfig derives the configures for trie database.
func (cfg *BlockChainConfig) triedbConfig(isVerkle bool) *triedb.Config {
	config := &triedb.Config{
		Preimages: cfg.Preimages,
		IsVerkle:  isVerkle,
	}
	if cfg.StateScheme == rawdb.HashScheme {
		config.HashDB = &hashdb.Config{
			CleanCacheSize: cfg.TrieCleanLimit * 1024 * 1024,
		}
	}
	if cfg.StateScheme == rawdb.PathScheme {
		config.PathDB = &pathdb.Config{
			StateHistory:        cfg.StateHistory,
			EnableStateIndexing: cfg.ArchiveMode,
			TrieCleanSize:       cfg.TrieCleanLimit * 1024 * 1024,
			StateCleanSize:      cfg.SnapshotLimit * 1024 * 1024,
			JournalDirectory:    cfg.TrieJournalDirectory,

			// TODO(rjl493456442): The write buffer represents the memory limit used
			// for flushing both trie data and state data to disk. The config name
			// should be updated to eliminate the confusion.
			WriteBufferSize: cfg.TrieDirtyLimit * 1024 * 1024,
			NoAsyncFlush:    cfg.TrieNoAsyncFlush,
		}
	}
	return config
}

// txLookup is wrapper over transaction lookup along with the corresponding
// transaction object.
type txLookup struct {
	lookup      *rawdb.LegacyTxLookupEntry
	transaction *types.Transaction
}

// BlockChain represents the canonical chain given a database with a genesis
// block. The Blockchain manages chain imports, reverts, chain reorganisations.
//
// Importing blocks in to the block chain happens according to the set of rules
// defined by the two stage Validator. Processing of blocks is done using the
// Processor which processes the included transaction. The validation of the state
// is done in the second part of the Validator. Failing results in aborting of
// the import.
//
// The BlockChain also helps in returning blocks from **any** chain included
// in the database as well as blocks that represents the canonical chain. It's
// important to note that GetBlock can return any block and does not need to be
// included in the canonical one where as GetBlockByNumber always represents the
// canonical chain.
type BlockChain struct {
	chainConfig *params.ChainConfig // Chain & network configuration
	cfg         *BlockChainConfig   // Blockchain configuration

	db            ethdb.Database                   // Low level persistent database to store final content in
	snaps         *snapshot.Tree                   // Snapshot tree for fast trie leaf access
	triegc        *prque.Prque[int64, common.Hash] // Priority queue mapping block numbers to tries to gc
	gcproc        time.Duration                    // Accumulates canonical block processing for trie dumping
	lastWrite     uint64                           // Last block when the state was flushed
	flushInterval atomic.Int64                     // Time interval (processing time) after which to flush a state
	triedb        *triedb.Database                 // The database handler for maintaining trie nodes.
	statedb       *state.CachingDB                 // State database to reuse between imports (contains state cache)
	txIndexer     *txIndexer                       // Transaction indexer, might be nil if not enabled

	hc               *HeaderChain
	rmLogsFeed       event.Feed
	chainFeed        event.Feed
	chainHeadFeed    event.Feed
	logsFeed         event.Feed
	blockProcFeed    event.Feed
	blockProcCounter int32
	scope            event.SubscriptionScope
	genesisBlock     *types.Block

	// This mutex synchronizes chain write operations.
	// Readers don't need to take it, they can just read the database.
	chainmu *syncx.ClosableMutex

	currentBlock      atomic.Pointer[types.Header] // Current head of the chain
	currentSnapBlock  atomic.Pointer[types.Header] // Current head of snap-sync
	currentFinalBlock atomic.Pointer[types.Header] // Latest (consensus) finalized block
	currentSafeBlock  atomic.Pointer[types.Header] // Latest (consensus) safe block
	historyPrunePoint atomic.Pointer[history.PrunePoint]

	bodyCache     *lru.Cache[common.Hash, *types.Body]
	bodyRLPCache  *lru.Cache[common.Hash, rlp.RawValue]
	receiptsCache *lru.Cache[common.Hash, []*types.Receipt] // Receipts cache with all fields derived
	blockCache    *lru.Cache[common.Hash, *types.Block]

	txLookupLock  sync.RWMutex
	txLookupCache *lru.Cache[common.Hash, txLookup]

	stopping      atomic.Bool // false if chain is running, true when stopped
	procInterrupt atomic.Bool // interrupt signaler for block processing

	engine     consensus.Engine
	validator  Validator // Block and state validator interface
	prefetcher Prefetcher
	processor  Processor // Block transaction processor interface
	vmConfig   vm.Config

	hvmEnabled          bool
	tbcHeaderNode       *tbc.Server
	tbcHeaderNodeConfig *tbc.Config
	// hvmDiffEnforceable: true once the header node is up on its correct, validated,
	// NON-deferred network — a genuine testnet3/localnet node, or a MIGRATED mainnet node. False ONLY while a
	// legacy node is in the DEFER state this boot (running testnet3 params over the Bitcoin-mainnet pair
	// {883092,…eda8}), where enforcing testnet3 difficulty on mainnet headers would split the fleet. Gates the
	// enforceBTCDiff path in applyHvmHeaderConsensusUpdate (the difficulty-enforcement gate). Set by initHvmHeaderNode
	// after the genesis guards. atomic.Bool: the snap-completion reset re-sets it (holding tbcHeaderNodeMu) while the
	// apply/build/snap-observe paths read it without that lock, so access must be atomic.
	hvmDiffEnforceable atomic.Bool
	// hvmMigrationInProgress is true only while migrateHvmHeaderNode is in its committed rebuild window
	// (in_progress gauge == 1). It makes initHvmHeaderNode's fatal I/O crits (NewServer / ExternalHeaderSetup /
	// BlockHeaderBest) route through migrationCrit so the "failed" meter is marked and the
	// in-progress gauge cleared before log.Crit's os.Exit — the deferred gauge-clear in migrateHvmHeaderNode
	// never runs across os.Exit. False on the normal boot / reset init paths, where a plain fatal crit is correct.
	hvmMigrationInProgress bool
	// tbcHeaderNodeMu guards the lifecycle of the lightweight header-only TBC node — its teardown +
	// reassignment in resetHvmHeaderNodeToGenesis — and the missingProgressionBlocks field. Lightweight-TBC
	// access falls into three buckets (this mutex closes the gap between bucket 2 and the writers):
	//   (1) chainmu-held callers: the apply/import path, the sequencer (getBitcoinAttributesForNextBlock,
	//       which TryLocks chainmu), ResetWithGenesisBlock, and ProcessBlockForWitness (the debug_executionWitness*
	//       RPC path — it TryLocks chainmu before ProcessBlock). These are serialized by chainmu and do not
	//       co-occur with the bucket-3 non-chainmu reset, so chainmu alone suffices.
	//   (2) GetMissingBtcBlocks: the one reader that runs outside chainmu (the per-peer broadcast goroutine
	//       prefetchBTCBlocks, every 5s) and so can co-occur with a teardown/reassign from either reset
	//       trigger. It takes the read side of this mutex (TryRLock -> bail to nil if a reset is mid-flight).
	//   (3) non-chainmu mutators that also trigger reset: SnapSyncHvm (the snap completion path) resets +
	//       rebuilds the node lock-free. Its reset goes through resetHvmHeaderNodeToGenesis, which takes Lock
	//       unconditionally, so bucket-2's reader is protected against the teardown/reassign. Its post-reset
	//       content rebuild (AddExternalHeaders etc.) is NOT taken under this mutex, and the bucket-2 reader
	//       does not consult the snap latch, so that rebuild can run concurrently with bucket-2's
	//       BlockHeaderBest read on the same node. That concurrency is safe: the underlying header store is
	//       concurrency-safe for a reader racing a writer (BlockHeaderBest is deliberately lock-free), and the
	//       only effect is the 5s broadcast reader may observe a tip mid-rebuild, which is benign (not a
	//       consensus path). This mutex therefore guards only the node LIFECYCLE (teardown/reassign) and the
	//       missingProgressionBlocks field, not the node's content.
	// Writers take Lock; the reader TryRLocks. Lock ordering is always chainmu -> tbcHeaderNodeMu (the reader
	// takes nothing else under RLock), so there is no inversion.
	tbcHeaderNodeMu sync.RWMutex
	// hvmSnapMu guards the hVM snap-sync latch bools below. SnapSyncHvm can run concurrently on multiple
	// snap peer-handler goroutines (one per response to a broadcast request), so all reads/writes of these
	// flags go through it (and the helpers hvmSnap*).
	hvmSnapMu             sync.Mutex
	awaitingHvmSnapSync   bool
	processingHvmSnapSync bool // true once a goroutine has claimed the exclusive completion work
	finishedHvmSnapSync   bool
	// hvmSnapWaiters tracks the distinct Bitcoin tips a runHvmSnapWaiter goroutine is currently waiting on
	// (guarded by hvmSnapMu), so duplicate responses for the same tip do not spawn redundant waiters and the
	// total is capped (maxHvmSnapWaiters) — a peer cannot spawn unbounded waiter goroutines. hvmSnapWg joins
	// the waiters on shutdown (so an in-flight completion finishes rather than being torn mid-write).
	hvmSnapWaiters map[chainhash.Hash]struct{}
	hvmSnapWg      sync.WaitGroup
	// hvmSnapBodyAbsentPollsLimit, when > 0, overrides maxHvmSnapBodyAbsentPolls for the body-absent give-up horizon.
	// Test-only (lets a test lower the ~100-poll/~100s horizon so the give-up/slot-release path is reachable); 0 in
	// production so effectiveMaxBodyAbsentPolls returns the const.
	hvmSnapBodyAbsentPollsLimit int
	healthyNode                 atomic.Bool

	// Temporary workaround to allow restarting TBC Full Node when its not progressing
	fullBlockFailureCount       uint32
	tempRestartTestTriggerCount uint32

	// A temporary holding pen for blocks that are being considered but not yet
	// written to disk to allow hVM consensus update functions to access these
	// to extract the geometry changes they represent.
	// TODO: consider refactor that allows these blocks to be passed directly
	// into the hVM consensus update functions to make this easier to reason about.
	tempBlocks   map[string]*types.Block
	futureBlocks *lru.Cache[common.Hash, *types.Block]
	tempHeaders  map[string]*types.Header

	btcAttributesDepCacheKey   btcAttrCacheKey
	btcAttributesDepCacheEntry *types.BtcAttributesDepositedTx

	missingProgressionBlocks *wire.MsgHeaders

	ctx context.Context

	keystoneMtx         sync.RWMutex
	keystoneBackfillMtx sync.RWMutex

	keystonesBackfilled bool

	logger *tracing.Hooks

	lastForkReadyAlert time.Time // Last time there was a fork readiness print out

	stateSizer *state.SizeTracker // State size tracking

}

// getHeaderModeTBCEVMHeader returns the EVM header for which the
// header-only TBC node represents the cumulative Bitcoin state knowledge
func (bc *BlockChain) getHeaderModeTBCEVMHeader() (*types.Header, error) {
	if !bc.hvmEnabled {
		return nil, fmt.Errorf("getHeaderModeTBCEVMHeader() called but hVM is not enabled")
	}

	stateId, err := bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
	if err != nil {
		return nil, err
	}

	// We are at genesis configuration, no error but no header represented yet
	if bytes.Equal(stateId[:], hVMGenesisUpstreamId[:]) {
		return nil, nil
	}

	stateBlockHash := common.BytesToHash(stateId[:])
	header := bc.getHeaderFromDiskOrHoldingPen(stateBlockHash)

	if header != nil {
		return header, nil
	}
	return nil, fmt.Errorf("unable to find EVM header corresponding to hash %x", stateBlockHash[:])
}

// getHvmPhase0ActivationBlock descends the blockchain until it
// finds the first block which is after the hVM Phase 0 activation timestamp.
// TODO: cache this somewhere after calculating and make sure reorgs are considered to update cache
func (bc *BlockChain) getHvmPhase0ActivationBlock() (*types.Header, error) {
	if !bc.hvmEnabled {
		log.Warn("getHvmPhase0ActivationBlock called when hVM is disabled")
		return nil, fmt.Errorf("hVM is disabled")
	}

	cursor := bc.CurrentBlock()

	// Find the block where hVM Phase 0 activation occurs
	// TODO: Make this more efficient with intelligent indexing based on timestamp
	// instead of this simple descent.
	// Note: genesis block cannot contain a Bitcoin Attributes Deposited tx.
	for cursor.Number.Uint64() > 1000 {
		header := bc.GetHeaderByNumber(cursor.Number.Uint64() - 1000)
		if !bc.chainConfig.IsHvm0(header.Time) {
			// Our tip is now less than 1000 blocks above activation height, descend individually
			break
		}

		cursor = header
	}

	// Walk back until we are either at genesis or we pass behind the hVM Phase 0 activation timestamp
	for {
		// we are at genesis, no ParentHash should exist
		if cursor.Number.Uint64() == 0 {
			break
		}

		header := bc.GetHeaderByHash(cursor.ParentHash)
		if bc.chainConfig.IsHvm0(header.Time) && header.Number.Uint64() > 0 {
			cursor = header
			continue
		}
		break
	}

	return cursor, nil
}

// performFullHvmHeaderStateRestore is used to clear and completely regenerate
// the embedded header-only TBC node from genesis state, applying all
// hVM header state transitions in all blocks up to the current configured
// EVM tip.
func (bc *BlockChain) performFullHvmHeaderStateRestore() {
	if !bc.hvmEnabled {
		log.Warn("performFullHvmHeaderStateRestore called but hVM is disabled")
		return
	}

	log.Info("*****************************************************************")
	log.Info("Performing full hVM header state restore, this could take awhile.")

	bc.resetHvmHeaderNodeToGenesis()

	tip := bc.CurrentBlock()

	cursor, err := bc.getHvmPhase0ActivationBlock()
	if err != nil {
		log.Crit("Unable to get hVM Phase 0 activation block", "err", err)
	}

	// Walk cursor forward until we get to our tip, assumes GetBlockByNumber correctly returns
	// blocks on the canonical chain which will eventually reach the tip returned by bc.CurrentBlock() above
	log.Info(fmt.Sprintf("Performing full hVM header state restore starting at block %s @ %d",
		cursor.Hash().String(), cursor.Number.Uint64()))

	for {
		// Print out progress so we know restore is progressing
		if cursor.Number.Uint64()%1000 == 0 {
			log.Info(fmt.Sprintf("Processing hVM header state changes for block %s @ %d",
				cursor.Hash().String(), cursor.Number.Uint64()))
		}
		err := bc.applyHvmHeaderConsensusUpdate(cursor, false, false)
		if err != nil {
			log.Crit(fmt.Sprintf("Failed to fully restore hVM state, encountered an error processing hVM "+
				"state updates for block %s @ %d", cursor.Hash().String(), cursor.Number.Uint64()), "err", err)
		}
		if cursor.Number.Uint64() < tip.Number.Uint64() {
			next := bc.GetHeaderByNumber(cursor.Number.Uint64() + 1)
			if next != nil {
				cursor = next
			} else {
				// next should never be nil because we are below tip
				log.Crit(fmt.Sprintf("Reached unexpected end of chain while restoring hVM header state, "+
					"last header applied: %s @ %d", cursor.Hash().String(), cursor.Number.Uint64()))
			}
		} else {
			break
		}
	}
	log.Info(fmt.Sprintf("Done performing full hVM header state restore. Tip: %s @ %d", cursor.Hash().String(),
		cursor.Number.Uint64()))
}

// resetHvmHeaderNodeToGenesis is used in the event that chain corruption
// occurs either in the header-only TBC node specifically or in geth in general.
// This method deletes the entire header-only TBC node's data directory,
// and configures it with the effective genesis block defined in the config.
// If this is called to fix a header mode TBC corruption (rather than as part of
// a broader overall EVM reset to genesis), caller must also process all of
// the header state transitions defined by Bitcoin Attributes Deposited
// transactions in the current chain since the activation of hVM Phase 0.
// If this function fails to delete the data directory and restart external
// header mode TBC correctly, it fails with a critical error as we will be
// unable to properly process Hemi state transitions.
func (bc *BlockChain) resetHvmHeaderNodeToGenesis() {
	// Exclude the lock-free GetMissingBtcBlocks reader for the whole teardown+reassign: between
	// ExternalHeaderTearDown (which closes the old node's leveldb) and initHvmHeaderNode (which reassigns
	// bc.tbcHeaderNode) the node is unusable, so a concurrent read would hit a torn pointer / use-after-
	// teardown. See tbcHeaderNodeMu. initHvmHeaderNode is also called directly at startup via
	// SetupHvmHeaderNode, before the broadcast goroutine exists, so that path needs no lock; locking only
	// here also avoids a reentrant Lock when reset calls initHvmHeaderNode.
	bc.tbcHeaderNodeMu.Lock()
	defer bc.tbcHeaderNodeMu.Unlock()

	log.Info("Resetting hVM header TBC node to genesis")
	if bc.tbcHeaderNode != nil {
		log.Info("Header-only TBC instance running, tearing down...")
		err := bc.tbcHeaderNode.ExternalHeaderTearDown()
		if err != nil {
			log.Crit("resetHvmHeaderNodeToGenesis failed when calling ExternalHeaderTearDown on TBC", "err", err)
		}
	} else {
		log.Info("Header-only TBC instance is not running, nothing to tear down. Continuing with genesis reset.")
	}

	// Network-scoped delete: remove ONLY this node's own <LevelDBHome>/<canonicalNet> store, NEVER the
	// parent LevelDBHome. The parent can also hold a sibling network's store — e.g. a migrated <…>/mainnet/
	// alongside the retired <…>/testnet3.migrated-*/ rollback backup — that a parent-wipe would destroy, and
	// every steady-state recovery path (recoverReapplyHvmState, the writeBlockAndSetHead inline restore, the
	// snap-completion reset) routes through here. canonicalBTCNetwork is load-bearing, not cosmetic: TBC writes
	// "upgradetest" under <…>/testnet3/, so a raw-name Join would delete a nonexistent dir and leave the real
	// store, after which the genesis-state assertion below would crit on the stale reopen.
	dataDir := hvmHeaderStoreDir(bc.tbcHeaderNodeConfig.LevelDBHome, bc.tbcHeaderNodeConfig.Network)

	path, _ := filepath.Abs(dataDir)
	log.Info(fmt.Sprintf("Deleting TBC external header mode instance data directory: %s", path))

	if err := os.RemoveAll(dataDir); err != nil {
		log.Crit(fmt.Sprintf("ResetHvmHeaderNodeToGenesis unable to delete external header mode TBC "+
			"data directory %s", dataDir))
	}

	if _, err := os.Open(dataDir); os.IsNotExist(err) {
		log.Info(fmt.Sprintf("Successfully deleted external header mode TBC data directory %s", dataDir))
	} else {
		log.Crit(fmt.Sprintf("The data directory %s still exists after attempting to delete", dataDir))
	}

	log.Info("Deleted hVM header TBC node data directory", "dataDir", dataDir)

	bc.initHvmHeaderNode(bc.tbcHeaderNodeConfig)

	// Make sure after initializing, the stateId is set to the hVMGenesisUpstreamId as expected
	stateId, err := bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
	if err != nil {
		log.Crit("Unable to reset external header mode TBC to genesis configuration, after reset unable to "+
			"query upstream state id", "err", err)
	}
	if !bytes.Equal(stateId[:], hVMGenesisUpstreamId[:]) {
		log.Crit(fmt.Sprintf("Unable to reset external header mode TBC to genesis configuration, after reset "+
			"the TBC instance reports an unexpected upstream state id of %x when the default of %x was expected",
			stateId[:], hVMGenesisUpstreamId[:]))
	}
}

// btcGenesisCheckpoint pins a canonical (effective-genesis height, Bitcoin block hash) pair.
type btcGenesisCheckpoint struct {
	height uint64
	hash   string // EffectiveGenesisBlock.BlockHash().String()
}

// hvmGenesisCheckpoints maps a TBC network to its canonical effective-genesis checkpoint(s). The
// testnet3 entry is op-geth's compiled default (ethconfig.Defaults.HvmGenesisHeader/Height); the
// mainnet and testnet deployments set no override and rely on the binary default, so the
// default is the canonical pairing. upgradetest == testnet3 (TBC lockstep). A Hemi-mainnet
// op-geth build compiles in its own Bitcoin-mainnet default; add its checkpoint here when this build
// supports mainnet hVM (today eth/backend.go defaults the consensus node to testnet3 via
// config.TBCNetwork → ethconfig.DefaultTBCNetwork).
// TestHvmGenesisCheckpointMatchesCanonicalHeader pins these to the canonical header so they cannot drift.
var hvmGenesisCheckpoints = map[string][]btcGenesisCheckpoint{
	// testnet3 pins two accepted effective-genesis pairs:
	//
	//   [0] The compiled default (ethconfig.Defaults.HvmGenesisHeader/Height). This MUST stay element
	//       [0]: the lockstep tests in eth/backend_hvm_genesis_test.go pin the default to this pair, and
	//       the in-core inspection test reads testnet3[0].
	//
	//   [1] Backwards-compatibility pin for the deployed fleet. These nodes have run this Bitcoin-mainnet
	//       effective-genesis pair (set via --hvm.genesisheight / --hvm.genesisheader) since before this
	//       genesis-pairing guard existed. The TBC consensus network defaults to "testnet3" in
	//       eth/backend.go (buildHvmHeaderNodeConfig sets it from config.TBCNetwork → ethconfig.DefaultTBCNetwork)
	//       even though this pair is a Bitcoin-mainnet
	//       (height, header); because the ENTIRE fleet shares the same override the pairing is internally
	//       consistent and does not split the network — it is a legacy mislabel, not a desync. The guard
	//       is config-only and runs at every startup for every node (snap-synced or full), so without this
	//       entry the running fleet would log.Crit on boot. Keep it pinned until the network is properly
	//       migrated off the override (i.e. the TBC network is wired from chain config and the data dir is
	//       relocated); removing it bricks the live fleet.
	"testnet3": {
		{height: 3522419, hash: "000000000000000096c98151accc5ee217d7cc4ff1e59a3d91e4c9365c4ea144"},
		// [1] DEFER-state pin: a legacy node (or the migration's defer fallback) runs Network=testnet3 over
		//     the Bitcoin-mainnet pair below. Sourced from the ONE shared constant (core/vm/hvm_genesis.go),
		//     dual-pinned identically under "mainnet" so BOTH the deferred and migrated states pass the guard.
		{height: vm.MainnetHvmGenesisHeight, hash: vm.MainnetHvmGenesisHash},
	},
	// MIGRATED-state pin: a migrated mainnet node runs Network=mainnet over the SAME {883092,…eda8} pair.
	// Keep this dual-pin (with testnet3[1]) until a verifiable fleet-wide "migration complete" signal confirms
	// zero deferred nodes remain; removing testnet3[1] on a timer would crit any still-deferred node.
	"mainnet":     {{height: vm.MainnetHvmGenesisHeight, hash: vm.MainnetHvmGenesisHash}},
	"upgradetest": {{height: 3522419, hash: "000000000000000096c98151accc5ee217d7cc4ff1e59a3d91e4c9365c4ea144"}},
}

// canonicalBTCNetwork maps a configured TBC network name to its on-disk / chaincfg canonical form, mirroring
// TBC's own network-name rewrite in the heminetwork database/tbcd/level package: "upgradetest" is stored as
// "testnet3"; everything else is identity. The on-disk store path (<HvmHeaderDataDir>/<net>), the
// network-scoped reset, and the migration detection must all use this canonical form so they agree with
// where TBC actually writes — a raw-name Join would target a nonexistent dir and silently miss the real store.
func canonicalBTCNetwork(network string) string {
	if network == "upgradetest" {
		return "testnet3"
	}
	return network
}

type hvmGenesisPairing int

const (
	hvmGenesisPairingCanonical hvmGenesisPairing = iota // matches a known checkpoint exactly
	hvmGenesisPairingCustom                             // touches no checkpoint -> fully custom (allowed)
	hvmGenesisPairingMismatch                           // height XOR hash matches a checkpoint -> desynced pair
)

// classifyHvmGenesisPairing detects a desynced hVM effective-genesis pair: the height
// (GenesisHeightOffset) and the header (EffectiveGenesisBlock) are two independently-overridable
// knobs, and the btcd absolute-height retarget math is correct only if the height is the true Bitcoin
// height of the header. For the network's canonical checkpoints, if exactly one of (height, hash)
// matches while the other diverges the knobs are out of sync (mismatch); a full match is canonical;
// touching neither is a fully-custom genesis (allowed, e.g. localnet or the height-0 test harness).
// Pure, so it is unit-testable without log.Crit.
func classifyHvmGenesisPairing(network string, height uint64, hash string) hvmGenesisPairing {
	mismatch := false
	for _, cp := range hvmGenesisCheckpoints[network] {
		hEq, sEq := cp.height == height, cp.hash == hash
		if hEq && sEq {
			return hvmGenesisPairingCanonical
		}
		if hEq != sEq {
			mismatch = true
		}
	}
	if mismatch {
		return hvmGenesisPairingMismatch
	}
	return hvmGenesisPairingCustom
}

// IsCanonicalHvmGenesisPairing reports whether (network, height, headerHash) exactly matches a pinned
// canonical hVM effective-genesis checkpoint. Exported so a package that imports both core and
// ethconfig (e.g. package eth) can assert that ethconfig.Defaults.HvmGenesisHeader/Height stays in
// lockstep with hvmGenesisCheckpoints: ethconfig imports core, so the checkpoint map cannot be
// compared against the defaults from within core itself without an import cycle. Without that external
// assertion, re-pinning ethconfig.Defaults without updating the checkpoint would brick every enforced
// node at startup (initHvmHeaderNode crits) while the in-core binding test stays green.
func IsCanonicalHvmGenesisPairing(network string, height uint64, hash string) bool {
	return classifyHvmGenesisPairing(network, height, hash) == hvmGenesisPairingCanonical
}

// hvmMigrationAwareCrit fatally fails a hVM operation. During an in-progress migration rebuild
// (bc.hvmMigrationInProgress) it routes through migrationCrit so the "failed" meter is marked and the
// in-progress gauge cleared before log.Crit's os.Exit (the deferred gauge-clear in
// migrateHvmHeaderNode never runs across os.Exit). On the normal boot / reset / steady-state apply paths it is a
// plain fatal crit. Used by initHvmHeaderNode's I/O crits and by applyHvmHeaderConsensusUpdate's crits, both of
// which are reachable inside the migration rebuild window (init during the rebuild, applyHvmHeaderConsensusUpdate during the
// forward catch-up).
func (bc *BlockChain) hvmMigrationAwareCrit(msg string, ctx ...interface{}) {
	if bc.hvmMigrationInProgress {
		migrationCrit(msg, ctx...)
		return
	}
	log.Crit(msg, ctx...)
}

func (bc *BlockChain) initHvmHeaderNode(config *tbc.Config) {
	if config.ExternalHeaderMode != true {
		log.Crit("initHvmHeaderNode called with a TBC config that does not have ExternalHeaderMode set")
	}

	// Contextual-difficulty: refuse to start on a desynced hVM effective-genesis pair. A wrong GenesisHeightOffset
	// for the configured EffectiveGenesisBlock mis-aligns the contextual-difficulty retarget boundary
	// (%BlocksPerRetarget) and, under contextual-difficulty enforcement, can false-reject every honest boundary header
	// — a network-wide split. The node's own ExternalHeaderSetup trusts the pair, so this is the one
	// place to catch the misconfiguration.
	if config.EffectiveGenesisBlock != nil {
		switch classifyHvmGenesisPairing(config.Network, config.GenesisHeightOffset, config.EffectiveGenesisBlock.BlockHash().String()) {
		case hvmGenesisPairingMismatch:
			log.Crit("Refusing to start: hVM effective-genesis height/header pair (from --hvm.genesisheight / "+
				"--hvm.genesisheader, or the compiled defaults) is DESYNCED from the canonical checkpoint for this "+
				"network (the height must be the true Bitcoin height of the genesis header; a mismatched pair "+
				"mis-aligns the retarget boundary and can split the network — revert to the canonical pair, or if "+
				"ethconfig.Defaults was re-pinned update core.hvmGenesisCheckpoints to match)",
				"network", config.Network, "height", config.GenesisHeightOffset,
				"header", config.EffectiveGenesisBlock.BlockHash().String())
		case hvmGenesisPairingCustom:
			// GenesisHeightOffset feeds the absolute-height retarget boundary (%BlocksPerRetarget), so
			// on a difficulty-enforced network it is a consensus parameter. A pair that matches no canonical
			// checkpoint cannot be trusted as the true Bitcoin (height,header) and would split from
			// canonical nodes whose offset differs — so refuse to start (fail closed) on any real network.
			// Only the localnet/regtest dev network (single-operator, intentionally without a pinned
			// genesis) is allowed through with a warning; any other network (including a mainnet build
			// that has not yet added its checkpoint here) must be pinned before it can run enforced.
			if config.Network != "localnet" {
				// Include the canonical remediation values for this network so the operator can
				// recover (mirrors the migration's defer-fallback crit). For mainnet that is the shared constant pair.
				canonHint := "<none pinned for this network>"
				if cps := hvmGenesisCheckpoints[config.Network]; len(cps) > 0 {
					canonHint = fmt.Sprintf("height=%d hash=%s", cps[0].height, cps[0].hash)
				}
				wantHeader := ""
				if canonicalBTCNetwork(config.Network) == "mainnet" {
					wantHeader = vm.MainnetHvmGenesisHeader // the exact --hvm.genesisheader bytes the flag needs
				}
				log.Crit("Refusing to start: hVM effective-genesis (height,header) pair (from --hvm.genesisheight / "+
					"--hvm.genesisheader, or the compiled defaults) is NOT a pinned canonical pair for this "+
					"difficulty-enforced network; the height is a consensus parameter (it positions the retarget "+
					"boundary) and a non-canonical offset splits from canonical nodes — set --hvm.genesisheight / "+
					"--hvm.genesisheader to the canonical pair below (or add the canonical checkpoint to core.hvmGenesisCheckpoints)",
					"network", config.Network, "gotHeight", config.GenesisHeightOffset,
					"gotHash", config.EffectiveGenesisBlock.BlockHash().String(),
					"wantCanonical", canonHint, "wantHeader", wantHeader)
			}
			log.Warn("hVM effective-genesis pair has no canonical checkpoint for the localnet dev network; cannot "+
				"verify the height/header pairing — ensure GenesisHeightOffset is the true Bitcoin height of the header",
				"network", config.Network, "height", config.GenesisHeightOffset,
				"header", config.EffectiveGenesisBlock.BlockHash().String())
		case hvmGenesisPairingCanonical:
			// matches the canonical checkpoint; nothing to verify
		default:
			// Defensive: the switch is exhaustive over today's three classifications, but a future
			// classification value must fail closed, never silently boot a node on an unclassified pairing.
			// The zero value is hvmGenesisPairingCanonical (routes to the Canonical arm), so this guards
			// only a hypothetical added enum value.
			log.Crit("Refusing to start: hVM effective-genesis pairing returned an unknown classification",
				"network", config.Network, "height", config.GenesisHeightOffset,
				"header", config.EffectiveGenesisBlock.BlockHash().String())
		}
	}

	// Contextual-difficulty: chaincfg <-> genesis-pairing lockstep. The consensus node's Network is used in two
	// independent places — the genesis-pairing classifier above (network -> hvmGenesisCheckpoints) and
	// the contextual-difficulty + PoW validators (network -> btcd chaincfg.Params, via vm.paramsForNetwork).
	// If a node booted on a Network the classifier accepts (or a localnet custom pair) but that has no
	// chaincfg params, every contextual-difficulty validation would return the unavailable/skip sentinel — mapping to
	// ErrCorruptHVMHeaderOnlyModeState on the apply path and wedging the node in a per-block restore loop.
	// Cross-check the two maps are in lockstep here (fail fast at startup). vm.SupportsBTCNetwork is the
	// dedicated chaincfg-membership probe (true iff vm.paramsForNetwork resolves the network).
	if !vm.SupportsBTCNetwork(config.Network) {
		log.Crit("Refusing to start: the hVM consensus node's Network has no btcd chaincfg params, so "+
			"contextual-difficulty / proof-of-work validation cannot be parameterized (the genesis-pairing "+
			"network and the validator-params network must be in lockstep) — add the network to "+
			"core/vm.paramsForNetwork or fix the configured network",
			"network", config.Network)
	}

	tbcHeaderNode, err := tbc.NewServer(config)
	if err != nil {
		bc.hvmMigrationAwareCrit("initHvmHeaderNode unable to create new TBC server", "err", err)
	}

	// Pass in the hVMGenesisUpstreamId, which will only be set by ExternalHeaderSetup if the TBC instance
	// has not been initialized with any headers yet.
	err = tbcHeaderNode.ExternalHeaderSetup(bc.ctx, hVMGenesisUpstreamId[:])
	if err != nil {
		// A re-open failure here is most often the store being held by another process (exactly one op-geth
		// process per HvmHeaderDataDir is required), or a still-held goleveldb directory lock leaked by an
		// upstream level.New error path on a prior deferred migration, or corrupt store
		// metadata. Name the likely causes so the failure is diagnosable instead of an opaque fatal.
		bc.hvmMigrationAwareCrit("initHvmHeaderNode unable to run ExternalHeaderSetup on TBC — the hVM header store could "+
			"not be opened; ensure exactly ONE op-geth process uses this HvmHeaderDataDir and restart. If it "+
			"recurs, a prior boot may have leaked the goleveldb directory lock or the store metadata is corrupt "+
			"and must be restored from backup", "err", err)
	}

	height, header, err := tbcHeaderNode.BlockHeaderBest(bc.ctx)
	if err != nil {
		bc.hvmMigrationAwareCrit("initHvmHeaderNode unable to get best block header after initialization", "err", err)
	}

	log.Info(fmt.Sprintf("After hVM external header node initialization, best header = %s @ %d",
		header.BlockHash().String(), height))

	bc.tbcHeaderNode = tbcHeaderNode
	bc.tbcHeaderNodeConfig = config
	bc.hvmEnabled = true
	// A node is difficulty-enforceable unless it is in the DEFER state — running testnet3
	// params over the Bitcoin-mainnet effective-genesis pair (the legacy mislabel / the migration's defer
	// fallback). A genuine testnet3 node (height 3522419), a localnet node, and a MIGRATED mainnet node
	// (Network=mainnet) are all enforceable. Keyed on the (network, height) pair, NOT the word "migrated", so
	// the genuine testnet3 fleet and the post-migration mainnet steady state both enforce correctly.
	bc.hvmDiffEnforceable.Store(!isLegacyDeferredPairing(config.Network, config.GenesisHeightOffset))
	if !bc.hvmDiffEnforceable.Load() {
		log.Warn("hVM difficulty enforcement DISABLED this boot: node is in the legacy DEFER state (testnet3 "+
			"params over the Bitcoin-mainnet genesis pair); it enforces only after migrating to network=mainnet. "+
			"Do NOT run this node as the active op-stack sequencer until it has migrated (it can package a "+
			"Bitcoin-Attributes header that enforced validators reject -> chain split)",
			"network", config.Network, "genesisHeight", config.GenesisHeightOffset)
	}
}

// isLegacyDeferredPairing reports the DEFER state: a node running on the RAW "testnet3" network over the
// Bitcoin-MAINNET effective-genesis pair (height 883092) — the legacy "mainnet-as-testnet3" mislabel and the
// migration's defer fallback (which sets config.Network = "testnet3"). Such a node must NOT enforce difficulty:
// it would validate real mainnet headers under TestNet3Params (the ReduceMinDifficulty 20-minute rule),
// splitting from a correctly-migrated fleet.
//
// Matched on the RAW network "testnet3", NOT canonicalBTCNetwork — to stay CONSISTENT with the
// genesis-pairing guard, whose dual-pin {883092,…eda8} lives under the "testnet3" (and "mainnet") checkpoint
// keys but NOT under "upgradetest". An upgradetest node over the mainnet pair is rejected (Custom -> crit) by
// classifyHvmGenesisPairing before it ever runs, so it is not a valid defer state; canonicalizing here would
// have this function disagree (call it deferred) with a guard that refuses to boot it. The genuine fleet and
// the defer path both use the raw "testnet3" network, so this narrowing does not affect any real node.
func isLegacyDeferredPairing(network string, genesisHeight uint64) bool {
	return network == "testnet3" && genesisHeight == vm.MainnetHvmGenesisHeight
}

func (bc *BlockChain) SetupDeucalion(pctx context.Context, address string) error {
	d, err := deucalion.New(&deucalion.Config{
		ListenAddress: address,
	})
	if err != nil {
		return err
	}

	ctx, cancel := context.WithCancel(pctx)

	go func() {
		defer cancel()
		err := d.Run(ctx, nil, func(ctx context.Context) (bool, any, error) {
			return bc.healthyNode.Load(), bc.CurrentBlock(), nil
		})
		if err != nil && !errors.Is(err, context.Canceled) {
			log.Error("deucalion terminated with error", "err", err)
			return
		}
		log.Info("deucalion clean shutdown")
	}()

	go func() {
		defer cancel()
		for {
			select {
			case <-ctx.Done():
				return
			case <-time.After(progressionInterval):
				bestTime := time.Unix(int64(bc.CurrentHeader().Time), 0)
				if time.Since(bestTime) > maxBlockAge {
					bc.healthyNode.Store(false)
				} else {
					bc.healthyNode.Store(true)
				}
			}
		}
	}()

	return nil
}

func (bc *BlockChain) SetupHvmHeaderNode(config *tbc.Config) {
	// Automatic legacy "mainnet-as-testnet3" migration, at the TOP before any dir is opened. When
	// it fully rebuilt a migrated mainnet store it returns true and bc.tbcHeaderNode is already initialized at
	// the EVM tip — skip the normal init/restore. When it deferred it mutated config.Network back to "testnet3"
	// and returns false, so the normal boot below runs on the untouched legacy store. When no migration was
	// needed it returns false unchanged (the common path: genuine testnet3, or an already-migrated mainnet).
	if bc.maybeMigrateHvmHeaderNode(config) {
		return
	}

	bc.initHvmHeaderNode(config)

	// Get the current state ID
	stateId, err := bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
	if err != nil {
		log.Crit("Unable to get upstream state ID from TBC header node", "err", err)
	}

	current := bc.currentBlock.Load()
	currentHash := current.Hash()

	log.Info(fmt.Sprintf("hVM node initiated, stateId=%x, current EVM tip=%s", stateId[:], currentHash.String()))

	tnFix, _ := hex.DecodeString("2decc762c95d7c392b5e852fc861aab2044b5e5748d1696a0cb00de70014d0f4")
	// Special case for testnet — network-gated so this testnet3-specific bad-BTC-header surgery
	// can NEVER run on a migrated mainnet node (which reaches this block on its 2nd+ boot, when the migration
	// is already complete and maybeMigrateHvmHeaderNode returns false). The stateId is testnet3-specific, but
	// the guard makes the intent structural rather than relying on hash non-collision.
	if canonicalBTCNetwork(config.Network) == "testnet3" && bytes.Equal(stateId[:], tnFix[:]) {
		correctPrevStateId, _ := hex.DecodeString("4d1bafde31ffe9d02b81131333340c762a639865361b9429cdf21181e78d8bff")
		badBTCBlock, _ := hex.DecodeString("aef45566e1303e620317eb7073aff8eca8d58834d58fa4cceabd010000000000")

		var badBlock chainhash.Hash
		_ = badBlock.SetBytes(badBTCBlock[:])
		badBlockHeader, _, err := bc.tbcHeaderNode.BlockHeaderByHash(context.Background(), badBlock)
		if err != nil {
			log.Error("Unable to get bad BTC block", "block", badBTCBlock, "err", err)
			// Backup: get tip which will be same bad BTC block
			_, badBlockHeader, err = bc.tbcHeaderNode.BlockHeaderBest(context.Background())
			if err != nil {
				log.Crit("Unable to get tip")
			}

		}

		headersToRemove := make([]*wire.BlockHeader, 1)
		headersToRemove[0] = badBlockHeader

		msgHeaders := &wire.MsgHeaders{
			Headers: headersToRemove,
		}

		correctHead, _ := hex.DecodeString("d870eebda743ce0b264480ffbaec8686f1baadb9634a2eb4c511a80000000000")

		var ch chainhash.Hash
		_ = ch.SetBytes(correctHead[:])
		prevHeader, _, err := bc.tbcHeaderNode.BlockHeaderByHash(context.Background(), ch)
		if err != nil {
			log.Error("Unable to get correct previous block", "block", badBTCBlock, "err", err)
			// Backup: get previous block
			prevHeader, _, err = bc.tbcHeaderNode.BlockHeaderByHash(context.Background(), badBlockHeader.PrevBlock)
			if err != nil {
				log.Crit("Unable to get previous block")
			}
		}

		// Remove partial hVM state transition and set state back to hVM state at 4d1bafde31ffe9d02b81131333340c762a639865361b9429cdf21181e78d8bff
		_, _, err = bc.tbcHeaderNode.RemoveExternalHeaders(context.Background(), msgHeaders, prevHeader, correctPrevStateId)
		if err != nil {
			log.Crit("Unable to remove external headers", "err", err)
		}

		// Get updated state ID after fix to continue initialization
		stateId, err = bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
		if err != nil {
			log.Crit("Unable to get upstream state ID from TBC header node", "err", err)
		}
	}

	if bytes.Equal(stateId[:], hVMGenesisUpstreamId[:]) {
		// TBC claims to be in its genesis configuration, check to ensure its best header is the hVM genesis header
		_, bestHeader, err := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
		if err != nil {
			log.Crit("SetupHvmHeaderNode unable to get best block header from TBC which claims to be in genesis"+
				" initialization state", "err", err)
		}

		bestHeaderHash := bestHeader.BlockHash()
		genesisHash := config.EffectiveGenesisBlock.BlockHash()

		if bc.chainConfig.IsHvm0(current.Time) {
			// Current tip is after hVM Phase 0 activation time, so header-only mode TBC node should not be
			// at genesis state ID. Attempt recovery to align header-only mode TBC with current EVM chain tip.
			bc.performFullHvmHeaderStateRestore()

			// Check to make sure state restore was successful
			postRestoreStateId, err := bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
			if err != nil {
				log.Crit("Unable to get upstream state ID from lightweight TBC node after attempting restore.")
			}

			if bytes.Equal(postRestoreStateId[:], currentHash[:]) {
				log.Info(fmt.Sprintf("Successfully regenerated lightweight TBC state to match EVM tip %s", currentHash.String()))
			} else {
				// Failed to restore, exit
				log.Crit(fmt.Sprintf("Attempted to regenerate lightweight tBC state to match EVM tip %s "+
					"but after restore upstream state ID is %x", currentHash.String(), postRestoreStateId[:]))
			}
		} else {
			if bytes.Equal(bestHeaderHash[:], genesisHash[:]) {
				log.Info("SetupHvmHeaderNode has determined that the external header mode TBC is in its genesis state" +
					" and initialized correctly.")
			}
		}

	} else {
		potentialBlockHash := common.BytesToHash(stateId[:])
		potentialHeader := bc.GetHeaderByHash(potentialBlockHash)

		if potentialHeader != nil {
			// TBC has already been progressed with EVM blocks prior, as its upstream state ID corresponds
			// to a known block from the Hemi chain
			log.Info(fmt.Sprintf("SetupHvmHeaderNode had determined that the external header mode TBC currently"+
				" represents block %s @ %d", potentialHeader.Hash().String(), potentialHeader.Number.Uint64()))
		} else {
			// TBC is in an invalid state, attempt to recover it
			log.Info(fmt.Sprintf("The hVM header-only TBC node has an invaid state on startup; stateId=%x,"+
				" attempting full restore from hVM activation height", stateId))
			bc.performFullHvmHeaderStateRestore()
		}
	}
}

// NewBlockChain returns a fully initialised block chain using information
// available in the database. It initialises the default Ethereum Validator
// and Processor.
func NewBlockChain(db ethdb.Database, genesis *Genesis, overrides *ChainOverrides, engine consensus.Engine, cfg *BlockChainConfig, shouldPreserve func(header *types.Header) bool, txLookupLimit *uint64, ctx context.Context) (*BlockChain, error) {
	if cfg == nil {
		cfg = DefaultConfig()
	}

	// Open trie database with provided config
	enableVerkle, err := EnableVerkleAtGenesis(db, genesis)
	if err != nil {
		return nil, err
	}
	triedb := triedb.NewDatabase(db, cfg.triedbConfig(enableVerkle))

	// Write the supplied genesis to the database if it has not been initialized
	// yet. The corresponding chain config will be returned, either from the
	// provided genesis or from the locally stored configuration if the genesis
	// has already been initialized.
	chainConfig, genesisHash, compatErr, err := SetupGenesisBlockWithOverride(db, triedb, genesis, cfg.Overrides)
	if err != nil {
		return nil, err
	}
	log.Info("")
	log.Info(strings.Repeat("-", 153))
	for _, line := range strings.Split(chainConfig.Description(), "\n") {
		log.Info(line)
	}
	log.Info(strings.Repeat("-", 153))
	log.Info("")

	if chainConfig.IsOptimism() && chainConfig.RegolithTime == nil {
		log.Warn("Optimism RegolithTime has not been set")
	}

	log.Info("going to create block chain", "isthmus time", chainConfig.IsthmusTime)

	bc := &BlockChain{
		chainConfig:   chainConfig,
		cfg:           cfg,
		db:            db,
		triedb:        triedb,
		triegc:        prque.New[int64, common.Hash](nil),
		chainmu:       syncx.NewClosableMutex(),
		bodyCache:     lru.NewCache[common.Hash, *types.Body](bodyCacheLimit),
		bodyRLPCache:  lru.NewCache[common.Hash, rlp.RawValue](bodyCacheLimit),
		receiptsCache: lru.NewCache[common.Hash, []*types.Receipt](receiptsCacheLimit),
		blockCache:    lru.NewCache[common.Hash, *types.Block](blockCacheLimit),
		txLookupCache: lru.NewCache[common.Hash, txLookup](txLookupCacheLimit),
		futureBlocks:  lru.NewCache[common.Hash, *types.Block](maxFutureBlocks),
		tempBlocks:    make(map[string]*types.Block),
		tempHeaders:   make(map[string]*types.Header),
		engine:        engine,
		ctx:           ctx,
		logger:        cfg.VmConfig.Tracer,
	}
	bc.hc, err = NewHeaderChain(db, chainConfig, engine, bc.insertStopped)
	if err != nil {
		return nil, err
	}
	bc.flushInterval.Store(int64(cfg.TrieTimeLimit))
	bc.statedb = state.NewDatabase(bc.triedb, nil)
	bc.validator = NewBlockValidator(chainConfig, bc)
	bc.prefetcher = newStatePrefetcher(chainConfig, bc.hc)
	bc.processor = NewStateProcessor(bc.hc)

	genesisHeader := bc.GetHeaderByNumber(0)
	if genesisHeader == nil {
		return nil, ErrNoGenesis
	}
	bc.genesisBlock = types.NewBlockWithHeader(genesisHeader)

	bc.currentBlock.Store(nil)
	bc.currentSnapBlock.Store(nil)
	bc.currentFinalBlock.Store(nil)
	bc.currentSafeBlock.Store(nil)

	// Update chain info data metrics
	chainInfoGauge.Update(metrics.GaugeInfoValue{"chain_id": bc.chainConfig.ChainID.String()})

	// If Geth is initialized with an external ancient store, re-initialize the
	// missing chain indexes and chain flags. This procedure can survive crash
	// and can be resumed in next restart since chain flags are updated in last step.
	if bc.empty() {
		rawdb.InitDatabaseFromFreezer(bc.db)
	}
	// Load blockchain states from disk
	if err := bc.loadLastState(); err != nil {
		return nil, err
	}
	// Make sure the state associated with the block is available, or log out
	// if there is no available state, waiting for state sync.
	head := bc.CurrentBlock()
	if !bc.HasState(head.Root) {
		if head.Number.Uint64() == 0 {
			// The genesis state is missing, which is only possible in the path-based
			// scheme. This situation occurs when the initial state sync is not finished
			// yet, or the chain head is rewound below the pivot point. In both scenarios,
			// there is no possible recovery approach except for rerunning a snap sync.
			// Do nothing here until the state syncer picks it up.
			log.Info("Genesis state is missing, wait state sync")
		} else {
			// Head state is missing, before the state recovery, find out the disk
			// layer point of snapshot(if it's enabled). Make sure the rewound point
			// is lower than disk layer.
			//
			// Note it's unnecessary in path mode which always keep trie data and
			// state data consistent.
			var diskRoot common.Hash
			if bc.cfg.SnapshotLimit > 0 && bc.cfg.StateScheme == rawdb.HashScheme {
				diskRoot = rawdb.ReadSnapshotRoot(bc.db)
			}
			if diskRoot != (common.Hash{}) {
				log.Warn("Head state missing, repairing", "number", head.Number, "hash", head.Hash(), "snaproot", diskRoot)

				snapDisk, err := bc.setHeadBeyondRoot(head.Number.Uint64(), 0, diskRoot, true)
				if err != nil {
					return nil, err
				}
				// Chain rewound, persist old snapshot number to indicate recovery procedure
				if snapDisk != 0 {
					rawdb.WriteSnapshotRecoveryNumber(bc.db, snapDisk)
				}
			} else {
				log.Warn("Head state missing, repairing", "number", head.Number, "hash", head.Hash())
				if _, err := bc.setHeadBeyondRoot(head.Number.Uint64(), 0, common.Hash{}, true); err != nil {
					return nil, err
				}
			}
		}
	}
	// Ensure that a previous crash in SetHead doesn't leave extra ancients
	if frozen, err := bc.db.Ancients(); err == nil && frozen > 0 {
		var (
			needRewind bool
			low        uint64
		)
		// The head full block may be rolled back to a very low height due to
		// blockchain repair. If the head full block is even lower than the ancient
		// chain, truncate the ancient store.
		fullBlock := bc.CurrentBlock()
		if fullBlock != nil && fullBlock.Hash() != bc.genesisBlock.Hash() && fullBlock.Number.Uint64() < frozen-1 {
			needRewind = true
			low = fullBlock.Number.Uint64()
		}
		// In snap sync, it may happen that ancient data has been written to the
		// ancient store, but the LastFastBlock has not been updated, truncate the
		// extra data here.
		snapBlock := bc.CurrentSnapBlock()
		if snapBlock != nil && snapBlock.Number.Uint64() < frozen-1 {
			needRewind = true
			if snapBlock.Number.Uint64() < low || low == 0 {
				low = snapBlock.Number.Uint64()
			}
		}
		if needRewind {
			log.Error("Truncating ancient chain", "from", bc.CurrentHeader().Number.Uint64(), "to", low)
			if err := bc.SetHead(low); err != nil {
				return nil, err
			}
		}
	}

	if bc.logger != nil && bc.logger.OnBlockchainInit != nil {
		bc.logger.OnBlockchainInit(chainConfig)
	}
	if bc.logger != nil && bc.logger.OnGenesisBlock != nil {
		if block := bc.CurrentBlock(); block.Number.Uint64() == 0 {
			alloc, err := getGenesisState(bc.db, block.Hash())
			if err != nil {
				return nil, fmt.Errorf("failed to get genesis state: %w", err)
			}
			if alloc == nil {
				return nil, errors.New("live blockchain tracer requires genesis alloc to be set")
			}
			bc.logger.OnGenesisBlock(bc.genesisBlock, alloc)
		}
	}
	bc.setupSnapshot()

	// Rewind the chain in case of an incompatible config upgrade.
	if compatErr != nil {
		log.Warn("Rewinding chain to upgrade configuration", "err", compatErr)
		if compatErr.RewindToTime > 0 {
			bc.SetHeadWithTimestamp(compatErr.RewindToTime)
		} else {
			bc.SetHead(compatErr.RewindToBlock)
		}
		rawdb.WriteChainConfig(db, genesisHash, chainConfig)
	}

	bc.engine.VerifyHeader(bc, bc.CurrentHeader())

	// Start tx indexer if it's enabled.
	if bc.cfg.TxLookupLimit >= 0 {
		bc.txIndexer = newTxIndexer(uint64(bc.cfg.TxLookupLimit), bc)
	}

	// Start state size tracker
	if bc.cfg.StateSizeTracking {
		stateSizer, err := state.NewSizeTracker(bc.db, bc.triedb)
		if err == nil {
			bc.stateSizer = stateSizer
			log.Info("Enabled state size metrics")
		} else {
			log.Info("Failed to setup size tracker", "err", err)
		}
	}
	return bc, nil
}

func (bc *BlockChain) setupSnapshot() {
	// Short circuit if the chain is established with path scheme, as the
	// state snapshot has been integrated into path database natively.
	if bc.cfg.StateScheme == rawdb.PathScheme {
		return
	}
	// Load any existing snapshot, regenerating it if loading failed
	if bc.cfg.SnapshotLimit > 0 {
		// If the chain was rewound past the snapshot persistent layer (causing
		// a recovery block number to be persisted to disk), check if we're still
		// in recovery mode and in that case, don't invalidate the snapshot on a
		// head mismatch.
		var recover bool
		head := bc.CurrentBlock()
		if layer := rawdb.ReadSnapshotRecoveryNumber(bc.db); layer != nil && *layer >= head.Number.Uint64() {
			log.Warn("Enabling snapshot recovery", "chainhead", head.Number, "diskbase", *layer)
			recover = true
		}
		snapconfig := snapshot.Config{
			CacheSize:  bc.cfg.SnapshotLimit,
			Recovery:   recover,
			NoBuild:    bc.cfg.SnapshotNoBuild,
			AsyncBuild: !bc.cfg.SnapshotWait,
		}
		bc.snaps, _ = snapshot.New(snapconfig, bc.db, bc.triedb, head.Root)

		// Re-initialize the state database with snapshot
		bc.statedb = state.NewDatabase(bc.triedb, bc.snaps)
	}
}

// empty returns an indicator whether the blockchain is empty.
// Note, it's a special case that we connect a non-empty ancient
// database with an empty node, so that we can plugin the ancient
// into node seamlessly.
func (bc *BlockChain) empty() bool {
	genesis := bc.genesisBlock.Hash()
	for _, hash := range []common.Hash{rawdb.ReadHeadBlockHash(bc.db), rawdb.ReadHeadHeaderHash(bc.db), rawdb.ReadHeadFastBlockHash(bc.db)} {
		if hash != genesis {
			return false
		}
	}
	return true
}

// loadLastState loads the last known chain state from the database. This method
// assumes that the chain manager mutex is held.
func (bc *BlockChain) loadLastState() error {
	// Restore the last known head block
	head := rawdb.ReadHeadBlockHash(bc.db)
	if head == (common.Hash{}) {
		// Corrupt or empty database, init from scratch
		log.Warn("Empty database, resetting chain")
		return bc.Reset()
	}
	headHeader := bc.GetHeaderByHash(head)
	if headHeader == nil {
		// Corrupt or empty database, init from scratch
		log.Warn("Head header missing, resetting chain", "hash", head)
		return bc.Reset()
	}

	var headBlock *types.Block
	if cmp := headHeader.Number.Cmp(new(big.Int)); cmp == 1 {
		// Make sure the entire head block is available.
		headBlock = bc.GetBlockByHash(head)
	} else if cmp == 0 {
		// On a pruned node the block body might not be available. But a pruned
		// block should never be the head block. The only exception is when, as
		// a last resort, chain is reset to genesis.
		headBlock = bc.genesisBlock
	}
	if headBlock == nil {
		// Corrupt or empty database, init from scratch
		log.Warn("Head block missing, resetting chain", "hash", head)
		return bc.Reset()
	}
	// Everything seems to be fine, set as the head block
	bc.currentBlock.Store(headHeader)
	headBlockGauge.Update(int64(headBlock.NumberU64()))

	// Restore the last known head header
	if head := rawdb.ReadHeadHeaderHash(bc.db); head != (common.Hash{}) {
		if header := bc.GetHeaderByHash(head); header != nil {
			headHeader = header
		}
	}
	bc.hc.SetCurrentHeader(headHeader)

	// Initialize history pruning.
	latest := max(headBlock.NumberU64(), headHeader.Number.Uint64())
	if err := bc.initializeHistoryPruning(latest); err != nil {
		return err
	}

	// Restore the last known head snap block
	bc.currentSnapBlock.Store(headBlock.Header())
	headFastBlockGauge.Update(int64(headBlock.NumberU64()))

	if head := rawdb.ReadHeadFastBlockHash(bc.db); head != (common.Hash{}) {
		if block := bc.GetBlockByHash(head); block != nil {
			bc.currentSnapBlock.Store(block.Header())
			headFastBlockGauge.Update(int64(block.NumberU64()))
		}
	}

	// Restore the last known finalized block and safe block
	// Note: the safe block is not stored on disk and it is set to the last
	// known finalized block on startup
	if head := rawdb.ReadFinalizedBlockHash(bc.db); head != (common.Hash{}) {
		if block := bc.GetBlockByHash(head); block != nil {
			bc.currentFinalBlock.Store(block.Header())
			headFinalizedBlockGauge.Update(int64(block.NumberU64()))
			bc.currentSafeBlock.Store(block.Header())
			headSafeBlockGauge.Update(int64(block.NumberU64()))
		}
	}

	// Issue a status log for the user
	var (
		currentSnapBlock  = bc.CurrentSnapBlock()
		currentFinalBlock = bc.CurrentFinalBlock()
	)
	if headHeader.Hash() != headBlock.Hash() {
		log.Info("Loaded most recent local header", "number", headHeader.Number, "hash", headHeader.Hash(), "age", common.PrettyAge(time.Unix(int64(headHeader.Time), 0)))
	}
	log.Info("Loaded most recent local block", "number", headBlock.Number(), "hash", headBlock.Hash(), "age", common.PrettyAge(time.Unix(int64(headBlock.Time()), 0)))
	if headBlock.Hash() != currentSnapBlock.Hash() {
		log.Info("Loaded most recent local snap block", "number", currentSnapBlock.Number, "hash", currentSnapBlock.Hash(), "age", common.PrettyAge(time.Unix(int64(currentSnapBlock.Time), 0)))
	}
	if currentFinalBlock != nil {
		log.Info("Loaded most recent local finalized block", "number", currentFinalBlock.Number, "hash", currentFinalBlock.Hash(), "age", common.PrettyAge(time.Unix(int64(currentFinalBlock.Time), 0)))
	}
	if pivot := rawdb.ReadLastPivotNumber(bc.db); pivot != nil {
		log.Info("Loaded last snap-sync pivot marker", "number", *pivot)
	}
	if pruning := bc.historyPrunePoint.Load(); pruning != nil {
		log.Info("Chain history is pruned", "earliest", pruning.BlockNumber, "hash", pruning.BlockHash)
	}
	return nil
}

// initializeHistoryPruning sets bc.historyPrunePoint.
func (bc *BlockChain) initializeHistoryPruning(latest uint64) error {
	freezerTail, _ := bc.db.Tail()

	switch bc.cfg.ChainHistoryMode {
	case history.KeepAll:
		if freezerTail == 0 {
			return nil
		}
		// The database was pruned somehow, so we need to figure out if it's a known
		// configuration or an error.
		predefinedPoint := history.PrunePoints[bc.genesisBlock.Hash()]
		if predefinedPoint == nil || freezerTail != predefinedPoint.BlockNumber {
			log.Error("Chain history database is pruned with unknown configuration", "tail", freezerTail)
			return errors.New("unexpected database tail")
		}
		bc.historyPrunePoint.Store(predefinedPoint)
		return nil

	case history.KeepPostMerge:
		if freezerTail == 0 && latest != 0 {
			// This is the case where a user is trying to run with --history.chain
			// postmerge directly on an existing DB. We could just trigger the pruning
			// here, but it'd be a bit dangerous since they may not have intended this
			// action to happen. So just tell them how to do it.
			log.Error(fmt.Sprintf("Chain history mode is configured as %q, but database is not pruned.", bc.cfg.ChainHistoryMode.String()))
			log.Error(fmt.Sprintf("Run 'geth prune-history' to prune pre-merge history."))
			return errors.New("history pruning requested via configuration")
		}
		predefinedPoint := history.PrunePoints[bc.genesisBlock.Hash()]
		if predefinedPoint == nil {
			log.Error("Chain history pruning is not supported for this network", "genesis", bc.genesisBlock.Hash())
			return errors.New("history pruning requested for unknown network")
		} else if freezerTail > 0 && freezerTail != predefinedPoint.BlockNumber {
			log.Error("Chain history database is pruned to unknown block", "tail", freezerTail)
			return errors.New("unexpected database tail")
		}
		bc.historyPrunePoint.Store(predefinedPoint)
		return nil

	default:
		return fmt.Errorf("invalid history mode: %d", bc.cfg.ChainHistoryMode)
	}
}

// SetHead rewinds the local chain to a new head. Depending on whether the node
// was snap synced or full synced and in which state, the method will try to
// delete minimal data from disk whilst retaining chain consistency.
func (bc *BlockChain) SetHead(head uint64) error {
	if _, err := bc.setHeadBeyondRoot(head, 0, common.Hash{}, false); err != nil {
		return err
	}
	// Send chain head event to update the transaction pool
	header := bc.CurrentBlock()
	if block := bc.GetBlock(header.Hash(), header.Number.Uint64()); block == nil {
		// In a pruned node the genesis block will not exist in the freezer.
		// It should not happen that we set head to any other pruned block.
		if header.Number.Uint64() > 0 {
			// This should never happen. In practice, previously currentBlock
			// contained the entire block whereas now only a "marker", so there
			// is an ever so slight chance for a race we should handle.
			log.Error("Current block not found in database", "block", header.Number, "hash", header.Hash())
			return fmt.Errorf("current block missing: #%d [%x..]", header.Number, header.Hash().Bytes()[:4])
		}
	}
	bc.chainHeadFeed.Send(ChainHeadEvent{Header: header})
	return nil
}

// SetHeadWithTimestamp rewinds the local chain to a new head that has at max
// the given timestamp. Depending on whether the node was snap synced or full
// synced and in which state, the method will try to delete minimal data from
// disk whilst retaining chain consistency.
func (bc *BlockChain) SetHeadWithTimestamp(timestamp uint64) error {
	if _, err := bc.setHeadBeyondRoot(0, timestamp, common.Hash{}, false); err != nil {
		return err
	}
	// Send chain head event to update the transaction pool
	header := bc.CurrentBlock()
	if block := bc.GetBlock(header.Hash(), header.Number.Uint64()); block == nil {
		// In a pruned node the genesis block will not exist in the freezer.
		// It should not happen that we set head to any other pruned block.
		if header.Number.Uint64() > 0 {
			// This should never happen. In practice, previously currentBlock
			// contained the entire block whereas now only a "marker", so there
			// is an ever so slight chance for a race we should handle.
			log.Error("Current block not found in database", "block", header.Number, "hash", header.Hash())
			return fmt.Errorf("current block missing: #%d [%x..]", header.Number, header.Hash().Bytes()[:4])
		}
	}
	bc.chainHeadFeed.Send(ChainHeadEvent{Header: header})
	return nil
}

// SetFinalized sets the finalized block.
func (bc *BlockChain) SetFinalized(header *types.Header) {
	bc.currentFinalBlock.Store(header)
	if header != nil {
		rawdb.WriteFinalizedBlockHash(bc.db, header.Hash())
		headFinalizedBlockGauge.Update(int64(header.Number.Uint64()))
	} else {
		rawdb.WriteFinalizedBlockHash(bc.db, common.Hash{})
		headFinalizedBlockGauge.Update(0)
	}
}

// SetSafe sets the safe block.
func (bc *BlockChain) SetSafe(header *types.Header) {
	bc.currentSafeBlock.Store(header)
	if header != nil {
		headSafeBlockGauge.Update(int64(header.Number.Uint64()))
	} else {
		headSafeBlockGauge.Update(0)
	}
}

// findCommonAncestor finds the common ancestor between two provided
// headers, or returns an error if it is unable to walk backwards the chain
// correctly.
// If either header is a direct parent of the other header, returns
// the parent header itself.
func (bc *BlockChain) findCommonAncestor(a *types.Header, b *types.Header) (*types.Header, error) {
	// Set cursor to the higher of the two headers
	highCursor := a
	lowCursor := b
	if b.Number.Uint64() > a.Number.Uint64() {
		highCursor = b
		lowCursor = a
	}

	lowHeight := lowCursor.Number.Uint64()

	// Cursor is the higher header, walk it back to lowHeight
	for i := highCursor.Number.Uint64(); i > lowHeight; i-- {
		highCursor = bc.GetHeader(highCursor.ParentHash, i-1)
	}

	if highCursor.Hash().Cmp(lowCursor.Hash()) == 0 {
		// If they are equal, then lowCursor is the ancestor
		return lowCursor, nil
	}

	if lowCursor.Number.Uint64() != highCursor.Number.Uint64() {
		// Sanity check, should be impossible
		log.Crit(fmt.Sprintf("when looking for common ancestor between %s @ %d and %s @ %d, "+
			"highCursor was walked back to height %d which doesn't match lowCursor height %d",
			a.Hash().String(), a.Number.Uint64(), b.Hash().String(), b.Number.Uint64(),
			highCursor.Number.Uint64(), lowCursor.Number.Uint64()))
	}

	// While high and low cursors are not the same block, walk each back together block-by-block
	for highCursor.Hash().Cmp(lowCursor.Hash()) != 0 {
		// Walk each cursor back to their parent
		highCursor = bc.GetHeader(highCursor.ParentHash, highCursor.Number.Uint64()-1)
		lowCursor = bc.GetHeader(lowCursor.ParentHash, lowCursor.Number.Uint64()-1)

		if highCursor.Number.Uint64() == 0 {
			return nil, fmt.Errorf("when looking for common ancestor between %s @ %d and %s @ %d, "+
				"we walked backwards to the genesis block without finding a common ancestor",
				a.Hash().String(), a.Number.Uint64(), b.Hash().String(), b.Number.Uint64())
		}
	}

	// high and low cursors match, found common ancestor
	return highCursor, nil
}

func (bc *BlockChain) HvmEnabled() bool {
	return bc.hvmEnabled
}

// SetAwaitingHvmSnapSync is called when an Ethereum protocol snap-sync has
// been completed to inform the blockchain to wait for an hVM snap sync instruction
// before performing any chain progression.
func (bc *BlockChain) SetAwaitingHvmSnapSync() {
	if !bc.HvmEnabled() {
		panic("cannot SetAwaitingHvmSnapSync with hvm disabled")
	}

	bc.hvmSnapMu.Lock()
	defer bc.hvmSnapMu.Unlock()
	// Do not re-arm the latch once this process has already completed its hVM snap sync. finishedHvmSnapSync
	// is the only set-once gate hvmSnapShouldRun/hvmSnapClaimCompletion consult (awaitingHvmSnapSync and
	// processingHvmSnapSync are transient), so a re-arm here (e.g. a
	// second in-process SnapSync entry after a rewind/restart-below-pivot) would leave awaitingHvmSnapSync=true
	// with no path back to hvmSnapMarkFinished — permanently closing the apply-path hVM consensus gate
	// (updateHvmHeaderConsensus / lightweight-tip advance / BtcAttr validation skipped for every later block).
	if bc.finishedHvmSnapSync {
		log.Info("Ignoring await-hVM-snap-sync request; this process already completed hVM snap sync")
		return
	}
	log.Info("Blockchain informed to await hVM snap sync")
	bc.awaitingHvmSnapSync = true
	hvmSnapAwaitingGauge.Update(1)
}

func (bc *BlockChain) HvmSnapSyncCompleted() bool {
	bc.hvmSnapMu.Lock()
	defer bc.hvmSnapMu.Unlock()
	return bc.finishedHvmSnapSync
}

// isAwaitingHvmSnapSync reports whether the chain is paused awaiting an hVM snap
// sync (block processing checks this on the hot path).
func (bc *BlockChain) isAwaitingHvmSnapSync() bool {
	bc.hvmSnapMu.Lock()
	defer bc.hvmSnapMu.Unlock()
	return bc.awaitingHvmSnapSync
}

// hvmSnapShouldRun reports whether the latch is in a state where a fresh snap attempt would be allowed to
// proceed: the chain is awaiting a snap sync, it has not finished, and no goroutine has claimed the
// exclusive completion work. The live entry gate is claimHvmSnapWaiterSlot, which re-checks these
// conditions (plus the stopping flag, dedupe, and the waiter cap); this predicate is a readable probe of
// that latch state. Multiple attempts may run the wait loop concurrently — that is what lets a later
// response with a reachable tip take over when an earlier one is wedged on an unreachable tip.
func (bc *BlockChain) hvmSnapShouldRun() bool {
	bc.hvmSnapMu.Lock()
	defer bc.hvmSnapMu.Unlock()
	return bc.awaitingHvmSnapSync && !bc.finishedHvmSnapSync && !bc.processingHvmSnapSync
}

// hvmSnapShouldStop reports whether a running attempt's wait loop should abandon:
// the round was finished, is no longer awaited, or another goroutine has claimed
// the completion work.
func (bc *BlockChain) hvmSnapShouldStop() bool {
	bc.hvmSnapMu.Lock()
	defer bc.hvmSnapMu.Unlock()
	return !bc.awaitingHvmSnapSync || bc.finishedHvmSnapSync || bc.processingHvmSnapSync
}

// hvmSnapClaimCompletion atomically claims the exclusive right to perform the non-idempotent
// completion work — resetting the lightweight TBC and adding headers. Only the first caller after a
// reachable tip is found succeeds; any concurrent caller for the same round gets false and must abandon.
func (bc *BlockChain) hvmSnapClaimCompletion() bool {
	bc.hvmSnapMu.Lock()
	defer bc.hvmSnapMu.Unlock()
	if !bc.awaitingHvmSnapSync || bc.finishedHvmSnapSync || bc.processingHvmSnapSync {
		return false
	}
	bc.processingHvmSnapSync = true
	return true
}

// hvmSnapMarkFinished records that the completion work succeeded.
func (bc *BlockChain) hvmSnapMarkFinished() {
	bc.hvmSnapMu.Lock()
	bc.awaitingHvmSnapSync = false
	bc.finishedHvmSnapSync = true
	bc.hvmSnapMu.Unlock()
	hvmSnapAwaitingGauge.Update(0)
}

// SnapSyncHvm is called when completing an initial snap sync, and uses the headers from the full TBC
// node to reconstruct the lightweight TBC node from scratch up to the snap-synced tip.
// maxHvmSnapWaiters caps the number of concurrent runHvmSnapWaiter goroutines (distinct candidate Bitcoin
// tips). Honest peers all report the same committed tip (one waiter); the cap bounds a peer that sends
// many distinct tips so it cannot exhaust goroutines. The wait runs off the per-peer snap read loop, so it
// is not implicitly bounded by that loop's serialization and needs this explicit cap.
const maxHvmSnapWaiters = 16

// maxHvmSnapBodyAbsentPolls bounds how long a waiter whose BTC data is fully available will keep polling for
// its pinned hVM base block's body before abandoning the candidate and releasing its slot. Without a bound, a
// candidate whose base body is never local (e.g. a peer pinning a BtcAttr ancestor below the snap body
// floor) would hold its slot indefinitely and — repeated across distinct tips — could exhaust maxHvmSnapWaiters
// and stall snap completion. An honest base sits within snap's downloaded body range, so its body is
// present within a poll or two; this bound (~polls × 1s) is far above that, and a slow-to-download honest base
// is simply re-attempted on the downloader's next re-issue once its body lands.
const maxHvmSnapBodyAbsentPolls = 100

// bodyAbsentShouldGiveUp reports whether a snap waiter that has polled `polls` times with its pinned base
// block's body still absent should abandon the candidate and release its waiter slot, given the give-up
// horizon `maxPolls`. The live waiter passes bc.effectiveMaxBodyAbsentPolls() (= maxHvmSnapBodyAbsentPolls in
// production, or the test-only override); a unit test may pass a lower bound. Extracted as a pure predicate —
// AND called from the live give-up site below — so the boundary (the defense that stops a peer pinning
// never-local bases from holding every slot and wedging snap completion) is unit-testable without standing up
// a live TBC full node, and the live decision cannot drift from the tested predicate.
func bodyAbsentShouldGiveUp(polls, maxPolls int) bool {
	return polls >= maxPolls
}

// effectiveMaxBodyAbsentPolls is the give-up horizon used by the live waiter. It honors the test-only
// hvmSnapBodyAbsentPollsLimit override (so the give-up/slot-release path is reachable in a bounded test window);
// production leaves the field 0 and gets maxHvmSnapBodyAbsentPolls.
func (bc *BlockChain) effectiveMaxBodyAbsentPolls() int {
	if bc.hvmSnapBodyAbsentPollsLimit > 0 {
		return bc.hvmSnapBodyAbsentPollsLimit
	}
	return maxHvmSnapBodyAbsentPolls
}

// snapShouldObserveBtcDiff reports whether the snap-completion path should run the observe-only
// contextual-difficulty check on the reconstructed base: ONLY when there is at least one reconstructed header AND
// the node is difficulty-enforceable. A DEFER-state node (TestNet3Params over Bitcoin-mainnet data) must SKIP it,
// else it emits a stream of spurious btcdiff_reject alerts under the wrong params.
// Extracted as a pure predicate so the skip-when-deferred gate is unit-testable without a live TBC node.
func snapShouldObserveBtcDiff(headerCount int, enforceable bool) bool {
	return headerCount > 0 && enforceable
}

// markSnapBtcDiffObservation marks the snap-sync observe-only alert meters and emits the advisory logs from an
// observeSnapBtcDiff result. It is pure side effects (meters + logs) and NEVER halts or mutates state — the
// observe-only safety net is telemetry, not enforcement. Split out (mirroring observeSnapBtcDiff) so the
// meter-marking, which is the snap path's ONLY externally-visible safety signal, is unit-testable without the async
// full-node snap harness. firstHeaderID is the snap base's first header hash (for the skip-arm log only).
func (bc *BlockChain) markSnapBtcDiffObservation(obs snapObserveResult, firstHeaderID string) {
	if obs.powFailed {
		hvmSnapPoWRejectMeter.Mark(1)
		log.Error("hVM snap sync observe-only check: a snap-loaded BTC header failed proof-of-work "+
			"validation; proceeding under the canonical-tip + cumulative-work backstops — investigate",
			"err", obs.powErr)
	}

	switch {
	case obs.clearanceErr != nil:
		// Unknown network => cannot parameterize the observability split. Telemetry, not enforcement, so
		// do not halt: skip the observation and proceed (canonical-tip + cumulative-work backstops below).
		log.Warn(fmt.Sprintf("hVM snap sync observe-only contextual-difficulty: cannot determine the contextual-difficulty "+
			"floor clearance for network %q; skipping the snap-base observation", bc.tbcHeaderNodeConfig.Network), "err", obs.clearanceErr)
	case obs.firstHeightErr != nil:
		// The full node returned this header moments ago during the walk-back; a read error now is odd,
		// but observe-only — skip the observation rather than crashing the snap.
		log.Warn(fmt.Sprintf("hVM snap sync observe-only contextual-difficulty: cannot read the height of first snap header "+
			"%s from the full node; skipping the snap-base observation", firstHeaderID), "err", obs.firstHeightErr)
	default:
		// headersToAdd[0] is the child of the just-reset effective genesis, so its height should be
		// GenesisHeightOffset+1. The enforce/defer split does not depend on that (btcEnforceableSuffix
		// uses the true queried firstHeight); a mismatch is a tripwire that the reset/walk-back did not
		// start at the effective genesis as expected — surface it rather than letting it pass silently.
		if obs.firstHeightMismatch {
			log.Warn(fmt.Sprintf("hVM snap sync contextual-difficulty: first reconstructed header height %d != expected "+
				"effective-genesis+1 (%d) — unexpected reconstruction start (the enforce/defer split still uses "+
				"the true queried height)", obs.firstHeight, bc.tbcHeaderNodeConfig.GenesisHeightOffset+1))
		}
		log.Info(fmt.Sprintf("hVM snap sync observe-only contextual-difficulty: checking %d headers at/above height %d, "+
			"not checking %d near-floor headers", obs.enforcedCount, obs.enforceFloor, obs.deferredCount))
		if obs.contextualRan {
			switch obs.ctxObservation {
			case snapObsClean:
				// the checked suffix is contextually clean — nothing to report
			case snapObsBelowFloor:
				// Unexpected (the suffix is above the enforce floor) but benign; nothing to report.
				log.Debug("hVM snap sync observe-only contextual-difficulty: checked suffix reported below-floor; not checked")
			case snapObsIncomplete:
				// A connectivity gap or a transient/corrupt full-node read while resolving deep ancestry — not a
				// forged-difficulty statement and not actionable here. AddExternalHeaders below remains the
				// connectivity authority; the snap-base check simply could not complete.
				log.Warn(fmt.Sprintf("hVM snap sync observe-only contextual-difficulty: could not complete the snap-base check "+
					"(connectivity/transient read); proceeding"), "err", obs.ctxErr)
			case snapObsReject:
				// A genuine btcd contextual-difficulty RuleError on the snap base. Alertable but not enforced
				// (see the rationale on the if-block above): emit the meter + alert, indicating the full node
				// served a header that fails contextual validation, and proceed.
				hvmSnapBtcDiffRejectMeter.Mark(1)
				log.Error(fmt.Sprintf("hVM snap sync observe-only check: a snap-loaded BTC header failed contextual "+
					"validation (difficulty / median-time-past / version); proceeding under the canonical-tip + "+
					"cumulative-work backstops — investigate"), "err", obs.ctxErr)
			}
		}
	}
}

// SnapSyncHvm is the snap downloader's hook for an hVM light-state response. It runs the wait-for-Bitcoin-data
// loop and the (exclusive) completion work in a dedicated goroutine, returning immediately so it does NOT
// block the caller's per-peer snap read loop (a long Bitcoin-data wait would otherwise stall EVM snap sync
// across every responding peer). Multiple responses may report distinct candidate tips that are waited on
// concurrently — a forged/unreachable tip must not wedge an honest one — but identical tips are deduped and
// the total is capped (maxHvmSnapWaiters); only one waiter may claim the non-idempotent completion.
func (bc *BlockChain) SnapSyncHvm(btcTipHeader *chainhash.Hash, hvmTipHeader *types.Header, quit <-chan struct{}) {
	if !bc.claimHvmSnapWaiterSlot(*btcTipHeader) {
		log.Debug("hVM snap sync not started for this tip (already done/claimed, a duplicate of an active waiter, or the waiter cap is reached)",
			"tip", btcTipHeader.String())
		return
	}
	go bc.runHvmSnapWaiter(btcTipHeader, hvmTipHeader, quit)
}

// claimHvmSnapWaiterSlot atomically decides whether a new runHvmSnapWaiter should start for btcTip. It
// returns true (and registers the slot in hvmSnapWaiters + hvmSnapWg) only if the round is still awaiting and
// neither claimed nor finished, no waiter is already on this tip (dedupe), and the cap is not reached. On a
// true return the caller MUST eventually call releaseHvmSnapWaiterSlot(btcTip) exactly once.
func (bc *BlockChain) claimHvmSnapWaiterSlot(btcTip chainhash.Hash) bool {
	bc.hvmSnapMu.Lock()
	defer bc.hvmSnapMu.Unlock()
	// Never register a new waiter once shutdown has begun. stopWithoutSaving publishes bc.stopping under
	// hvmSnapMu (this same lock) immediately before hvmSnapWg.Wait(), so this load-and-Add under the lock is
	// ordered against that barrier: the "no hvmSnapWg.Add after Wait" invariant holds locally within the
	// snap-latch code, not via the cross-package Stop() ordering.
	if bc.stopping.Load() {
		return false
	}
	if !bc.awaitingHvmSnapSync || bc.finishedHvmSnapSync || bc.processingHvmSnapSync {
		return false
	}
	if bc.hvmSnapWaiters == nil {
		bc.hvmSnapWaiters = make(map[chainhash.Hash]struct{})
	}
	if _, active := bc.hvmSnapWaiters[btcTip]; active {
		return false
	}
	if len(bc.hvmSnapWaiters) >= maxHvmSnapWaiters {
		log.Warn("hVM snap sync waiter cap reached; ignoring additional candidate tip", "tip", btcTip.String(), "cap", maxHvmSnapWaiters)
		return false
	}
	bc.hvmSnapWaiters[btcTip] = struct{}{}
	bc.hvmSnapWg.Add(1)
	return true
}

// releaseHvmSnapWaiterSlot frees the slot claimed by claimHvmSnapWaiterSlot. Call exactly once per true claim.
func (bc *BlockChain) releaseHvmSnapWaiterSlot(btcTip chainhash.Hash) {
	bc.hvmSnapMu.Lock()
	delete(bc.hvmSnapWaiters, btcTip)
	bc.hvmSnapMu.Unlock()
	bc.hvmSnapWg.Done()
}

// runHvmSnapWaiter is the detached wait+completion body of a single SnapSyncHvm candidate tip. It is joined
// on shutdown via hvmSnapWg (the wait loop aborts on bc.stopping; an in-flight completion runs to finish).
func (bc *BlockChain) runHvmSnapWaiter(btcTipHeader *chainhash.Hash, hvmTipHeader *types.Header, quit <-chan struct{}) {
	defer bc.releaseHvmSnapWaiterSlot(*btcTipHeader)

	log.Debug("Blockchain processing hVM light state snap sync message")
	missing := make(map[string]uint8)
	bodyAbsentPolls := 0

	for {
		// Abort on shutdown/cancellation before any TBC access. bc.stopping is set at the start of
		// stopWithoutSaving, so the hvmSnapWg.Wait() there joins promptly. The downloader closes quit via
		// Terminate() during handler.Stop(); bc.ctx is a defensive secondary signal (not cancelled in cmd/geth today).
		if bc.stopping.Load() {
			log.Debug("hVM snap sync aborted: blockchain stopping")
			return
		}
		select {
		case <-quit:
			log.Debug("hVM snap sync aborted: downloader terminating")
			return
		case <-bc.ctx.Done():
			log.Warn("Context exited while waiting for TBC full node data to finish hVM snap sync; aborting")
			return
		default:
		}
		// Abandon if another response already finished or claimed the round.
		if bc.hvmSnapShouldStop() {
			log.Debug("hVM snap sync completed/claimed by another response; abandoning this attempt")
			return
		}

		header, _, err := vm.TBCFullNode.BlockHeaderByHash(bc.ctx, *btcTipHeader)
		if err != nil || header == nil {
			log.Warn(fmt.Sprintf("Unable to get hVM snap sync header %s from full TBC node, waiting...", btcTipHeader.String()))
		} else {
			// We have header, now check for all blocks
			available, missingHeaders, missingHeaderHash, err := vm.TBCBlocksAvailableToHeader(bc.ctx, header)
			if err != nil {
				log.Crit(fmt.Sprintf("Encountered unrecoverable error while attempting hVM snap sync, "+
					"unable to check block availability in full TBC to block %s", btcTipHeader.String()), "err", err)
			}
			if missingHeaderHash != nil {
				log.Crit(fmt.Sprintf("Encountered unrecoverable error while attempting hVM snap sync, "+
					"TBC full node missing header for block %s", missingHeaderHash.String()))
			}

			if !available {
				log.Info("Full TBC missing blocks, checking if a refetch is required...")
				for _, missingHeader := range *missingHeaders {
					bh := missingHeader.BlockHash()
					bhs := bh.String()
					if seenCount, ok := missing[bhs]; ok {
						seenCount++
						missing[bhs] = seenCount
						if seenCount >= 100 {
							// If we have seen the same block missing for more than 100 loops,
							// then assume we have to re-request
							log.Info(fmt.Sprintf("During hVM snap sync, BTC block %s is not available,"+
								" attempting to re-fetch over Bitcoin P2P", bhs))

							_, err := vm.TBCFullNode.DownloadBlockFromRandomPeers(
								bc.ctx, bh, uint(vm.TBCFullNodeConfig.PeersWanted/4))

							if err != nil {
								log.Crit(fmt.Sprintf("Encountered unrecoverable error while attempting hVM "+
									"snap sync and forcing Bitcoin P2P request for block %s", bhs), "err", err)
							}

							// Since we requested this block, remove from map so we don't constantly re-request
							delete(missing, bhs)
						}
					} else {
						missing[bhs] = uint8(1)
					}
				}

				// If we are tracking more than 1000 missing blocks, then reset the array.
				// Worst case we spend longer waiting before re-requesting a missing block.
				if len(missing) >= 1000 {
					clear(missing)
				}
			} else if bc.GetBlockByHash(hvmTipHeader.Hash()) == nil {
				// All BTC blocks for this candidate are available, but the hVM base block this response pins
				// (hvmTipHeader) is not present on local disk as a FULL block. We probe disk via the
				// goroutine-safe GetBlockByHash, NOT getBlockFromDiskOrHoldingPen: this waiter runs lock-free
				// (no chainmu), while the holding-pen maps (tempBlocks/tempHeaders) are unsynchronized and
				// guarded only by the chainmu-held apply/import path — reading them from here would be a data
				// race (fatal "concurrent map read and map write"). Disk-only is also the correct semantics: the
				// pinned base is a committed historical block at/below the snap pivot, present on disk once snap
				// has downloaded its body — never an in-flight holding-pen entry of the current import batch.
				// Completing here would persist it as the TBC upstream-state-id (AddExternalHeaders below), and
				// the first post-snap reconciliation
				// walk re-applies every block from it forward via applyHvmHeaderConsensusUpdate, which fetches
				// each block's BODY. An honest response pins the NEAREST BtcAttr ancestor of the snap pivot —
				// recent, and well within snap's downloaded body range [chainOffset, head] — so its body is (or
				// shortly will be) present. A response can instead pin an older BtcAttr block below the
				// node's body floor (the history-pruning cutoff or sync origin), whose body is never downloaded;
				// completing on it would fail the walk (missing body) and not recover across restarts.
				// So do NOT complete on a base we cannot reconcile from: keep waiting. A body-present (honest)
				// response then wins the round via the completion claim below; an all-malicious round merely
				// stalls (recoverable, and the downloader re-issues the request) instead of corrupting state.
				bodyAbsentPolls++
				log.Warn(fmt.Sprintf("hVM snap sync candidate base %s @ %d is not locally available as a full "+
					"block (below the body floor or not yet synced); not completing on this candidate (poll %d/%d)",
					hvmTipHeader.Hash().String(), hvmTipHeader.Number.Uint64(), bodyAbsentPolls, bc.effectiveMaxBodyAbsentPolls()))
				if bodyAbsentShouldGiveUp(bodyAbsentPolls, bc.effectiveMaxBodyAbsentPolls()) {
					// Give up on this candidate and RELEASE its slot (via the deferred releaseHvmSnapWaiterSlot)
					// rather than holding it indefinitely. Otherwise a peer pinning a base whose body is never local
					// could, across maxHvmSnapWaiters distinct tips, hold every slot indefinitely and stall snap
					// completion. The downloader re-issues the request, so an honest (body-present)
					// candidate still completes the round, and a slow-to-download honest base is retried later.
					log.Warn(fmt.Sprintf("hVM snap sync abandoning candidate base %s @ %d after %d polls with its "+
						"body still unavailable; releasing the waiter slot",
						hvmTipHeader.Hash().String(), hvmTipHeader.Number.Uint64(), bodyAbsentPolls))
					return
				}
			} else {
				// All BTC blocks available and the hVM base block body is present, exit loop and continue
				break
			}
		}

		select {
		case <-time.After(1000 * time.Millisecond):
		case <-quit:
			log.Debug("hVM snap sync aborted: downloader terminating")
			return
		case <-bc.ctx.Done():
			log.Warn("Context exited while waiting for TBC full node data to finish hVM snap sync; aborting")
			return
		}
	}

	// A reachable tip was found. Claim the exclusive right to run the completion work (resetting the
	// lightweight TBC and adding headers is not idempotent); concurrent attempts that also found the tip
	// get false here and abandon.
	if !bc.hvmSnapClaimCompletion() {
		log.Debug("hVM snap sync completion already claimed/finished by another response; abandoning")
		return
	}

	log.Info("All required BTC data available, resetting lightweight TBC and adding headers")
	bc.resetHvmHeaderNodeToGenesis()

	targetHeight, target, err := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
	if err != nil {
		log.Crit(fmt.Sprintf("Unable to get best header from lighweight TBC node after reset"))
	}
	targetHash := target.BlockHash()

	cursor, cursorHeight, err := vm.TBCFullNode.BlockHeaderByHash(bc.ctx, *btcTipHeader)
	if err != nil {
		// Should never happen as this is part of the check in the above loop, indicates some form of corruption
		log.Crit(fmt.Sprintf("After finding all BTC data, unable to fetch ending tip %s", btcTipHeader.String()))
	}

	cursorHash := cursor.BlockHash()

	headersToAdd := make([]*wire.BlockHeader, 0)
	for !bytes.Equal(cursorHash[:], targetHash[:]) {
		// Height floor (mirrors gatherHeadersBackToGenesis): the snap candidate tip MUST descend from the
		// lightweight node's reset tip (target). If the walk reaches the target's height or below without
		// matching its hash, btcTipHeader is not a descendant of target — a forged/corrupt full-node tip — so
		// crit rather than walk toward real Bitcoin genesis (buffering hundreds of thousands of headers / OOM).
		if cursorHeight <= targetHeight {
			log.Crit("hVM snap sync: full-node header walk reached the lightweight tip's height without matching it (forged/corrupt full-node tip?)",
				"reachedHeight", cursorHeight, "targetHeight", targetHeight, "header", cursorHash.String())
		}
		headersToAdd = append(headersToAdd, cursor)

		// Move cursor back
		prevHeight := cursorHeight
		prev := cursor.PrevBlock
		cursor, cursorHeight, err = vm.TBCFullNode.BlockHeaderByHash(bc.ctx, prev)
		if err != nil {
			// Should never happen as these headers were already found above
			log.Crit(fmt.Sprintf("Unable to get header %s from TBC full node", prev.String()), "err", err)
		}
		cursorHash = cursor.BlockHash()
		// CYCLE / corrupt-index guard (mirrors the migration walk): an honest PrevBlock walk strictly
		// DECREASES height each step. The full node is not trusted (a torn index / malicious peer header forming a
		// PrevBlock cycle above the target would otherwise spin this completion goroutine forever and OOM the
		// node). A non-decrease is corruption — crit (consistent with the missing-ancestor crit above) rather
		// than loop unboundedly.
		if cursorHeight >= prevHeight {
			log.Crit("hVM snap sync: full-node header walk did not strictly descend in height (PrevBlock cycle / corrupt full-node index?)",
				"fromHeight", prevHeight, "toHeight", cursorHeight, "header", cursorHash.String())
		}
	}

	slices.Reverse(headersToAdd)

	msgHeaders := &wire.MsgHeaders{
		Headers: headersToAdd,
	}

	log.Info(fmt.Sprintf("hVM snap sync adding %d headers", len(msgHeaders.Headers)))

	// Contextual-difficulty (snap-sync — the second writer into bc.tbcHeaderNode). Observe-only contextual
	// Bitcoin-difficulty check of the bulk-loaded chain (vs the full node, which holds ancestry to real
	// Bitcoin genesis). It never halts — it emits an alertable signal (hvmSnapBtcDiffRejectMeter + a
	// log.Error) and proceeds. Why observe-only, not enforce:
	//   - Redundant: headersToAdd is built by walking back from the snap target btcTip, so the loaded
	//     chain is btcTip's cryptographic ancestry by construction, and the post-add canonical-tip crit
	//     (cbh.Hash == btcTipHeader) already pins it. A full node cannot substitute a forged base that
	//     still reconstructs to btcTip (hash-linked headers). So a contextual-difficulty failure here is a
	//     property of the L2-committed chain, not a node-local forged injection this check could stop.
	//   - Unsafe to halt: forward-sync rejects such a header per-block, restore (enforceBTCDiff=false)
	//     accepts it (grandfather), so a snap log.Crit would split snap nodes from forward/restore nodes
	//     on a non-clean-history network, crash-loop with no recourse, and be self-defeating (a crashed
	//     gateless node re-routes into the enforce-exempt restore that accepts the very header snap refused).
	// The enforce/defer split below is retained only to keep the alert low-noise — we flag only headers in
	// the band the forward path would itself enforce (at/above floor+clearance+(MaximumBtcHeadersInTx-1);
	// see btcSnapEnforceFloor), deferring the near-floor band the forward path also defers. Real consensus
	// enforcement remains the apply path (forward) + the canonical-tip crit; this arm is telemetry.
	// Skip the observe-only difficulty check in the legacy DEFER state: a deferred node runs
	// TestNet3Params (bc.tbcHeaderNodeConfig.Network=="testnet3") over Bitcoin-MAINNET data, so observing those
	// headers under the wrong params produces a systematic stream of spurious btcdiff_reject alerts. Enforceable
	// nodes (genuine testnet3, migrated mainnet) have matching params and observe meaningfully.
	if snapShouldObserveBtcDiff(len(headersToAdd), bc.hvmDiffEnforceable.Load()) {
		// Observe-only contextual-difficulty (never halts, never mutates): PoW + contextual-difficulty check of the
		// reconstructed base. The verdict-dispatch composition lives in observeSnapBtcDiff (unit-testable);
		// this block only marks the alert meters and logs from its advisory result.
		obs := observeSnapBtcDiff(bc.ctx, vm.TBCFullNode, bc.tbcHeaderNodeConfig.Network,
			bc.tbcHeaderNodeConfig.GenesisHeightOffset, headersToAdd)
		// The verdict-dispatch (meter marks + advisory logs) lives in markSnapBtcDiffObservation, split out
		// (mirroring observeSnapBtcDiff) so the meter-marking — the snap path's only externally-visible
		// safety signal — is unit-testable without the async full-node snap harness.
		bc.markSnapBtcDiffObservation(obs, headersToAdd[0].BlockHash().String())
	}

	// Add all headers between genesis and the hVM snap sync height, and set upstream ID to snap header.
	_, cbh, _, _, err := bc.tbcHeaderNode.AddExternalHeaders(bc.ctx, msgHeaders, hvmTipHeader.Hash().Bytes()[:])
	if err != nil {
		// Guard the diagnostic indexing: an empty headersToAdd would index-out-of-range here and panic while
		// formatting the crit args (masking the real AddExternalHeaders error). Fall back to a placeholder.
		firstHdr, lastHdr := "<none>", "<none>"
		if len(headersToAdd) > 0 {
			firstHdr = headersToAdd[0].BlockHash().String()
			lastHdr = headersToAdd[len(headersToAdd)-1].BlockHash().String()
		}
		log.Crit(fmt.Sprintf("Encountered unrecoverable error while attempting hVM snap sync, "+
			"unable to add BTC headers from %s to %s to lightweight view", firstHdr, lastHdr), "err", err)
	}

	if !bytes.Equal(cbh.Hash[:], btcTipHeader[:]) {
		log.Crit(fmt.Sprintf("After adding hVM snap sync headers, lightweight TBC does not have "+
			"expected canonical block hash %s", btcTipHeader.String()))
	}

	log.Info(fmt.Sprintf("Successfully snap synced lightweight hVM to BTC tip %s for Hemi tip %s,"+
		" indexing full TBC", cbh.Hash.String(), hvmTipHeader.Hash().String()))

	err = bc.updateFullTBCToLightweight()
	if err != nil {
		// This snap-sync completion crit is deliberately left as a fail-stop, not given the
		// isHvmFullNodeBehind treatment. It runs only after the wait loop confirmed all required BTC data
		// for the snap tip is available, so a deferrable sentinel here would require a TOCTOU eviction/reorg
		// and is largely unreachable. More importantly, on the completion path fail-stop is intentional:
		// converting it to non-fatal would require resetting the completion-claim latch and making
		// completion idempotent from partial state, else it risks a latch wedge or a corrupting double-run.
		log.Crit(fmt.Sprintf("Unable to update full TBC indexers during hVM snap sync, hVM snap tip = %s",
			hvmTipHeader.Hash().String()), "err", err)
	}

	si := vm.TBCFullNode.Synced(bc.ctx)

	log.Info(fmt.Sprintf("Finished hVM snap sync, hVM snap tip = %s, TBC full node utxo = %s, tx = %s",
		hvmTipHeader.Hash().String(), si.Utxo.Hash.String(), si.Tx.Hash.String()))

	// TODO: review and get this from op-node CL sync
	bc.SetSafe(hvmTipHeader)
	bc.SetFinalized(hvmTipHeader)

	bc.hvmSnapMarkFinished()
}

// btcAttrDepIsHeaderless reports whether a block's Bitcoin Attributes Deposited data carries no BTC
// headers — either because there is no BtcAttr tx at all (btcAttrDep == nil) or because the tx is
// present but empty (len(Headers) == 0). In both cases applying/unapplying the block makes no TBC
// header change (only the upstream-state-id moves), so apply and unapply take the no-op path. This is
// load-bearing: an unapply guard that matched only btcAttrDep == nil would let an empty-but-present tx
// fall through to RemoveExternalHeaders with zero headers (an invalid call that crashes on reorg). Keep
// nil and empty unified here; do not narrow to btcAttrDep == nil.
func btcAttrDepIsHeaderless(btcAttrDep *types.BtcAttributesDepositData) bool {
	return btcAttrDep == nil || len(btcAttrDep.Headers) == 0
}

// unapplyHvmHeaderConsensusUpdate retrieves the block corresponding to
// the provided block header, extracts its Bitcoin Attributes Deposited
// transaction and, if it exists, removes the header information contained
// in it from the protocol's lightweight view of Bitcoin and verifies that
// TBC has been correctly returned to the canonical tip claimed by the
// previous block which contains a Bitcoin Attributes Deposited tx.
func (bc *BlockChain) unapplyHvmHeaderConsensusUpdate(header *types.Header) error {
	block := bc.getBlockFromDiskOrHoldingPen(header.Hash())
	if block == nil {
		// Symmetric to the prevBlock / walk-cursor guards below: the block being unapplied is absent from
		// disk + holding pen (a deep reorg/rewind orphaned its body). Since this is an already-applied block,
		// an absent body is a torn-store condition, not a bad block — return the recoverable corrupt-state
		// sentinel so the walkHvmHeaderConsensusBack caller rebuilds the lightweight view from genesis rather
		// than escalating to a crit.
		log.Error(fmt.Sprintf("block %s @ %d to unapply hVM consensus updates is nil; treating as corrupt hVM state",
			header.Hash().String(), header.Number.Uint64()))
		return consensus.ErrCorruptHVMHeaderOnlyModeState
	}

	// When we unapply the current block, TBC's state will reflect that of the
	// previous block
	prevBlock := bc.getHeaderFromDiskOrHoldingPen(header.ParentHash)
	if prevBlock == nil {
		// Symmetric to the apply-side currentHead==nil guards in updateHvmHeaderConsensus: the parent of the
		// block being unapplied is absent from both disk and the holding pen (a deep reorg/rewind orphaned it,
		// or recoverReapplyHvmState reset us to genesis with the parent already gone). Dereferencing
		// prevBlock.Time / prevBlock.Hash() below would nil-panic and crash the process; return the recoverable
		// corrupt-state sentinel so the caller rebuilds the lightweight view from genesis instead (the
		// walkHvmHeaderConsensusBack caller routes ErrCorruptHVMHeaderOnlyModeState through recovery, not crit).
		log.Error(fmt.Sprintf("prevBlock (parent %x of block %s @ %d being unapplied) is nil; treating as corrupt hVM state",
			header.ParentHash[:], header.Hash().String(), header.Number.Uint64()))
		return consensus.ErrCorruptHVMHeaderOnlyModeState
	}
	stateTransitionTargetHash := [32]byte{}

	if bc.chainConfig.IsHvm0(header.Time) && !bc.chainConfig.IsHvm0(prevBlock.Time) {
		// Special case, we are unapplying the hVM state transition for the activation block,
		// so set the state transition target hash back to the genesis default
		copy(stateTransitionTargetHash[0:32], hVMGenesisUpstreamId[0:32])
	} else {
		// Previous block had hVM active, so we will set its hash as the upstream
		// state id of the external header TBC node after reverting hVM state transition
		// from the block to unapply
		copy(stateTransitionTargetHash[0:32], prevBlock.Hash().Bytes()[0:32])
	}

	btcAttrDep, err := block.Transactions().ExtractBtcAttrData()
	if err != nil {
		// Error implies that state of Bitcoin Attributes Deposited tx in the transaction list is invalid.
		// This should be impossible because any block which is being unapplied would have undergone the
		// same check previously and passed when it was originally applied.
		// TODO: Bubble this error up and invalidate this block and restore external header TBC node from genesis to prev tip?
		log.Crit(fmt.Sprintf("Error while extracting Bitcoin Attributes Deposited transaction to unwind "+
			"hVM state application for block %s @ %d", header.Hash().String(), header.Number.Uint64()),
			"err", err)
	}

	if btcAttrDepIsHeaderless(btcAttrDep) {
		// No Bitcoin headers to unapply: the block either has no Bitcoin Attributes Deposited tx, or has
		// one carrying zero headers (an empty-but-present tx). In both cases forward-apply made no TBC
		// header change (it only advanced the upstream state id), so the inverse is to roll the upstream
		// state id back — there is nothing to remove. Treating empty-but-present as a no-op here mirrors
		// the forward path so apply/unapply remain exact inverses (see btcAttrDepIsHeaderless).
		log.Info(fmt.Sprintf("No Bitcoin headers to unapply in hVM state for block %s @ %d (no Bitcoin "+
			"Attributes Deposited transaction, or one carrying zero headers)", header.Hash().String(),
			header.Number.Uint64()))

		// Even with no header changes, explicitly update TBC's state id so it is correct for the previous
		// block after removing this one. stateTransitionTargetHash is already set to the previous block or
		// the genesis upstream state ID depending on whether the previous parent had hVM Phase 0 active.
		if bc.chainConfig.IsHvm0(header.Time) {
			err := bc.tbcHeaderNode.SetUpstreamStateId(bc.ctx, stateTransitionTargetHash)
			if err != nil {
				// TODO: Recovery mode that resets TBC header mode to genesis configuration and rebuilds it from hVM activation block
				log.Crit(fmt.Sprintf("Error while updating the upstream state id in TBC with no corresponding "+
					"consensus state modifications for unapplying block %s @ %d", header.Hash().String(),
					header.Number.Uint64()), "err", err)
			}
		}
		return nil
	}

	if !bc.chainConfig.IsHvm0(header.Time) {
		// This should never happen, because the block shouldn't have a Bitcoin Attributes Deposited tx before this
		// activation timestamp and already would have failed validation in the forward direction when originally
		// applied
		// TODO: Bubble this error up and invalidate this previous block?
		log.Crit(fmt.Sprintf("block %s @ %d has a Bitcoin Attributes Deposited transaction but its timestamp "+
			"%d is before the hVM Phase 0 activation height %d", header.Hash().String(), header.Number.Uint64(),
			header.Time, *bc.chainConfig.Hvm0Time))
	}

	currentTipHeight, currentTip, err := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
	if err != nil {
		// This is a critical TBC failure, not related to block validity
		// TODO: Recovery mode that resets TBC header mode to genesis configuration and rebuilds it from hVM activation block
		log.Crit(fmt.Sprintf("when unapplying hVM changes for block %s @ %d, unable to retrieve tip "+
			"from lightweight TBC!", header.Hash().String(), header.Number.Uint64()), "err", err)
	}
	currentTipHash := currentTip.BlockHash()

	// Descend the Hemi chain from this height until either we find a block with a Bitcoin Attributes Deposited
	// transaction or we get to before the hVM Phase 0 activation height to determine the correct previous
	// tip.
	// TODO: Get this state more efficiently?
	var expectedPreviousTipHash [32]byte
	cursor := bc.getBlockFromDiskOrHoldingPen(header.ParentHash)
	if cursor == nil {
		// Symmetric to the prevBlock guard above, but for the BLOCK store: the parent header can resolve while
		// its full block is absent from disk + holding pen (a deep reorg/rewind orphaned the body). The loop
		// condition cursor.Time() below would nil-panic; return the recoverable sentinel so the caller rebuilds
		// the lightweight view from genesis instead of crashing the process.
		log.Error(fmt.Sprintf("parent block %x of %s @ %d is nil while walking back to the previous BtcAttr tip; treating as corrupt hVM state",
			header.ParentHash[:], header.Hash().String(), header.Number.Uint64()))
		return consensus.ErrCorruptHVMHeaderOnlyModeState
	}
	for bc.chainConfig.IsHvm0(cursor.Time()) {
		oldBtcAttrDep, err := cursor.Transactions().ExtractBtcAttrData()
		if err != nil {
			// Error implies that state of Bitcoin Attributes Deposited tx in the transaction list is invalid.
			// This should be impossible because any block which is being unapplied would have undergone the
			// same check previously in the forward direction and passed.
			// TODO: Bubble this error up to invalidate the old block?
			log.Crit(fmt.Sprintf("Error while extracting Bitcoin Attributes Deposited transaction from "+
				"prior block %s @ %d when attempting to unwind hVM state application for block %s @ %d",
				cursor.Hash().String(), cursor.NumberU64(), header.Hash().String(), header.Number.Uint64()), "err", err)
		}
		if oldBtcAttrDep != nil {
			// Found previous state
			expectedPreviousTipHash = oldBtcAttrDep.CanonicalTip
			break
		}
		cursor = bc.getBlockFromDiskOrHoldingPen(cursor.ParentHash())
		if cursor == nil {
			// Same orphaned-ancestor recovery: an ancestor block on the walk-back is absent from disk +
			// holding pen. The next loop-condition cursor.Time() would nil-panic; recover instead of crashing.
			log.Error(fmt.Sprintf("ancestor block on the unapply walk-back for %s @ %d is nil; treating as corrupt hVM state",
				header.Hash().String(), header.Number.Uint64()))
			return consensus.ErrCorruptHVMHeaderOnlyModeState
		}
	}
	if bytes.Equal(expectedPreviousTipHash[:], emptyArray[:]) {
		// Walked back the chain to the hVM Phase 0 activation height and did not find any previous BTC Attr Dep
		// transactions, so the previous state to the change we are unapplying is the genesis state
		genHash := bc.tbcHeaderNodeConfig.EffectiveGenesisBlock.BlockHash()
		copy(expectedPreviousTipHash[0:32], genHash[0:32])
		log.Info(fmt.Sprintf("when unapplying hVM changes for block %s @ %d, got to block %s @ %d with timestamp "+
			"%d which is before the hVM Phase 0 activation timestamp %d, so previous canonical tip should be "+
			"the genesis block %x", header.Hash().String(), header.Number.Uint64(), cursor.Hash().String(),
			cursor.NumberU64(), cursor.Time(), bc.chainConfig.Hvm0Time, genHash[:]))
	} else {
		log.Info(fmt.Sprintf("expectedPreviousTipHash=%x is not zeroed, so a non-genesis previous canonical "+
			"BTC tip was found", expectedPreviousTipHash[:]))
	}

	// Convert the expected previous BTC tip hash to a chainhash
	expectedPreviousTipHashParsed, err := chainhash.NewHash(expectedPreviousTipHash[:])
	if err != nil {
		log.Warn(fmt.Sprintf("Unable to create blockhash from %x", expectedPreviousTipHash[:]), "err", err)
	}

	if expectedPreviousTipHashParsed == nil {
		log.Crit("expectedPreviousTipHashParsed is nil")
	}

	// Get the actual header represented by the previous canonical tip hash
	expectedPreviousTip, expectedPreviousTipHeight, err :=
		bc.tbcHeaderNode.BlockHeaderByHash(bc.ctx, *expectedPreviousTipHashParsed)

	if err != nil {
		// This should never happen, it means TBC doesn't have a header which either:
		// 1. Should have already been added to it when this older block was originally processed, or
		// 2. Is the genesis block TBC is configured with
		// TODO: TBC recovery from genesis?
		log.Crit(fmt.Sprintf("when unapplying hVM changes for block %s @ %d, previous canonical tip "+
			"should be %x but TBC encountered an error when fetching that header", header.Hash().String(),
			header.Number.Uint64(), expectedPreviousTipHash[:]), "err", err)
	}

	// TODO: Better header to slice
	var expectedPreviousTipBuf bytes.Buffer
	err = expectedPreviousTip.Serialize(&expectedPreviousTipBuf)
	if err != nil {
		// This is a critical failure, not related to block validity
		// TODO: TBC recovery from genesis
		log.Crit(fmt.Sprintf("when unapplying hVM changes from block %s @ %d, unable to serialize "+
			"tip from lightweight TBC!", header.Hash().String(), header.Number.Uint64()), "err", err)
	}

	// Unflatten the BTC headers stored in the BTC Attr Dep transaction to unapply into wire.MsgHeaders
	reconstitutedHeaders, err := unflattenBTCHeaders(btcAttrDep.Headers)
	if err != nil {
		// This is a critical failure as the headers should be valid if the hVM consensus update we are
		// now unapplying was able to be applied in the first place in the forward direction
		log.Crit(fmt.Sprintf("when unapplying hVM changes for block %s @ %d, unable to unflatten "+
			"one of the BTC headers from the block", header.Hash().String(), header.Number.Uint64()),
			"err", err)
	}

	log.Info(fmt.Sprintf("[Unapply HVM Header Consensus Update] *REMOVING* external BTC headers:"))
	for i := 0; i < len(reconstitutedHeaders.Headers); i++ {
		log.Info(fmt.Sprintf("\t %s", reconstitutedHeaders.Headers[i].BlockHash().String()))
	}

	rt, lastHeader, err := bc.tbcHeaderNode.RemoveExternalHeaders(
		bc.ctx, reconstitutedHeaders, expectedPreviousTip, stateTransitionTargetHash[:])
	if err != nil {
		// This is a critical failure, not related to block validity
		// TODO: TBC recovery from genesis
		log.Crit(fmt.Sprintf("when unapplying hVM changes from block %s @ %d, unable to remove "+
			"%d headers and change the canonical tip from %s @ %d to %s @ %d", header.Hash().String(),
			header.Number.Uint64(), len(btcAttrDep.Headers), currentTipHash.String(), currentTipHeight,
			expectedPreviousTip.BlockHash().String(), expectedPreviousTipHeight), "err", err)
	}
	lastHeaderHash := lastHeader.BlockHash()

	newHeight, newTip, err := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
	if err != nil {
		// TODO: TBC recovery from genesis
		log.Crit(fmt.Sprintf("when unapplying hVM changes from block %s @ %d, attempted to remove "+
			"%d headers and change the canonical tip from %s @ %d to %s @ %d, but TBC reports an error "+
			"getting the canonical tip after state transition", header.Hash().String(),
			header.Number.Uint64(), len(btcAttrDep.Headers), currentTipHash.String(), currentTipHeight,
			expectedPreviousTipHash[:], expectedPreviousTipHeight), "err", err)
	}

	newTipHash := newTip.BlockHash()

	if !bytes.Equal(newTipHash[:], expectedPreviousTipHash[:]) {
		// TODO: TBC recovery from genesis
		log.Crit(fmt.Sprintf("when unapplying hVM changes from block %s @ %d, attempted to remove "+
			"%d headers and change the canonical tip from %s @ %d to %s @ %d, but TBC reports that the "+
			"canonical tip after state transition is %s @ %d which is incorrect", header.Hash().String(),
			header.Number.Uint64(), len(btcAttrDep.Headers), currentTipHash.String(), currentTipHeight,
			expectedPreviousTip.BlockHash().String(), expectedPreviousTipHeight, newTipHash.String(), newHeight),
			"err", err)
	}

	log.Info(fmt.Sprintf("successfully unapplied hVM changes from block %s @ %d, removed %d headers "+
		"and changed the canonical tip from %s @ %d to %s @ %d, last header before removed chunk is %x, rt=%d",
		header.Hash().String(), header.Number.Uint64(), len(btcAttrDep.Headers), currentTipHash.String(),
		currentTipHeight, expectedPreviousTip.BlockHash().String(), expectedPreviousTipHeight, lastHeaderHash[:], rt))

	return nil
}

func (bc *BlockChain) getBlockFromDiskOrHoldingPen(hash common.Hash) *types.Block {
	block := bc.GetBlockByHash(hash)
	if block == nil {
		// Check the holding pen
		block = bc.tempBlocks[hash.String()]
	}
	return block // Upstream must check if nil
}

func (bc *BlockChain) getHeaderFromDiskOrHoldingPen(hash common.Hash) *types.Header {
	header := bc.GetHeaderByHash(hash)
	if header == nil {
		// Check the holding pen
		header = bc.tempHeaders[hash.String()]
	}
	return header // Upstream must check if nil
}

// addExternalHeadersOutcome is the classification of a non-nil error returned by
// tbc.AddExternalHeaders on the hVM apply path. The mapping to a consensus error is consensus-binding:
// a wrong classification either false-rejects a canonical block (treating a torn store as a bad block)
// or fails to reject an invalid one. See classifyAddExternalHeadersError.
type addExternalHeadersOutcome int

const (
	// addHeadersDuplicate: every header in the batch is already present (database.DuplicateError) — an
	// idempotent re-application (post-restore retry / reorg re-apply). Never a bad block.
	addHeadersDuplicate addExternalHeadersOutcome = iota
	// addHeadersCorrupt: a typed database.NotFoundError after connectivity-validation confirmed the
	// parents were present — a header just proven present is now missing, a torn store. Recoverable via
	// restore, never a bad block. (A non-typed leveldb/IO fault is not classified here — it maps to
	// addHeadersBadBlock; see consensusErrorForAddHeadersOutcome.)
	addHeadersCorrupt
	// addHeadersBadBlock: the batch genuinely does not connect to committed state, or is malformed —
	// the block is invalid.
	addHeadersBadBlock
)

// classifyAddExternalHeadersError maps a non-nil AddExternalHeaders error to a consensus outcome. It is
// pure (no receiver, no IO) so the consensus-binding mapping is unit-testable without a torn leveldb.
// The discriminator for a database.NotFoundError is connectivityConfirmed: the floor-aware validator's
// anchor loop resolves every header's parent (returning Unconnected/IO first) before the floor gate, so
// a nil or below-floor verdict both prove every parent was resolvable (against the committed view or an
// earlier header in the same batch). The only parent AddExternalHeaders looks up in the committed store
// is the first new header's parent, which the anchor loop confirmed. Hence a NotFound when connectivity
// was confirmed can only be a torn store (corrupt -> self-heal); a NotFound when connectivity was not
// confirmed (Unconnected, or the validator did not run) is the genuine non-connecting signal (bad block,
// preserving pre-difficulty-enforcement behavior). database.DuplicateError is always idempotent. Any other (non-typed)
// error — intra-batch non-contiguity (malformed) or a leveldb fault — conservatively maps to bad block.
func classifyAddExternalHeadersError(err error, connectivityConfirmed bool) addExternalHeadersOutcome {
	var dupErr database.DuplicateError
	if errors.As(err, &dupErr) {
		return addHeadersDuplicate
	}
	var notFoundErr database.NotFoundError
	if errors.As(err, &notFoundErr) {
		if connectivityConfirmed {
			return addHeadersCorrupt
		}
		return addHeadersBadBlock
	}
	return addHeadersBadBlock
}

const (
	// btcAddHeadersMaxRetries / btcAddHeadersRetryDelay bound an in-place retry of AddExternalHeaders on a
	// transient (non-typed) IO/leveldb fault before the error is classified. 3 retries x 20ms = 60ms
	// worst-case added latency, only on the rare transient fault — far cheaper than the alternatives it
	// avoids (a node-local false-reject that costs a re-derive, or a full from-genesis restore).
	btcAddHeadersMaxRetries = 3
	btcAddHeadersRetryDelay = 20 * time.Millisecond
)

// isTransientAddHeadersError reports whether an AddExternalHeaders error is the transient IO/leveldb class
// an in-place retry can ride out — i.e. not a semantic outcome. A database.DuplicateError (idempotent —
// the headers are already present) and a typed database.NotFoundError (a genuine missing parent / torn
// store, handled deterministically by classifyAddExternalHeadersError) are semantic and must not be
// retried: retrying changes nothing and only delays the correct handling. Everything else is the
// non-typed leveldb/IO fault that today maps straight to addHeadersBadBlock -> consensus.ErrInvalidHVMHeaders,
// a node-local false-reject of a possibly-valid block — exactly what a retry should ride out.
// Consensus-neutral: a retry only changes whether a transient local fault rejects; the accept/reject
// verdict on healthy IO is unchanged, so it never introduces divergence — it only narrows the window of
// an already-existing node-local IO-induced reject (recoverable by re-derive/restart).
func isTransientAddHeadersError(err error) bool {
	if err == nil {
		return false
	}
	var dupErr database.DuplicateError
	var notFoundErr database.NotFoundError
	return !errors.As(err, &dupErr) && !errors.As(err, &notFoundErr)
}

// shouldRetryAddHeadersIO reports whether a non-typed AddExternalHeaders error at the apply path can only
// be a transient IO fault (retry-worthy), as opposed to a deterministic malformed-batch reject (the TBC node's
// pre-IO intra-batch contiguity check returns a plain, non-typed error that retry can never clear). It is
// retry-worthy iff op-geth's own validator already confirmed the batch connects (connectivityConfirmed —
// the accept / below-floor-defer arms) or this is restore-replay of already-committed, known-contiguous
// history (!enforceBTCDiff, where the contextual-difficulty validation block is skipped). When enforcing a batch the
// validator did not confirm (ErrBTCBatchUnconnected -> connectivityConfirmed stays false), a non-typed error
// is the deterministic contiguity reject — do not retry (avoids a redundant ~60ms-under-chainmu retry +
// per-attempt Warn spam on a bad block). Residual: a rare batch shape that op-geth's overlay accepts but
// the TBC node's stricter contiguity rejects would still be retried — bounded (one retry, then a bad block);
// the common non-connecting case is excluded.
func shouldRetryAddHeadersIO(connectivityConfirmed, enforceBTCDiff bool) bool {
	return connectivityConfirmed || !enforceBTCDiff
}

// retryWhileTransient retries `call` while its error is transient (per isTransient) up to maxRetries,
// sleeping `delay` between attempts, aborting (returning the last error) on ctx cancellation. `firstErr`
// is the error from the initial, already-made attempt; `call` re-invokes the operation. `onRetry` (if
// non-nil) is invoked before each retry's sleep with the 1-based attempt number and the error, for
// logging. It is a free function (no *BlockChain, no tbcd types) so the loop control is unit-testable
// with stub closures. Returns the final error (nil once an attempt succeeds, the last transient error
// after the bound/cancellation, or firstErr immediately when it is nil/semantic).
func retryWhileTransient(ctx context.Context, maxRetries int, delay time.Duration, isTransient func(error) bool,
	firstErr error, call func() error, onRetry func(attempt int, err error)) error {
	err := firstErr
	for attempt := 1; err != nil && isTransient(err) && attempt <= maxRetries; attempt++ {
		if onRetry != nil {
			onRetry(attempt, err)
		}
		select {
		case <-ctx.Done():
			return err
		case <-time.After(delay):
		}
		err = call()
	}
	return err
}

// consensusErrorForAddHeadersOutcome maps the two terminal AddExternalHeaders outcomes to their consensus
// error. Pure, so each arm's consensus-binding return is unit-pinned without a torn leveldb.
// addHeadersDuplicate is not mapped here: it performs IO (verify the canonical-tip claim + advance the
// state id) and returns nil on success, so it is handled inline at the call site.
func consensusErrorForAddHeadersOutcome(o addExternalHeadersOutcome) error {
	switch o {
	case addHeadersCorrupt:
		return consensus.ErrCorruptHVMHeaderOnlyModeState
	case addHeadersBadBlock:
		return consensus.ErrInvalidHVMHeaders
	default:
		// addHeadersDuplicate (handled inline) must never reach here; fail closed to an invalid block
		// (a reject), never a silent accept.
		return consensus.ErrInvalidHVMHeaders
	}
}

// applyHvmHeaderConsensusUpdate retrieves the block corresponding to
// the provided block header, extracts its Bitcoin Attributes Deposited
// transaction and, if it exists, applies the headers contained in it
// to the protocol's lightweight view of Bitcoin and verifies that the
// claimed canonical tip is correct.
// enforceBTCDiff gates contextual-difficulty enforcement. It is true on the live forward-apply
// and reorg paths and false during a full state restore/replay of already-accepted canonical blocks
// (performFullHvmHeaderStateRestore log.Crits on any apply error, so re-judging a historical block under
// the new rule must not turn recovery into a crash).
func (bc *BlockChain) applyHvmHeaderConsensusUpdate(header *types.Header, attemptPrefetch bool, enforceBTCDiff bool) error {
	// Migrate-before-enforce: a node in the DEFER state (testnet3 params over the mainnet pair
	// this boot) must NOT enforce contextual difficulty on the import path — it would judge mainnet headers
	// under TestNet3Params and split. Fold the per-boot enforceability gate in here so every caller (forward
	// apply, reorg) is covered at one point; when not enforceable the path behaves like restore/replay (the
	// already-accepted canonical headers are re-applied without re-judging difficulty).
	enforceBTCDiff = enforceBTCDiff && bc.hvmDiffEnforceable.Load()
	block := bc.getBlockFromDiskOrHoldingPen(header.Hash())
	if block == nil {
		// Block not on disk or in holding pen
		return fmt.Errorf("unable to get block %s @ %d to apply hVM consensus updates",
			header.Hash().String(), header.Number.Uint64())
	}

	stateTransitionTargetHash := [32]byte{}
	copy(stateTransitionTargetHash[0:32], header.Hash().Bytes()[0:32])

	// Store the current TBC state hash so we can put it back if we revert our changes here
	previousStateTransitionHash, err := bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
	if err != nil {
		// Migration-aware: this apply path is reachable from the forward catch-up inside the
		// migration rebuild window, where a plain log.Crit's os.Exit would leak the in-progress gauge and skip
		// the "failed" meter; route through migrationCrit when a migration is in progress.
		bc.hvmMigrationAwareCrit("Unable to get upstream state id from TBC", "err", err)
	} else {
		log.Info(fmt.Sprintf("Applying hVM header update: adding block %s @ %d, previous state id is %x",
			header.Hash().String(), header.Number.Uint64(), previousStateTransitionHash[:]))
	}

	prevHashSanity := common.BytesToHash(previousStateTransitionHash[:])
	if bytes.Equal(prevHashSanity[:], hVMGenesisUpstreamId[:]) {
		log.Info(fmt.Sprintf("Applying first hVM header update on block %s @ %d",
			header.Hash().String(), header.Number.Uint64()))
	} else {
		check := bc.getBlockFromDiskOrHoldingPen(prevHashSanity)
		if check == nil {
			// Symmetric to the currentHead==nil / unapply orphaned-store guards: the upstream-state-id's
			// block body is absent from disk + holding pen (a deep reorg/rewind orphaned it; its header may
			// still resolve, which is why the header-store currentHead guard upstream did not catch it).
			// check.Hash() below would nil-panic; return the recoverable corrupt-state sentinel so the caller
			// rebuilds the lightweight view from genesis instead of crashing.
			log.Error(fmt.Sprintf("prior-state block %x is nil while applying hVM update for %s @ %d; treating as corrupt hVM state",
				prevHashSanity[:], header.Hash().String(), header.Number.Uint64()))
			return consensus.ErrCorruptHVMHeaderOnlyModeState
		}
		checkHash := check.Hash()
		if !bytes.Equal(checkHash[:], header.ParentHash[:]) {
			// This implies a code bug as upstream calls of this function should be guarded to
			// only occur when the new block is the direct child of the current state. Migration-aware:
			// also reachable from the forward catch-up window — route through migrationCrit so the
			// failed meter/gauge are cleared before os.Exit.
			bc.hvmMigrationAwareCrit(fmt.Sprintf("Applying hVM header update for block %s @ %d failed, "+
				"previous state id is %x but parent of updated block is %s @ %d",
				header.Hash().String(), header.Number.Uint64(), previousStateTransitionHash[:],
				header.ParentHash[:], header.Number.Uint64()-1))
		}
	}

	btcAttrDep, err := block.Transactions().ExtractBtcAttrData()
	if err != nil {
		// Error implies that state of Bitcoin Attributes Deposited tx in the transaction list is invalid
		log.Error(fmt.Sprintf("Error while extracting Bitcoin Attributes Deposited transaction to process hVM state "+
			"application for applying block %s @ %d", header.Hash().String(), header.Number.Uint64()), "err", err)
		return consensus.ErrInvalidHVMBlockFormat // Block will never be valid, error was extracting BTC Attr. Dep. tx
	}

	if btcAttrDep == nil {
		log.Info(fmt.Sprintf("Nothing to apply in hVM state for block %s @ %d; doesn't contain a Bitcoin "+
			"Attributes Deposited transaction", header.Hash().String(), header.Number.Uint64()))

		// Even though we didn't make any changes, explicitly update TBC's state id to indicate that
		// TBC's current state is correct after processing this block if hVM Phase 0 is active at
		// this block's timestamp
		if bc.chainConfig.IsHvm0(header.Time) {
			err := bc.tbcHeaderNode.SetUpstreamStateId(bc.ctx, stateTransitionTargetHash)
			if err != nil {
				// Being unable to set the upstream state id implies possible data corruption
				log.Error(fmt.Sprintf("Error while updating the upstream state id in TBC with no corresponding "+
					"consensus state modifications for block %s @ %d", header.Hash().String(), header.Number.Uint64()), "err", err)
				return consensus.ErrCorruptHVMHeaderOnlyModeState
			}
		}
		return nil
	}

	if !bc.chainConfig.IsHvm0(header.Time) { // && btcAttrDep != nil per above check
		log.Error(fmt.Sprintf("block %s @ %d has a Bitcoin Attributes Deposited transaction but its timestamp "+
			"%d is before the hVM Phase 0 activation height %d", header.Hash().String(), header.Number.Uint64(),
			header.Time, *bc.chainConfig.Hvm0Time))
		return consensus.ErrInvalidHVMBlockFormat // Block will never be valid
	}

	prevHeight, prevTip, err := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
	if err != nil {
		// Being unable to get the best block header implies possible data corruption
		log.Error(fmt.Sprintf("when processing block %s @ %d, unable to retrieve tip from lightweight TBC!",
			header.Hash().String(), header.Number.Uint64()), "err", err)
		return consensus.ErrCorruptHVMHeaderOnlyModeState
	}
	log.Debug(fmt.Sprintf("before processing BTC headers from block %s @ %d, the lightweight TBC node's tip "+
		"is %s @ %d", header.Hash().String(), header.Number.Uint64(), prevTip.BlockHash().String(), prevHeight))

	prevTipHash := prevTip.BlockHash()

	headersToAdd := len(btcAttrDep.Headers)
	var lastHeader *[80]byte
	if headersToAdd > 0 {
		// BTC Attributes Deposited transaction communicates at least one new header, store the last one for reference
		lastHeader = &btcAttrDep.Headers[headersToAdd-1]

		reconstitutedHeaders, err := unflattenBTCHeaders(btcAttrDep.Headers)
		if err != nil {
			// Being unable to parse the BTC headers in the Bitcoin Attributes Deposited transaction means the
			// transaction (and thus block) is invalid
			log.Error(fmt.Sprintf("when applying hVM changes for block %s @ %d, unable to unflatten "+
				"one of the BTC headers from the block", header.Hash().String(), header.Number.Uint64()),
				"err", err)
			return consensus.ErrInvalidHVMBlockFormat
		}

		// Contextual-difficulty (enforce on the consensus path — floor-aware). Validate the batch's contextual Bitcoin
		// difficulty against the lightweight consensus view before committing it. This is the
		// consensus-binding ingress, so it is the authoritative enforcement point. The other two writers
		// into bc.tbcHeaderNode are also covered: the
		// sequencer build path validates+truncates and snap-sync validates the enforceable suffix before
		// bulk-loading (see getBitcoinAttributesForNextBlock and SnapSyncHvm). Outcomes:
		//   - accept (nil): proceed to commit.
		//   - below floor: the lightweight node is seeded from an effective-genesis floor
		//     (GenesisHeightOffset), so near-floor headers' required walks cross below the floor and are
		//     unverifiable here; defer (fall through to AddExternalHeaders, whose cumulative-work + the
		//     canonical-tip check below still apply). Bounded near-floor band, but not one-time: the floor
		//     gate is stateless, so a reorg back below floor+clearance re-enters the defer band (see the
		//     vm.ErrBTCBatchBelowFloor doc).
		//   - unconnected: the batch does not connect to committed state; fall through so the existing
		//     AddExternalHeaders no-orphan path reports it as ErrInvalidHVMHeaders.
		//   - genuine RuleError: a real contextual violation -> ErrInvalidHVMHeaders (returns before any
		//     AddExternalHeaders commit; the insertChain caller walks consensus state back).
		//   - IO/corrupt read: ErrCorruptHVMHeaderOnlyModeState (recoverable; never a silent accept).
		// Gated on the hVM fork and on enforceBTCDiff (skipped during restore/replay).
		// batchConnectivityConfirmed records whether the floor-aware validator confirmed the batch connects
		// to committed state. The validator's anchor loop resolves every header's parent (returning
		// Unconnected / IO-corrupt first) before the floor gate, so both a nil and a below-floor verdict
		// prove the parents were present. The AddExternalHeaders error classifier below uses this to tell a
		// torn store (connectivity confirmed, yet a header now missing -> corrupt) apart from a genuinely
		// non-connecting batch (-> invalid block). Left false when the validator reported Unconnected or did
		// not run (replay / pre-fork).
		batchConnectivityConfirmed := false
		if enforceBTCDiff && bc.chainConfig.IsHvm0(header.Time) {
			// Proof-of-work gate (context-free; runs on every header, not subject to the
			// effective-genesis floor defer the contextual check below uses, because hash<=target needs no
			// ancestry). This verifies the header's hash meets its claimed target (real work), independent
			// of the difficulty field the contextual check validates. Gated on
			// the same enforceBTCDiff as the contextual check. A btcd RuleError here is an invalid block; an
			// unknown-network/nil fail-closes to recoverable corrupt state (never a silent accept).
			switch err := vm.CheckBTCHeaderBatchPoWForNetwork(bc.tbcHeaderNodeConfig.Network,
				reconstitutedHeaders.Headers); {
			case err == nil:
				// every header meets its claimed PoW target; fall through to the contextual check
			case errors.Is(err, vm.ErrBTCHeaderContextUnavailable):
				log.Error(fmt.Sprintf("block %s @ %d: BTC-header PoW validation could not be parameterized "+
					"(unknown network / nil) — treating as recoverable corrupt state",
					header.Hash().String(), header.Number.Uint64()), "err", err)
				return consensus.ErrCorruptHVMHeaderOnlyModeState
			default:
				log.Error(fmt.Sprintf("block %s @ %d: REJECTED — its Bitcoin Attributes Deposited tx carries a "+
					"BTC header whose hash does not meet its claimed proof-of-work target",
					header.Hash().String(), header.Number.Uint64()), "err", err)
				return consensus.ErrInvalidHVMHeaders
			}

			switch err := vm.ValidateBTCHeaderBatchForNetwork(bc.ctx, bc.tbcHeaderNode,
				bc.tbcHeaderNodeConfig.Network, bc.tbcHeaderNodeConfig.GenesisHeightOffset,
				reconstitutedHeaders.Headers); {
			case err == nil:
				// every header is contextually valid AND connects; proceed to commit
				batchConnectivityConfirmed = true
			case errors.Is(err, vm.ErrBTCBatchBelowFloor):
				// near-floor: enforcement deferred, but the anchor loop still confirmed connectivity
				batchConnectivityConfirmed = true
				log.Debug(fmt.Sprintf("block %s @ %d: BTC header batch is within the effective-genesis-floor "+
					"clearance; deferring contextual-difficulty enforcement to AddExternalHeaders for this batch",
					header.Hash().String(), header.Number.Uint64()))
			case errors.Is(err, vm.ErrBTCBatchUnconnected):
				log.Warn(fmt.Sprintf("block %s @ %d: BTC header batch does not connect to the committed "+
					"consensus view; letting AddExternalHeaders reject it", header.Hash().String(), header.Number.Uint64()))
			case errors.Is(err, vm.ErrBTCHeaderContextUnavailable):
				log.Error(fmt.Sprintf("block %s @ %d: contextual BTC-difficulty validation hit an IO/unreadable "+
					"lightweight-TBC error — treating as recoverable corrupt state",
					header.Hash().String(), header.Number.Uint64()), "err", err)
				return consensus.ErrCorruptHVMHeaderOnlyModeState
			default:
				log.Error(fmt.Sprintf("block %s @ %d: REJECTED — its Bitcoin Attributes Deposited tx carries a "+
					"contextually-invalid BTC header (wrong difficulty / median-time-past / version)",
					header.Hash().String(), header.Number.Uint64()), "err", err)
				return consensus.ErrInvalidHVMHeaders
			}
		}

		log.Info(fmt.Sprintf("[Apply HVM Header Consensus Update] *ADDING* external BTC headers:"))
		for i := 0; i < len(reconstitutedHeaders.Headers); i++ {
			log.Info(fmt.Sprintf("\t %s", reconstitutedHeaders.Headers[i].BlockHash().String()))
		}

		it, cbh, lbh, _, err := bc.tbcHeaderNode.AddExternalHeaders(
			bc.ctx, reconstitutedHeaders, stateTransitionTargetHash[:])
		// Retry in place on a transient (non-typed) IO/leveldb fault before classifying — rides out a
		// momentary blip that would otherwise be classified addHeadersBadBlock -> ErrInvalidHVMHeaders (a
		// node-local false-reject) or, on the restore-replay path, log.Crit the rebuild.
		//
		// Why retry is idempotent (the underlying store write is not atomic, so a fault mid-write can leave
		// a partial commit): (1) a re-insert is duplicate-skipped (keyed on the header hash) — cumulative
		// work is recomputed deterministically from Bits, never double-counted; and (2) the one partial-commit
		// window that matters — headers committed but the upstream-state-id not — re-surfaces on retry as
		// DuplicateError, which the addHeadersDuplicate arm below repairs idempotently (re-verifies the
		// canonical tip and re-issues SetUpstreamStateId).
		// That duplicate-arm SetUpstreamStateId advance is load-bearing for this case; do not remove it.
		// See isTransientAddHeadersError. Bounded; aborts on ctx cancellation. Gated by shouldRetryAddHeadersIO
		// so a deterministic malformed-batch reject (which retry can never clear) is classified immediately
		// rather than burning the retry budget + Warn spam.
		if shouldRetryAddHeadersIO(batchConnectivityConfirmed, enforceBTCDiff) {
			err = retryWhileTransient(bc.ctx, btcAddHeadersMaxRetries, btcAddHeadersRetryDelay, isTransientAddHeadersError, err,
				func() error {
					it, cbh, lbh, _, err = bc.tbcHeaderNode.AddExternalHeaders(
						bc.ctx, reconstitutedHeaders, stateTransitionTargetHash[:])
					return err
				},
				func(attempt int, e error) {
					log.Warn(fmt.Sprintf("block %s @ %d: transient IO fault adding BtcAttr BTC headers to the "+
						"lightweight view; retrying in place (attempt %d/%d) before classifying",
						header.Hash().String(), header.Number.Uint64(), attempt, btcAddHeadersMaxRetries), "err", e)
				})
		}
		// This retry is deliberately scoped to the consensus apply funnel (all three consensus callers —
		// forward-apply, reorg, and restore-replay — route through applyHvmHeaderConsensusUpdate). The
		// other AddExternalHeaders sites (snap reconstruction; sequencer build-path dry-run) keep their
		// fail-stop crits: those are node-local and restart-recoverable, and the sequencer dry-run's
		// Add-then-Remove would need separate idempotency reasoning to retry safely.
		if err != nil {
			addOutcome := classifyAddExternalHeadersError(err, batchConnectivityConfirmed)
			switch addOutcome {
			case addHeadersDuplicate:
				// Idempotent: every header in the batch is already present (a post-restore retry or a reorg
				// re-apply), never a bad block. AddExternalHeaders returned before running its state-id batch
				// hook, so — like the empty-but-present path — verify the claimed canonical tip against the
				// (already-updated) view and advance the upstream state id to this block ourselves. On any
				// inconsistency, self-heal (corrupt) rather than false-reject a possibly-canonical block.
				_, curTip, e := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
				if e != nil {
					log.Error(fmt.Sprintf("block %s @ %d: BtcAttr headers already present, but reading the current "+
						"canonical tip failed", header.Hash().String(), header.Number.Uint64()), "err", e)
					return consensus.ErrCorruptHVMHeaderOnlyModeState
				}
				curTipHash := curTip.BlockHash()
				if !bytes.Equal(curTipHash[:], btcAttrDep.CanonicalTip[:]) {
					log.Error(fmt.Sprintf("block %s @ %d: BtcAttr headers already present, but the canonical tip "+
						"%x does not match the claimed %x — treating as recoverable corrupt state",
						header.Hash().String(), header.Number.Uint64(), curTipHash[:], btcAttrDep.CanonicalTip[:]))
					return consensus.ErrCorruptHVMHeaderOnlyModeState
				}
				if e := bc.tbcHeaderNode.SetUpstreamStateId(bc.ctx, stateTransitionTargetHash); e != nil {
					log.Error(fmt.Sprintf("block %s @ %d: BtcAttr headers already present, but advancing the upstream "+
						"state id failed", header.Hash().String(), header.Number.Uint64()), "err", e)
					return consensus.ErrCorruptHVMHeaderOnlyModeState
				}
				log.Info(fmt.Sprintf("block %s @ %d: BtcAttr BTC headers already present in the lightweight view "+
					"(duplicate); treated as idempotent, advanced upstream state id, canonical tip unchanged",
					header.Hash().String(), header.Number.Uint64()))
				return nil
			case addHeadersCorrupt:
				// Connectivity was just confirmed by the validator, yet AddExternalHeaders reports a typed
				// NotFound -> a header just proven present is missing -> a torn lightweight view, not a bad
				// block. Recoverable via restore.
				log.Error(fmt.Sprintf("block %s @ %d: adding BtcAttr BTC headers failed although connectivity was "+
					"confirmed — treating as recoverable corrupt state", header.Hash().String(), header.Number.Uint64()),
					"err", err)
				return consensusErrorForAddHeadersOutcome(addOutcome)
			default: // addHeadersBadBlock
				// The batch genuinely does not connect to committed state (no validator connectivity
				// confirmation), is malformed (intra-batch non-contiguity), or hit a non-typed leveldb/IO
				// fault -> invalid block (preserves pre-difficulty-enforcement AddExternalHeaders no-orphan behavior). An IO
				// fault here is a node-local false-reject (a known residual; healthy peers still accept) — it
				// is never a silent accept and never a consensus split.
				log.Error(fmt.Sprintf("block %s @ %d has a Bitcoin Attributes Deposited transaction which contains "+
					"%d Bitcoin headers, and adding these headers to hVM's lightweight BTC consensus view caused an "+
					"error", header.Hash().String(), header.Number.Uint64(), len(btcAttrDep.Headers)), "err", err)
				// Pass the classified outcome (not a literal) so the test-pinned mapper is the single source
				// of the consensus return: a deleted case label or a swapped literal cannot change it.
				return consensusErrorForAddHeadersOutcome(addOutcome)
			}
		}

		// Proactively check for any missing full blocks between full TBC's current indexed height and the
		// new canonical tip that resulted from adding the new headers, and trigger a fetch from peers for
		// any blocks that we will need in the future when the full TBC node's indexers are advanced.

		// Convert tbcd.BlockHeader (contains position and cumulative diff. info) to wire.BlockHeader
		cbhWire, err := cbh.Wire()
		if err != nil {
			// Although this failure does not immediately prevent chain progression, the inability to convert
			// the canonical block hash returned from TBC by adding headers to a wire indicates something has
			// gone very wrong so exit. Also reachable from the migration forward catch-up window — route through
			// migrationCrit so the failed meter/gauge are cleared before os.Exit.
			bc.hvmMigrationAwareCrit(fmt.Sprintf("after applying Bitcoin consensus information from block %s @ %d to "+
				"hVM's lightweight BTC consensus view, the canonical header %s returned could not be converted "+
				"to a wire message", header.Hash().String(), header.Number.Uint64(), cbh.Hash.String()),
				"err", err)
		}

		if attemptPrefetch {
			_, blocksMissing, _, err := vm.TBCBlocksAvailableToHeader(bc.ctx, cbhWire)
			if err != nil {
				log.Error(fmt.Sprintf("unable to proactively check for full TBC node containing blocks to tip %s",
					cbh.Hash.String()), "err", err)
			}

			if blocksMissing != nil {
				if len(*blocksMissing) > 0 {
					for _, blockMissing := range *blocksMissing {
						// Note that it's possible the canonical tip returned by lightweight consensus is not canonical
						// on the actual Bitcoin network and one or more blocks cannot be acquired, but as long as
						// the reorg is smaller than the hVM indexing delay/lag it will be fine.
						log.Info(fmt.Sprintf("Proactively attempting to fetch missing full BTC block %s from TBC peers "+
							"so it will be available when needed for indexing", blockMissing.BlockHash().String()))
						vm.TBCAttemptBlockRefetch(bc.ctx, &blockMissing)
					}
				}
			}
		}

		cbHash := cbh.Hash[:]
		// Check that the Bitcoin Attributes Deposited transaction claims the correct canonical tip
		if !bytes.Equal(cbHash, btcAttrDep.CanonicalTip[:]) {
			// Canonical tip determined by TBC based on the new headers does not match canonical tip claimed by
			// Bitcoin Attributes Deposited transaction

			// Print out error, then remove the bad headers to return TBC to the correct state
			log.Error(fmt.Sprintf("block %s @ %d has a Bitcoin Attributes Deposited transaction which "+
				"claims that after adding %d headers ending with %x, the canonical tip should be %x, but after "+
				"adding the headers to TBC the canonical tip is %x", header.Hash().String(), header.Number.Uint64(),
				headersToAdd, lastHeader[:], btcAttrDep.CanonicalTip[:], cbHash[:]))

			log.Info(fmt.Sprintf("[Apply HVM Header Consensus Update] *REMOVING* external BTC headers:"))
			for i := 0; i < len(reconstitutedHeaders.Headers); i++ {
				log.Info(fmt.Sprintf("\t %s", reconstitutedHeaders.Headers[i].BlockHash().String()))
			}

			// Remove the added headers and set the canonical tip and previous upstream state id back to
			// what it was prior to the invalid addition
			rt, removalParent, err := bc.tbcHeaderNode.RemoveExternalHeaders(
				bc.ctx, reconstitutedHeaders, prevTip, previousStateTransitionHash[:])

			if err != nil {
				log.Error(fmt.Sprintf("after adding headers ending with %x from the Bitcoin Attributes "+
					" Deposited transaction in block %s @ %d, unable to remove those headers from TBC's view",
					lastHeader[:], header.Hash().String(), header.Number), "err", err)

				// Unable to unapply our undesired changes, TBC lightweight node could be recovered
				return consensus.ErrCorruptHVMHeaderOnlyModeState
			}

			removalParentHash := removalParent.BlockHash()

			log.Error(fmt.Sprintf("successfully removed headers applied from invalid block %s @ %d, last header "+
				"before removed section is %x. Removal type: %d", header.Hash().String(), header.Number.Uint64(),
				removalParentHash[:], rt))

			// Headers this block adds to lightweight view don't result in the claimed new canonical tip
			return consensus.ErrInvalidHVMHeaders
		}

		lbHash := lbh.Hash[:]
		if !bytes.Equal(lbh.Header[:], lastHeader[:]) {
			// Indicates a bug in TBC, as TBC didn't add all the headers we passed in.
			// Unlikely this would be due to data corruption, so assume bug and exit. Also reachable from the
			// migration forward catch-up window — route through migrationCrit so the failed meter/gauge are
			// cleared before os.Exit.
			bc.hvmMigrationAwareCrit(fmt.Sprintf("block %s @ %d has a Bitcoin Attributes Deposited transaction which "+
				"contains %d headers ending in %x, but after adding those headers to lightweight TBC, TBC's last "+
				"added block was %x", header.Hash().String(), header.Number.Uint64(), headersToAdd, lastHeader[:],
				lbHash[:]))
		}

		log.Info(fmt.Sprintf("Successfully added %d bitcoin headers from the Bitcoin Attributes Deposited tx "+
			"from block %s @ %d, current canonical tip is %x, former tip was %x @ %d, insertType=%d", headersToAdd,
			header.Hash().String(), header.Number.Uint64(), lbHash[:], prevTipHash[:], prevHeight, it))
		return nil
	} else {
		// Empty-but-present case (btcAttrDep != nil, zero headers): the forward counterpart of the unapply
		// btcAttrDepIsHeaderless(...) no-op branch; the two must stay exact inverses, so keep this
		// structural classification consistent with that helper if refactored.
		//
		// No headers to add, make sure that claimed canonical in BTC Attributes Deposited matches TBC's current
		if !bytes.Equal(prevTipHash[:], btcAttrDep.CanonicalTip[:]) {
			log.Error(fmt.Sprintf("block %s @ %d contains a Bitcoin Attributes Deposited transaction which "+
				"does not contain any headers, but claims the canonical tip should be %x when light TBC's tip "+
				"is %x", header.Hash().String(), header.Number.Uint64(), btcAttrDep.CanonicalTip[:], prevTipHash[:]))
			// Block contains a BTC Attr. Dep. transaction which claims an incorrect canonical claim, reject
			return consensus.ErrInvalidHVMHeaders
		}
		// An empty-but-present BtcAttr tx makes no TBC header change, but — like the no-BtcAttr-tx path
		// above and the headers-added path (which advances the id via AddExternalHeaders) — we must still
		// advance the TBC upstream state id to represent this block. Omitting it would leave the id at the
		// parent, which then trips the parent-mismatch check when the next block is applied (and during a
		// full state restore). The upstream state id is TBC-internal metadata (never part of the EVM state
		// root / block hash), so advancing it here is consensus-safe and changes no block's acceptance —
		// the CanonicalTip check above is the only acceptance decision and is preserved. The matching
		// unapply rolls it back.
		if bc.chainConfig.IsHvm0(header.Time) {
			err := bc.tbcHeaderNode.SetUpstreamStateId(bc.ctx, stateTransitionTargetHash)
			if err != nil {
				// Being unable to set the upstream state id implies possible data corruption
				log.Error(fmt.Sprintf("Error while updating the upstream state id in TBC for a Bitcoin "+
					"Attributes Deposited transaction with no headers for block %s @ %d", header.Hash().String(),
					header.Number.Uint64()), "err", err)
				return consensus.ErrCorruptHVMHeaderOnlyModeState
			}
		}
		return nil
	}
}

// setMissingProgressionBlocks updates the missing-BTC-progression cache under tbcHeaderNodeMu so the
// lock-free GetMissingBtcBlocks reader (peer-broadcast goroutine) cannot race this write. tbcHeaderNodeMu
// — not chainmu — serializes this write against that reader, so the guard is correct regardless of
// caller: the writers are reached from both the chainmu-held apply path and the non-chainmu SnapSyncHvm
// completion path (both via updateFullTBCToLightweight). For chainmu-held callers the lock ordering is
// chainmu -> tbcHeaderNodeMu; reset never holds the mutex while reaching here, so there is no reentrant Lock.
func (bc *BlockChain) setMissingProgressionBlocks(m *wire.MsgHeaders) {
	bc.tbcHeaderNodeMu.Lock()
	bc.missingProgressionBlocks = m
	bc.tbcHeaderNodeMu.Unlock()
}

func (bc *BlockChain) GetMissingBtcBlocks() []common.Hash {
	if bc == nil {
		return nil
	}
	// This runs on the per-peer broadcast goroutine (prefetchBTCBlocks), outside chainmu, so it can race
	// resetHvmHeaderNodeToGenesis tearing down + reassigning bc.tbcHeaderNode (and the missingProgressionBlocks
	// writes). Hold the read side of tbcHeaderNodeMu only around the lifecycle-sensitive accesses — the
	// tbcHeaderNode nil-check, the missingProgressionBlocks read, and BlockHeaderBest (which produces `tip`) —
	// and release it before the unbounded full-node walk below. `tip` is a freshly-decoded *wire.BlockHeader
	// that does not alias the torn-down node, and TBCBlocksAvailableToHeader touches only the independent
	// global vm.TBCFullNode, so it is safe to run unlocked; releasing first means a from-genesis restore
	// (which takes tbcHeaderNodeMu.Lock while holding chainmu on the re-apply path) is never stalled behind
	// this broadcast read, avoiding a priority inversion that would freeze block insertion. TryRLock (not
	// RLock) so we never even briefly block on an in-progress reset — a missed 5s prefetch round is benign.
	tip, early, done := func() (*wire.BlockHeader, []common.Hash, bool) {
		if !bc.tbcHeaderNodeMu.TryRLock() {
			log.Debug("GetMissingBtcBlocks() skipped: lightweight TBC node reset in progress")
			return nil, nil, true
		}
		defer bc.tbcHeaderNodeMu.RUnlock()

		if bc.tbcHeaderNode == nil {
			log.Warn("GetMissingBtcBlocks() does not have tbcHeaderNode active yet")
			return nil, nil, true
		}

		if bc.missingProgressionBlocks != nil {
			headers := bc.missingProgressionBlocks.Headers
			missingHashArr := make([]common.Hash, len(headers))
			for i := 0; i < len(headers); i++ {
				blockhash := headers[i].BlockHash()
				bhBytes := blockhash.CloneBytes()
				var hash common.Hash
				hash.SetBytes(bhBytes)
				missingHashArr[i] = hash
			}
			return nil, missingHashArr, true
		}

		_, t, err := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
		if err != nil {
			log.Debug("Unable to get best block header from TBC node in GetMissingBtcBlocks()", "err", err)
			return nil, nil, true
		}
		return t, nil, false
	}()
	if done {
		return early
	}

	// tbcHeaderNodeMu is released here: the rest operates on the independent global vm.TBCFullNode using the
	// already-captured `tip`, so it runs unlocked and cannot stall a concurrent lightweight-node reset.
	_, blocksMissing, missingHeaderHash, err := vm.TBCBlocksAvailableToHeader(bc.ctx, tip)
	if err != nil {
		log.Error(fmt.Sprintf("unable to proactively check for full TBC node containing blocks to tip %s",
			tip.BlockHash().String()), "err", err)
	}

	if missingHeaderHash != nil {
		// Create an array with just the hash of the one known missing header
		missingHashArr := make([]common.Hash, 0)
		bhBytes := missingHeaderHash.CloneBytes()
		var hash common.Hash
		hash.SetBytes(bhBytes)
		missingHashArr = append(missingHashArr, hash)
		return missingHashArr
	}

	if blocksMissing != nil {
		if len(*blocksMissing) > 0 {
			missingFullBlocks := make([]common.Hash, 0)
			for _, blockMissing := range *blocksMissing {
				bh := blockMissing.BlockHash()
				bhBytes := bh.CloneBytes()
				var hash common.Hash
				hash.SetBytes(bhBytes)
				missingFullBlocks = append(missingFullBlocks, hash)
			}
			return missingFullBlocks
		}
	}

	return nil
}

func (bc *BlockChain) IsHvmEnabled() bool {
	return bc.hvmEnabled
}

// btcAttrCacheKey identifies the inputs the cached Bitcoin Attributes Deposited tx was built from. The
// tx is a pure function of these three: the EVM tip it is built on top of, and the lightweight and
// full-node BTC consensus tips (which together drive the walk-back and the set of headers the tx
// carries), so the cached entry is valid only while all three are unchanged. Keying on the EVM tip alone
// would let a BTC-view change (the full node syncing new headers or a Bitcoin reorg) while the EVM tip is
// unchanged keep re-serving a stale tx; if that stale tx is then rejected, the sequencer re-serves it
// forever — a permanent self-inflicted halt. Keying on all three (a comparable struct, so no dimension
// can be silently dropped) invalidates the entry on any BTC-view change. See TestBtcAttrCacheKey.
type btcAttrCacheKey struct {
	evmTip   common.Hash    // the EVM block the next block is built on top of
	lightTip chainhash.Hash // lightweight TBC node's best BTC header at build time
	fullTip  chainhash.Hash // full TBC node's best BTC header at build time
}

// cachedBtcAttrFor returns the cached Bitcoin Attributes Deposited tx iff a non-nil entry was built for
// exactly this (evmTip, lightTip, fullTip) view; otherwise nil. Pure over the receiver's cache fields, so
// the hit/miss decision (the all-three-must-match key and the non-nil-entry guard) is unit-testable
// without a live full node. Callers must hold bc.chainmu.
func (bc *BlockChain) cachedBtcAttrFor(key btcAttrCacheKey) *types.BtcAttributesDepositedTx {
	if bc.btcAttributesDepCacheEntry != nil && bc.btcAttributesDepCacheKey == key {
		return bc.btcAttributesDepCacheEntry
	}
	return nil
}

// storeBtcAttrCache records the freshly-built tx under its full (evmTip, lightTip, fullTip) key. Callers
// must hold bc.chainmu. Paired with cachedBtcAttrFor so the inline check and write are pinned together by
// TestBtcAttrCacheRoundTrip.
func (bc *BlockChain) storeBtcAttrCache(key btcAttrCacheKey, tx *types.BtcAttributesDepositedTx) {
	bc.btcAttributesDepCacheKey = key
	bc.btcAttributesDepCacheEntry = tx
}

// errHvmBtcAttrPendingBlocked is an internal sentinel returned by getBitcoinAttributesForNextBlock when
// the TBC full node has BTC consensus headers the lightweight view lacks (so the hVM Bitcoin view is
// supposed to advance) but they could not be turned into a BtcAttr tx this round — the full block for the
// next header is not yet available, or a should-never-happen header inconsistency was hit. Not a hard
// error (the caller still builds a valid block without the tx), but it must not be reported as a healthy
// idle cycle or a persistent stall would be invisible to operators. The public wrapper maps it to the
// stuck gauge and hides it from the caller.
var errHvmBtcAttrPendingBlocked = errors.New("hVM BtcAttr: pending BTC headers could not be communicated this build")

// GetBitcoinAttributesForNextBlock computes the optional Bitcoin Attributes Deposited tx for
// the next block on the sequencer build path. It wraps getBitcoinAttributesForNextBlock to
// record an alertable failure metric: on the build path a returned error makes the caller skip
// this block's (optional) BtcAttr tx and retry, so a persistent failure is otherwise only
// visible as a recurring per-build log.Error.
func (bc *BlockChain) GetBitcoinAttributesForNextBlock(timestamp uint64) (*types.BtcAttributesDepositedTx, error) {
	return finalizeHvmBtcAttrResult(bc.getBitcoinAttributesForNextBlock(timestamp))
}

// finalizeHvmBtcAttrResult records the observability metrics (via recordHvmBtcAttrResult) and
// produces the public (tx, err) pair. On any error surfaced to the caller it never leaks a
// partial tx (returns nil, rerr); otherwise it returns tx unchanged — nil for an idle cycle or a
// hidden "pending blocked" sentinel, the built tx on success. Extracted as a pure function so the
// "no partial tx alongside an error" guarantee can be unit-tested without a TBC node.
func finalizeHvmBtcAttrResult(tx *types.BtcAttributesDepositedTx, err error) (*types.BtcAttributesDepositedTx, error) {
	if rerr := recordHvmBtcAttrResult(err); rerr != nil {
		return nil, rerr
	}
	return tx, nil
}

// recordHvmBtcAttrResult records the observability metrics for a BtcAttr generation outcome and
// returns the error the public method should expose to the caller. It is the single place that
// classifies the inner result, so it can be unit-tested without a TBC node:
//   - nil (success or a legitimately idle cycle): clear the stuck gauge.
//   - errHvmBtcAttrPendingBlocked: pending BTC work that did not advance this round (e.g. the
//     next full block is not yet downloaded). Raise the stuck gauge but hide the sentinel from
//     the caller (return nil) so it surfaces as a plain (nil, nil) idle return — no error log spam.
//   - shutdown (errChainStopped, or context.Canceled): not an hVM fault — leave metrics untouched
//     to avoid a spurious alert during shutdown.
//   - any other error: a genuine failure; mark the fail meter and raise the stuck gauge.
func recordHvmBtcAttrResult(err error) error {
	switch {
	case err == nil:
		hvmBtcAttrFailingGauge.Update(0)
	case errors.Is(err, errHvmBtcAttrPendingBlocked):
		hvmBtcAttrFailingGauge.Update(1)
		return nil
	case errors.Is(err, errChainStopped) || errors.Is(err, context.Canceled):
		// Shutdown teardown only. bc.ctx is cancel-only (context.WithCancel, no deadline), so a
		// context.Canceled on this path is the chain context being torn down at Stop(), not a
		// fault — leave metrics untouched to avoid a spurious alert.
		//
		// Load-bearing: we deliberately do not fold context.DeadlineExceeded here. No shutdown path
		// produces it (bc.ctx has no deadline), so a DeadlineExceeded could only originate from a
		// downstream per-call timeout — a genuine backend stall that must raise the alert, so it falls
		// through to the default branch below. If a future change gives bc.ctx a deadline, revisit this.
	default:
		hvmBtcAttrFailMeter.Mark(1)
		hvmBtcAttrFailingGauge.Update(1)
	}
	return err
}

// btcAttrFutureSkewWindow is how far a block timestamp may lead wall-clock (seconds) before the sequencer
// skips attaching a Bitcoin Attributes Deposited tx to it.
const btcAttrFutureSkewWindow = 60 * 60

// btcAttrFutureSkewExceeded reports whether a candidate block timestamp is too far in the FUTURE (more than
// btcAttrFutureSkewWindow ahead of wall-clock `now`) for the sequencer to attach a BtcAttr tx. The ordered
// compare (timestamp > now first) avoids the uint64 underflow that `timestamp - now` would hit for a
// past-timestamped catch-up block — which must still get the tx — so it returns false for every timestamp
// at or before now. Extracted as a pure predicate so this build-path decision is unit-testable.
func btcAttrFutureSkewExceeded(timestamp, now uint64) bool {
	return timestamp > now && timestamp-now > btcAttrFutureSkewWindow
}

// enforceableBTCBatch is the build-path difficulty-enforceability classifier used by longestEnforceableBTCHeaderPrefix to
// truncate the sequencer's proposed BTC-header prefix at the first non-enforceable header. A DEFER-state node
// (hvmDiffEnforceable=false: testnet3 params over the mainnet pair) must NOT truncate — it would judge real
// mainnet headers under TestNet3Params (the 20-min rule) and drop honest headers a correctly-migrated sequencer
// keeps, diverging the build path; it returns nil (accept the full prefix; the apply path is the enforcement
// point and is also gated). When enforceable it checks proof-of-work first (a PoW RuleError truncates like a
// contextual one, so the sequencer never proposes a header whose hash does not meet its target), then contextual
// difficulty. Extracted so the deferred-vs-enforced gate is unit-testable on the real logic.
func (bc *BlockChain) enforceableBTCBatch(batch []*wire.BlockHeader) error {
	if !bc.hvmDiffEnforceable.Load() {
		return nil
	}
	if e := vm.CheckBTCHeaderBatchPoWForNetwork(bc.tbcHeaderNodeConfig.Network, batch); e != nil {
		return e
	}
	return vm.ValidateBTCHeaderBatchForNetwork(bc.ctx, bc.tbcHeaderNode,
		bc.tbcHeaderNodeConfig.Network, bc.tbcHeaderNodeConfig.GenesisHeightOffset, batch)
}

func (bc *BlockChain) getBitcoinAttributesForNextBlock(timestamp uint64) (*types.BtcAttributesDepositedTx, error) {
	// Lock the chain mutex - all other code that modifies lightweight TBC node respects this mutex
	// and locking this resource ensures that we can safely modify the lightweight TBC node to ensure
	// the new Bitcoin Attributes Deposited transaction we generate can be successfully applied
	// when it occurs in a block for real, and also to ensure the canonical tip we report matches what
	// canonical tip lightweight TBC will report after the specified headers are added.
	if !bc.chainmu.TryLock() {
		return nil, errChainStopped
	}
	defer bc.chainmu.Unlock()

	// Don't generate a Bitcoin Attributes deposited transaction unless we're building for a recent block.
	// Only FUTURE skew gates: a past-timestamped block (e.g. sequencer catch-up after downtime, where L2
	// timestamps lag wall clock) must still generate the BtcAttr tx. The ordered compare avoids the uint64
	// underflow that `timestamp - now` would hit when timestamp < now (which would wrongly drop the tx and
	// stall the BTC view for the whole catch-up window). XXX: Move this upstream?
	now := uint64(time.Now().Unix())
	if btcAttrFutureSkewExceeded(timestamp, now) {
		// No error, but no BTC Attributes Dep tx
		return nil, nil
	}

	if !bc.hvmEnabled {
		// hVM not enabled, nothing to do
		return nil, nil
	}

	if !bc.chainConfig.IsHvm0(timestamp) {
		// hVM enabled but not yet at activation time, nothing to do
		return nil, nil
	}

	if bc.isAwaitingHvmSnapSync() {
		// During an hVM snap sync the lightweight TBC view is owned and rebuilt by SnapSyncHvm (via
		// AddExternalHeaders), so reading its BTC tip here would race that rebuild and could emit a BtcAttr
		// tx bound to a half-restored view. Skip the (optional) BtcAttr tx for this block and retry on the
		// next; the post-snap catch-up re-syncs the view. Mirrors the same latch gate in ProcessBlock and
		// updateHvmHeaderConsensus. Safe under chainmu: chainmu->hvmSnapMu is the established lock order
		// (ProcessBlock takes this latch under chainmu too), and hvmSnapMu is a leaf.
		return nil, nil
	}

	lastTip := bc.CurrentBlock()
	if lastTip == nil {
		// Build path: returning an error makes the sequencer skip the (optional) Bitcoin
		// Attributes Deposited tx for this block and retry on the next one, rather than
		// crashing the process. No lightweight-TBC state has been mutated at this point.
		return nil, errors.New("unable to generate the Bitcoin Attributes Deposited transaction, " +
			"as the current EVM tip is unknown")
	}
	lastTipHash := lastTip.Hash()

	log.Info(fmt.Sprintf("Generating Bitcoin Attributes Deposited transaction for a new block with timestamp "+
		"%d on top of prior block %s @ %d", timestamp, lastTip.Hash().String(), lastTip.Number.Uint64()))

	// NOTE: the build cache is checked BELOW, after the lightweight + full-node BTC tips are read, because
	// the cache key includes both (a BTC-view change must invalidate the entry — see btcAttrCacheKey).

	// Sanity check: lightweight TBC node's state should always reflect lastTip when this is called.
	// If it doesn't, log the error and manually move the lightweight node to represent the current
	// tip so we can return valid data.
	currentTbcEvmTip, err := bc.getHeaderModeTBCEVMHeader()
	if err != nil {
		// Read-only lookup; no lightweight-TBC mutation yet. Skip this block's BtcAttr tx
		// and retry on the next, rather than crashing the sequencer.
		return nil, fmt.Errorf("unable to get the EVM block that lightweight TBC's state represents "+
			"while trying to generate a Bitcoin Attributes Deposited transaction for the next block after "+
			"%s @ %d: %w", lastTip.Hash().String(), lastTip.Number.Uint64(), err)
	}
	if currentTbcEvmTip != nil {
		if currentTbcEvmTip.Hash().Cmp(lastTip.Hash()) != 0 {
			log.Error(fmt.Sprintf("When attempting to generate a Bitcoin Attributes Deposited transaction "+
				"for the next block after %s @ %d, lightweight TBC represents an incorrect EVM state of %s @ %d",
				lastTip.Hash().String(), lastTip.Number.Uint64(), currentTbcEvmTip.Hash().String(),
				currentTbcEvmTip.Number.Uint64()))

			// Attempting to generate Bitcoin Attributes Deposited transaction for the block after current tip
			// but lightweight TBC's state isn't at the current tip, move it here manually
			err := bc.updateHvmHeaderConsensus(lastTip, false)
			if err != nil {
				// The lightweight TBC was already at the wrong EVM state on entry (that is why
				// we are here); a failed recovery move leaves it in an indeterminate state that
				// the next call's same sanity check (above) will detect and re-attempt to repair.
				// Return so the sequencer skips this block's BtcAttr tx and retries, instead of
				// crashing on this *returned* error.
				//
				// updateHvmHeaderConsensus may still terminate via log.Crit on a should-never-happen
				// internal condition before it returns an error here, so this recovery branch only converts
				// the returned error. Reaching this branch at
				// all requires the lightweight TBC to already be at the wrong EVM tip relative to the
				// canonical head, which the steady-state build path avoids (each head promotion re-syncs
				// the lightweight view); it is only transiently reachable on recovery/import paths.
				return nil, fmt.Errorf("when attempting to generate a Bitcoin Attributes Deposited transaction "+
					"for the next block after %s @ %d, lightweight TBC represented an incorrect EVM state of %s @ %d "+
					"and an error occurred trying to move its EVM state: %w",
					lastTip.Hash().String(), lastTip.Number.Uint64(), currentTbcEvmTip.Hash().String(),
					currentTbcEvmTip.Number.Uint64(), err)
			}
		} else {
			log.Info(fmt.Sprintf("Lightweight TBC correctly represents block %s @ %d when attempting to "+
				"generate a Bitcoin Attributes Deposited transaction for the next block",
				currentTbcEvmTip.Hash().String(), currentTbcEvmTip.Number.Uint64()))
		}
	} else {
		log.Info(fmt.Sprintf("The EVM block corresponding to lightweight TBC's current state is nil, "+
			"which should indicate that the next block after %s @ %d at time %d is the hVM Phase 0 "+
			"activation block", lastTip.Hash().String(), lastTip.Number.Uint64(), timestamp))
	}

	originalTbcUpstreamId, err := bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
	if err != nil {
		// Read-only lookup; no lightweight-TBC mutation yet. Skip and retry next block.
		return nil, fmt.Errorf("unable to get the upstream state id from TBC when creating the Bitcoin "+
			"Attributes Deposited transaction for the block after %s @ %d: %w", lastTip.Hash().String(),
			lastTip.Number.Uint64(), err)
	}

	// Get current tips known by our lightweight and full TBC nodes
	lightTipHeight, lightTipHeader, err := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
	if err != nil {
		// Read-only lookup; no lightweight-TBC mutation yet. Skip and retry next block.
		return nil, fmt.Errorf("unable to get the best block header from lightweight TBC node when attempting "+
			"to calculate the Bitcoin Attributes Deposited transaction for next block after %s @ %d: %w",
			lastTip.Hash().String(), lastTip.Number.Uint64(), err)
	}
	lightTipHash := lightTipHeader.BlockHash()

	fullTipHeight, fullTipHeader, err := vm.TBCFullNode.BlockHeaderBest(bc.ctx)
	if err != nil {
		// Read-only lookup; no lightweight-TBC mutation yet. Skip and retry next block.
		return nil, fmt.Errorf("unable to get the best block header from TBC full node when attempting "+
			"to calculate the Bitcoin Attributes Deposited transaction for next block after %s @ %d: %w",
			lastTip.Hash().String(), lastTip.Number.Uint64(), err)
	}
	fullTipHash := fullTipHeader.BlockHash()

	// Build cache (BTC-view-aware). The cached BtcAttr is valid only while the EVM tip and both BTC tips
	// are unchanged (see btcAttrCacheKey). The reads above are cheap; the sanity check is read-only on a
	// hit but may have repaired a desynced lightweight view, in which case lightTipHash already reflects
	// the repaired view. The expensive work the cache saves is the walk-back + add/revert dry-run below.
	// Keying on the BTC tips (not the EVM tip alone) is what de-pins the permanent sequencer halt: a
	// full-node sync/reorg now forces a rebuild instead of re-serving a stale tx. Block availability is not
	// a key dimension: the fully-blocked case (no header available, i==0) returns errHvmBtcAttrPendingBlocked
	// without caching, so it is re-attempted. The partially-blocked case (availability truncates to a
	// non-empty prefix at i>0) does cache the truncated tx, but that is bounded and self-correcting: the
	// under-advance lasts only until the next L2 block promotes the EVM tip (new evmTip => cache miss =>
	// rebuild that re-checks availability), so a late-arriving full block is picked up on the next build.
	curCacheKey := btcAttrCacheKey{evmTip: lastTipHash, lightTip: lightTipHash, fullTip: fullTipHash}
	if cached := bc.cachedBtcAttrFor(curCacheKey); cached != nil {
		return cached, nil
	}

	// Check whether the TBC Full Node has new header information compared to lightweight TBC node.
	// Note this is looking at what block headers the TBC full node knows about, so is unrelated to
	// where the full node is indexed to.
	if bytes.Equal(lightTipHash[:], fullTipHash[:]) {
		log.Info(fmt.Sprintf("lightTipHash %s == fullTipHash %s, not generating Bitcoin Attributes Deposited "+
			"transaction", lightTipHash.String(), fullTipHash.String()))
		// Both TBC nodes have same consensus tip, nothing to do
		return nil, nil
	}

	// Tips are different - determine whether the lightweight tip is a direct ancestor.
	// Note: we aren't using existing methods for finding common ancestor, because there is an
	// edge case where lightweight consensus could know about a block header on a fork
	// which the TBC full node is not aware of, so in the event of a fork we need to walk
	// back each tip from their respective data source. This edge case could happen either
	// in a benign way when there is a Bitcoin reorg and our TBC full node only heard about
	// the canonical chain from peers, or if a malicious Sequencer intentionally privately
	// mined a Bitcoin block and included the header in a Bitcoin Attributes Deposited tx
	// in an attempt to cause an error in the hVM state transition.
	lightCursorHeader := lightTipHeader
	lightCursorHeight := lightTipHeight
	lightCursorHash := lightTipHeader.BlockHash()

	fullCursorHeader := fullTipHeader
	fullCursorHeight := fullTipHeight
	fullCursorHash := fullTipHeader.BlockHash()

	log.Info(fmt.Sprintf("Generating Bitcoin Attributes Deposited transaction for the next block after "+
		"%s @ %d, lightweight TBC node consensus tip is %s @ %d, full TBC node consensus tip is %s @ %d",
		lastTip.Hash().String(), lastTip.Number.Uint64(), lightCursorHash.String(), lightCursorHeight,
		fullCursorHash.String(), fullCursorHeight))

	// Walk back the light cursor until we get to the same height if it's ahead
	for lightCursorHeight > fullCursorHeight {
		// Get height even though we could calculate it as a sanity check
		header, height, err := bc.tbcHeaderNode.BlockHeaderByHash(bc.ctx, lightCursorHeader.PrevBlock)
		if err != nil {
			// Should never happen, implies lightweight TBC has a header before its current canonical
			// tip which it is unable to return, probably signals corruption. This walk-back is read-only
			// (no lightweight-TBC mutation), so we return and let the sequencer skip this block's BtcAttr
			// tx rather than crash. If such corruption were persistent the hVM Bitcoin view would stop
			// advancing while the L2 keeps producing blocks; the GetBitcoinAttributesForNextBlock wrapper
			// records hvmBtcAttrFailMeter / hvmBtcAttrFailingGauge as an alertable signal.
			// TODO: Lightweight TBC recovery from genesis
			return nil, fmt.Errorf("unable to get header %x @ %d from lightweight TBC node when walking "+
				"backwards from %x @ %d: %w", lightCursorHeader.PrevBlock[:], lightCursorHeight-1,
				lightCursorHash[:], lightCursorHeight, err)
		}
		if height != lightCursorHeight-1 {
			// Should never happen, means lightweight TBC node is returning bad heights
			return nil, fmt.Errorf("lightweight TBC node returned an incorrect height for block %x: "+
				"expected %d but got %d", lightCursorHeader.PrevBlock[:], lightCursorHeight-1, height)
		}
		lightCursorHeader = header
		lightCursorHeight = height // same as lightCursorHeight - 1
		lightCursorHash = lightCursorHeader.BlockHash()
	}
	// Walk back the full cursor until we get to the same height if it's ahead
	for fullCursorHeight > lightCursorHeight {
		// Get height even though we could calculate it as a sanity check
		header, height, err := vm.TBCFullNode.BlockHeaderByHash(bc.ctx, fullCursorHeader.PrevBlock)
		if err != nil {
			// Should never happen, implies full TBC node has a header before its current
			// canonical tip which it is unable to return, probably signals corruption.
			// Read-only walk-back; return and skip this block's BtcAttr tx rather than crash.
			// TODO: Full TBC node recovery?
			return nil, fmt.Errorf("unable to get header %x @ %d from full TBC node when walking "+
				"backwards from %x @ %d: %w", fullCursorHeader.PrevBlock[:], fullCursorHeight-1,
				fullCursorHash[:], fullCursorHeight, err)
		}
		if height != fullCursorHeight-1 {
			// Should never happen, means full TBC node is returning bad heights
			return nil, fmt.Errorf("full TBC node returned an incorrect height for block %x: "+
				"expected %d but got %d", fullCursorHeader.PrevBlock[:], fullCursorHeight-1, height)
		}
		fullCursorHeader = header
		fullCursorHeight = height // same as fullCursorHeight - 1
		fullCursorHash = fullCursorHeader.BlockHash()
	}

	// Whether or not lightweight and full TBC nodes are on the same chain, find their common ancestor
	// (the same as one of the node's tips if they are on the same chain) so the walk-back logic runs once
	// rather than separately for the different forking scenarios.
	var commonAncestorHash chainhash.Hash

	// Now the cursors for the lightweight and full node chains are at the same height.
	// If both cursors match, both chains' current tips are on the same chain.
	if bytes.Equal(fullCursorHash[:], lightCursorHash[:]) {
		// They match, so they are on the same chain.
		if lightTipHeight > fullTipHeight {
			// Lightweight TBC has consensus ahead of full tip, on same chain, so nothing to do. We did
			// not check this until both cursors were at the lowest height of either tip, because of an
			// edge case where the lightweight tip could have been advanced onto a fork higher than the
			// canonical block known by the full node, while the full node still has one or more canonical
			// headers that should be communicated to the lightweight view.
			return nil, nil
		} else {
			// Full TBC node has consensus ahead of lightweight tip on the
			// same chain, so we just need to provide the new headers between
			// lightweight TBC's tip and full TBC node's tip.
			commonAncestorHash = lightTipHash
			// Walk backwards from full TBC node's tip, adding all headers
			// until we get to this common ancestor.
			// We walk backwards from a known tip instead of advancing
			// by index even though we know the tip we are walking towards
			// is canonical to avoid an edge-case where the TBC full node
			// could experience a reorg deeper than the common ancestor
			// which would cause us to return headers which may not connect
			// to the ancestor we know the lightweight TBC node will be able
			// to progress on.
		}
	} else {
		// Lightweight tip isn't the common ancestor, meaning the two nodes
		// are on different chains. Need to continue walking both back
		// until we do find a common ancestor.
		// TODO: way to dedup this code with the previous walk-back to equal height,
		// could move to a walkback function where caller can specify whether height
		// or hash is used as exit condition and return all final cursors?
		for !bytes.Equal(fullCursorHash[:], lightCursorHash[:]) {
			lHeader, lHeight, err := bc.tbcHeaderNode.BlockHeaderByHash(bc.ctx, lightCursorHeader.PrevBlock)
			if err != nil {
				// Should never happen, implies lightweight TBC has a header before its current
				// canonical tip which it is unable to return, probably signals corruption.
				// Read-only walk-back; return and skip this block's BtcAttr tx rather than crash.
				// TODO: Lightweight TBC recovery from genesis
				return nil, fmt.Errorf("unable to get header %x @ %d from lightweight TBC node when walking "+
					"backwards from %x @ %d: %w", lightCursorHeader.PrevBlock[:], lightCursorHeight-1,
					lightCursorHash[:], lightCursorHeight, err)
			}
			if lHeight != lightCursorHeight-1 {
				// Should never happen, means lightweight TBC node is returning bad heights
				return nil, fmt.Errorf("lightweight TBC node returned an incorrect height for block %x: "+
					"expected %d but got %d", lightCursorHeader.PrevBlock[:], lightCursorHeight-1, lHeight)
			}

			fHeader, fHeight, err := vm.TBCFullNode.BlockHeaderByHash(bc.ctx, fullCursorHeader.PrevBlock)
			if err != nil {
				// Should never happen, implies full TBC node has a header before its current
				// canonical tip which it is unable to return, probably signals corruption.
				// Read-only walk-back; return and skip this block's BtcAttr tx rather than crash.
				// TODO: Full TBC node recovery?
				return nil, fmt.Errorf("unable to get header %x @ %d from full TBC node when walking "+
					"backwards from %x @ %d: %w", fullCursorHeader.PrevBlock[:], fullCursorHeight-1,
					fullCursorHash[:], fullCursorHeight, err)
			}
			if fHeight != fullCursorHeight-1 {
				// Should never happen, means full TBC node is returning bad heights
				return nil, fmt.Errorf("full TBC node returned an incorrect height for block %x: "+
					"expected %d but got %d", fullCursorHeader.PrevBlock[:], fullCursorHeight-1, fHeight)
			}

			lightCursorHeader = lHeader
			lightCursorHeight = lHeight
			lightCursorHash = lHeader.BlockHash()

			fullCursorHeader = fHeader
			fullCursorHeight = fHeight
			fullCursorHash = fHeader.BlockHash()
		}
		commonAncestorHash = fullCursorHash
	}

	// Whether or not the light and full TBC nodes are on the same chain, we
	// have their common ancestor so any headers from the TBC full node which
	// connect to this ancestor are guaranteed to fit onto lightweight TBC's
	// current knowledge.
	commonAncestorHeight := fullCursorHeight // Both former cursors are ancestor now

	log.Info(fmt.Sprintf("When generating the Bitcoin Attributes Deposited transaction for the next block "+
		"after %s @ %d, the common ancestor between lightweight TBC tip %x @ %d and full node TBC tip %x @ %d is "+
		"%x @ %d", lastTip.Hash().String(), lastTip.Number.Uint64(), lightTipHash[:], lightTipHeight,
		fullTipHash[:], fullTipHeight, commonAncestorHash[:], commonAncestorHeight))

	// # of headers will always be the full tip minus the height of the common ancestor
	var headersToTip []wire.BlockHeader
	cursorHeight := fullTipHeight
	cursorHeader := fullTipHeader
	cursorHash := fullTipHash

	// Loop until cursor's hash matches the common ancestor
	for !bytes.Equal(commonAncestorHash[:], cursorHash[:]) {
		headersToTip = append(headersToTip, *cursorHeader)
		tHeader, tHeight, err := vm.TBCFullNode.BlockHeaderByHash(bc.ctx, cursorHeader.PrevBlock)
		if err != nil {
			// Should never happen, implies full TBC node has a header before its current
			// canonical tip which it is unable to return, probably signals corruption.
			// Read-only walk-back; return and skip this block's BtcAttr tx rather than crash.
			// TODO: Full TBC node recovery?
			return nil, fmt.Errorf("unable to get header %x @ %d from full TBC node when walking "+
				"backwards from %x @ %d: %w", cursorHeader.PrevBlock[:], cursorHeight-1,
				cursorHash[:], cursorHeight, err)
		}
		if tHeight != cursorHeight-1 {
			// Should never happen, means full TBC node is returning bad heights
			return nil, fmt.Errorf("full TBC node returned an incorrect height for block %x: "+
				"expected %d but got %d", cursorHeader.PrevBlock[:], cursorHeight-1, tHeight)
		}
		cursorHeader = tHeader
		cursorHeight = tHeight
		cursorHash = tHeader.BlockHash()
	}

	if headersToTip == nil || len(headersToTip) == 0 {
		// Sanity check just in case, this should never happen because the only way this array
		// is empty should be if lightweight and full node tips are the same
		log.Error(fmt.Sprintf("When generating Bitcoin Attributes Deposited transaction for block after "+
			"%s @ %d got past checks for whether any new headers are available from TBC full node that should be "+
			"communicated to TBC light mode, but did not find any headers to add. Common ancestor: %x",
			lastTip.Hash().String(), lastTip.Number.Uint64(), commonAncestorHash[:]))
		// We already established the tips differ (pending work), so producing no headers here is
		// an anomaly, not an idle cycle — surface it as a stuck signal rather than "healthy".
		return nil, errHvmBtcAttrPendingBlocked
	}

	var headersToAdd []wire.BlockHeader
	// Check that none of the headers we are going to add are already known by lightweight TBC. This is
	// possible in an edge case where we are communicating a reorg, as lightweight TBC could know some
	// blocks on the fork since the common ancestor which we did not yet check for. Note headersToTip is
	// in reverse order, so this loop visits headers in ascending (ancestor->tip) order.
	//
	// Contiguity guarantee (keeps the kept AddExternalHeaders fail-stop unreachable on clean input): TBC
	// cannot hold a header without its parent, so the set of headers the lightweight node already knows
	// along this single ancestor->tip chain is downward-closed (a prefix). Dropping a prefix from an
	// ascending contiguous chain leaves a contiguous suffix, so headersToAdd is always contiguous. The
	// contiguity check that would otherwise reject a gap runs at the header store's service layer, not the
	// underlying DB write, so this invariant must be guaranteed here rather than relied upon downstream.
	// The NotFound discrimination below preserves it.
	for index := len(headersToTip) - 1; index >= 0; index-- {
		headerToAdd := headersToTip[index]
		headerToAddHash := headerToAdd.BlockHash()
		_, _, err := bc.tbcHeaderNode.BlockHeaderByHash(bc.ctx, headerToAddHash)
		if err != nil {
			// Only a genuine "not found" means lightweight TBC does not already know this header (so it
			// must be added). Discriminate it from a real backend/I/O error via errors.As against
			// database.NotFoundError: the header store's lookup returns the NotFoundError
			// unwrapped on a miss, and the store wrapper adds only a "db block header by hash: %w"
			// wrap, which errors.As traverses (the sibling "block header get: %w" string is the leveldb
			// I/O-error path, intentionally not a NotFoundError, so it does not match here).
			//
			// This matters: treating a transient read failure as "not found" and appending an
			// already-known interior header would make headersToAdd non-contiguous; the AddExternalHeaders
			// service wrapper's contiguity check then rejects it, hitting the deliberately-kept fail-stop
			// log.Crit and crashing the sequencer over a transient read (or, past it, the DB-layer insert
			// would write wrong heights). This loop is still read-only (no lightweight-TBC mutation), so on
			// any non-not-found error we skip this block's BtcAttr tx and retry next block.
			var notFound database.NotFoundError
			if errors.As(err, &notFound) {
				headersToAdd = append(headersToAdd, headerToAdd)
			} else {
				return nil, fmt.Errorf("unable to check whether lightweight TBC already knows header %s "+
					"while generating the Bitcoin Attributes Deposited transaction for the block after %s @ %d: %w",
					headerToAddHash.String(), lastTip.Hash().String(), lastTip.Number.Uint64(), err)
			}
		}
	}

	// It's possible that all headers were already known by lightweight TBC if it is
	// fully aware of the alternate chain in a chain-split scenario.
	if len(headersToAdd) == 0 {
		log.Info("No headers to add found!")
		return nil, nil
	}

	// Trim headersToAdd to the maximum number of headers we are allowed to include.
	// if len(headersToAdd) > types.MaximumBtcHeadersInTx {
	// 	headersToAdd = headersToAdd[0:types.MaximumBtcHeadersInTx]
	// }
	if len(headersToAdd) > 8 {
		headersToAdd = headersToAdd[0:8]
	}
	log.Info(fmt.Sprintf("Headers to add while generating Bitcoin Attributes Deposited transaction: %x", headersToAdd))

	// Walk up headersToAdd, and truncate blocks that TBC Full Node does not have complete information for
	for i := 0; i < len(headersToAdd); i++ {
		hashToCheck := headersToAdd[i].BlockHash()
		headerAvailable, err := vm.TBCFullNode.FullBlockAvailable(bc.ctx, hashToCheck)
		if err != nil {
			// A backend/I-O fault while determining availability is a genuine failure, distinct
			// from a full block that is simply not downloaded yet (handled below as a
			// non-advancing "blocked" round). Return it as a real error so it is counted on the
			// fail meter like every other backend read in this function, consistent rather than
			// being silently downgraded to "not available". Still read-only here, so the
			// sequencer just skips this block's BtcAttr tx and retries.
			return nil, fmt.Errorf("TBC full node was unable to determine whether the full block for hash %s "+
				"is available while generating the Bitcoin Attributes Deposited transaction for the block after "+
				"%s @ %d: %w", hashToCheck.String(), lastTip.Hash().String(), lastTip.Number.Uint64(), err)
		}

		if !headerAvailable {
			log.Warn(fmt.Sprintf("TBC does not have full block available for %s!", hashToCheck.String()))
			vm.TBCAttemptBlockRefetch(bc.ctx, &headersToAdd[i])

			// Header is not available; if this is the first block then return nothing, otherwise truncate
			if i == 0 {
				// No blocks to add this round: the full node has the consensus header but not yet
				// the full block for it (a refetch was just kicked off). The tips differ, so this
				// is pending work that did not advance — surface it as a stuck signal (the wrapper
				// hides the sentinel and the caller still builds a valid block without the tx).
				return nil, errHvmBtcAttrPendingBlocked
			} else {
				log.Info(fmt.Sprintf("Generating Bitcoin Attributes Deposited transaction for the next block "+
					"after %s @ %d, and TBC Full Node does not have the full block for %s, so removing from headers "+
					"to add to hVM's lightweight view", lastTip.Hash().String(), lastTip.Number.Uint64(),
					hashToCheck.String()))

				headersToAdd = headersToAdd[0:i]
				break
			}
		}
	}

	// Contextual-difficulty (sequencer build path — liveness). Before the dry-run AddExternalHeaders below mutates the
	// shared lightweight view, validate the candidate headers with the same floor-aware
	// contextual-difficulty validator the consensus apply path runs, and truncate to the longest prefix
	// the apply path will accept. This keeps the sequencer from packaging a header the apply path would
	// reject (which would leave the BTC view unable to advance); truncating advances the view by the
	// acceptable prefix instead. Build-path only, changes nothing about consensus: every validator
	// re-derives the BtcAttr independently and the apply path remains the enforcement point.
	headerPtrsForValidation := make([]*wire.BlockHeader, len(headersToAdd))
	for i := range headersToAdd {
		headerPtrsForValidation[i] = &headersToAdd[i]
	}
	validPrefix, skipBuild, verr := longestEnforceableBTCHeaderPrefix(headerPtrsForValidation, bc.enforceableBTCBatch)
	if skipBuild {
		// The validator collapses any read error into ErrBTCHeaderContextUnavailable, losing the underlying
		// identity. Defensive guard: if the chain's context has been cancelled, surface that (so
		// recordHvmBtcAttrResult classifies it as cancellation, not a backend fault). On a normal cmd/geth
		// shutdown bc.ctx is not cancelled (see the SnapSyncHvm note) and shutdown is caught instead by the
		// chainmu TryLock at the top of this function (errChainStopped), so this guard is not load-bearing
		// for cmd/geth today; it handles a parent-context cancellation (embeddings / tests) and future-proofs
		// the function if a future change wires Stop() to cancel bc.ctx.
		if ctxErr := bc.ctx.Err(); ctxErr != nil {
			return nil, ctxErr
		}
		// Otherwise a genuine transient/corrupt lightweight-TBC read; no mutation yet. Skip this block's
		// BtcAttr tx and retry next build (surfaced on the fail meter like the other read faults here).
		return nil, fmt.Errorf("contextual BTC-difficulty validation hit a transient/unreadable lightweight-TBC "+
			"error while generating the Bitcoin Attributes Deposited transaction for the block after %s @ %d: %w",
			lastTip.Hash().String(), lastTip.Number.Uint64(), verr)
	}
	if len(validPrefix) < len(headersToAdd) {
		// Distinguish a contextually-invalid header (this meter) from a benign undownloaded-block stall:
		// both otherwise surface only as the shared stuck gauge, leaving operators without a distinct signal.
		// A sustained rate here => the full node is feeding contextually-invalid BTC headers.
		hvmBtcAttrDiffTruncMeter.Mark(1)
		if len(validPrefix) == 0 {
			// The very next BTC header the full node wants to communicate is contextually invalid (a
			// forged-difficulty header the apply path would reject). We cannot advance the hVM Bitcoin
			// view this round; build a block without a BtcAttr tx and retry. The stuck gauge (via the
			// pending-blocked sentinel) plus the truncation meter above make a persistent forged-base
			// stall alertable and distinguishable from a benign availability stall.
			log.Warn(fmt.Sprintf("Generating Bitcoin Attributes Deposited transaction for the block after %s @ %d: "+
				"the next BTC header %s is contextually invalid under contextual-difficulty enforcement (wrong difficulty / median-time-past / "+
				"version); not advancing the hVM Bitcoin view this build", lastTip.Hash().String(),
				lastTip.Number.Uint64(), headersToAdd[0].BlockHash().String()))
			return nil, errHvmBtcAttrPendingBlocked
		}
		log.Warn(fmt.Sprintf("Generating Bitcoin Attributes Deposited transaction for the block after %s @ %d: "+
			"truncating %d candidate BTC headers to the %d-header prefix that passes contextual-difficulty "+
			"validation (first rejected header %s)", lastTip.Hash().String(), lastTip.Number.Uint64(),
			len(headersToAdd), len(validPrefix), headersToAdd[len(validPrefix)].BlockHash().String()))
		headersToAdd = headersToAdd[:len(validPrefix)]
	}

	// Serialize headers to bytes
	headersToAddSerialized, err := types.SerializeHeadersToArray(headersToAdd)
	if err != nil {
		// Pure serialization, before any lightweight-TBC mutation. Skip and retry next block.
		return nil, fmt.Errorf("unable to serialize Bitcoin headers to create Bitcoin Attributes Deposited "+
			"transaction for the block after %s @ %d: %w", lastTip.Hash().String(), lastTip.Number.Uint64(), err)
	}

	// Add the headers to lightweight TBC's view to make sure they are valid, and also to
	// determine the correct new canonical tip (which won't be the last header in this array
	// if we are adding knowledge to a fork that doesn't become canonical). That is possible
	// if there is a split tip or if we are handling a BTC reorg that is more than
	// MaximumBtcHeadersInTx deep and requires multiple Bitcoin Attributes Deposited transactions
	// to communicate enough headers for it to be considered canonical by our lightweight view.

	// Convert []wire.BlockHeader to []*wire.BlockHeader
	// TODO: Review this, should we use []*wire.BlockHeader the entire time to be consistent?
	headersToAddPtr := make([]*wire.BlockHeader, len(headersToAdd))
	for i := 0; i < len(headersToAdd); i++ {
		headersToAddPtr[i] = &headersToAdd[i]
	}

	msgHeaders := &wire.MsgHeaders{
		Headers: headersToAddPtr,
	}

	log.Info(fmt.Sprintf("[Bitcoin Attributes for Next Block] *ADDING* external BTC headers:"))
	for i := 0; i < len(msgHeaders.Headers); i++ {
		log.Info(fmt.Sprintf("\t %s", msgHeaders.Headers[i].BlockHash().String()))
	}
	// Contextual-difficulty: headersToAdd was validated and truncated above to the longest prefix the apply path accepts
	// under contextual-difficulty enforcement, so this dry-run add cannot package a self-invalidating
	// header. The dry-run add itself remains the cumulative-work / canonical-tip oracle; the contextual-difficulty check only
	// narrows which headers reach it.
	_, canonical, _, _, err := bc.tbcHeaderNode.AddExternalHeaders(
		bc.ctx,
		msgHeaders,
		hVMDummyUpstreamId[:])

	if err != nil {
		// Fail-stop (one of the two deliberate crits in this function). This is the dry-run mutation of
		// the shared lightweight TBC node. The underlying store write is not atomic: a failure during the
		// write/commit phase can leave the canonical tip advanced onto the dry-run headers while other
		// records are not — a partially-mutated, dirty lightweight view. We cannot distinguish that from a clean pre-write
		// rejection here, and on a graceful return we would never run RemoveExternalHeaders to restore it,
		// so every later block build would silently compute its BTC view from a corrupted tip and diverge
		// consensus. Crashing stops this process from building further on the dirty state. It does not by
		// itself clean up: the lightweight TBC persists to leveldb, so the partial write may survive a
		// restart; restart-time recovery is out of scope here.
		first := headersToAdd[0].BlockHash()
		last := headersToAdd[len(headersToAdd)-1].BlockHash()
		log.Crit(fmt.Sprintf("Unable to add %d external headers %x to %x to lightweight TBC view on top "+
			"of prior canonical tip %x @ %d!", len(headersToAdd), first[:], last[:], lightTipHash[:],
			lightTipHeight), "err", err)
	}

	log.Info(fmt.Sprintf("[Bitcoin Attributes for Next Block] *REMOVING* external BTC headers:"))
	for i := 0; i < len(msgHeaders.Headers); i++ {
		log.Info(fmt.Sprintf("\t %s", msgHeaders.Headers[i].BlockHash().String()))
	}

	// Revert lightweight TBC's view back to what it was before we started.
	rt, prevHeader, err := bc.tbcHeaderNode.RemoveExternalHeaders(bc.ctx, msgHeaders, lightTipHeader, originalTbcUpstreamId[:])
	if err != nil {
		// Fail-stop (the second of the two deliberate crits). AddExternalHeaders above already persisted
		// the dry-run headers. This is the revert; like the insert it commits across multiple independent
		// (non-atomic) store transactions, so a failure here can leave the
		// canonical tip and/or upstream state id only partially restored — a dirty lightweight view. We
		// have no clean way to retry, and returning would let every subsequent block build silently
		// compute its BTC view from a corrupted tip, diverging consensus. Crashing stops this process from
		// building on the dirty state. (Same caveat as the Add crit: the dirty leveldb may survive a
		// restart; restart-time recovery is out of scope.) Should never happen: Remove mirrors an Add that
		// just succeeded on the same headers.
		first := headersToAdd[0].BlockHash()
		last := headersToAdd[len(headersToAdd)-1].BlockHash()
		log.Crit(fmt.Sprintf("Unable to remove %d external headers %x to %x from lightweight TBC view after "+
			"they were temporarily added when creating the Bitcoin Attributes Deposited transaction for the block "+
			"after %s @ %d", len(headersToAdd), first[:], last[:], lastTip.Hash().String(),
			lastTip.Number.Uint64()), "err", err)
	}

	log.Info(fmt.Sprintf("Successfully removed %d block headers from lightweight TBC view after temporarily "+
		"adding them when generating the Bitcoin Attributes Deposited transaction for the block after %s @ %d. "+
		"RemoveType=%d, prevHeader=%x", len(*headersToAddSerialized), lastTip.Hash().String(), lastTip.Number.Uint64(),
		rt, prevHeader.Hash[:]))

	// No post-revert assertion here, by design. Asserting on the returned value (prevHeader) would be
	// wrong: RemoveExternalHeaders returns parentToRemovalSet (the parent of the first removed header),
	// which equals the original light tip only on the same-chain case — in a fork/reorg it is the common
	// ancestor — so `prevHeader.Hash == lightTipHash` would false-positive and crash on normal reorg
	// handling. A re-read via BlockHeaderBest() compared to lightTipHash would be correct (the canonical
	// tip is written unconditionally to tipAfterRemoval==lightTipHeader in all geometries) but is
	// redundant: a nil error from RemoveExternalHeaders already implies its canonical-tip commit landed,
	// and the emitted tx uses `canonical` from AddExternalHeaders, not the post-revert state.
	canonHashAfterDepTx := canonical.BlockHash()
	btcAttrDepTx, err := types.MakeBtcAttributesDepositedTx(canonHashAfterDepTx, headersToAdd)
	if err != nil {
		// The lightweight TBC view has already been reverted to its original state above, so
		// returning here leaves no dirty state. Skip this block's BtcAttr tx and retry next block.
		return nil, fmt.Errorf("unable to construct a Bitcoin Attributes Deposited tx containing %d headers "+
			"with canonical hash %x for placement in the block after %s @ %d: %w", len(headersToAdd),
			canonHashAfterDepTx[:], lastTip.Hash().String(), lastTip.Number.Uint64(), err)
	}

	// Store the calculated Bitcoin Attributes Deposited transaction so we don't recalculate it on
	// subsequent calls — keyed on the EVM tip and both BTC views (curCacheKey), so any BTC-view change
	// invalidates it. lightTipHash/fullTipHash are the pre-build values read above and are unchanged here
	// (the dry-run add was reverted), so they correctly identify the view this tx extends.
	bc.storeBtcAttrCache(curCacheKey, btcAttrDepTx)

	return btcAttrDepTx, nil
}

// headersBetweenBlocks returns an array of headers from ancestor (inclusive) to head (inclusive).
// This function requires that ancestor is an ancestor of head; if the ancestor cannot be found by
// walking backwards from the head an error will be thrown.
// This function does not depend on canonical indexes, so it can safely be used to find the route
// to walk forward from an ancestor to its descendant whether or not some or all of the headers
// on the route are canonical, as long as all of the block headers exist in the database.
// Headers are returned in ascending order: [ancestor, ..., head]
func (bc *BlockChain) headersBetweenBlocks(ancestor *types.Header, head *types.Header) ([]*types.Header, error) {
	if ancestor == nil {
		return nil, fmt.Errorf("headersBetweenBlocks called with nil ancestor")
	}
	if head == nil {
		return nil, fmt.Errorf("headersBetweenBlocks called with nil head")
	}

	headIndex := head.Number.Uint64()
	ancestorIndex := ancestor.Number.Uint64()
	path := make([]*types.Header, headIndex-ancestorIndex+1)

	cursor := head
	path[headIndex-ancestorIndex] = cursor
	for index := int32(headIndex - ancestorIndex - 1); index >= 0; index-- {
		// Don't overwrite cursor so we can print error correctly
		cursorTmp := bc.getHeaderFromDiskOrHoldingPen(cursor.ParentHash)
		if cursorTmp == nil {
			return nil, fmt.Errorf("headersBetweenBlocks could not retrieve header %s @ %d",
				cursor.ParentHash.String(), cursor.Number.Uint64()-1)
		}
		path[index] = cursorTmp
		cursor = cursorTmp
	}

	return path, nil
}

func (bc *BlockChain) walkHvmHeaderConsensusForward(currentHead *types.Header, newHead *types.Header) error {
	// Can't walk forwards from a block that is the same height or higher than the destination
	if currentHead.Number.Uint64() >= newHead.Number.Uint64() {
		return fmt.Errorf("Cannot walk hVM consensus forewards from "+
			"%s @ %d to %s @ %d - bad geometry", currentHead.Hash().String(), currentHead.Number.Uint64(),
			newHead.Hash().String(), newHead.Number.Uint64())
	}

	// It may be unsafe to walk forwards by number in case this method is called
	// before the appropriate canonical chain is fully updated in the database
	// (meaning walking forward could return blocks that aren't between the
	// current and new head), so walk backwards from newHead until we get to
	// currentHead, and then walk forwards through the list.
	headers, err := bc.headersBetweenBlocks(currentHead, newHead)
	if err != nil {
		// Critical error, this indicates that a path between the block responsible
		// for hVM's latest state update and the new head we are setting cannot
		// be found.
		// TODO: Attempt to recover hVM state from genesis
		return fmt.Errorf("unable to find a path between hVM's latest state update block %s @ %d and "+
			"the new head %s @ %d", currentHead.Hash().String(), currentHead.Number.Uint64(),
			newHead.Hash().String(), newHead.Number.Uint64())
	}

	// Start at 1 to skip the currentHead which has been processed previously
	for index := 1; index < len(headers); index++ {
		err := bc.applyHvmHeaderConsensusUpdate(headers[index], true, true)
		if err != nil {
			if errors.Is(err, consensus.ErrInvalidHVMBlockFormat) || errors.Is(err, consensus.ErrInvalidHVMHeaders) {
				// Something is wrong with the block, report it as invalid
				badBlock := bc.getBlockFromDiskOrHoldingPen(headers[index].Hash())
				bc.reportBlock(badBlock, nil, err)
				for backIndex := index - 1; backIndex >= 1; backIndex-- {
					// Walk backwards to restore state to where it was originally. Unapply the
					// already-applied predecessor at backIndex, not the failing block headers[index]: the
					// failed apply committed no TBC state (every ErrInvalidHVMHeaders/ErrInvalidHVMBlockFormat
					// return path above leaves the upstream state id at the parent, and the
					// canonical-tip-mismatch path even removes the headers it added), so headers[index]
					// itself must not be unwound. Only the successfully-applied headers[index-1]..headers[1]
					// are rolled back, in reverse order (mirroring walkHvmHeaderConsensusBack). Unwinding the
					// constant headers[index] each iteration instead would repeatedly "unapply" the failed
					// block while leaving the real predecessors applied, corrupting the lightweight view.
					// headers[0] is currentHead (applied by a previous call) and is preserved by
					// backIndex >= 1.
					err := bc.unapplyHvmHeaderConsensusUpdate(headers[backIndex])
					if err != nil {
						if errors.Is(err, consensus.ErrCorruptHVMHeaderOnlyModeState) {
							// A torn-store condition surfaced mid-rollback (an orphaned block/header body).
							// Route it to recovery instead of halting, mirroring walkHvmHeaderConsensusBack
							// and the updateHvmHeaderConsensus dispatch: the caller rebuilds the lightweight
							// view from genesis, which supersedes this partial rollback. Effectively
							// unreachable on honest data (these predecessors were just applied in this same
							// call, so their bodies are present), but kept consistent for defense-in-depth.
							return err
						}
						// Unable to walk consensus updates we just performed backwards, critical
						log.Crit(fmt.Sprintf("Unable to undo hVM consensus updates when an error was encountered "+
							"walking from %s @ %d to %s @ %d and block %s @ %d was deemed invalid",
							currentHead.Hash().String(), currentHead.Number.Uint64(), newHead.Hash().String(),
							newHead.Number.Uint64(), badBlock.Hash().String(), badBlock.Number().Uint64()),
							"err", err)
					}
				}
				// Return the original error
				return err
			} else if errors.Is(err, consensus.ErrCorruptHVMHeaderOnlyModeState) {
				return err
			} else {
				// Unhandled error, for now exit on critical
				log.Crit(fmt.Sprintf("Unhandled error occurred while walking hVM consensus forward from "+
					"%s @ %d to %s @ %d, the hVM state transition for block %s @ %d could not be handled",
					currentHead.Hash().String(), currentHead.Number.Uint64(), newHead.Hash().String(),
					newHead.Number.Uint64(), headers[index].Hash().String(), headers[index].Number.Uint64()), "err", err)
			}
			// Impossible to reach this, but placeholder to ensure error gets returned if logic for unhandled errors
			// is modified.
			return err
		}
	}

	return nil
}

func (bc *BlockChain) walkHvmHeaderConsensusBack(currentHead *types.Header, newHead *types.Header) error {
	// Can't walk backwards from a block that is the same height or lower than the destination
	if currentHead.Number.Uint64() <= newHead.Number.Uint64() {
		log.Error(fmt.Sprintf("Cannot walk hVM consensus backwards from "+
			"%s @ %d to %s @ %d - bad geometry", currentHead.Hash().String(), currentHead.Number.Uint64(),
			newHead.Hash().String(), newHead.Number.Uint64()))
		return consensus.ErrBadTraversalGeometry
	}

	log.Info(fmt.Sprintf("walkHvmHeaderConsensusBack called to walk backwards from %s @ %d to %s @ %d",
		currentHead.Hash().String(), currentHead.Number.Uint64(), newHead.Hash().String(), newHead.Number.Uint64()))

	cursor := currentHead
	// Loop walking back the cursor until the cursor points to the newHead, since
	// newHead is the ancestor and once we unapply the hVM state transition from
	// newHead's direct child TBC's state will be reverted to the appropriate state.
	for cursor.Hash().Cmp(newHead.Hash()) != 0 {
		if cursor.Number.Uint64() == newHead.Number.Uint64() {
			// Should be impossible, this indicates that newHead is not actually
			// a direct ancestor of currentHead and our common ancestor is incorrect
			log.Error(fmt.Sprintf("walking backwards from block %s @ %d, reached block %s @ %d but "+
				"was expecting the block at index %d to be %s which is the new head we are unwinding to",
				currentHead.Hash().String(), currentHead.Number.Uint64(), cursor.Hash().String(),
				cursor.Number.Uint64(), cursor.Number.Uint64(), newHead.Hash().String()))
			return consensus.ErrBadTraversalGeometry
		}

		err := bc.unapplyHvmHeaderConsensusUpdate(cursor)
		if err != nil {
			// If we are unable to apply a previously-applied consensus update, this is critical unless
			// due to a data corruption issue which can be recovered from
			if errors.Is(err, consensus.ErrCorruptHVMHeaderOnlyModeState) {
				return err
			} else {
				log.Crit(fmt.Sprintf("Unable to unapply the hVM header %s @ %d",
					cursor.Hash().String(), cursor.Number.Uint64()), "err", err)
			}
		}
		newCursor := bc.getHeaderFromDiskOrHoldingPen(cursor.ParentHash)
		if newCursor == nil {
			// The ancestor header should have existed (it was already applied), so its absence is a torn-store
			// condition (a rewind/deep-reorg orphaned it), not a bad block. Mirror the orphaned-store guards
			// elsewhere in this file and return the recoverable sentinel so the caller rebuilds from genesis
			// via recoverReapplyHvmState rather than halting the process; effectively unreachable on honest
			// data with intact bodies, and every node would hit it identically (no fleet split).
			log.Error(fmt.Sprintf("header for block %s @ %d to walk hVM consensus back is nil; treating as corrupt hVM state",
				cursor.ParentHash.String(), cursor.Number.Uint64()-1))
			return consensus.ErrCorruptHVMHeaderOnlyModeState
		}
		cursor = newCursor
	}

	// We expect hVM to have an upstream state id corresponding to newHead, sanity check it
	upstreamStateId, err := bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
	if err != nil {
		return err
	}
	if !bytes.Equal(upstreamStateId[:], newHead.Hash().Bytes()[:]) {
		// If we didn't get an error but the upstream state ID is not what we expect, exit as there is
		// likely a code bug (rather than a data corruption issue that could be repaired).
		log.Crit(fmt.Sprintf("after walking backwards from block %s @ %d to %s @ %d, expected TBC "+
			"upstream state id to be %s but got %x instead", currentHead.Hash().String(), currentHead.Number.Uint64(),
			newHead.Hash().String(), newHead.Number.Uint64(), newHead.Hash().String(), upstreamStateId[:]))
	}

	return nil
}

func (bc *BlockChain) calculateHvmIndexerTipLagTestnet3(cursorHeader *wire.BlockHeader, cursorHeight uint64, defaultTipLag uint64) (uint64, error) {
	lowDiffThreshold := blockchain.CalcWork(testnet3LowDiffThresholdForTipLag)

	tipDiff := blockchain.CalcWork(cursorHeader.Bits)
	if tipDiff.Cmp(lowDiffThreshold) <= 0 {
		tipTimestamp := cursorHeader.Timestamp.Unix()
		prevTipDiffLow := false
		var prevHeader *wire.BlockHeader
		if cursorHeight > bc.tbcHeaderNodeConfig.GenesisHeightOffset {
			// Grab previous block's difficulty.
			var err error
			prevHeader, _, err = bc.tbcHeaderNode.BlockHeaderByHash(bc.ctx, cursorHeader.PrevBlock)
			if err != nil {
				return 0, err
			}

			prevHeaderDiff := blockchain.CalcWork(prevHeader.Bits)
			if prevHeaderDiff.Cmp(lowDiffThreshold) <= 0 {
				prevTipDiffLow = true
			}
		}

		// If there are two blocks in a row with too low of a difficulty, set higher lag
		if prevTipDiffLow {
			// We are in a difficulty bomb scenario.
			// Generally we want to lag 100 blocks behind tip here to be safe against reorgs, but we don't
			// want to artificially index backwards before the start of the difficulty bomb, so walk backwards
			// in Bitcoin chain until we are either 100 blocks back, *or* we hit a block above the low
			// difficulty threshold.

			lookbackCursor := prevHeader

			// We are starting two blocks behind cursor (looking at previous-to-previous)
			// This is not based on the setting of hVMIndexerTipLag, but rather how far back we must be starting
			// in the walk-back to find the beginning of the difficulty bomb (if recent)
			effectiveHVMIndexerTipLag := defaultTipLag

			for lookback := int64(effectiveHVMIndexerTipLag); lookback <= 100; lookback++ {
				lookbackHeight := int64(cursorHeight) - lookback
				if lookbackHeight < 0 {
					// Can't look before the genesis block
					break
				}

				if lookbackHeight < int64(bc.tbcHeaderNodeConfig.GenesisHeightOffset) {
					log.Info(fmt.Sprintf("lookbackHeight of %d takes us lower than GenesisHeightOffset %d, "+
						"not looking further back", lookbackHeight, bc.tbcHeaderNodeConfig.GenesisHeightOffset))
					break
				}

				tempCursor, _, err := bc.tbcHeaderNode.BlockHeaderByHash(bc.ctx, lookbackCursor.PrevBlock)
				if err != nil {
					return 0, err
				}

				if tempCursor.Timestamp.Unix()+(3600*5) < tipTimestamp {
					// If we encounter a header with a timestamp more than 5 hours behind current tip (3600*5),
					// stop here to avoid overly long waits on false triggers of difficulty bomb
					// due to low mining difficulty or mining 1-diff blocks on 20-min interval as regular
					log.Info(fmt.Sprintf("while walking back during difficulty bomb, block %s has a timestamp "+
						"more than 5 hours in the past, breaking at lookback=%d", tempCursor.BlockHash().String(),
						lookback))
					break
				}

				tempDiff := blockchain.CalcWork(tempCursor.Bits)
				if tempDiff.Cmp(lowDiffThreshold) > 0 {
					// Walked back to a block whose difficulty is not below the threshold
					break
				} else {
					// cursor difficulty is still below threshold, keep going
					lookbackCursor = tempCursor
					effectiveHVMIndexerTipLag = uint64(lookback)
				}
			}

			// Should not be possible but additional sanity check
			if effectiveHVMIndexerTipLag < defaultTipLag {
				effectiveHVMIndexerTipLag = defaultTipLag
			}

			return effectiveHVMIndexerTipLag, nil
		} else {
			// This was just a single low-difficulty block which can be mined after 20 minutes of no regular-difficulty
			// blocks on testnet3 but does not indicate a difficulty bomb, so return the default tip lag
			return defaultTipLag, nil
		}
	} else {
		return defaultTipLag, nil
	}
}

// hvmIndexErrToConsensus maps the vm-local missing-header sentinel (core/vm cannot
// import consensus — import cycle) to the consensus.ErrFullTBCMissingBTCHeader the
// block-import path treats as a deferrable retry. Any other error (including nil) is
// returned unchanged, so genuine faults remain fail-stop.
func hvmIndexErrToConsensus(err error) error {
	if errors.Is(err, vm.ErrTBCMissingHeader) {
		return consensus.ErrFullTBCMissingBTCHeader
	}
	return err
}

// shouldWalkBackTipLag reports whether updateFullTBCToLightweight should walk the full-node cursor back `lag`
// BTC blocks from `cursorHeight`, or stay at the configured genesis offset. It returns true only when there
// are at least `lag` blocks above the genesis offset, i.e. cursorHeight > genesisOffset + lag. Phrased as an
// addition (not the subtraction cursorHeight - lag > genesisOffset, which underflows uint64 when
// cursorHeight < lag, e.g. right after the hVM Phase-0 transition on a near-zero-offset regtest network) so
// the boundary is overflow-safe and unit-testable.
func shouldWalkBackTipLag(cursorHeight, genesisOffset, lag uint64) bool {
	return cursorHeight > genesisOffset+lag
}

// Update TBC Full Node's indexing to represent lightweight view minus 2 BTC blocks (or more during testnet3 diff bomb)
func (bc *BlockChain) updateFullTBCToLightweight() error {
	lightTipHeight, lightTipHeader, err := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
	if err != nil {
		log.Error("Attempting to update the full TBC node's indexers based on the header-only TBC consensus "+
			"view of Bitcoin, but unable to get the best block from the lightweight TBC node", "err", err)
		// This likely indicates something is broken with the header-only TBC node which could be recovered
		return consensus.ErrCorruptHVMHeaderOnlyModeState
	}

	// if there was no error, but the tip hash is blank, no-op

	lightTipHash := lightTipHeader.BlockHash()

	cursorHeight, cursorHeader := lightTipHeight, lightTipHeader
	cursorHash := cursorHeader.BlockHash()

	effectiveHVMIndexerTipLag := uint64(hVMIndexerTipLag)
	if vm.TBCFullNodeConfig.Network == chaincfg.TestNet3Params.Name {
		// Special case to fix an issue with testnet3 difficulty bomb - when difficulty is low, give a longer tip lag
		log.Debug("Chain is testnet3, checking whether a difficulty bomb is ongoing and a longer effective " +
			"hVM indexer tip lag should be used")
		effectiveHVMIndexerTipLag, err = bc.calculateHvmIndexerTipLagTestnet3(cursorHeader, cursorHeight, effectiveHVMIndexerTipLag)
		if err != nil {
			log.Error("An unexpected error was encountered when attempting to determine whether a higher "+
				"hVM lag behind consensus tip should be used due to a difficulty bomb", "err", err)
			return err
		}

		if effectiveHVMIndexerTipLag != hVMIndexerTipLag {
			log.Info(fmt.Sprintf("Due to a difficulty bomb, hVM will be lagging %d blocks behind known "+
				"consensus tip", effectiveHVMIndexerTipLag))
		}
	}

	// walk back hVMIndexerTipLag blocks from tip
	// On initial init when we have less than hVMIndexerTipLag previous blocks (right after
	// hVM phase 0 transition), correct indexer behavior is to remain at the genesis-configured
	// height until walking backwards the specified number of lag blocks doesn't surpass
	// configured genesis.
	if shouldWalkBackTipLag(cursorHeight, bc.tbcHeaderNodeConfig.GenesisHeightOffset, effectiveHVMIndexerTipLag) {
		for i := uint64(0); i < effectiveHVMIndexerTipLag; i++ {
			head, height, err := bc.tbcHeaderNode.BlockHeaderByHash(bc.ctx, cursorHeader.PrevBlock)
			if err != nil {
				// Being unable to walk back through header-only TBC node's best block indicates data corruption
				// which could be solved by recovering the lightweight TBC node
				log.Error(fmt.Sprintf("an error occurred walking back Bitcoin headers from lightweight "+
					"TBC tip %s @ %d, unable to get header %s @ %d", lightTipHash.String(), lightTipHeight,
					cursorHeader.PrevBlock.String(), cursorHeight-1), "err", err)
				return consensus.ErrCorruptHVMHeaderOnlyModeState
			}

			cursorHeader, cursorHeight = head, height // Storing them temporarily for verbose logging
			cursorHash = cursorHeader.BlockHash()
		}
	}

	log.Info(fmt.Sprintf("After walking back from lightweight tip to determine full node indexer target, "+
		"cursorHeight=%d, cursorHeader=%s", cursorHeight, cursorHeader.BlockHash().String()))

	// Check that the TBC Full Node has sufficient chain knowledge to sync to this height.
	available, missingFullBlockHeaders, missingHeaderHash, err := vm.TBCBlocksAvailableToHeader(bc.ctx, cursorHeader)
	if err != nil {
		return err
	}

	if !available {
		log.Warn("Unable to update full TBC node to lightweight tip (minus effective lag) due to at least one missing block.")
		if missingHeaderHash != nil {
			// TBC Full Node does not even have knowledge of at least one header that is needed to update the Full TBC node
			// indexers. Op-geth should insert the missing header into the TBC full node so that the P2P fetcher can attempt
			// to re-fetch.
			log.Error(fmt.Sprintf("TBC missing block header for block: %s", missingHeaderHash))

			// A missing header hash indicates at least one missing tip block, need to determine how many blocks are actually
			// missing from full TBC compared to lightweight canonical

			// Only walk back a maximum of 100 blocks
			_, headerCursor, err := bc.tbcHeaderNode.BlockHeaderBest(bc.ctx)
			if err != nil || headerCursor == nil {
				log.Crit("Unable to fetch best header from TBC lightweight node!", "err", err)
			}

			headers := make([]*wire.BlockHeader, 0)

			for count := 0; count < 100; count++ {
				hash := headerCursor.BlockHash()
				header, _, err := vm.TBCFullNode.BlockHeaderByHash(bc.ctx, hash)
				if err != nil || header == nil {
					// Prepend so headers are in correct (ascending) order
					headers = append([]*wire.BlockHeader{headerCursor}, headers...)
					vm.TBCAttemptBlockRefetch(bc.ctx, headerCursor)
				}
				// Do NOT break when the full node already has this header: continue the back-walk so a NON-CONTIGUOUS
				// gap (a present block above a deeper absent one) is still re-injected/refetched, rather than stopping
				// at the first present block and missing the deeper hole. (In practice the full node's headers are
				// contiguous from genesis — BlockHeadersInsert enforces linkage — so present blocks are simply skipped
				// down to genesis; this is defensive against any future non-contiguous state. Bounded by the
				// 100-iteration cap and the genesis/PrevBlock-NotFound guard below.)
				headerCursor, _, err = bc.tbcHeaderNode.BlockHeaderByHash(bc.ctx, headerCursor.PrevBlock)
				if err != nil || headerCursor == nil {
					// Reached genesis (zero PrevBlock -> NotFound) or the lightweight node errored mid-walk (e.g. ctx
					// cancelled on shutdown). Stop here rather than letting the swallowed error leave headerCursor nil
					// and nil-deref headerCursor.BlockHash() on the next iteration.
					break
				}
			}

			msgHeaders := &wire.MsgHeaders{
				Headers: headers,
			}

			bc.setMissingProgressionBlocks(msgHeaders)

			// Best-effort injection so the full node's P2P fetcher can re-request the missing headers; log (don't fail)
			// if it errors, since this function already returns the missing-header sentinel below.
			if _, _, _, _, err = vm.TBCFullNode.BlockHeadersInsert(bc.ctx, msgHeaders); err != nil {
				log.Warn("Best-effort injection of missing progression headers into the full TBC node failed", "err", err)
			}

			hvmFullTBCBehindGauge.Update(1)
			return consensus.ErrFullTBCMissingBTCHeader
		}
		if missingFullBlockHeaders != nil && len(*missingFullBlockHeaders) > 0 {
			headers := make([]*wire.BlockHeader, len(*missingFullBlockHeaders))

			// Log all of the missing full blocks and trigger an attempt at refetching them over P2P
			for i := 0; i < len(*missingFullBlockHeaders); i++ {
				headers[i] = &(*missingFullBlockHeaders)[i]
				log.Warn(fmt.Sprintf("\tTBC missing full block: %s", (*missingFullBlockHeaders)[i].BlockHash().String()))
				vm.TBCAttemptBlockRefetch(bc.ctx, &(*missingFullBlockHeaders)[i])
			}

			msgHeaders := &wire.MsgHeaders{
				Headers: headers,
			}

			bc.setMissingProgressionBlocks(msgHeaders)

			hvmFullTBCBehindGauge.Update(1)
			return consensus.ErrFullTBCMissingFullBTCBlock
		} else {
			// Should never get available=false but neither a missing full block or block header, so if this happens
			// exit on crit.
			log.Crit(fmt.Sprintf("When attempting to update full TBC node indexers to tip %s @ %d, was "+
				"unable to determine whether any required headers or blocks were missing in full TBC node as the "+
				"call to TBCBlocksAvailableToHeader returned available=false but did not indicate any missing headers "+
				"or full blocks which should not be possible", cursorHeader.BlockHash().String(), cursorHeight))
		}
	}

	// If we got to here, there are no missing progression blocks
	bc.setMissingProgressionBlocks(nil)
	hvmFullTBCBehindGauge.Update(0)

	log.Info(fmt.Sprintf("Moving TBC Full Node indexes to BTC block %s", cursorHeader.BlockHash().String()))

	// This single indexer function handles any reorgs required to move the TBC full node to the specified index.
	err = vm.TBCIndexToHeader(cursorHeader, lightTipHeader)
	if err != nil {
		if mapped := hvmIndexErrToConsensus(err); errors.Is(mapped, consensus.ErrFullTBCMissingBTCHeader) {
			// The full TBC node is missing a not-yet-synced BTC header on the path to the target. The
			// vm-local sentinel is mapped (core/vm cannot import consensus) to the deferrable error so
			// the block-import path returns it before EVM execution and the engine API returns SYNCING;
			// the consensus layer then re-drives the payload once the header syncs, rather than crashing.
			// Matches the early missing-header return above.
			log.Warn(fmt.Sprintf("Deferring TBC full node index move to BTC block %s @ %d: full node is "+
				"missing a required BTC header; will retry as it continues to sync", cursorHash.String(), cursorHeight), "err", err)
			hvmFullTBCBehindGauge.Update(1)
			return mapped
		}
		// All required data was reported available by TBCBlocksAvailableToHeader above, so any
		// OTHER error here indicates a bug or data corruption in the full TBC node — fail-stop.
		log.Crit(fmt.Sprintf("Unable to move TBC Full Node indexers to BTC block %s @ %d",
			cursorHash.String(), cursorHeight), "err", err)
	}

	return nil
}

// updateHvmHeaderConsensus must be called each time when the canonical
// tip is changed. This method determines the change in chain geometry
// that the switch to the new block represents, and modifies the
// external-header-mode TBC instance's Bitcoin header knowledge to
// account for only information contained in the canonical chain ending
// at the new head.
func (bc *BlockChain) updateHvmHeaderConsensus(newHead *types.Header, updateFullNode bool) error {
	if !bc.hvmEnabled {
		log.Warn("updateHvmHeaderConsensus called but hVM is disabled")
		return nil
	}

	// Single chokepoint for the hVM snap-sync pause. While awaiting an in-flight hVM snap sync the
	// lightweight TBC node is owned by SnapSyncHvm (which rebuilds it via AddExternalHeaders, never through
	// this function), so no normal block-apply / head-move / reorg path may advance hVM consensus. ProcessBlock
	// gates its own apply block separately (it also calls updateFullTBCToLightweight directly); this early
	// return covers every OTHER caller — writeHeadBlock, setHeadBeyondRoot, SetCanonical, the reorg/revert
	// paths, and the build path — uniformly, so the latch cannot be bypassed. Blocks deferred during the
	// window are caught up by the first updateHvmHeaderConsensus after the snap completes (it walks the gap).
	if bc.isAwaitingHvmSnapSync() {
		log.Debug("updateHvmHeaderConsensus skipped: awaiting hVM snap sync (lightweight TBC owned by SnapSyncHvm)")
		return nil
	}

	log.Info(fmt.Sprintf("updateHvmHeaderConsensus called with new head: %s @ %d",
		newHead.Hash().String(), newHead.Number.Uint64()))

	if !bc.chainConfig.IsHvm0(newHead.Time) {
		log.Info(fmt.Sprintf("New head %s @ %d does not have hVM Phase 0 active yet.",
			newHead.Hash().String(), newHead.Number.Uint64()))
		return nil
	}

	// We store the EVM block which was last applied to update hVM
	// independently in order to gracefully handle updates to EVM
	// blockchain state that occurred without TBC's knowledge.
	// In the future, this may also be used for some kind of
	// snap sync of TBC state or similar.
	currentHeadHashRaw, err := bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
	if err != nil || currentHeadHashRaw == nil {
		// A faulted lightweight-store read (a torn/IO-failed leveldb, or external-header-mode disabled)
		// returns a nil pointer, and the dereferences below (currentHeadHashRaw[:]) would nil-panic before
		// any of this function's currentHead==nil recovery guards run. Treat it as the recoverable torn-store
		// condition the re-apply callers heal from via recoverReapplyHvmState/performFullHvmHeaderStateRestore.
		// (applyHvmHeaderConsensusUpdate reads the same UpstreamStateId but log.Crits on its error and does not
		// guard the nil pointer; that read is reached only after this entry-point read has already succeeded,
		// so the narrower handling there is acceptable.)
		log.Error("unable to get upstream state id from lightweight TBC; treating as corrupt hVM state", "err", err)
		return consensus.ErrCorruptHVMHeaderOnlyModeState
	}
	log.Info(fmt.Sprintf("current upstream state id from TBC is %x", currentHeadHashRaw[:]))

	if bytes.Equal(currentHeadHashRaw[:], newHead.Hash().Bytes()[:]) {
		log.Info(fmt.Sprintf("updateHvmHeaderConsensus called to update chain to new head %x but lightweight "+
			"TBC node's state already reflects this block, no-op", currentHeadHashRaw[:]))
		return nil
	}

	var currentHead *types.Header
	currentHeadHash := common.BytesToHash(currentHeadHashRaw[:])

	if bytes.Equal(currentHeadHashRaw[:], hVMGenesisUpstreamId[:]) {
		// Should only be printed at hVM activation time or if something is wrong (genesis state but not activation time)
		log.Info(fmt.Sprintf("Current head from lightweight TBC upstream ID is the hVM Genesis Upstream ID"))
		// Upstream id is genesis, so this should be the first hVM block
		currentHead = bc.getHeaderFromDiskOrHoldingPen(newHead.ParentHash)
		if currentHead == nil {
			// Same recoverable corruption case the currentHead == nil guard below handles for the other
			// branch: the parent is absent from both disk and the holding pen (a rewind/deep-reorg orphaned
			// it, or recoverReapplyHvmState reset us to genesis with the parent already gone). Return the
			// recoverable sentinel instead of nil-dereferencing .Hash()/.Time here and crashing the process.
			log.Error(fmt.Sprintf("currentHead (parent %x of first hVM block %s) is nil; treating as corrupt hVM state",
				newHead.ParentHash[:], newHead.Hash().String()))
			return consensus.ErrCorruptHVMHeaderOnlyModeState
		}
		currentHeadHash = currentHead.Hash()
		if bc.chainConfig.IsHvm0(currentHead.Time) {
			// This is critical as it means hVM is in an unexpected state (upstream state ID is genesis but should not be)
			log.Crit(fmt.Sprintf("When updating hVM state transition for block %s @ %d, the upstream id is the "+
				" hVMGenesisUpstreamId, but the parent at time %d should have hVM Phase 0 activated!",
				newHead.Hash().String(), newHead.Number.Uint64(), currentHead.Time))
		}
	} else {
		log.Debug(fmt.Sprintf("Getting header %x from disk or holding pen", currentHeadHash[:]))
		currentHead = bc.getHeaderFromDiskOrHoldingPen(currentHeadHash)
	}

	if currentHead == nil {
		// The lightweight TBC's upstream-state-id references an EVM header that is absent from both disk and
		// the holding pen (e.g. a rewind/deep-reorg orphaned it). Falling through to findCommonAncestor would
		// nil-deref and crash the process (reachable on followers via the head-move callers, not just the
		// sequencer build path). Return the recoverable sentinel so the callers rebuild from genesis via
		// recoverReapplyHvmState instead of panicking.
		log.Error(fmt.Sprintf("currentHead is nil, but should have been %x; treating as corrupt hVM state", currentHeadHash[:]))
		return consensus.ErrCorruptHVMHeaderOnlyModeState
	}
	log.Debug(fmt.Sprintf("Going to look for ancestor of %s @ %d and %s @ %d", newHead.Hash().String(),
		newHead.Number.Uint64(), currentHead.Hash().String(), currentHead.Number.Uint64()))

	log.Debug(fmt.Sprintf("updateHvmHeaderConsensus found current head hash: %x", currentHeadHashRaw[:]))

	// Get common ancestor between newHead and currentHead
	ancestor, err := bc.findCommonAncestor(newHead, currentHead)
	if err != nil || ancestor == nil {
		log.Error(fmt.Sprintf("Unable to find common ancestor between %s @ %d and %s @ %d,"+
			" cannot transition hVM's header knowledge to the correct state",
			newHead.Hash().String(), newHead.Number.Uint64(),
			currentHead.Hash().String(), currentHead.Number.Uint64()), "err", err)
		// We are missing at least one block in the EVM chain geometry between the requested new head and
		// the current head which hVM currently represents state for
		return consensus.ErrUnknownAncestor
	}

	log.Debug(fmt.Sprintf("Common ancestor between %s @ %d and %s @ %d is %s @ %d",
		currentHead.Hash().String(), currentHead.Number.Uint64(), newHead.Hash().String(),
		newHead.Number.Uint64(), ancestor.Hash().String(), ancestor.Number.Uint64()))

	// If currentHead is direct parent, then just apply state change from newHead
	if newHead.ParentHash.Cmp(currentHead.Hash()) == 0 {
		err := bc.applyHvmHeaderConsensusUpdate(newHead, true, true)
		if err != nil {
			if errors.Is(err, consensus.ErrInvalidHVMBlockFormat) || errors.Is(err, consensus.ErrInvalidHVMHeaders) {
				// Block is invalid, ban block and bubble error up
				badBlock := bc.getBlockFromDiskOrHoldingPen(newHead.Hash())
				bc.reportBlock(badBlock, nil, err)
				return err
			} else if errors.Is(err, consensus.ErrCorruptHVMHeaderOnlyModeState) {
				// Bubble up corruption to potentially fix upstream
				return err
			} else {
				// Error is unrecognized, for now fail with crit
				log.Crit(fmt.Sprintf("Encountered an error applying hVM header state transition for block %s @ %d",
					newHead.Hash().String(), newHead.Number.Uint64()), "err", err)
			}
			// Unreachable
			return err
		}
		log.Info(fmt.Sprintf("Successfully applied hVM header state transition for single block %s @ %d",
			newHead.Hash().String(), newHead.Number.Uint64()))
	} else if bytes.Equal(currentHead.Hash().Bytes(), ancestor.Hash().Bytes()) {
		// If currentHead is the ancestor, then we are walking directly forwards.
		err := bc.walkHvmHeaderConsensusForward(currentHead, newHead)
		if err != nil {
			if errors.Is(err, consensus.ErrInvalidHVMBlockFormat) || errors.Is(err, consensus.ErrInvalidHVMHeaders) {
				// The offending block has already been reported by the walk-forward function, bubble error up
				return err
			} else if errors.Is(err, consensus.ErrCorruptHVMHeaderOnlyModeState) {
				// Bubble up corruption to potentially fix upstream
				return err
			} else {
				// Error is unrecognized, for now fail with crit
				log.Crit("Unable to walk hVM consensus forwards", "err", err)
			}
			// Unreachable
			return err
		}

	} else if bytes.Equal(newHead.Hash().Bytes(), ancestor.Hash().Bytes()) {
		// Otherwise if newHead is the ancestor, then we are walking directly backwards.
		err := bc.walkHvmHeaderConsensusBack(currentHead, newHead)
		if err != nil {
			if errors.Is(err, consensus.ErrCorruptHVMHeaderOnlyModeState) {
				// Bubble potential corruption error upstream
				return err
			} else {
				// Any error that isn't possibly fixed by reconstructing lightweight TBC state is critical,
				// as any other error walking backwards means something that was applied could not be
				// unapplied and is likely a bug
				log.Crit("Unable to walk hVM consensus backwards", "err", err)
			}
		}
	} else {
		// Finally if neither newHead or currentHead is the ancestor, then we are in a fork and need to walk
		// backwards from currentHead until we reach ancestor, then forward to newHead.

		// First, walk backwards from currentHead to common ancestor
		err := bc.walkHvmHeaderConsensusBack(currentHead, ancestor)
		if err != nil {
			if errors.Is(err, consensus.ErrCorruptHVMHeaderOnlyModeState) {
				// Bubble potential corruption error upstream
				return err
			} else {
				// Any error that isn't possibly fixed by reconstructing lightweight TBC state is critical,
				// as any other error walking backwards means something that was applied could not be
				// unapplied and is likely a bug
				log.Crit("Unable to walk hVM consensus backwards", "err", err)
			}
		}
		// Then, walk forwards from the common ancestor
		err = bc.walkHvmHeaderConsensusForward(ancestor, newHead)
		if err != nil {
			if errors.Is(err, consensus.ErrInvalidHVMBlockFormat) || errors.Is(err, consensus.ErrInvalidHVMHeaders) {
				// The offending block has already been reported by the walk-forward function, bubble error up
				return err
			} else if errors.Is(err, consensus.ErrCorruptHVMHeaderOnlyModeState) {
				// Bubble up corruption to potentially fix upstream
				return err
			} else {
				// Error is unrecognized, for now fail with crit
				log.Crit("Unable to walk hVM consensus forwards", "err", err)
			}
			// Unreachable
			return err
		}
	}

	if updateFullNode {
		// Now make sure TBC indexer represents this final state
		err = bc.updateFullTBCToLightweight()
		if err != nil {
			log.Error("Unable to update full TBC node according to lightweight", "err", err)
			return err
		}
	}

	return nil
}

// revertHvmStateAfterInvalidBlock rolls the lightweight (and full) TBC nodes back to the EVM block they
// represented before this insert advanced them to `block`, captured in `tbcHeader`. It is used when
// `block` passed its hVM header-consensus update (so the upstream-state-id, and any BTC headers the
// block's Bitcoin Attributes Deposited tx added, were durably committed) but then failed EVM Process /
// ValidateState.
//
// Without this, the persisted TBC upstream-state-id keeps pointing at a block the EVM rejected and never
// wrote to disk — a consensus-divergence window (hVM precompile reads served from a Bitcoin view derived
// from a rejected block) until the next canonical head re-drives updateHvmHeaderConsensus or a restart
// triggers a full restore. The TBC commit deliberately precedes EVM execution (the hVM precompiles read
// the advanced view during Process), so the correct response is to revert on failure rather than reorder.
//
// The revert target is `tbcHeader` (the pre-insert EVM tip), not the rejected block's parent: a rejected
// reorg block leaves the node on the old canonical chain that tbcHeader represents, so reverting there is
// canonical-consistent. This mirrors the established non-canonical (!setHead) revert (and the
// updateFullTBCToLightweight-failure revert, which additionally skips the full-node re-advance since the
// full node just failed), with two deliberate differences: there is no "direct child
// of current head -> skip" optimization (an invalid block must always be unwound), and
// ErrCorruptHVMHeaderOnlyModeState is recovered via performFullHvmHeaderStateRestore (matching the
// parent-move path) rather than crashing. A nil tbcHeader means `block` was the first hVM block (the
// pre-state is TBC genesis, not an EVM header); we log and rely on restart recovery, matching the
// existing !setHead nil handling. Callers must invoke this only when hVM was activated for `block`.
func (bc *BlockChain) revertHvmStateAfterInvalidBlock(tbcHeader *types.Header, block *types.Block) {
	if tbcHeader == nil {
		// First hVM block failed EVM validation: its pre-state is TBC genesis, which we cannot express
		// as an EVM header to revert to here. Leave the state; SetupHvmHeaderNode performs a full
		// restore on restart when it finds the persisted upstream-state-id unknown on disk.
		log.Warn(fmt.Sprintf("hVM state was advanced for invalid first-hVM block %s @ %d; leaving TBC "+
			"state (recovers on restart via full restore)", block.Hash().String(), block.NumberU64()))
		return
	}

	err := bc.updateHvmHeaderConsensus(tbcHeader, true)
	if err != nil {
		if isHvmFullNodeBehind(err) {
			// Transient full-TBC BTC-sync lag, not fatal — the lightweight (consensus) view was reverted
			// successfully (it precedes the full-node advance); the full-node indexer catches up on a
			// later import. (Same predicate the head-set / !setHead paths use.)
			log.Warn(fmt.Sprintf("Full TBC node is behind reverted state at block %s @ %d after invalid "+
				"block %s @ %d; its indexers will catch up on a later import (deferred, not fatal)",
				tbcHeader.Hash().String(), tbcHeader.Number.Uint64(), block.Hash().String(), block.NumberU64()),
				"err", err)
		} else if isHvmReapplyRecoverableError(err) {
			// Re-apply (revert) onto the already-committed pre-invalid-block state: a torn store
			// (ErrCorrupt) or a fresh grandfathered-rule reject (ErrInvalidHVMHeaders/Format) on this
			// already-committed target is recoverable — rebuild from genesis (enforcement off) rather than
			// crashing the fleet. The revert target tbcHeader is already-committed, so a reject here is
			// never a genuine bad block.
			bc.recoverReapplyHvmState(fmt.Sprintf("revert to %s @ %d after invalid block %s @ %d",
				tbcHeader.Hash().String(), tbcHeader.Number.Uint64(), block.Hash().String(), block.NumberU64()), err)
		} else {
			log.Crit(fmt.Sprintf("Unable to revert TBC node to represent state at block %s @ %d after "+
				"invalid block %s @ %d.", tbcHeader.Hash().String(), tbcHeader.Number.Uint64(),
				block.Hash().String(), block.NumberU64()), "err", err)
		}
	} else {
		log.Info(fmt.Sprintf("Successfully reverted TBC node to represent state at block %s @ %d after "+
			"invalid block %s @ %d.", tbcHeader.Hash().String(), tbcHeader.Number.Uint64(),
			block.Hash().String(), block.NumberU64()))
	}
}

// rewindHashHead implements the logic of rewindHead in the context of hash scheme.
func (bc *BlockChain) rewindHashHead(head *types.Header, root common.Hash) (*types.Header, uint64) {
	var (
		limit      uint64                             // The oldest block that will be searched for this rewinding
		beyondRoot = root == common.Hash{}            // Flag whether we're beyond the requested root (no root, always true)
		pivot      = rawdb.ReadLastPivotNumber(bc.db) // Associated block number of pivot point state
		rootNumber uint64                             // Associated block number of requested root

		start  = time.Now() // Timestamp the rewinding is restarted
		logged = time.Now() // Timestamp last progress log was printed
	)
	// The oldest block to be searched is determined by the pivot block or a constant
	// searching threshold. The rationale behind this is as follows:
	//
	// - Snap sync is selected if the pivot block is available. The earliest available
	//   state is the pivot block itself, so there is no sense in going further back.
	//
	// - Full sync is selected if the pivot block does not exist. The hash database
	//   periodically flushes the state to disk, and the used searching threshold is
	//   considered sufficient to find a persistent state, even for the testnet. It
	//   might be not enough for a chain that is nearly empty. In the worst case,
	//   the entire chain is reset to genesis, and snap sync is re-enabled on top,
	//   which is still acceptable.
	if pivot != nil {
		limit = *pivot
	} else if head.Number.Uint64() > params.FullImmutabilityThreshold {
		limit = head.Number.Uint64() - params.FullImmutabilityThreshold
	}
	for {
		logger := log.Trace
		if time.Since(logged) > time.Second*8 {
			logged = time.Now()
			logger = log.Info
		}
		logger("Block state missing, rewinding further", "number", head.Number, "hash", head.Hash(), "elapsed", common.PrettyDuration(time.Since(start)))

		// If a root threshold was requested but not yet crossed, check
		if !beyondRoot && head.Root == root {
			beyondRoot, rootNumber = true, head.Number.Uint64()
		}
		// If search limit is reached, return the genesis block as the
		// new chain head.
		if head.Number.Uint64() < limit {
			log.Info("Rewinding limit reached, resetting to genesis", "number", head.Number, "hash", head.Hash(), "limit", limit)
			return bc.genesisBlock.Header(), rootNumber
		}
		// If the associated state is not reachable, continue searching
		// backwards until an available state is found.
		if !bc.HasState(head.Root) {
			// If the chain is gapped in the middle, return the genesis
			// block as the new chain head.
			parent := bc.GetHeader(head.ParentHash, head.Number.Uint64()-1)
			if parent == nil {
				log.Error("Missing block in the middle, resetting to genesis", "number", head.Number.Uint64()-1, "hash", head.ParentHash)
				return bc.genesisBlock.Header(), rootNumber
			}
			head = parent

			// If the genesis block is reached, stop searching.
			if head.Number.Uint64() == 0 {
				log.Info("Genesis block reached", "number", head.Number, "hash", head.Hash())
				return head, rootNumber
			}
			continue // keep rewinding
		}
		// Once the available state is found, ensure that the requested root
		// has already been crossed. If not, continue rewinding.
		if beyondRoot || head.Number.Uint64() == 0 {
			log.Info("Rewound to block with state", "number", head.Number, "hash", head.Hash())
			return head, rootNumber
		}
		log.Debug("Skipping block with threshold state", "number", head.Number, "hash", head.Hash(), "root", head.Root)
		head = bc.GetHeader(head.ParentHash, head.Number.Uint64()-1) // Keep rewinding
	}
}

// rewindPathHead implements the logic of rewindHead in the context of path scheme.
func (bc *BlockChain) rewindPathHead(head *types.Header, root common.Hash) (*types.Header, uint64) {
	var (
		pivot      = rawdb.ReadLastPivotNumber(bc.db) // Associated block number of pivot block
		rootNumber uint64                             // Associated block number of requested root

		// BeyondRoot represents whether the requested root is already
		// crossed. The flag value is set to true if the root is empty.
		beyondRoot = root == common.Hash{}

		// noState represents if the target state requested for search
		// is unavailable and impossible to be recovered.
		noState = !bc.HasState(root) && !bc.stateRecoverable(root)

		start  = time.Now() // Timestamp the rewinding is restarted
		logged = time.Now() // Timestamp last progress log was printed
	)
	// Rewind the head block tag until an available state is found.
	for {
		logger := log.Trace
		if time.Since(logged) > time.Second*8 {
			logged = time.Now()
			logger = log.Info
		}
		logger("Block state missing, rewinding further", "number", head.Number, "hash", head.Hash(), "elapsed", common.PrettyDuration(time.Since(start)))

		// If a root threshold was requested but not yet crossed, check
		if !beyondRoot && head.Root == root {
			beyondRoot, rootNumber = true, head.Number.Uint64()
		}
		// If the root threshold hasn't been crossed but the available
		// state is reached, quickly determine if the target state is
		// possible to be reached or not.
		if !beyondRoot && noState && bc.HasState(head.Root) {
			beyondRoot = true
			log.Info("Disable the search for unattainable state", "root", root)
		}
		// Check if the associated state is available or recoverable if
		// the requested root has already been crossed.
		if beyondRoot && (bc.HasState(head.Root) || bc.stateRecoverable(head.Root)) {
			break
		}
		// If pivot block is reached, return the genesis block as the
		// new chain head. Theoretically there must be a persistent
		// state before or at the pivot block, prevent endless rewinding
		// towards the genesis just in case.
		if pivot != nil && *pivot >= head.Number.Uint64() {
			log.Info("Pivot block reached, resetting to genesis", "number", head.Number, "hash", head.Hash())
			return bc.genesisBlock.Header(), rootNumber
		}
		// If the chain is gapped in the middle, return the genesis
		// block as the new chain head
		parent := bc.GetHeader(head.ParentHash, head.Number.Uint64()-1) // Keep rewinding
		if parent == nil {
			log.Error("Missing block in the middle, resetting to genesis", "number", head.Number.Uint64()-1, "hash", head.ParentHash)
			return bc.genesisBlock.Header(), rootNumber
		}
		head = parent

		// If the genesis block is reached, stop searching.
		if head.Number.Uint64() == 0 {
			log.Info("Genesis block reached", "number", head.Number, "hash", head.Hash())
			return head, rootNumber
		}
	}
	// Recover if the target state if it's not available yet.
	if !bc.HasState(head.Root) {
		if err := bc.triedb.Recover(head.Root); err != nil {
			log.Crit("Failed to rollback state", "err", err)
		}
	}
	log.Info("Rewound to block with state", "number", head.Number, "hash", head.Hash())
	return head, rootNumber
}

// rewindHead searches the available states in the database and returns the associated
// block as the new head block.
//
// If the given root is not empty, then the rewind should attempt to pass the specified
// state root and return the associated block number as well. If the root, typically
// representing the state corresponding to snapshot disk layer, is deemed impassable,
// then block number zero is returned, indicating that snapshot recovery is disabled
// and the whole snapshot should be auto-generated in case of head mismatch.
func (bc *BlockChain) rewindHead(head *types.Header, root common.Hash) (*types.Header, uint64) {
	if bc.triedb.Scheme() == rawdb.PathScheme {
		return bc.rewindPathHead(head, root)
	}
	return bc.rewindHashHead(head, root)
}

// setHeadBeyondRoot rewinds the local chain to a new head with the extra condition
// that the rewind must pass the specified state root. This method is meant to be
// used when rewinding with snapshots enabled to ensure that we go back further than
// persistent disk layer. Depending on whether the node was snap synced or full, and
// in which state, the method will try to delete minimal data from disk whilst
// retaining chain consistency.
//
// The method also works in timestamp mode if `head == 0` but `time != 0`. In that
// case blocks are rolled back until the new head becomes older or equal to the
// requested time. If both `head` and `time` is 0, the chain is rewound to genesis.
//
// The method returns the block number where the requested root cap was found.
func (bc *BlockChain) setHeadBeyondRoot(head uint64, time uint64, root common.Hash, repair bool) (uint64, error) {
	if !bc.chainmu.TryLock() {
		return 0, errChainStopped
	}
	defer bc.chainmu.Unlock()

	var (
		// Track the block number of the requested root hash
		rootNumber uint64 // (no root == always 0)

		// Retrieve the last pivot block to short circuit rollbacks beyond it
		// and the current freezer limit to start nuking it's underflown.
		pivot = rawdb.ReadLastPivotNumber(bc.db)
	)
	updateFn := func(db ethdb.KeyValueWriter, header *types.Header) (*types.Header, bool) {
		// Rewind the blockchain, ensuring we don't end up with a stateless head
		// block. Note, depth equality is permitted to allow using SetHead as a
		// chain reparation mechanism without deleting any data!
		if currentBlock := bc.CurrentBlock(); currentBlock != nil && header.Number.Uint64() <= currentBlock.Number.Uint64() {
			var newHeadBlock *types.Header
			newHeadBlock, rootNumber = bc.rewindHead(header, root)
			rawdb.WriteHeadBlockHash(db, newHeadBlock.Hash())

			// Degrade the chain markers if they are explicitly reverted.
			// In theory we should update all in-memory markers in the
			// last step, however the direction of SetHead is from high
			// to low, so it's safe to update in-memory markers directly.
			bc.currentBlock.Store(newHeadBlock)
			headBlockGauge.Update(int64(newHeadBlock.Number.Uint64()))

			log.Info(fmt.Sprintf("Updating hVM header consensus in setHeadBeyondRoot updateFn to %s @ %d",
				newHeadBlock.Hash().String(), newHeadBlock.Number))
			err := bc.updateHvmHeaderConsensus(newHeadBlock, true)
			if err != nil {
				if isHvmFullNodeBehind(err) {
					// Transient full-TBC BTC-sync lag, not fatal — full-node indexer catches up
					// on a later import. (See isHvmFullNodeBehind.)
					log.Warn(fmt.Sprintf("Full TBC node is behind head %s @ %d in setHeadBeyondRoot updateFn; "+
						"its indexers will catch up on a later import (deferred, not fatal)",
						newHeadBlock.Hash(), newHeadBlock.Number), "err", err)
				} else if isHvmReapplyRecoverableError(err) {
					// Re-apply (rewind) onto an already-committed canonical head: recover via a from-genesis
					// rebuild rather than halting the fleet (currentBlock is already newHeadBlock).
					bc.recoverReapplyHvmState(fmt.Sprintf("rewound head %s @ %d in setHeadBeyondRoot",
						newHeadBlock.Hash().String(), newHeadBlock.Number.Uint64()), err)
				} else {
					log.Crit(fmt.Sprintf("Unable to udpate hVM header consensus in setHeadBeyondRoot updateFn to %s @ %d",
						newHeadBlock.Hash(), newHeadBlock.Number), "err", err)
				}
			}

			// The head state is missing, which is only possible in the path-based
			// scheme. This situation occurs when the chain head is rewound below
			// the pivot point. In this scenario, there is no possible recovery
			// approach except for rerunning a snap sync. Do nothing here until the
			// state syncer picks it up.
			if !bc.HasState(newHeadBlock.Root) {
				if newHeadBlock.Number.Uint64() != 0 {
					log.Crit("Chain is stateless at a non-genesis block")
				}
				log.Info("Chain is stateless, wait state sync", "number", newHeadBlock.Number, "hash", newHeadBlock.Hash())
			}
		}
		// Rewind the snap block in a simpleton way to the target head
		if currentSnapBlock := bc.CurrentSnapBlock(); currentSnapBlock != nil && header.Number.Uint64() < currentSnapBlock.Number.Uint64() {
			newHeadSnapBlock := bc.GetBlock(header.Hash(), header.Number.Uint64())
			// If either blocks reached nil, reset to the genesis state
			if newHeadSnapBlock == nil {
				newHeadSnapBlock = bc.genesisBlock
			}
			rawdb.WriteHeadFastBlockHash(db, newHeadSnapBlock.Hash())

			// Degrade the chain markers if they are explicitly reverted.
			// In theory we should update all in-memory markers in the
			// last step, however the direction of SetHead is from high
			// to low, so it's safe the update in-memory markers directly.
			bc.currentSnapBlock.Store(newHeadSnapBlock.Header())
			headFastBlockGauge.Update(int64(newHeadSnapBlock.NumberU64()))
		}
		var (
			headHeader = bc.CurrentBlock()
			headNumber = headHeader.Number.Uint64()
		)
		// If setHead underflown the freezer threshold and the block processing
		// intent afterwards is full block importing, delete the chain segment
		// between the stateful-block and the sethead target.
		var wipe bool
		frozen, _ := bc.db.Ancients()
		if headNumber+1 < frozen {
			wipe = pivot == nil || headNumber >= *pivot
		}
		return headHeader, wipe // Only force wipe if full synced
	}
	// Rewind the header chain, deleting all block bodies until then
	delFn := func(db ethdb.KeyValueWriter, hash common.Hash, num uint64) {
		// Ignore the error here since light client won't hit this path
		frozen, _ := bc.db.Ancients()
		if num+1 <= frozen {
			// The chain segment, such as the block header, canonical hash,
			// body, and receipt, will be removed from the ancient store
			// in one go.
			//
			// The hash-to-number mapping in the key-value store will be
			// removed by the hc.SetHead function.
		} else {
			// Remove the associated body and receipts from the key-value store.
			// The header, hash-to-number mapping, and canonical hash will be
			// removed by the hc.SetHead function.
			rawdb.DeleteBody(db, hash, num)
			rawdb.DeleteReceipts(db, hash, num)
		}
		// Todo(rjl493456442) txlookup, log index, etc
	}
	// If SetHead was only called as a chain reparation method, try to skip
	// touching the header chain altogether, unless the freezer is broken
	if repair {
		if target, force := updateFn(bc.db, bc.CurrentBlock()); force {
			bc.hc.SetHead(target.Number.Uint64(), nil, delFn)
		}
	} else {
		// Rewind the chain to the requested head and keep going backwards until a
		// block with a state is found or snap sync pivot is passed
		if time > 0 {
			log.Warn("Rewinding blockchain to timestamp", "target", time)
			bc.hc.SetHeadWithTimestamp(time, updateFn, delFn)
		} else {
			log.Warn("Rewinding blockchain to block", "target", head)
			bc.hc.SetHead(head, updateFn, delFn)
		}
	}
	// Clear out any stale content from the caches
	bc.bodyCache.Purge()
	bc.bodyRLPCache.Purge()
	bc.receiptsCache.Purge()
	bc.blockCache.Purge()
	bc.txLookupCache.Purge()

	// Clear safe block, finalized block if needed
	if safe := bc.CurrentSafeBlock(); safe != nil && head < safe.Number.Uint64() {
		log.Warn("SetHead invalidated safe block")
		bc.SetSafe(nil)
	}
	if finalized := bc.CurrentFinalBlock(); finalized != nil && head < finalized.Number.Uint64() {
		log.Error("SetHead invalidated finalized block")
		bc.SetFinalized(nil)
	}
	return rootNumber, bc.loadLastState()
}

// SnapSyncCommitHead sets the current head block to the one defined by the hash
// irrelevant what the chain contents were prior.
func (bc *BlockChain) SnapSyncCommitHead(hash common.Hash) error {
	log.Info("Blockhain SnapSyncCommitHead", "hash", hash.String())
	// Make sure that both the block as well at its state trie exists
	block := bc.GetBlockByHash(hash)
	if block == nil {
		return fmt.Errorf("non existent block [%x..]", hash[:4])
	}
	// Reset the trie database with the fresh snap synced state.
	root := block.Root()
	if bc.triedb.Scheme() == rawdb.PathScheme {
		if err := bc.triedb.Enable(root); err != nil {
			return err
		}
	}
	if !bc.HasState(root) {
		return fmt.Errorf("non existent state [%x..]", root[:4])
	}
	// If all checks out, manually set the head block.
	if !bc.chainmu.TryLock() {
		return errChainStopped
	}
	bc.currentBlock.Store(block.Header())
	headBlockGauge.Update(int64(block.NumberU64()))
	bc.chainmu.Unlock()

	// Destroy any existing state snapshot and regenerate it in the background,
	// also resuming the normal maintenance of any previously paused snapshot.
	if bc.snaps != nil {
		bc.snaps.Rebuild(root)
	}
	log.Info("Committed new head block", "number", block.Number(), "hash", hash)
	return nil
}

// Reset purges the entire blockchain, restoring it to its genesis state.
func (bc *BlockChain) Reset() error {
	return bc.ResetWithGenesisBlock(bc.genesisBlock)
}

// ResetWithGenesisBlock purges the entire blockchain, restoring it to the
// specified genesis state.
func (bc *BlockChain) ResetWithGenesisBlock(genesis *types.Block) error {
	// Dump the entire block chain and purge the caches
	if err := bc.SetHead(0); err != nil {
		return err
	}
	if !bc.chainmu.TryLock() {
		return errChainStopped
	}
	defer bc.chainmu.Unlock()

	// Prepare the genesis block and reinitialise the chain
	batch := bc.db.NewBatch()
	rawdb.WriteBlock(batch, genesis)
	if err := batch.Write(); err != nil {
		log.Crit("Failed to write genesis block", "err", err)
	}
	bc.writeHeadBlock(genesis)

	// Last update all in-memory chain markers
	bc.genesisBlock = genesis
	bc.currentBlock.Store(bc.genesisBlock.Header())
	bc.resetHvmHeaderNodeToGenesis() // No need to restore as we're resetting EVM state to genesis too
	headBlockGauge.Update(int64(bc.genesisBlock.NumberU64()))
	bc.hc.SetGenesis(bc.genesisBlock.Header())
	bc.hc.SetCurrentHeader(bc.genesisBlock.Header())
	bc.currentSnapBlock.Store(bc.genesisBlock.Header())
	headFastBlockGauge.Update(int64(bc.genesisBlock.NumberU64()))

	// Reset history pruning status.
	return bc.initializeHistoryPruning(0)
}

// Export writes the active chain to the given writer.
func (bc *BlockChain) Export(w io.Writer) error {
	return bc.ExportN(w, uint64(0), bc.CurrentBlock().Number.Uint64())
}

// ExportN writes a subset of the active chain to the given writer.
func (bc *BlockChain) ExportN(w io.Writer, first uint64, last uint64) error {
	if first > last {
		return fmt.Errorf("export failed: first (%d) is greater than last (%d)", first, last)
	}
	log.Info("Exporting batch of blocks", "count", last-first+1)

	var (
		parentHash common.Hash
		start      = time.Now()
		reported   = time.Now()
	)
	for nr := first; nr <= last; nr++ {
		block := bc.GetBlockByNumber(nr)
		if block == nil {
			return fmt.Errorf("export failed on #%d: not found", nr)
		}
		if nr > first && block.ParentHash() != parentHash {
			return errors.New("export failed: chain reorg during export")
		}
		parentHash = block.Hash()
		if err := block.EncodeRLP(w); err != nil {
			return err
		}
		if time.Since(reported) >= statsReportLimit {
			log.Info("Exporting blocks", "exported", block.NumberU64()-first, "elapsed", common.PrettyDuration(time.Since(start)))
			reported = time.Now()
		}
	}
	return nil
}

// writeHeadBlock injects a new head block into the current block chain. This method
// assumes that the block is indeed a true head. It will also reset the head
// header and the head snap sync block to this very same block if they are older
// or if they are on a different side chain.
//
// Note, this function assumes that the `mu` mutex is held!
// isHvmFullNodeBehind reports whether err is the transient, no-attacker condition in which the embedded
// full TBC Bitcoin node has not yet P2P-synced the BTC headers/blocks needed to advance its indexers to
// a head's BTC state (consensus.ErrFullTBCMissingBTCHeader / ErrFullTBCMissingFullBTCBlock). These are
// the same deferrable sentinels the block-import path already handles gracefully (insertChain returns
// the sentinel before EVM execution; eth/catalyst maps it to STATUS_SYNCING so the consensus layer
// re-drives the payload later).
//
// On the head-set / reorg / forkchoice path the head has already been chosen and persisted, so we cannot
// defer the whole block as the import path does — but updateHvmHeaderConsensus updates the lightweight
// (consensus-relevant) header view before this error is produced (the error comes only from the
// subsequent full-node indexer advance), so the consensus state is already correct and the lagging
// full-node indexer self-corrects on a later import. Callers on the head-set path must therefore not
// log.Crit (os.Exit) on this condition: doing so turns an ordinary BTC-sync race during a normal
// reorg/forkchoice into a synchronized network-wide halt. They log a warning and continue; genuine
// faults still fail-stop.
//
// Catch-up: the lagging indexer is re-advanced by the next new-head block import, which calls
// updateFullTBCToLightweight and either succeeds or again returns the deferrable sentinel — in which
// case the engine API responds STATUS_SYNCING (delayPayloadImport) and the consensus layer re-drives the
// payload until BTC sync delivers the data. (insertChain also does bc.futureBlocks.Add on defer, but
// that lru is vestigial in this fork — written and removed but never re-processed; recovery is the CL
// re-drive, not a retry queue.) It is not re-advanced by a forkchoiceUpdated that re-points at the same
// head: updateHvmHeaderConsensus short-circuits to nil before the full-node advance when the upstream
// state id already equals the head. So if L2 progression pauses while the full node is behind, the
// indexer stays behind until the next new head — benign (see divergence-safety below). Observable via
// hvmFullTBCBehindGauge (alert on gauge==1 for N minutes).
//
// Divergence-safety: continuing with a lagging full-node indexer is consensus-safe because the only code
// that reads the full TBC indexer into a consensus-committed result is the hVM precompile set during
// processor.Process on the import path — and that path defers the whole block (early return before
// processor.Process) when the full node is behind, so a lagging indexer is never observed by
// consensus-committed execution. The head-set warn branches do no EVM execution. (The same precompiles
// also run on the sequencer build path — guarded separately — and on read-only RPC paths, which are
// non-consensus; neither is affected by this head-set warn branch.)
func isHvmFullNodeBehind(err error) bool {
	return errors.Is(err, consensus.ErrFullTBCMissingBTCHeader) || errors.Is(err, consensus.ErrFullTBCMissingFullBTCBlock)
}

// isHvmReapplyRecoverableError reports whether a non-nil updateHvmHeaderConsensus error on a re-apply path
// — the head-set / canonical / post-invalid-block revert / parent-move paths, which move the lightweight
// view onto a block already in the canonical chain (enforced at its first import) — should be recovered by
// rebuilding the lightweight view from genesis, rather than escalated to a fleet-wide log.Crit halt.
// Callers route a recoverable error through recoverReapplyHvmState (uniform log + metric + restore).
//
// On a re-apply path the block already passed contextual-difficulty validation at first import, so a fresh consensus reject here is
// not a genuine bad block: ErrInvalidHVMHeaders / ErrInvalidHVMBlockFormat can only mean already-committed
// history is being re-judged against a stricter/grandfathered rule (the same class the activation-gate-skip
// covers — impossible on the verified-clean mainnet), and ErrCorruptHVMHeaderOnlyModeState is a torn store.
// ErrUnknownAncestor is deliberately NOT recoverable here: at a re-apply site the block has connected
// ancestry, so a missing common ancestor is an unexpected geometry condition the from-genesis rebuild cannot
// reliably repair (a genuinely disconnected chain crits during replay anyway), and fail-stop is correct so it
// is not silently masked — see TestIsHvmReapplyRecoverableError.
//
// Why restore recovers (and its limits): performFullHvmHeaderStateRestore replays from genesis to the EVM
// tip (bc.CurrentBlock()) with enforcement off (applyHvmHeaderConsensusUpdate(_, _, false)). That suppresses
// the contextual-difficulty / PoW reject — the only fresh-grandfathered cause — and a torn store is
// discarded by the genesis rebuild, so the recoverable classes above self-heal. Restore is not crit-proof in
// general, though: the non-enforce-gated structural checks (header connectivity, BtcAttr parse) still run
// during replay and, if one fails, restore log.Crits. That is acceptable — those checks pass for
// genuinely-committed canonical blocks, so a structural failure during restore signals real disk corruption
// / a bug, not a grandfathered reject, and halting is correct.
//
// The naive alternative — downgrading the crit to warn-and-proceed — is unsafe: it would leave the
// lightweight view not advanced to the new head while the EVM head moved, silently diverging consensus.
// Restore target: the rebuild lands the view on bc.CurrentBlock(). For the head-set / canonical sites
// currentBlock is set to the new head before the call, so this targets the intended head. For the revert
// sites currentBlock is not modified (the rejected block never advanced the head); it remains the pre-insert
// canonical tip, so the rebuild lands on that tip — a correct (and, if the lightweight view lagged the EVM
// head, stronger) recovery than the narrow revert. The one site whose intended target is not CurrentBlock()
// is the ProcessBlock parent-move: during a fork import its target `parent` is a non-tip ancestor, so that
// site re-drives updateHvmHeaderConsensus(parent, false) after the rebuild (and crits only if that re-drive
// also fails) — see the comment there.
//
// First-import must not use this: the genuine first-import enforcement gate is ProcessBlock's
// `updateHvmHeaderConsensus(block.Header(), false)`, which reportBlocks and returns the reject so the import
// fails cleanly — never restored, which would accept an invalid block. (The hVM block guarded by
// `if status == CanonStatTy` in writeBlockAndSetHead is dead code — `status` is the zero-valued named return
// NonStatTy there, so the guard is always false; the ProcessBlock gate is what enforces first import.)
func isHvmReapplyRecoverableError(err error) bool {
	return errors.Is(err, consensus.ErrCorruptHVMHeaderOnlyModeState) ||
		errors.Is(err, consensus.ErrInvalidHVMHeaders) ||
		errors.Is(err, consensus.ErrInvalidHVMBlockFormat)
}

// recoverReapplyHvmState handles a recoverable (isHvmReapplyRecoverableError) hVM error on a re-apply path
// uniformly across all sites: it emits an alertable Error log + increments hvmReapplyRestoreMeter, then
// rebuilds the lightweight view from genesis (performFullHvmHeaderStateRestore) instead of halting the
// fleet. `where` names the call site (with block context) for the log. Callers must have already gated on
// isHvmReapplyRecoverableError(err); this exists so no site can silently restore (masking a re-judge of
// committed history) or skip the alertable metric.
func (bc *BlockChain) recoverReapplyHvmState(where string, err error) {
	log.Error(fmt.Sprintf("Re-applying already-committed hVM history (%s) hit a recoverable error; rebuilding "+
		"the lightweight view from genesis instead of halting the fleet", where), "err", err)
	hvmReapplyRestoreMeter.Mark(1)
	bc.performFullHvmHeaderStateRestore()
}

func (bc *BlockChain) writeHeadBlock(block *types.Block) {
	// Add the block to the canonical chain number scheme and mark as the head
	batch := bc.db.NewBatch()
	rawdb.WriteHeadHeaderHash(batch, block.Hash())
	rawdb.WriteHeadFastBlockHash(batch, block.Hash())
	rawdb.WriteCanonicalHash(batch, block.Hash(), block.NumberU64())
	rawdb.WriteTxLookupEntriesByBlock(batch, block)
	rawdb.WriteHeadBlockHash(batch, block.Hash())

	// Flush the whole batch into the disk, exit the node if failed
	if err := batch.Write(); err != nil {
		log.Crit("Failed to update chain indexes and markers", "err", err)
	}
	// Update all in-memory chain markers in the last step
	bc.hc.SetCurrentHeader(block.Header())

	bc.currentSnapBlock.Store(block.Header())
	headFastBlockGauge.Update(int64(block.NumberU64()))

	bc.currentBlock.Store(block.Header())
	headBlockGauge.Update(int64(block.NumberU64()))

	log.Info(fmt.Sprintf("Updating hVM header consensus to block %s @ %d in writeHeadBlock()",
		block.Hash().String(), block.Number().Uint64()))
	err := bc.updateHvmHeaderConsensus(block.Header(), true)
	if err != nil {
		if isHvmFullNodeBehind(err) {
			// Transient full-TBC BTC-sync lag, not fatal. The lightweight (consensus) view is already
			// updated; the full-node indexer catches up on a later import. Crashing here would halt every
			// node mid-reorg/forkchoice during an ordinary BTC-sync race.
			log.Warn(fmt.Sprintf("Full TBC node is behind the new canonical head %s @ %d in writeHeadBlock(); "+
				"its indexers will catch up on a later import (deferred, not fatal)",
				block.Hash().String(), block.Number().Uint64()), "err", err)
		} else if isHvmReapplyRecoverableError(err) {
			// Re-apply of an already-committed head: a fresh reject/corrupt is the grandfathered-rule /
			// torn-store class, not a genuine bad block (currentBlock is already this block). Rebuild the
			// lightweight view from genesis (enforcement off) rather than halting the fleet; never
			// warn-and-proceed (that would diverge the lightweight view from the moved EVM head).
			bc.recoverReapplyHvmState(fmt.Sprintf("head %s @ %d in writeHeadBlock",
				block.Hash().String(), block.Number().Uint64()), err)
		} else {
			log.Crit(fmt.Sprintf("Unable to update hVM header consensus to block %s @ %d in writeHeadBlock()",
				block.Hash().String(), block.Number().Uint64()), "err", err)
		}
	}
	// OPStack addition
	updateOptimismBlockMetrics(block.Header())
}

// stopWithoutSaving stops the blockchain service. If any imports are currently in progress
// it will abort them using the procInterrupt. This method stops all running
// goroutines, but does not do all the post-stop work of persisting data.
// OBS! It is generally recommended to use the Stop method!
// This method has been exposed to allow tests to stop the blockchain while simulating
// a crash.
func (bc *BlockChain) stopWithoutSaving() {
	if !bc.stopping.CompareAndSwap(false, true) {
		return
	}
	// Signal shutdown tx indexer.
	if bc.txIndexer != nil {
		bc.txIndexer.close()
	}
	// Unsubscribe all subscriptions registered from blockchain.
	bc.scope.Close()

	// Signal shutdown to all goroutines.
	bc.InterruptInsert(true)

	// Stop state size tracker
	if bc.stateSizer != nil {
		bc.stateSizer.Stop()
	}
	// Now wait for all chain modifications to end and persistent goroutines to exit.
	//
	// Note: Close waits for the mutex to become available, i.e. any running chain
	// modification will have exited when Close returns. Since we also called StopInsert,
	// the mutex should become available quickly. It cannot be taken again after Close has
	// returned.
	bc.chainmu.Close()

	// Join any in-flight hVM snap-sync waiter goroutines. bc.stopping is already true (set above), so a
	// waiter in its wait loop aborts within one poll; a waiter that has claimed the exclusive completion runs
	// to finish rather than being torn mid-write. Waiters take no chainmu, so this cannot deadlock with the
	// Close above. No-op on a non-hVM node (no waiters are ever started).
	//
	// Publish the shutdown flag under hvmSnapMu (the lock claimHvmSnapWaiterSlot loads bc.stopping under)
	// before waiting. This mutex barrier establishes the happens-before that makes the join airtight within
	// the snap-latch code itself: any concurrent claim either observes stopping==true and refuses, or
	// completed its hvmSnapWg.Add before this barrier — so no Add can follow this Wait. Without it the join
	// would rely on the cross-package Stop() ordering (handler.Stop joining the snap handlers before this
	// runs), which is correct today but fragile to reordering. hvmSnapMu is released before Wait so a waiter
	// can still take it in releaseHvmSnapWaiterSlot — no deadlock.
	bc.hvmSnapMu.Lock()
	bc.stopping.Store(true)
	bc.hvmSnapMu.Unlock()
	bc.hvmSnapWg.Wait()
}

// Stop stops the blockchain service. If any imports are currently in progress
// it will abort them using the procInterrupt.
func (bc *BlockChain) Stop() {
	bc.stopWithoutSaving()

	// Ensure that the entirety of the state snapshot is journaled to disk.
	var snapBase common.Hash
	if bc.snaps != nil {
		var err error
		if snapBase, err = bc.snaps.Journal(bc.CurrentBlock().Root); err != nil {
			log.Error("Failed to journal state snapshot", "err", err)
		}
		bc.snaps.Release()
	}
	if bc.triedb.Scheme() == rawdb.PathScheme {
		// Ensure that the in-memory trie nodes are journaled to disk properly.
		if err := bc.triedb.Journal(bc.CurrentBlock().Root); err != nil {
			log.Info("Failed to journal in-memory trie nodes", "err", err)
		}
	} else {
		// Ensure the state of a recent block is also stored to disk before exiting.
		// We're writing three different states to catch different restart scenarios:
		//  - HEAD:     So we don't need to reprocess any blocks in the general case
		//  - HEAD-1:   So we don't do large reorgs if our HEAD becomes an uncle
		//  - HEAD-127: So we have a hard limit on the number of blocks reexecuted
		if !bc.cfg.ArchiveMode {
			triedb := bc.triedb

			for _, offset := range []uint64{0, 1, state.TriesInMemory - 1} {
				if number := bc.CurrentBlock().Number.Uint64(); number > offset {
					recent := bc.GetBlockByNumber(number - offset)

					log.Info("Writing cached state to disk", "block", recent.Number(), "hash", recent.Hash(), "root", recent.Root())
					if err := triedb.Commit(recent.Root(), true); err != nil {
						log.Error("Failed to commit recent state trie", "err", err)
					}
				}
			}
			if snapBase != (common.Hash{}) {
				log.Info("Writing snapshot state to disk", "root", snapBase)
				if err := triedb.Commit(snapBase, true); err != nil {
					log.Error("Failed to commit recent state trie", "err", err)
				}
			}
			for !bc.triegc.Empty() {
				triedb.Dereference(bc.triegc.PopItem())
			}
			if _, nodes, _ := triedb.Size(); nodes != 0 { // all memory is contained within the nodes return for hashdb
				log.Error("Dangling trie nodes after full cleanup")
			}
		}
	}
	// Allow tracers to clean-up and release resources.
	if bc.logger != nil && bc.logger.OnClose != nil {
		bc.logger.OnClose()
	}
	// Close the trie database, release all the held resources as the last step.
	if err := bc.triedb.Close(); err != nil {
		log.Error("Failed to close trie database", "err", err)
	}
	log.Info("Blockchain stopped")
}

// InterruptInsert interrupts all insertion methods, causing them to return
// errInsertionInterrupted as soon as possible, or resume the chain insertion
// if required.
func (bc *BlockChain) InterruptInsert(on bool) {
	if on {
		bc.procInterrupt.Store(true)
	} else {
		bc.procInterrupt.Store(false)
	}
}

// insertStopped returns true after StopInsert has been called.
func (bc *BlockChain) insertStopped() bool {
	return bc.procInterrupt.Load()
}

// WriteStatus status of write
type WriteStatus byte

const (
	NonStatTy WriteStatus = iota
	CanonStatTy
	SideStatTy
)

// InsertReceiptChain inserts a batch of blocks along with their receipts into
// the database. Unlike InsertChain, this function does not verify the state root
// in the blocks. It is used exclusively for snap sync. All the inserted blocks
// will be regarded as canonical, chain reorg is not supported.
//
// The optional ancientLimit can also be specified and chain segment before that
// will be directly stored in the ancient, getting rid of the chain migration.
func (bc *BlockChain) InsertReceiptChain(blockChain types.Blocks, receiptChain []rlp.RawValue, ancientLimit uint64) (int, error) {
	// Verify the supplied headers before insertion without lock
	var headers []*types.Header
	for _, block := range blockChain {
		headers = append(headers, block.Header())
		// Here we also validate that blob transactions in the block do not
		// contain a sidecar. While the sidecar does not affect the block hash
		// or tx hash, sending blobs within a block is not allowed.
		for txIndex, tx := range block.Transactions() {
			if tx.Type() == types.BlobTxType && tx.BlobTxSidecar() != nil {
				return 0, fmt.Errorf("block #%d contains unexpected blob sidecar in tx at index %d", block.NumberU64(), txIndex)
			}
		}
	}
	if n, err := bc.hc.ValidateHeaderChain(headers); err != nil {
		return n, err
	}
	// Hold the mutation lock
	if !bc.chainmu.TryLock() {
		return 0, errChainStopped
	}
	defer bc.chainmu.Unlock()

	var (
		stats = struct{ processed, ignored int32 }{}
		start = time.Now()
		size  = int64(0)
	)
	// updateHead updates the head header and head snap block flags.
	updateHead := func(header *types.Header) error {
		batch := bc.db.NewBatch()
		hash := header.Hash()
		rawdb.WriteHeadHeaderHash(batch, hash)
		rawdb.WriteHeadFastBlockHash(batch, hash)
		if err := batch.Write(); err != nil {
			return err
		}
		bc.hc.currentHeader.Store(header)
		bc.currentSnapBlock.Store(header)
		headHeaderGauge.Update(header.Number.Int64())
		headFastBlockGauge.Update(header.Number.Int64())

		// OPStack addition
		updateOptimismBlockMetrics(header)
		return nil
	}
	// writeAncient writes blockchain and corresponding receipt chain into ancient store.
	//
	// this function only accepts canonical chain data. All side chain will be reverted
	// eventually.
	writeAncient := func(blockChain types.Blocks, receiptChain []rlp.RawValue) (int, error) {
		// Ensure genesis is in the ancient store
		if blockChain[0].NumberU64() == 1 {
			if frozen, _ := bc.db.Ancients(); frozen == 0 {
				writeSize, err := rawdb.WriteAncientBlocks(bc.db, []*types.Block{bc.genesisBlock}, []rlp.RawValue{rlp.EmptyList})
				if err != nil {
					log.Error("Error writing genesis to ancients", "err", err)
					return 0, err
				}
				size += writeSize
				log.Info("Wrote genesis to ancients")
			}
		}
		// Write all chain data to ancients.
		writeSize, err := rawdb.WriteAncientBlocks(bc.db, blockChain, receiptChain)
		if err != nil {
			log.Error("Error importing chain data to ancients", "err", err)
			return 0, err
		}
		size += writeSize

		// Sync the ancient store explicitly to ensure all data has been flushed to disk.
		if err := bc.db.SyncAncient(); err != nil {
			return 0, err
		}
		// Write hash to number mappings
		batch := bc.db.NewBatch()
		for _, block := range blockChain {
			rawdb.WriteHeaderNumber(batch, block.Hash(), block.NumberU64())
		}
		if err := batch.Write(); err != nil {
			return 0, err
		}
		// Update the current snap block because all block data is now present in DB.
		if err := updateHead(blockChain[len(blockChain)-1].Header()); err != nil {
			return 0, err
		}
		stats.processed += int32(len(blockChain))
		return 0, nil
	}

	// writeLive writes the blockchain and corresponding receipt chain to the active store.
	//
	// Notably, in different snap sync cycles, the supplied chain may partially reorganize
	// existing local chain segments (reorg around the chain tip). The reorganized part
	// will be included in the provided chain segment, and stale canonical markers will be
	// silently rewritten. Therefore, no explicit reorg logic is needed.
	writeLive := func(blockChain types.Blocks, receiptChain []rlp.RawValue) (int, error) {
		var (
			skipPresenceCheck = false
			batch             = bc.db.NewBatch()
		)
		for i, block := range blockChain {
			// Short circuit insertion if shutting down or processing failed
			if bc.insertStopped() {
				return 0, errInsertionInterrupted
			}
			if !skipPresenceCheck {
				// Ignore if the entire data is already known
				if bc.HasBlock(block.Hash(), block.NumberU64()) {
					stats.ignored++
					continue
				} else {
					// If block N is not present, neither are the later blocks.
					// This should be true, but if we are mistaken, the shortcut
					// here will only cause overwriting of some existing data
					skipPresenceCheck = true
				}
			}
			// Write all the data out into the database
			rawdb.WriteCanonicalHash(batch, block.Hash(), block.NumberU64())
			rawdb.WriteBlock(batch, block)
			rawdb.WriteRawReceipts(batch, block.Hash(), block.NumberU64(), receiptChain[i])

			// Write everything belongs to the blocks into the database. So that
			// we can ensure all components of body is completed(body, receipts)
			// except transaction indexes(will be created once sync is finished).
			if batch.ValueSize() >= ethdb.IdealBatchSize {
				if err := batch.Write(); err != nil {
					return 0, err
				}
				size += int64(batch.ValueSize())
				batch.Reset()
			}
			stats.processed++
		}
		// Write everything belongs to the blocks into the database. So that
		// we can ensure all components of body is completed(body, receipts,
		// tx indexes)
		if batch.ValueSize() > 0 {
			size += int64(batch.ValueSize())
			if err := batch.Write(); err != nil {
				return 0, err
			}
		}
		if err := updateHead(blockChain[len(blockChain)-1].Header()); err != nil {
			return 0, err
		}
		return 0, nil
	}

	// Split the supplied blocks into two groups, according to the
	// given ancient limit.
	index := sort.Search(len(blockChain), func(i int) bool {
		return blockChain[i].NumberU64() >= ancientLimit
	})
	if index > 0 {
		if n, err := writeAncient(blockChain[:index], receiptChain[:index]); err != nil {
			if err == errInsertionInterrupted {
				return 0, nil
			}
			return n, err
		}
	}
	if index != len(blockChain) {
		if n, err := writeLive(blockChain[index:], receiptChain[index:]); err != nil {
			if err == errInsertionInterrupted {
				return 0, nil
			}
			return n, err
		}
	}
	var (
		head    = blockChain[len(blockChain)-1]
		context = []interface{}{
			"count", stats.processed, "elapsed", common.PrettyDuration(time.Since(start)),
			"number", head.Number(), "hash", head.Hash(), "age", common.PrettyAge(time.Unix(int64(head.Time()), 0)),
			"size", common.StorageSize(size),
		}
	)
	if stats.ignored > 0 {
		context = append(context, []interface{}{"ignored", stats.ignored}...)
	}
	log.Debug("Imported new block receipts", context...)
	return 0, nil
}

// writeBlockWithoutState writes only the block and its metadata to the database,
// but does not write any state. This is used to construct competing side forks
// up to the point where they exceed the canonical total difficulty.
func (bc *BlockChain) writeBlockWithoutState(block *types.Block) (err error) {
	if bc.insertStopped() {
		return errInsertionInterrupted
	}
	batch := bc.db.NewBatch()
	rawdb.WriteBlock(batch, block)
	if err := batch.Write(); err != nil {
		log.Crit("Failed to write block into disk", "err", err)
	}
	return nil
}

// writeKnownBlock updates the head block flag with a known block
// and introduces chain reorg if necessary.
func (bc *BlockChain) writeKnownBlock(block *types.Block) error {
	current := bc.CurrentBlock()
	if block.ParentHash() != current.Hash() {
		if err := bc.reorg(current, block.Header()); err != nil {
			return err
		}
	}
	bc.writeHeadBlock(block)
	return nil
}

// writeBlockWithState writes block, metadata and corresponding state data to the
// database.
func (bc *BlockChain) writeBlockWithState(block *types.Block, receipts []*types.Receipt, statedb *state.StateDB) error {
	if !bc.HasHeader(block.ParentHash(), block.NumberU64()-1) {
		return consensus.ErrUnknownAncestor
	}
	// Irrelevant of the canonical status, write the block itself to the database.
	//
	// Note all the components of block(hash->number map, header, body, receipts)
	// should be written atomically. BlockBatch is used for containing all components.
	blockBatch := bc.db.NewBatch()
	rawdb.WriteBlock(blockBatch, block)
	rawdb.WriteReceipts(blockBatch, block.Hash(), block.NumberU64(), receipts)
	rawdb.WritePreimages(blockBatch, statedb.Preimages())
	if err := blockBatch.Write(); err != nil {
		log.Crit("Failed to write block into disk", "err", err)
	}
	// Commit all cached state changes into underlying memory database.
	root, stateUpdate, err := statedb.CommitWithUpdate(block.NumberU64(), bc.chainConfig.IsEIP158(block.Number()), bc.chainConfig.IsCancun(block.Number(), block.Time()))
	if err != nil {
		return err
	}
	// Emit the state update to the state sizestats if it's active
	if bc.stateSizer != nil {
		bc.stateSizer.Notify(stateUpdate)
	}
	// If node is running in path mode, skip explicit gc operation
	// which is unnecessary in this mode.
	if bc.triedb.Scheme() == rawdb.PathScheme {
		return nil
	}
	// If we're running an archive node, always flush
	if bc.cfg.ArchiveMode {
		return bc.triedb.Commit(root, false)
	}
	// Full but not archive node, do proper garbage collection
	bc.triedb.Reference(root, common.Hash{}) // metadata reference to keep trie alive
	bc.triegc.Push(root, -int64(block.NumberU64()))

	// Flush limits are not considered for the first TriesInMemory blocks.
	current := block.NumberU64()
	if current <= state.TriesInMemory {
		return nil
	}
	// If we exceeded our memory allowance, flush matured singleton nodes to disk
	var (
		_, nodes, imgs = bc.triedb.Size() // all memory is contained within the nodes return for hashdb
		limit          = common.StorageSize(bc.cfg.TrieDirtyLimit) * 1024 * 1024
	)
	if nodes > limit || imgs > 4*1024*1024 {
		bc.triedb.Cap(limit - ethdb.IdealBatchSize)
	}
	// Find the next state trie we need to commit
	chosen := current - state.TriesInMemory
	flushInterval := time.Duration(bc.flushInterval.Load())
	// If we exceeded time allowance, flush an entire trie to disk
	if bc.gcproc > flushInterval {
		// If the header is missing (canonical chain behind), we're reorging a low
		// diff sidechain. Suspend committing until this operation is completed.
		header := bc.GetHeaderByNumber(chosen)
		if header == nil {
			log.Warn("Reorg in progress, trie commit postponed", "number", chosen)
		} else {
			// If we're exceeding limits but haven't reached a large enough memory gap,
			// warn the user that the system is becoming unstable.
			if chosen < bc.lastWrite+state.TriesInMemory && bc.gcproc >= 2*flushInterval {
				log.Info("State in memory for too long, committing", "time", bc.gcproc, "allowance", flushInterval, "optimum", float64(chosen-bc.lastWrite)/state.TriesInMemory)
			}
			// Flush an entire trie and restart the counters
			bc.triedb.Commit(header.Root, true)
			bc.lastWrite = chosen
			bc.gcproc = 0
		}
	}
	// Garbage collect anything below our required write retention
	for !bc.triegc.Empty() {
		root, number := bc.triegc.Pop()
		if uint64(-number) > chosen {
			bc.triegc.Push(root, number)
			break
		}
		bc.triedb.Dereference(root)
	}
	return nil
}

// writeBlockAndSetHead is the internal implementation of WriteBlockAndSetHead.
// This function expects the chain mutex to be held.
func (bc *BlockChain) writeBlockAndSetHead(block *types.Block, receipts []*types.Receipt, logs []*types.Log, state *state.StateDB, emitHeadEvent bool) (status WriteStatus, err error) {
	if err := bc.writeBlockWithState(block, receipts, state); err != nil {
		return NonStatTy, err
	}
	currentBlock := bc.CurrentBlock()

	// Reorganise the chain if the parent is not the head block
	if block.ParentHash() != currentBlock.Hash() {
		if err := bc.reorg(currentBlock, block.Header()); err != nil {
			return NonStatTy, err
		}
	}

	// Set new head.
	if status == CanonStatTy {
		log.Info(fmt.Sprintf("Updating hVM header consensus to block %s @ %d in writeBlockAndSetHead()",
			block.Hash().String(), block.Number().Uint64()))

		// Update hVM lightweight and full node view
		err := bc.updateHvmHeaderConsensus(block.Header(), true)
		if err != nil {
			if errors.Is(err, consensus.ErrInvalidHVMBlockFormat) || errors.Is(err, consensus.ErrInvalidHVMHeaders) {
				// Block is bad and was already banned/reported by the updateHvmHeaderConsensus function
				log.Error(fmt.Sprintf("Block %s @ %d contains invalid hVM state transition, unable to set "+
					"as new head", block.Hash().String(), block.Number().Uint64()), "err", err)

				return NonStatTy, err
			} else if errors.Is(err, consensus.ErrUnknownAncestor) {
				// No route from current head to new set head was found
				log.Error(fmt.Sprintf("Unable to update hVM header consensus to blcok %s @ %d as the geometry "+
					"between the current head %s @ %d and the new head could be found", block.Hash().String(),
					block.Number().Uint64(), currentBlock.Hash().String(), currentBlock.Number.Uint64()), "err", err)

				return NonStatTy, err
			} else if errors.Is(err, consensus.ErrCorruptHVMHeaderOnlyModeState) {
				log.Error(fmt.Sprintf("When attempting to update hVM header consensus to block %s @ %d, "+
					"encountered an error which is suspected to be the result of corrupted header-only TBC node "+
					"state, attempting full restore", block.Hash().String(), block.Number().Uint64()), "err", err)

				// Attempt to recover hVM state
				bc.performFullHvmHeaderStateRestore()

				// Try update again
				err := bc.updateHvmHeaderConsensus(block.Header(), true)
				if err != nil {
					if errors.Is(err, consensus.ErrInvalidHVMBlockFormat) || errors.Is(err, consensus.ErrInvalidHVMHeaders) {
						// Contextual-difficulty: the restore cleared a transient fault (e.g. a momentary leveldb IO error
						// the validator mapped to skip -> ErrCorruptHVMHeaderOnlyModeState) and the block is
						// now correctly judged genuinely invalid. This is a clean bad block (already reported
						// by updateHvmHeaderConsensus) — return NonStatTy like the pre-restore arm above, not
						// log.Crit, which would escalate a designed reject into a fleet halt.
						log.Error(fmt.Sprintf("Block %s @ %d contains an invalid hVM state transition (confirmed "+
							"after header-only TBC restore); reporting bad block, not advancing head",
							block.Hash().String(), block.Number().Uint64()), "err", err)
						return NonStatTy, err
					} else if isHvmFullNodeBehind(err) {
						// A transient full-TBC BTC-sync lag after the restore is not fatal — the
						// lightweight (consensus) view is correct; the full-node indexer catches up on
						// a later import. (See isHvmFullNodeBehind.)
						log.Warn(fmt.Sprintf("Full TBC node is behind block %s @ %d after header-only TBC node "+
							"restore; its indexers will catch up on a later import (deferred, not fatal)",
							block.Hash().String(), block.Number().Uint64()), "err", err)
					} else {
						// Still getting an error after recovery (incl. a persistent ErrCorruptHVMHeaderOnlyModeState
						// that survived a full restore), exit with crit
						log.Crit(fmt.Sprintf("Updating hVM header consensus to block %s @ %d still failed after "+
							"header-only TBC node restore.", block.Hash().String(), block.Number().Uint64()), "err", err)
					}
				}
			} else if isHvmFullNodeBehind(err) {
				// Transient full-TBC BTC-sync lag, not fatal — the lightweight (consensus) view is already
				// updated; the full-node indexer catches up on a later import. Continue (set the head)
				// rather than crash. (See isHvmFullNodeBehind.)
				log.Warn(fmt.Sprintf("Full TBC node is behind block %s @ %d in writeBlockAndSetHead(); "+
					"its indexers will catch up on a later import (deferred, not fatal)",
					block.Hash().String(), block.Number().Uint64()), "err", err)
			} else {
				// Unexpected error, exit on crit
				log.Crit(fmt.Sprintf("Encountered unexpected error when attempting to update hVM header consensus "+
					"to block %s @ %d", block.Hash().String(), block.Number().Uint64()), "err", err)
			}
		}
		log.Info(fmt.Sprintf("Updated full TBC node indexers to reflect EVM block %s @ %d",
			block.Hash().String(), block.NumberU64()))
	} else {
		log.Info(fmt.Sprintf("In writeBlockAndSetHead, EVM block %s @ %d is not Canon, not updating hVM state",
			block.Hash().String(), block.NumberU64()))
	}
	bc.futureBlocks.Remove(block.Hash())
	bc.writeHeadBlock(block)

	bc.chainFeed.Send(ChainEvent{
		Header:       block.Header(),
		Receipts:     receipts,
		Transactions: block.Transactions(),
	})

	if len(logs) > 0 {
		bc.logsFeed.Send(logs)
	}
	// In theory, we should fire a ChainHeadEvent when we inject
	// a canonical block, but sometimes we can insert a batch of
	// canonical blocks. Avoid firing too many ChainHeadEvents,
	// we will fire an accumulated ChainHeadEvent and disable fire
	// event here.
	if emitHeadEvent {
		bc.chainHeadFeed.Send(ChainHeadEvent{Header: block.Header()})
	}
	return CanonStatTy, nil
}

// InsertChain attempts to insert the given batch of blocks in to the canonical
// chain or, otherwise, create a fork. If an error is returned it will return
// the index number of the failing block as well an error describing what went
// wrong. After insertion is done, all accumulated events will be fired.
func (bc *BlockChain) InsertChain(chain types.Blocks) (int, error) {
	// Sanity check that we have something meaningful to import
	if len(chain) == 0 {
		return 0, nil
	}

	// Do a sanity check that the provided chain is actually ordered and linked.
	for i := 1; i < len(chain); i++ {
		block, prev := chain[i], chain[i-1]
		if block.NumberU64() != prev.NumberU64()+1 || block.ParentHash() != prev.Hash() {
			log.Error("Non contiguous block insert",
				"number", block.Number(),
				"hash", block.Hash(),
				"parent", block.ParentHash(),
				"prevnumber", prev.Number(),
				"prevhash", prev.Hash(),
			)
			return 0, fmt.Errorf("non contiguous insert: item %d is #%d [%x..], item %d is #%d [%x..] (parent [%x..])", i-1, prev.NumberU64(),
				prev.Hash().Bytes()[:4], i, block.NumberU64(), block.Hash().Bytes()[:4], block.ParentHash().Bytes()[:4])
		}
	}
	// Pre-checks passed, start the full block imports
	if !bc.chainmu.TryLock() {
		return 0, errChainStopped
	}
	defer bc.chainmu.Unlock()
	start := chain[0]
	end := chain[len(chain)-1]
	log.Info(fmt.Sprintf("InsertChain called with blocks %s @ %d through %s @ %d",
		start.Hash().String(), start.NumberU64(), end.Hash().String(), start.NumberU64()))
	_, n, err := bc.insertChain(chain, true, false) // No witness collection for mass inserts (would get super large)
	return n, err
}

// insertChain is the internal implementation of InsertChain, which assumes that
// 1) chains are contiguous, and 2) The chain mutex is held.
//
// This method is split out so that import batches that require re-injecting
// historical blocks can do so without releasing the lock, which could lead to
// racey behaviour. If a sidechain import is in progress, and the historic state
// is imported, but then new canon-head is added before the actual sidechain
// completes, then the historic state could be pruned again
func (bc *BlockChain) insertChain(chain types.Blocks, setHead bool, makeWitness bool) (*stateless.Witness, int, error) {
	// If the chain is terminating, don't even bother starting up.
	if bc.insertStopped() {
		return nil, 0, nil
	}

	if atomic.AddInt32(&bc.blockProcCounter, 1) == 1 {
		bc.blockProcFeed.Send(true)
	}
	defer func() {
		if atomic.AddInt32(&bc.blockProcCounter, -1) == 0 {
			bc.blockProcFeed.Send(false)
		}
	}()

	// hVM holding-pen lifetime. tempBlocks/tempHeaders bridge access to blocks/headers that the hVM
	// consensus-update machinery (updateHvmHeaderConsensus and its apply/unapply/walk helpers, reached
	// via getBlockFromDiskOrHoldingPen/getHeaderFromDiskOrHoldingPen) needs while this block is in flight
	// — after it is added to the pen below but before it is durably written to disk inside its
	// ProcessBlock. The store below is the sole writer of these maps, and insertChain always runs under
	// chainmu (as does every pen reader), so clearing here cannot race a reader. The entries are only
	// needed for the duration of this call: every successfully-processed block is written to rawdb within
	// its ProcessBlock, so once this call returns the disk-first accessors find it without the pen; a
	// failed/rejected block must not be found and is correctly dropped. Clearing on return bounds the pen
	// to a single in-flight batch; without it the maps grow unbounded for the node's lifetime (a full
	// *types.Block + *types.Header per distinct hash ever imported) -> heap exhaustion / OOM. In-call
	// behaviour is unchanged: every entry stays present for the whole loop below.
	defer func() {
		clear(bc.tempBlocks)
		clear(bc.tempHeaders)
	}()

	// Start a parallel signature recovery (signer will fluke on fork transition, minimal perf loss)
	SenderCacher().RecoverFromBlocks(types.MakeSigner(bc.chainConfig, chain[0].Number(), chain[0].Time()), chain)

	var (
		stats     = insertStats{startTime: mclock.Now()}
		lastCanon *types.Block
	)
	// Fire a single chain head event if we've progressed the chain
	defer func() {
		if lastCanon != nil && bc.CurrentBlock().Hash() == lastCanon.Hash() {
			bc.chainHeadFeed.Send(ChainHeadEvent{Header: lastCanon.Header()})
		}
	}()
	// Start the parallel header verifier
	headers := make([]*types.Header, len(chain))
	for i, block := range chain {
		headers[i] = block.Header()
	}
	abort, results := bc.engine.VerifyHeaders(bc, headers)
	defer close(abort)

	// Peek the error for the first block to decide the directing import logic
	it := newInsertIterator(chain, results, bc.validator)
	block, err := it.next()

	// Left-trim all the known blocks that don't need to build snapshot
	if bc.skipBlock(err, it) {
		// First block (and state) is known
		//   1. We did a roll-back, and should now do a re-import
		//   2. The block is stored as a sidechain, and is lying about it's stateroot, and passes a stateroot
		//      from the canonical chain, which has not been verified.
		// Skip all known blocks that are behind us.
		current := bc.CurrentBlock()
		for block != nil && bc.skipBlock(err, it) {
			if block.NumberU64() > current.Number.Uint64() || bc.GetCanonicalHash(block.NumberU64()) != block.Hash() {
				break
			}
			log.Debug("Ignoring already known block", "number", block.Number(), "hash", block.Hash())
			stats.ignored++

			block, err = it.next()
		}
		// The remaining blocks are still known blocks, the only scenario here is:
		// During the snap sync, the pivot point is already submitted but rollback
		// happens. Then node resets the head full block to a lower height via `rollback`
		// and leaves a few known blocks in the database.
		//
		// When node runs a snap sync again, it can re-import a batch of known blocks via
		// `insertChain` while a part of them have higher total difficulty than current
		// head full block(new pivot point).
		for block != nil && bc.skipBlock(err, it) {
			log.Debug("Writing previously known block", "number", block.Number(), "hash", block.Hash())
			if err := bc.writeKnownBlock(block); err != nil {
				return nil, it.index, err
			}
			lastCanon = block

			block, err = it.next()
		}
		// Falls through to the block import
	}
	switch {
	// First block is pruned
	case errors.Is(err, consensus.ErrPrunedAncestor):
		if setHead {
			// First block is pruned, insert as sidechain and reorg only if TD grows enough
			log.Debug("Pruned ancestor, inserting as sidechain", "number", block.Number(), "hash", block.Hash())
			return bc.insertSideChain(block, it, makeWitness)
		} else {
			// We're post-merge and the parent is pruned, try to recover the parent state
			log.Debug("Pruned ancestor", "number", block.Number(), "hash", block.Hash())
			_, err := bc.recoverAncestors(block, makeWitness)
			return nil, it.index, err
		}
	// Some other error(except ErrKnownBlock) occurred, abort.
	// ErrKnownBlock is allowed here since some known blocks
	// still need re-execution to generate snapshots that are missing
	case err != nil && !errors.Is(err, ErrKnownBlock):
		stats.ignored += len(it.chain)
		bc.reportBlock(block, nil, err)
		return nil, it.index, err
	}
	// Track the singleton witness from this chain insertion (if any)
	var witness *stateless.Witness

	for ; block != nil && err == nil || errors.Is(err, ErrKnownBlock); block, err = it.next() {
		// Add this block to temporary holding pen so hVM consensus update functions have access
		// to it.
		bc.tempBlocks[block.Hash().String()] = block
		bc.tempHeaders[block.Hash().String()] = block.Header()

		// If the chain is terminating, stop processing blocks
		if bc.insertStopped() {
			log.Debug("Abort during block processing")
			break
		}
		// If the block is known (in the middle of the chain), it's a special case for
		// Clique blocks where they can share state among each other, so importing an
		// older block might complete the state of the subsequent one. In this case,
		// just skip the block (we already validated it once fully (and crashed), since
		// its header and body was already in the database). But if the corresponding
		// snapshot layer is missing, forcibly rerun the execution to build it.
		if bc.skipBlock(err, it) {
			logger := log.Debug
			if bc.chainConfig.Clique == nil {
				logger = log.Warn
			}
			logger("Inserted known block", "number", block.Number(), "hash", block.Hash(),
				"uncles", len(block.Uncles()), "txs", len(block.Transactions()), "gas", block.GasUsed(),
				"root", block.Root())

			// Special case. Commit the empty receipt slice if we meet the known
			// block in the middle. It can only happen in the clique chain. Whenever
			// we insert blocks via `insertSideChain`, we only commit `td`, `header`
			// and `body` if it's non-existent. Since we don't have receipts without
			// reexecution, so nothing to commit. But if the sidechain will be adopted
			// as the canonical chain eventually, it needs to be reexecuted for missing
			// state, but if it's this special case here(skip reexecution) we will lose
			// the empty receipt entry.
			if len(block.Transactions()) == 0 {
				rawdb.WriteReceipts(bc.db, block.Hash(), block.NumberU64(), nil)
			} else {
				log.Error("Please file an issue, skip known block execution without receipt",
					"hash", block.Hash(), "number", block.NumberU64())
			}
			if err := bc.writeKnownBlock(block); err != nil {
				return nil, it.index, err
			}
			stats.processed++
			if bc.logger != nil && bc.logger.OnSkippedBlock != nil {
				bc.logger.OnSkippedBlock(tracing.BlockEvent{
					Block:     block,
					Finalized: bc.CurrentFinalBlock(),
					Safe:      bc.CurrentSafeBlock(),
				})
			}
			// We can assume that logs are empty here, since the only way for consecutive
			// Clique blocks to have the same state is if there are no transactions.
			lastCanon = block
			continue
		}
		// Retrieve the parent block and it's state to execute on top
		parent := it.previous()
		if parent == nil {
			parent = bc.GetHeader(block.ParentHash(), block.NumberU64()-1)
		}
		// The traced section of block import.
		start := time.Now()
		res, err := bc.ProcessBlock(parent.Root, block, setHead, makeWitness && len(chain) == 1)
		if err != nil {
			return nil, it.index, err
		}
		// Report the import stats before returning the various results
		stats.processed++
		stats.usedGas += res.usedGas
		witness = res.witness

		var snapDiffItems, snapBufItems common.StorageSize
		if bc.snaps != nil {
			snapDiffItems, snapBufItems = bc.snaps.Size()
		}
		trieDiffNodes, trieBufNodes, _ := bc.triedb.Size()
		stats.report(chain, it.index, snapDiffItems, snapBufItems, trieDiffNodes, trieBufNodes, setHead)

		// Print confirmation that a future fork is scheduled, but not yet active.
		bc.logForkReadiness(block)

		if !setHead {
			// After merge we expect few side chains. Simply count
			// all blocks the CL gives us for GC processing time
			bc.gcproc += res.procTime
			return witness, it.index, nil // Direct block insertion of a single block
		}
		switch res.status {
		case CanonStatTy:
			log.Debug("Inserted new block", "number", block.Number(), "hash", block.Hash(),
				"uncles", len(block.Uncles()), "txs", len(block.Transactions()), "gas", block.GasUsed(),
				"elapsed", common.PrettyDuration(time.Since(start)),
				"root", block.Root())

			lastCanon = block

			// Only count canonical blocks for GC processing time
			bc.gcproc += res.procTime

		case SideStatTy:
			log.Debug("Inserted forked block", "number", block.Number(), "hash", block.Hash(),
				"diff", block.Difficulty(), "elapsed", common.PrettyDuration(time.Since(start)),
				"txs", len(block.Transactions()), "gas", block.GasUsed(), "uncles", len(block.Uncles()),
				"root", block.Root())

		default:
			// This in theory is impossible, but lets be nice to our future selves and leave
			// a log, instead of trying to track down blocks imports that don't emit logs.
			log.Warn("Inserted block with unknown status", "number", block.Number(), "hash", block.Hash(),
				"diff", block.Difficulty(), "elapsed", common.PrettyDuration(time.Since(start)),
				"txs", len(block.Transactions()), "gas", block.GasUsed(), "uncles", len(block.Uncles()),
				"root", block.Root())
		}
	}

	stats.ignored += it.remaining()
	return witness, it.index, err
}

// blockProcessingResult is a summary of block processing
// used for updating the stats.
type blockProcessingResult struct {
	usedGas  uint64
	procTime time.Duration
	status   WriteStatus
	witness  *stateless.Witness
}

func (bpr *blockProcessingResult) Witness() *stateless.Witness {
	return bpr.witness
}

// ProcessBlockForWitness runs ProcessBlock for the read-only debug execution-witness RPCs
// (debug_executionWitness / debug_executionWitnessByHash) under chainmu, with setHead=false.
//
// Those RPCs look read-only, but ProcessBlock transiently mutates the shared hVM lightweight TBC node
// (`bc.tbcHeaderNode`): to execute the block's hVM precompiles against the correct Bitcoin view it moves the
// lightweight view to the block's parent state and applies the block, then — because setHead=false — usually
// reverts it back to the former canonical state (the !setHead branch near the end of ProcessBlock). The
// hazard is the race: every other ProcessBlock caller (the import path, via insertChain) holds chainmu, and
// all other lightweight-TBC mutation respects it; calling ProcessBlock off-chainmu from the RPC goroutine
// would let its transient mutate/revert run concurrently with an import's ProcessBlock on the same node +
// EVM state. Taking chainmu here serializes witness generation against import. The lock is
// `chainmu.TryLock()`, mirroring insertChain/SetCanonical: per syncx.ClosableMutex semantics it blocks until
// chainmu is free — so a witness request during an in-flight import waits for it — and returns false only
// when the mutex is closed (the chain is stopping), which we surface as errChainStopped. Upstream
// go-ethereum has no shared-mutable hVM node, so its witness RPC needs no lock; this wrapper adds the lock
// that the fork's shared lightweight TBC node requires.
//
// State on return: ProcessBlock's setHead=false revert restores the lightweight view to the former
// canonical state in every case except one — when the witnessed block is a direct child of the current
// canonical head, an import-path optimization (the "not reverting hVM progression" special case at the
// !setHead branch) deliberately leaves the view advanced to that (non-canonical) block. We deliberately do
// not re-assert the view here: re-asserting would re-drive the consensus walk-back machinery
// (updateHvmHeaderConsensus / walkHvmHeaderConsensusBack / unapplyHvmHeaderConsensusUpdate), which log.Crit
// on any non-corruption TBC-store error — so re-asserting could crash the process on a transient store
// fault. Not worth it, because the residual drift is not a new state class: the import
// path's own child-of-head optimization routinely leaves exactly this advanced view between consecutive
// imports, and it self-heals on the next import's setHead (which re-bases the view regardless). The only
// delta from a witness call is the window's timing on an otherwise-idle node, which restart recovery
// (SetupHvmHeaderNode finds the persisted state-id on a block that is on disk) and the next import repair.
func (bc *BlockChain) ProcessBlockForWitness(parentRoot common.Hash, block *types.Block) (*blockProcessingResult, error) {
	if !bc.chainmu.TryLock() {
		return nil, errChainStopped
	}
	defer bc.chainmu.Unlock()
	return bc.ProcessBlock(parentRoot, block, false, true)
}

// ProcessBlock executes and validates the given block. If there was no error
// it writes the block and associated state to database.
func (bc *BlockChain) ProcessBlock(parentRoot common.Hash, block *types.Block, setHead bool, makeWitness bool) (_ *blockProcessingResult, blockEndErr error) {
	var (
		err       error
		startTime = time.Now()
		statedb   *state.StateDB
		interrupt atomic.Bool
	)
	defer interrupt.Store(true) // terminate the prefetch at the end

	if bc.cfg.NoPrefetch {
		statedb, err = state.New(parentRoot, bc.statedb)
		if err != nil {
			return nil, err
		}
	} else {
		// If prefetching is enabled, run that against the current state to pre-cache
		// transactions and probabilistically some of the account/storage trie nodes.
		//
		// Note: the main processor and prefetcher share the same reader with a local
		// cache for mitigating the overhead of state access.
		prefetch, process, err := bc.statedb.ReadersWithCacheStats(parentRoot)
		if err != nil {
			return nil, err
		}
		throwaway, err := state.NewWithReader(parentRoot, bc.statedb, prefetch)
		if err != nil {
			return nil, err
		}
		statedb, err = state.NewWithReader(parentRoot, bc.statedb, process)
		if err != nil {
			return nil, err
		}
		// Upload the statistics of reader at the end
		defer func() {
			stats := prefetch.GetStats()
			accountCacheHitPrefetchMeter.Mark(stats.AccountHit)
			accountCacheMissPrefetchMeter.Mark(stats.AccountMiss)
			storageCacheHitPrefetchMeter.Mark(stats.StorageHit)
			storageCacheMissPrefetchMeter.Mark(stats.StorageMiss)
			stats = process.GetStats()
			accountCacheHitMeter.Mark(stats.AccountHit)
			accountCacheMissMeter.Mark(stats.AccountMiss)
			storageCacheHitMeter.Mark(stats.StorageHit)
			storageCacheMissMeter.Mark(stats.StorageMiss)
		}()

		go func(start time.Time, throwaway *state.StateDB, block *types.Block) {
			// Disable tracing for prefetcher executions.
			vmCfg := bc.cfg.VmConfig
			vmCfg.Tracer = nil
			bc.prefetcher.Prefetch(block, throwaway, vmCfg, &interrupt)

			blockPrefetchExecuteTimer.Update(time.Since(start))
			if interrupt.Load() {
				blockPrefetchInterruptMeter.Mark(1)
			}
		}(time.Now(), throwaway, block)
	}

	// If we are past Byzantium, enable prefetching to pull in trie node paths
	// while processing transactions. Before Byzantium the prefetcher is mostly
	// useless due to the intermediate root hashing after each transaction.
	var (
		witness      *stateless.Witness
		witnessStats *stateless.WitnessStats
	)
	if bc.chainConfig.IsByzantium(block.Number()) {
		// Generate witnesses either if we're self-testing, or if it's the
		// only block being inserted. A bit crude, but witnesses are huge,
		// so we refuse to make an entire chain of them.
		if bc.cfg.VmConfig.StatelessSelfValidation || makeWitness {
			witness, err = stateless.NewWitness(block.Header(), bc)
			if err != nil {
				return nil, err
			}
			if bc.cfg.VmConfig.EnableWitnessStats {
				witnessStats = stateless.NewWitnessStats()
			}
		}
		statedb.StartPrefetcher("chain", witness, witnessStats)
		defer statedb.StopPrefetcher()
	}

	if bc.logger != nil && bc.logger.OnBlockStart != nil {
		bc.logger.OnBlockStart(tracing.BlockEvent{
			Block:     block,
			Finalized: bc.CurrentFinalBlock(),
			Safe:      bc.CurrentSafeBlock(),
		})
	}
	if bc.logger != nil && bc.logger.OnBlockEnd != nil {
		defer func() {
			bc.logger.OnBlockEnd(blockEndErr)
		}()
	}

	// Process block using the parent state as reference point
	pstart := time.Now()
	// Before processing a block:
	//   1. Check whether header-only TBC node's state is at this block's parent; if it's not move it
	//      here temporarily and store the former state to restore to once we're finished processing
	//   2. Apply this block's Bitcoin Attributes Deposited transaction to header-only TBC node's state
	//      (If this results in an error, report/invalidate the block same as an invalid EVM state transition)
	//   3. Update the full TBC node's indexed tip to be 2 blocks behind the header-only TBC node's tip
	//      (If this results in an error, report/invalidate the block same as an invalid EVM state transition)
	//
	// Then after processing a block:
	//   1. If block processing fails or setHead is false, walk header-only TBC node's state to former restore state
	//      Otherwise, leave header-only TBC in progressed state with this block as tip
	//   2. If we walk header-only TBC node's state back, then walk back TBC full node's indexed tip to be 2 blocks
	//      behind the header-only TBC node's tip after the restore

	var tbcHeader *types.Header // Original EVM tip that lightweight TBC knowledge represents to revert to when necessary
	isHvmActivated := false
	isFirstHvmBlock := false
	log.Info(fmt.Sprintf("Processing block %s @ %d", block.Hash().String(), block.NumberU64()))
	// If we are awaiting an hVM snap sync, that will be handled separately in response to a hVM light state P2P msg later
	if bc.hvmEnabled && !bc.isAwaitingHvmSnapSync() {
		var parent *types.Header

		if bc.chainConfig.IsHvm0(block.Time()) {
			log.Debug(fmt.Sprintf("For block %s @ %d, hVM is activated",
				block.Hash().String(), block.NumberU64()))
			isHvmActivated = true
			if block.NumberU64() != 0 {
				log.Debug(fmt.Sprintf("Block != 0, getting parent by hash %s", block.ParentHash()))
				parent = bc.GetHeaderByHash(block.ParentHash())
				if parent == nil {
					// The EVM parent header is absent from the chain DB for a non-genesis block. This never
					// happens on the import path (insertChain resolves and dereferences the parent before
					// calling ProcessBlock), so reaching here means a torn/inconsistent store. Return the
					// recoverable sentinel instead of nil-dereferencing parent.Time and crashing the process:
					// the block import fails cleanly and the corruption is logged.
					log.Error(fmt.Sprintf("Parent %s of hVM block %s @ %d is nil; treating as corrupt hVM state",
						block.ParentHash().String(), block.Hash().String(), block.NumberU64()))
					return nil, consensus.ErrCorruptHVMHeaderOnlyModeState
				}
				if !bc.chainConfig.IsHvm0(parent.Time) {
					// Parent is not hVM0, meaning this block is first activation
					log.Debug(fmt.Sprintf("Block %s @ %d is the hVM activation block",
						block.Hash().String(), block.NumberU64()))
					isFirstHvmBlock = true
				}
			} else {
				// Genesis is first hVM block
				isFirstHvmBlock = true
				log.Info(fmt.Sprintf("Genesis block %s @ %d is the hVM activation block",
					block.Hash().String(), block.NumberU64()))
			}
		}

		if isHvmActivated {
			if !isFirstHvmBlock {
				// Store current state of lightweight TBC to restore to later if necessary
				tbcHeader, err = bc.getHeaderModeTBCEVMHeader()
				if err != nil {
					log.Crit("Error encountered getting EVM block lightweight TBC's state represents", "err", err)
				}
			} // else: tbcHeader will remain nil, check later to know to revert to TBC genesis state rather than state based on EVM block
		}

		if tbcHeader != nil {
			log.Info(fmt.Sprintf("Processing block %s @ %d at timestamp %d, TBC state header is %s @ %d",
				block.Hash().String(), block.Number().Uint64(), block.Time(), tbcHeader.Hash().String(),
				tbcHeader.Number.Uint64()))
		} else if isHvmActivated {
			log.Info(fmt.Sprintf("Processing block %s @ %d at timestamp %d, this is the first hVM state "+
				"transition block", block.Hash().String(), block.Number().Uint64(), block.Time()))
		}

		// First, move lightweight TBC state to parent if this block is not the hVM Phase 0 activation block.
		// The full TBC node doesn't need any intermediate hop to parent consensus, since it only provides
		// linear indexed state based on a Bitcoin tip dictated by the lightweight TBC node. The lightweight
		// TBC node does need to be adjusted to a pre-state based on this block's parent so this block
		// communicates data correct in the context of its parent; otherwise different nodes could disagree
		// on the validity of this block's Bitcoin Attributes Deposited tx based on different lightweight
		// Bitcoin views. updateHvmHeaderConsensus() handles underlying reorganizations of TBC's EVM state
		// (reversing down a fork and up a new branch to the EVM header we specify), but moving the geometry
		// here gives more control over knowing why an error occurred.
		if isHvmActivated && !isFirstHvmBlock {
			if tbcHeader.Hash().Cmp(parent.Hash()) != 0 {
				log.Info(fmt.Sprintf("Lightweight TBC at block %s @ %d, moving to parent %s @ %d",
					tbcHeader.Hash().String(), tbcHeader.Number.Uint64(),
					parent.Hash().String(), parent.Number.Uint64()))
				err := bc.updateHvmHeaderConsensus(parent, false)
				if err != nil {
					if isHvmReapplyRecoverableError(err) {
						// Re-apply (parent-move) onto an already-committed canonical ancestor: the forward walk
						// to `parent` re-judges committed history, so a torn store (ErrCorrupt) or a fresh
						// grandfathered-rule reject (ErrInvalidHVMHeaders/Format) here is recoverable — rebuild
						// from genesis rather than halting the fleet. `parent` is already-committed so a reject
						// is never a genuine bad block.
						bc.recoverReapplyHvmState(fmt.Sprintf("parent-move to %s @ %d in ProcessBlock",
							parent.Hash().String(), parent.Number.Uint64()), err)
						// Unlike the head-set sites (whose target is bc.CurrentBlock()), this site must land the
						// view on `parent`, which during a fork import is a non-tip ancestor != CurrentBlock().
						// performFullHvmHeaderStateRestore rebuilds along the canonical CurrentBlock() lineage
						// only, so we must re-drive the move to `parent` afterward — otherwise the
						// parent-equality sanity check below would re-crit on the CurrentBlock-vs-parent
						// mismatch, merely relocating the halt. The re-drive is a fresh enforce-on call: for a
						// `parent` that is an ancestor of CurrentBlock it is a pure backward walk (no enforcement)
						// and succeeds once the rebuild cleared the torn store; for a fork `parent` it walks back
						// to the common ancestor then forward with enforcement, which can re-reject a fork-branch
						// block whose committed BtcAttr was never enforce-validated (the
						// insertSideChain/writeBlockWithoutState path skips the enforce-on gate).
						if reErr := bc.updateHvmHeaderConsensus(parent, false); reErr != nil {
							if isHvmReapplyRecoverableError(reErr) {
								// Grandfathered-dirty fork-branch history: the rebuild put the view on the
								// canonical lineage but the enforce-on forward walk to this fork `parent` re-judges
								// its committed history invalid, and restore cannot reach a non-canonical parent.
								// We cannot contextualize `parent`, so we cannot process this fork block — reject
								// this import (node-local) rather than halt the fleet, consistent with the other
								// re-apply sites: never fleet-halt on a recoverable reject. (Unreachable on verified-clean
								// mainnet; the view remains on the canonical CurrentBlock() tip, consistent.)
								log.Error(fmt.Sprintf("Cannot move lightweight TBC to fork parent %s @ %d after a "+
									"full restore (grandfathered-dirty fork history); rejecting this block's import "+
									"instead of halting", parent.Hash().String(), parent.Number.Uint64()), "err", reErr)
								bc.reportBlock(block, nil, reErr)
								return nil, reErr
							}
							// Non-recoverable (e.g. persistent corruption the rebuild did not clear): truly fatal.
							log.Crit(fmt.Sprintf("Unable to move lightweight TBC node to parent %s @ %d even "+
								"after a full restore", parent.Hash().String(), parent.Number.Uint64()), "err", reErr)
						}
					} else {
						// This is critical as we should always be able to walk to parent.
						// In future we could attempt a complex TBC recovery here.
						log.Crit(fmt.Sprintf("Unable to move lightweight TBC node to parent %s @ %d",
							parent.Hash().String(), parent.Number.Uint64()), "err", err)
					}
				}
			} else {
				log.Info(fmt.Sprintf("Lightweight TBC is already at parent %s @ %d",
					parent.Hash().String(), parent.Number.Uint64()))
			}
		}

		// Do an extra sanity check that lightweight TBC node is in the correct state, after above logic which
		// should have moved it to the correct state based on the parent of the block we're processing.
		// Incorrect state represents either data corruption or an issue with the reorg logic.
		if isHvmActivated && !isFirstHvmBlock {
			log.Info(fmt.Sprintf("Verifying before applying block %s @ %d, lightweight TBC's state is "+
				"correctly set to direct parent %s @ %d", block.Hash().String(), block.NumberU64(),
				parent.Hash().String(), parent.Number.Uint64()))
			representedBlock, err := bc.getHeaderModeTBCEVMHeader()
			if err != nil {
				// Critical error as this should correctly represent parent after previous code
				log.Crit(fmt.Sprintf("Error, unable to fetch the EVM tip which lightweight TBC state "+
					"currently represents!"), "err", err)
			}
			if representedBlock.Hash().Cmp(parent.Hash()) != 0 {
				stateId, err := bc.tbcHeaderNode.UpstreamStateId(bc.ctx)
				if err != nil {
					// Should never happen since UpstreamStateId is called by getHeaderModeTBCEVMHeader() too
					log.Crit(fmt.Sprintf("Error, lightweight TBC state represents unexpected EVM tip "+
						"%s @ %d, and we encountered an error fetching the upstream state id!",
						representedBlock.Hash().String(), representedBlock.Number.Uint64()), "err", err)
				}
				log.Crit(fmt.Sprintf("Error, lightweight TBC state represents unexpected EVM tip %s @ %d"+
					" with upstream state id %x instead", representedBlock.Hash().String(),
					representedBlock.Number.Uint64(), stateId[:]))
			}
		}

		if isHvmActivated {
			// Process this block's hVM lightweight update first
			err := bc.updateHvmHeaderConsensus(block.Header(), false)
			if err != nil {
				// Ensure block is reported, although generally this would have been done be hVM header consensus update
				bc.reportBlock(block, nil, err)
				return nil, err
			}

			// If lightweight update was successful, do full node update
			err = bc.updateFullTBCToLightweight()
			if err != nil {
				// On error update lightweight TBC node to its previous state
				revertErr := bc.updateHvmHeaderConsensus(tbcHeader, false)
				if revertErr != nil {
					if isHvmReapplyRecoverableError(revertErr) {
						// Re-apply (revert) onto the already-committed pre-insert tbcHeader after a full-node
						// update failure: a torn store (ErrCorrupt) or a grandfathered-rule reject on this
						// committed target is recoverable — rebuild from genesis rather than halting the fleet.
						// Same revert-to-tbcHeader shape as revertHvmStateAfterInvalidBlock and the !setHead
						// revert. The block is deferred / re-judged via the original-err handling below, so
						// leaving the rebuilt view at CurrentBlock() is consistent.
						bc.recoverReapplyHvmState(fmt.Sprintf("updateFullTBCToLightweight-failure revert to "+
							"%s @ %d in ProcessBlock", tbcHeader.Hash().String(), tbcHeader.Number.Uint64()), revertErr)
					} else {
						// Critical error if we cannot restore lightweight TBC state correctly
						log.Crit(fmt.Sprintf("unable to restore lightweight TBC node to previous state when "+
							"inserting block %s @ %d", block.Hash().String(), block.NumberU64()), "err", revertErr)
					}
				}

				if isHvmFullNodeBehind(err) {
					// This might recover, add this block as future block for later processing.
					// Same predicate the head-set path uses (isHvmFullNodeBehind) — single source of
					// truth so the import-defer and head-set-warn handling can never drift apart.
					bc.futureBlocks.Add(block.Hash(), block)
					return nil, err
				} else {
					// Another unexpected error on full TBC node update, crit for now
					log.Crit(fmt.Sprintf("Unexpected error updating Full TBC Node to represent block %s @ %d",
						block.Hash().String(), block.NumberU64()), "err", err)
				}
			}

			si := vm.TBCFullNode.Synced(bc.ctx)
			log.Info(fmt.Sprintf("Lightweight TBC is at canonical BTC block %s @ %d "+
				"(UTXOs: %s @ %d, TXs: %s @ %d)", si.BlockHeader.Hash.String(), si.BlockHeader.Height,
				si.Utxo.Hash.String(), si.Utxo.Height, si.Tx.Hash.String(), si.Tx.Height))
		}
	}

	res, err := bc.processor.Process(block, statedb, bc.cfg.VmConfig)
	if err != nil {
		bc.reportBlock(block, res, err)
		if isHvmActivated {
			// This block's hVM header-consensus update already committed (state-id +
			// any BTC headers), but EVM processing rejected it. Roll TBC back to the pre-insert state
			// so the persisted state-id does not point at a rejected block.
			bc.revertHvmStateAfterInvalidBlock(tbcHeader, block)
		}
		return nil, err
	}

	log.Info(fmt.Sprintf("Performed EVM processing of block %s @ %d",
		block.Hash().String(), block.NumberU64()))
	ptime := time.Since(pstart)

	if err := bc.validator.ValidateState(block, statedb, res, false); err != nil {
		bc.reportBlock(block, res, err)
		if isHvmActivated {
			// See the Process-failure path above — revert the committed TBC advance for
			// this block since state validation rejected it.
			bc.revertHvmStateAfterInvalidBlock(tbcHeader, block)
		}
		return nil, err
	}

	vstart := time.Now()
	vtime := time.Since(vstart)

	// Update the metrics touched during block processing and validation
	accountReadTimer.Update(statedb.AccountReads)                   // Account reads are complete(in processing)
	storageReadTimer.Update(statedb.StorageReads)                   // Storage reads are complete(in processing))
	accountUpdateTimer.Update(statedb.AccountUpdates)               // Account updates are complete(in validation)
	storageUpdateTimer.Update(statedb.StorageUpdates)               // Storage updates are complete(in validation)
	accountHashTimer.Update(statedb.AccountHashes)                  // Account hashes are complete(in validation)
	triehash := statedb.AccountHashes + statedb.StorageHashes       // The time spent on tries hashing
	trieUpdate := statedb.AccountUpdates + statedb.StorageUpdates   // The time spent on tries update
	trieRead := statedb.SnapshotAccountReads + statedb.AccountReads // The time spent on account read
	trieRead += statedb.SnapshotStorageReads + statedb.StorageReads // The time spent on storage read
	blockExecutionTimer.Update(ptime - trieRead)                    // The time spent on EVM processing
	blockValidationTimer.Update(vtime - (triehash + trieUpdate))    // The time spent on block validation                                // The time spent on stateless cross validation

	// Write the block to the chain and get the status.

	if !setHead {
		// Don't set the head, only insert the block
		log.Info(fmt.Sprintf("Writing block %s @ %d to disk but not setting as head.", block.Hash().String(),
			block.NumberU64()))
		// Because this block is not canonical, revert lightweight and full TBC nodes to former state
		if tbcHeader != nil {
			// Special case: if this block builds on the previous canonical block, then do not revert hVM state
			current := bc.currentBlock.Load()
			currentHash := current.Hash()
			parentToNewHash := block.ParentHash()
			log.Info(fmt.Sprintf("Processed block: %s, current: %s, parentToBlock: %s", block.Hash().String(),
				current.Hash().String(), parentToNewHash.String()))
			if bytes.Equal(parentToNewHash[:], currentHash[:]) {
				log.Info(fmt.Sprintf("Inserting block %s @ %d which is direct child of current block, "+
					"not reverting hVM progression", block.Hash().String(), block.NumberU64()))
			} else {
				log.Info(fmt.Sprintf("parentToNewHash %s != block.ParentHash %s, walking back hVM indexers",
					parentToNewHash.String(), currentHash.String()))
				err := bc.updateHvmHeaderConsensus(tbcHeader, true)
				if err != nil {
					if isHvmFullNodeBehind(err) {
						// Transient full-TBC BTC-sync lag, not fatal — the lightweight (consensus) view was
						// reverted successfully (it precedes the full-node advance); the full-node indexer
						// catches up on a later import. (See isHvmFullNodeBehind.)
						log.Warn(fmt.Sprintf("Full TBC node is behind reverted state at block %s @ %d; "+
							"its indexers will catch up on a later import (deferred, not fatal)",
							tbcHeader.Hash().String(), tbcHeader.Number.Uint64()), "err", err)
					} else if isHvmReapplyRecoverableError(err) {
						// Re-apply (revert) onto the already-committed tbcHeader: a torn store or a fresh
						// grandfathered-rule reject on this committed target is recoverable — rebuild from
						// genesis (enforcement off) rather than crashing the fleet.
						bc.recoverReapplyHvmState(fmt.Sprintf("revert lightweight view to %s @ %d in ProcessBlock",
							tbcHeader.Hash().String(), tbcHeader.Number.Uint64()), err)
					} else {
						log.Crit(fmt.Sprintf("Unable to revert lightweight TBC node to represent state at "+
							"block %s @ %d.", tbcHeader.Hash().String(), tbcHeader.Number.Uint64()), "err", err)
					}
				} else {
					log.Info(fmt.Sprintf("Successfully reverted lightweight TBC node to represent state at "+
						"block %s @ %d.", tbcHeader.Hash().String(), tbcHeader.Number.Uint64()))
				}
			}
		} else {
			log.Info("tbcHeader is nil")
		}
	} else {
		log.Info(fmt.Sprintf("Writing block %s @ %d to disk and setting as head, leaving lightweight and "+
			"full node TBC states progressed", block.Hash().String(), block.NumberU64()))
		// Write block and set head will re-do hVM checks but should be quick as we left hVM in correct state
	}

	// If witnesses was generated and stateless self-validation requested, do
	// that now. Self validation should *never* run in production, it's more of
	// a tight integration to enable running *all* consensus tests through the
	// witness builder/runner, which would otherwise be impossible due to the
	// various invalid chain states/behaviors being contained in those tests.
	if witness := statedb.Witness(); witness != nil && bc.cfg.VmConfig.StatelessSelfValidation {
		log.Warn("Running stateless self-validation", "block", block.Number(), "hash", block.Hash())

		// Remove critical computed fields from the block to force true recalculation
		context := block.Header()
		context.Root = common.Hash{}
		context.ReceiptHash = common.Hash{}

		task := types.NewBlockWithHeader(context).WithBody(*block.Body())

		// Run the stateless self-cross-validation
		crossStateRoot, crossReceiptRoot, err := ExecuteStateless(bc.chainConfig, bc.cfg.VmConfig, task, witness)
		if err != nil {
			return nil, fmt.Errorf("stateless self-validation failed: %v", err)
		}
		if crossStateRoot != block.Root() {
			return nil, fmt.Errorf("stateless self-validation root mismatch (cross: %x local: %x)", crossStateRoot, block.Root())
		}
		if crossReceiptRoot != block.ReceiptHash() {
			return nil, fmt.Errorf("stateless self-validation receipt root mismatch (cross: %x local: %x)", crossReceiptRoot, block.ReceiptHash())
		}
	}

	proctime := time.Since(startTime) // processing + validation + cross validation

	// Write the block to the chain and get the status.
	var (
		wstart = time.Now()
		status WriteStatus
	)
	if !setHead {
		// Don't set the head, only insert the block
		err = bc.writeBlockWithState(block, res.Receipts, statedb)
	} else {
		status, err = bc.writeBlockAndSetHead(block, res.Receipts, res.Logs, statedb, false)
	}
	if err != nil {
		return nil, err
	}
	// Report the collected witness statistics
	if witnessStats != nil {
		witnessStats.ReportMetrics(block.NumberU64())
	}

	// Update the metrics touched during block commit
	accountCommitTimer.Update(statedb.AccountCommits)   // Account commits are complete, we can mark them
	storageCommitTimer.Update(statedb.StorageCommits)   // Storage commits are complete, we can mark them
	snapshotCommitTimer.Update(statedb.SnapshotCommits) // Snapshot commits are complete, we can mark them
	triedbCommitTimer.Update(statedb.TrieDBCommits)     // Trie database commits are complete, we can mark them

	blockWriteTimer.Update(time.Since(wstart) - max(statedb.AccountCommits, statedb.StorageCommits) /* concurrent */ - statedb.SnapshotCommits - statedb.TrieDBCommits)
	elapsed := time.Since(startTime) + 1 // prevent zero division
	blockInsertTimer.Update(elapsed)

	// TODO(rjl493456442) generalize the ResettingTimer
	mgasps := float64(res.GasUsed) * 1000 / float64(elapsed)
	chainMgaspsMeter.Update(time.Duration(mgasps))

	return &blockProcessingResult{
		usedGas:  res.GasUsed,
		procTime: proctime,
		status:   status,
		witness:  witness,
	}, nil
}

// insertSideChain is called when an import batch hits upon a pruned ancestor
// error, which happens when a sidechain with a sufficiently old fork-block is
// found.
//
// The method writes all (header-and-body-valid) blocks to disk, then tries to
// switch over to the new chain if the TD exceeded the current chain.
// insertSideChain is only used pre-merge.
func (bc *BlockChain) insertSideChain(block *types.Block, it *insertIterator, makeWitness bool) (*stateless.Witness, int, error) {
	var current = bc.CurrentBlock()

	// The first sidechain block error is already verified to be ErrPrunedAncestor.
	// Since we don't import them here, we expect ErrUnknownAncestor for the remaining
	// ones. Any other errors means that the block is invalid, and should not be written
	// to disk.
	err := consensus.ErrPrunedAncestor
	for ; block != nil && errors.Is(err, consensus.ErrPrunedAncestor); block, err = it.next() {
		// Check the canonical state root for that number
		if number := block.NumberU64(); current.Number.Uint64() >= number {
			canonical := bc.GetBlockByNumber(number)
			if canonical != nil && canonical.Hash() == block.Hash() {
				// Not a sidechain block, this is a re-import of a canon block which has it's state pruned
				continue
			}
			if canonical != nil && canonical.Root() == block.Root() {
				// The sidechain block refers to a state that already exists in our canon chain. When a
				// fork is imported into the database and eventually reaches a block height that is not
				// pruned, we find the state already exists.
				//
				// If left unchecked, we would now proceed importing the blocks, without actually
				// having verified the state of the previous blocks.
				log.Warn("Sidechain block refers to existing canonical state; refusing import", "number", block.NumberU64(), "sideroot", block.Root(), "canonroot", canonical.Root())

				// If someone legitimately side-mines blocks, they would still be imported as usual. However,
				// we cannot risk writing unverified blocks to disk when they refer to state that already
				// exists in the canonical chain.
				return nil, it.index, errors.New("sidechain block refers to existing canonical state")
			}
		}
		if !bc.HasBlock(block.Hash(), block.NumberU64()) {
			start := time.Now()
			if err := bc.writeBlockWithoutState(block); err != nil {
				return nil, it.index, err
			}
			log.Debug("Injected sidechain block", "number", block.Number(), "hash", block.Hash(),
				"diff", block.Difficulty(), "elapsed", common.PrettyDuration(time.Since(start)),
				"txs", len(block.Transactions()), "gas", block.GasUsed(), "uncles", len(block.Uncles()),
				"root", block.Root())
		}
	}
	// Gather all the sidechain hashes (full blocks may be memory heavy)
	var (
		hashes  []common.Hash
		numbers []uint64
	)
	parent := it.previous()
	for parent != nil && !bc.HasState(parent.Root) {
		if bc.stateRecoverable(parent.Root) {
			if err := bc.triedb.Recover(parent.Root); err != nil {
				return nil, 0, err
			}
			break
		}
		hashes = append(hashes, parent.Hash())
		numbers = append(numbers, parent.Number.Uint64())

		parent = bc.GetHeader(parent.ParentHash, parent.Number.Uint64()-1)
	}
	if parent == nil {
		return nil, it.index, errors.New("missing parent")
	}
	// Import all the pruned blocks to make the state available
	var (
		blocks []*types.Block
		memory uint64
	)
	for i := len(hashes) - 1; i >= 0; i-- {
		// Append the next block to our batch
		block := bc.GetBlock(hashes[i], numbers[i])

		blocks = append(blocks, block)
		memory += block.Size()

		// If memory use grew too large, import and continue. Sadly we need to discard
		// all raised events and logs from notifications since we're too heavy on the
		// memory here.
		if len(blocks) >= 2048 || memory > 64*1024*1024 {
			log.Info("Importing heavy sidechain segment", "blocks", len(blocks), "start", blocks[0].NumberU64(), "end", block.NumberU64())
			if _, _, err := bc.insertChain(blocks, true, false); err != nil {
				return nil, 0, err
			}
			blocks, memory = blocks[:0], 0

			// If the chain is terminating, stop processing blocks
			if bc.insertStopped() {
				log.Debug("Abort during blocks processing")
				return nil, 0, nil
			}
		}
	}
	if len(blocks) > 0 {
		log.Info("Importing sidechain segment", "start", blocks[0].NumberU64(), "end", blocks[len(blocks)-1].NumberU64())
		return bc.insertChain(blocks, true, makeWitness)
	}
	return nil, 0, nil
}

// recoverAncestors finds the closest ancestor with available state and re-execute
// all the ancestor blocks since that.
// recoverAncestors is only used post-merge.
// We return the hash of the latest block that we could correctly validate.
func (bc *BlockChain) recoverAncestors(block *types.Block, makeWitness bool) (common.Hash, error) {
	// Gather all the sidechain hashes (full blocks may be memory heavy)
	var (
		hashes  []common.Hash
		numbers []uint64
		parent  = block
	)
	for parent != nil && !bc.HasState(parent.Root()) {
		if bc.stateRecoverable(parent.Root()) {
			if err := bc.triedb.Recover(parent.Root()); err != nil {
				return common.Hash{}, err
			}
			break
		}
		hashes = append(hashes, parent.Hash())
		numbers = append(numbers, parent.NumberU64())
		parent = bc.GetBlock(parent.ParentHash(), parent.NumberU64()-1)

		// If the chain is terminating, stop iteration
		if bc.insertStopped() {
			log.Debug("Abort during blocks iteration")
			return common.Hash{}, errInsertionInterrupted
		}
	}
	if parent == nil {
		return common.Hash{}, errors.New("missing parent")
	}
	// Import all the pruned blocks to make the state available
	for i := len(hashes) - 1; i >= 0; i-- {
		// If the chain is terminating, stop processing blocks
		if bc.insertStopped() {
			log.Debug("Abort during blocks processing")
			return common.Hash{}, errInsertionInterrupted
		}
		var b *types.Block
		if i == 0 {
			b = block
		} else {
			b = bc.GetBlock(hashes[i], numbers[i])
		}
		if _, _, err := bc.insertChain(types.Blocks{b}, false, makeWitness && i == 0); err != nil {
			return b.ParentHash(), err
		}
	}
	return block.Hash(), nil
}

// collectLogs collects the logs that were generated or removed during the
// processing of a block. These logs are later announced as deleted or reborn.
func (bc *BlockChain) collectLogs(b *types.Block, removed bool) []*types.Log {
	_, logs := bc.collectReceiptsAndLogs(b, removed)
	return logs
}

// collectReceiptsAndLogs retrieves receipts from the database and returns both receipts and logs.
// This avoids duplicate database reads when both are needed.
func (bc *BlockChain) collectReceiptsAndLogs(b *types.Block, removed bool) ([]*types.Receipt, []*types.Log) {
	var blobGasPrice *big.Int
	if b.ExcessBlobGas() != nil {
		blobGasPrice = eip4844.CalcBlobFee(bc.chainConfig, b.Header())
	}
	receipts := rawdb.ReadRawReceipts(bc.db, b.Hash(), b.NumberU64())
	if err := receipts.DeriveFields(bc.chainConfig, b.Hash(), b.NumberU64(), b.Time(), b.BaseFee(), blobGasPrice, b.Transactions()); err != nil {
		log.Error("Failed to derive block receipts fields", "hash", b.Hash(), "number", b.NumberU64(), "err", err)
	}
	var logs []*types.Log
	for _, receipt := range receipts {
		for _, log := range receipt.Logs {
			if removed {
				log.Removed = true
			}
			logs = append(logs, log)
		}
	}
	return receipts, logs
}

// reorg takes two blocks, an old chain and a new chain and will reconstruct the
// blocks and inserts them to be part of the new canonical chain and accumulates
// potential missing transactions and post an event about them.
//
// Note the new head block won't be processed here, callers need to handle it
// externally.
func (bc *BlockChain) reorg(oldHead *types.Header, newHead *types.Header) error {
	var (
		newChain    []*types.Header
		oldChain    []*types.Header
		commonBlock *types.Header
	)
	// Reduce the longer chain to the same number as the shorter one
	if oldHead.Number.Uint64() > newHead.Number.Uint64() {
		// Old chain is longer, gather all transactions and logs as deleted ones
		for ; oldHead != nil && oldHead.Number.Uint64() != newHead.Number.Uint64(); oldHead = bc.GetHeader(oldHead.ParentHash, oldHead.Number.Uint64()-1) {
			oldChain = append(oldChain, oldHead)
		}
	} else {
		// New chain is longer, stash all blocks away for subsequent insertion
		for ; newHead != nil && newHead.Number.Uint64() != oldHead.Number.Uint64(); newHead = bc.GetHeader(newHead.ParentHash, newHead.Number.Uint64()-1) {
			newChain = append(newChain, newHead)
		}
	}
	if oldHead == nil {
		return errInvalidOldChain
	}
	if newHead == nil {
		return errInvalidNewChain
	}
	// Both sides of the reorg are at the same number, reduce both until the common
	// ancestor is found
	for {
		// If the common ancestor was found, bail out
		if oldHead.Hash() == newHead.Hash() {
			commonBlock = oldHead
			break
		}
		// Remove an old block as well as stash away a new block
		oldChain = append(oldChain, oldHead)
		newChain = append(newChain, newHead)

		// Step back with both chains
		oldHead = bc.GetHeader(oldHead.ParentHash, oldHead.Number.Uint64()-1)
		if oldHead == nil {
			return errInvalidOldChain
		}
		newHead = bc.GetHeader(newHead.ParentHash, newHead.Number.Uint64()-1)
		if newHead == nil {
			return errInvalidNewChain
		}
	}
	// Ensure the user sees large reorgs
	if len(oldChain) > 0 && len(newChain) > 0 {
		logFn := log.Info
		msg := "Chain reorg detected"
		if len(oldChain) > 63 {
			msg = "Large chain reorg detected"
			logFn = log.Warn
		}
		logFn(msg, "number", commonBlock.Number, "hash", commonBlock.Hash(),
			"drop", len(oldChain), "dropfrom", oldChain[0].Hash(), "add", len(newChain), "addfrom", newChain[0].Hash())
		blockReorgAddMeter.Mark(int64(len(newChain)))
		blockReorgDropMeter.Mark(int64(len(oldChain)))
		blockReorgMeter.Mark(1)
	} else if len(newChain) > 0 {
		// Special case happens in the post merge stage that current head is
		// the ancestor of new head while these two blocks are not consecutive
		log.Info("Extend chain", "add", len(newChain), "number", newChain[0].Number, "hash", newChain[0].Hash())
		blockReorgAddMeter.Mark(int64(len(newChain)))
	} else {
		// len(newChain) == 0 && len(oldChain) > 0
		// rewind the canonical chain to a lower point.
		log.Error("Impossible reorg, please file an issue", "oldnum", oldHead.Number, "oldhash", oldHead.Hash(), "oldblocks", len(oldChain), "newnum", newHead.Number, "newhash", newHead.Hash(), "newblocks", len(newChain))
	}
	// Acquire the tx-lookup lock before mutation. This step is essential
	// as the txlookups should be changed atomically, and all subsequent
	// reads should be blocked until the mutation is complete.
	bc.txLookupLock.Lock()

	// Reorg can be executed, start reducing the chain's old blocks and appending
	// the new blocks
	var (
		deletedTxs []common.Hash
		rebirthTxs []common.Hash

		deletedLogs []*types.Log
		rebirthLogs []*types.Log
	)
	// Deleted log emission on the API uses forward order, which is borked, but
	// we'll leave it in for legacy reasons.
	//
	// TODO(karalabe): This should be nuked out, no idea how, deprecate some APIs?
	{
		for i := len(oldChain) - 1; i >= 0; i-- {
			block := bc.GetBlock(oldChain[i].Hash(), oldChain[i].Number.Uint64())
			if block == nil {
				return errInvalidOldChain // Corrupt database, mostly here to avoid weird panics
			}
			if logs := bc.collectLogs(block, true); len(logs) > 0 {
				deletedLogs = append(deletedLogs, logs...)
			}
			if len(deletedLogs) > 512 {
				bc.rmLogsFeed.Send(RemovedLogsEvent{deletedLogs})
				deletedLogs = nil
			}
		}
		if len(deletedLogs) > 0 {
			bc.rmLogsFeed.Send(RemovedLogsEvent{deletedLogs})
		}
	}
	// Undo old blocks in reverse order
	for i := 0; i < len(oldChain); i++ {
		// Collect all the deleted transactions
		block := bc.GetBlock(oldChain[i].Hash(), oldChain[i].Number.Uint64())
		if block == nil {
			return errInvalidOldChain // Corrupt database, mostly here to avoid weird panics
		}
		for _, tx := range block.Transactions() {
			deletedTxs = append(deletedTxs, tx.Hash())
		}
		// Collect deleted logs and emit them for new integrations
		if logs := bc.collectLogs(block, true); len(logs) > 0 {
			// Emit revertals latest first, older then
			slices.Reverse(logs)

			// TODO(karalabe): Hook into the reverse emission part
		}
	}
	// Apply new blocks in forward order
	for i := len(newChain) - 1; i >= 1; i-- {
		// Collect all the included transactions
		block := bc.GetBlock(newChain[i].Hash(), newChain[i].Number.Uint64())
		if block == nil {
			return errInvalidNewChain // Corrupt database, mostly here to avoid weird panics
		}
		for _, tx := range block.Transactions() {
			rebirthTxs = append(rebirthTxs, tx.Hash())
		}
		// Collect inserted logs and emit them
		if logs := bc.collectLogs(block, false); len(logs) > 0 {
			rebirthLogs = append(rebirthLogs, logs...)
		}
		if len(rebirthLogs) > 512 {
			bc.logsFeed.Send(rebirthLogs)
			rebirthLogs = nil
		}
		// Update the head block
		bc.writeHeadBlock(block)
	}
	if len(rebirthLogs) > 0 {
		bc.logsFeed.Send(rebirthLogs)
	}
	// Delete useless indexes right now which includes the non-canonical
	// transaction indexes, canonical chain indexes which above the head.
	batch := bc.db.NewBatch()
	for _, tx := range types.HashDifference(deletedTxs, rebirthTxs) {
		rawdb.DeleteTxLookupEntry(batch, tx)
	}
	// Delete all hash markers that are not part of the new canonical chain.
	// Because the reorg function does not handle new chain head, all hash
	// markers greater than or equal to new chain head should be deleted.
	number := commonBlock.Number
	if len(newChain) > 1 {
		number = newChain[1].Number
	}
	for i := number.Uint64() + 1; ; i++ {
		hash := rawdb.ReadCanonicalHash(bc.db, i)
		if hash == (common.Hash{}) {
			break
		}
		rawdb.DeleteCanonicalHash(batch, i)
	}
	if err := batch.Write(); err != nil {
		log.Crit("Failed to delete useless indexes", "err", err)
	}
	// Reset the tx lookup cache to clear stale txlookup cache.
	bc.txLookupCache.Purge()

	// Release the tx-lookup lock after mutation.
	bc.txLookupLock.Unlock()

	return nil
}

// InsertBlockWithoutSetHead executes the block, runs the necessary verification
// upon it and then persist the block and the associate state into the database.
// The key difference between the InsertChain is it won't do the canonical chain
// updating. It relies on the additional SetCanonical call to finalize the entire
// procedure.
func (bc *BlockChain) InsertBlockWithoutSetHead(block *types.Block, makeWitness bool) (*stateless.Witness, error) {
	if !bc.chainmu.TryLock() {
		return nil, errChainStopped
	}
	defer bc.chainmu.Unlock()

	log.Info(fmt.Sprintf("InsertBlockWithoutSetHead called for block %s @ %d",
		block.Hash().String(), block.NumberU64()))
	witness, _, err := bc.insertChain(types.Blocks{block}, false, makeWitness)
	return witness, err
}

// SetCanonical rewinds the chain to set the new head block as the specified
// block. It's possible that the state of the new head is missing, and it will
// be recovered in this function as well.
func (bc *BlockChain) SetCanonical(head *types.Block) (common.Hash, error) {
	if !bc.chainmu.TryLock() {
		return common.Hash{}, errChainStopped
	}
	defer bc.chainmu.Unlock()

	// Re-execute the reorged chain in case the head state is missing.
	if !bc.HasState(head.Root()) {
		if latestValidHash, err := bc.recoverAncestors(head, false); err != nil {
			return latestValidHash, err
		}
		log.Info("Recovered head state", "number", head.Number(), "hash", head.Hash())
	}
	// Run the reorg if necessary and set the given block as new head.
	start := time.Now()
	if head.ParentHash() != bc.CurrentBlock().Hash() {
		if err := bc.reorg(bc.CurrentBlock(), head.Header()); err != nil {
			return common.Hash{}, err
		}
	}
	bc.writeHeadBlock(head)

	log.Info(fmt.Sprintf("Updating hVM state to block %s @ %d in SetCanonical()",
		head.Hash().String(), head.Number().Uint64()))
	err := bc.updateHvmHeaderConsensus(head.Header(), true)
	if err != nil {
		if isHvmFullNodeBehind(err) {
			// Transient full-TBC BTC-sync lag, not fatal — full-node indexer catches up on a
			// later import. (See isHvmFullNodeBehind.)
			log.Warn(fmt.Sprintf("Full TBC node is behind the new canonical head %s @ %d in SetCanonical(); "+
				"its indexers will catch up on a later import (deferred, not fatal)",
				head.Hash().String(), head.Number().Uint64()), "err", err)
		} else if isHvmReapplyRecoverableError(err) {
			// Re-apply onto an already-committed canonical head: recover via a from-genesis rebuild rather
			// than halting the fleet (currentBlock is already head, set by the writeHeadBlock above).
			bc.recoverReapplyHvmState(fmt.Sprintf("canonical head %s @ %d in SetCanonical",
				head.Hash().String(), head.Number().Uint64()), err)
		} else {
			log.Crit(fmt.Sprintf("Unable to update hVM header consensus to block %s @ %d in SetCanonical()",
				head.Hash().String(), head.Number().Uint64()), "err", err)
		}
	}

	// Emit events
	receipts, logs := bc.collectReceiptsAndLogs(head, false)

	bc.chainFeed.Send(ChainEvent{
		Header:       head.Header(),
		Receipts:     receipts,
		Transactions: head.Transactions(),
	})

	if len(logs) > 0 {
		bc.logsFeed.Send(logs)
	}
	bc.chainHeadFeed.Send(ChainHeadEvent{Header: head.Header()})

	context := []interface{}{
		"number", head.Number(),
		"hash", head.Hash(),
		"root", head.Root(),
		"elapsed", time.Since(start),
	}
	if timestamp := time.Unix(int64(head.Time()), 0); time.Since(timestamp) > time.Minute {
		context = append(context, []interface{}{"age", common.PrettyAge(timestamp)}...)
	}
	log.Info("Chain head was updated", context...)

	return head.Hash(), nil
}

// skipBlock returns 'true', if the block being imported can be skipped over, meaning
// that the block does not need to be processed but can be considered already fully 'done'.
func (bc *BlockChain) skipBlock(err error, it *insertIterator) bool {
	// We can only ever bypass processing if the only error returned by the validator
	// is ErrKnownBlock, which means all checks passed, but we already have the block
	// and state.
	if !errors.Is(err, ErrKnownBlock) {
		return false
	}
	// If we're not using snapshots, we can skip this, since we have both block
	// and (trie-) state
	if bc.snaps == nil {
		return true
	}
	var (
		header     = it.current() // header can't be nil
		parentRoot common.Hash
	)
	// If we also have the snapshot-state, we can skip the processing.
	if bc.snaps.Snapshot(header.Root) != nil {
		return true
	}
	// In this case, we have the trie-state but not snapshot-state. If the parent
	// snapshot-state exists, we need to process this in order to not get a gap
	// in the snapshot layers.
	// Resolve parent block
	if parent := it.previous(); parent != nil {
		parentRoot = parent.Root
	} else if parent = bc.GetHeaderByHash(header.ParentHash); parent != nil {
		parentRoot = parent.Root
	}
	if parentRoot == (common.Hash{}) {
		return false // Theoretically impossible case
	}
	// Parent is also missing snapshot: we can skip this. Otherwise process.
	if bc.snaps.Snapshot(parentRoot) == nil {
		return true
	}
	return false
}

// reportBlock logs a bad block error.
func (bc *BlockChain) reportBlock(block *types.Block, res *ProcessResult, err error) {
	var receipts types.Receipts
	if res != nil {
		receipts = res.Receipts
	}
	rawdb.WriteBadBlock(bc.db, block)
	log.Error(summarizeBadBlock(block, receipts, bc.Config(), err))
}

// logForkReadiness will write a log when a future fork is scheduled, but not
// active. This is useful so operators know their client is ready for the fork.
func (bc *BlockChain) logForkReadiness(block *types.Block) {
	current := bc.Config().LatestFork(block.Time())

	// Short circuit if the timestamp of the last fork is undefined.
	t := bc.Config().Timestamp(current + 1)
	if t == nil {
		return
	}
	at := time.Unix(int64(*t), 0)

	// Only log if:
	// - Current time is before the fork activation time
	// - Enough time has passed since last alert
	now := time.Now()
	if now.Before(at) && now.After(bc.lastForkReadyAlert.Add(forkReadyInterval)) {
		log.Info("Ready for fork activation", "fork", current+1, "date", at.Format(time.RFC822),
			"remaining", time.Until(at).Round(time.Second), "timestamp", at.Unix())
		bc.lastForkReadyAlert = time.Now()
	}
}

// summarizeBadBlock returns a string summarizing the bad block and other
// relevant information.
func summarizeBadBlock(block *types.Block, receipts []*types.Receipt, config *params.ChainConfig, err error) string {
	var receiptString string
	for i, receipt := range receipts {
		receiptString += fmt.Sprintf("\n  %d: cumulative: %v gas: %v contract: %v status: %v tx: %v logs: %v bloom: %x state: %x",
			i, receipt.CumulativeGasUsed, receipt.GasUsed, receipt.ContractAddress.Hex(),
			receipt.Status, receipt.TxHash.Hex(), receipt.Logs, receipt.Bloom, receipt.PostState)
	}
	version, vcs := version.Info()
	platform := fmt.Sprintf("%s %s %s %s", version, runtime.Version(), runtime.GOARCH, runtime.GOOS)
	if vcs != "" {
		vcs = fmt.Sprintf("\nVCS: %s", vcs)
	}
	return fmt.Sprintf(`
########## BAD BLOCK #########
Block: %v (%#x)
Error: %v
Platform: %v%v
Chain config: %#v
Receipts: %v
##############################
`, block.Number(), block.Hash(), err, platform, vcs, config, receiptString)
}

// InsertHeaderChain attempts to insert the given header chain in to the local
// chain, possibly creating a reorg. If an error is returned, it will return the
// index number of the failing header as well an error describing what went wrong.
func (bc *BlockChain) InsertHeaderChain(chain []*types.Header) (int, error) {
	if len(chain) == 0 {
		return 0, nil
	}
	start := time.Now()
	if i, err := bc.hc.ValidateHeaderChain(chain); err != nil {
		return i, err
	}
	if !bc.chainmu.TryLock() {
		return 0, errChainStopped
	}
	defer bc.chainmu.Unlock()

	_, err := bc.hc.InsertHeaderChain(chain, start)
	return 0, err
}

// InsertHeadersBeforeCutoff inserts the given headers into the ancient store
// as they are claimed older than the configured chain cutoff point. All the
// inserted headers are regarded as canonical and chain reorg is not supported.
func (bc *BlockChain) InsertHeadersBeforeCutoff(headers []*types.Header) (int, error) {
	if len(headers) == 0 {
		return 0, nil
	}
	// TODO(rjl493456442): Headers before the configured cutoff have already
	// been verified by the hash of cutoff header. Theoretically, header validation
	// could be skipped here.
	if n, err := bc.hc.ValidateHeaderChain(headers); err != nil {
		return n, err
	}
	if !bc.chainmu.TryLock() {
		return 0, errChainStopped
	}
	defer bc.chainmu.Unlock()

	// Initialize the ancient store with genesis block if it's empty.
	var (
		frozen, _ = bc.db.Ancients()
		first     = headers[0].Number.Uint64()
	)
	if first == 1 && frozen == 0 {
		_, err := rawdb.WriteAncientBlocks(bc.db, []*types.Block{bc.genesisBlock}, []rlp.RawValue{rlp.EmptyList})
		if err != nil {
			log.Error("Error writing genesis to ancients", "err", err)
			return 0, err
		}
		log.Info("Wrote genesis to ancient store")
	} else if frozen != first {
		return 0, fmt.Errorf("headers are gapped with the ancient store, first: %d, ancient: %d", first, frozen)
	}

	// Write headers to the ancient store, with block bodies and receipts set to nil
	// to ensure consistency across tables in the freezer.
	_, err := rawdb.WriteAncientHeaderChain(bc.db, headers)
	if err != nil {
		return 0, err
	}
	// Sync the ancient store explicitly to ensure all data has been flushed to disk.
	if err := bc.db.SyncAncient(); err != nil {
		return 0, err
	}
	// Write hash to number mappings
	batch := bc.db.NewBatch()
	for _, header := range headers {
		rawdb.WriteHeaderNumber(batch, header.Hash(), header.Number.Uint64())
	}
	// Write head header and head snap block flags
	last := headers[len(headers)-1]
	rawdb.WriteHeadHeaderHash(batch, last.Hash())
	rawdb.WriteHeadFastBlockHash(batch, last.Hash())
	if err := batch.Write(); err != nil {
		return 0, err
	}
	// Truncate the useless chain segment (zero bodies and receipts) in the
	// ancient store.
	if _, err := bc.db.TruncateTail(last.Number.Uint64() + 1); err != nil {
		return 0, err
	}
	// Last step update all in-memory markers
	bc.hc.currentHeader.Store(last)
	bc.currentSnapBlock.Store(last)
	headHeaderGauge.Update(last.Number.Int64())
	headFastBlockGauge.Update(last.Number.Int64())

	// OPStack addition
	updateOptimismBlockMetrics(last)
	return 0, nil
}

// SetBlockValidatorAndProcessorForTesting sets the current validator and processor.
// This method can be used to force an invalid blockchain to be verified for tests.
// This method is unsafe and should only be used before block import starts.
func (bc *BlockChain) SetBlockValidatorAndProcessorForTesting(v Validator, p Processor) {
	bc.validator = v
	bc.processor = p
}

// SetTrieFlushInterval configures how often in-memory tries are persisted to disk.
// The interval is in terms of block processing time, not wall clock.
// It is thread-safe and can be called repeatedly without side effects.
func (bc *BlockChain) SetTrieFlushInterval(interval time.Duration) {
	bc.flushInterval.Store(int64(interval))
}

// GetTrieFlushInterval gets the in-memory tries flushAlloc interval
func (bc *BlockChain) GetTrieFlushInterval() time.Duration {
	return time.Duration(bc.flushInterval.Load())
}

func unflattenBTCHeaders(rawHeaders [][types.BitcoinHeaderLengthBytes]byte) (*wire.MsgHeaders, error) {
	parsedHeaders := make([]*wire.BlockHeader, len(rawHeaders))
	for i := 0; i < len(rawHeaders); i++ {
		parsedHeader, err := bytes2Header(rawHeaders[i])
		if err != nil {
			log.Error(fmt.Sprintf("Error decoding Bitcoin header %x", rawHeaders[i][:]), "err", err)
			return nil, err
		}
		parsedHeaders[i] = parsedHeader
	}

	msgHeaders := &wire.MsgHeaders{
		Headers: parsedHeaders,
	}

	return msgHeaders, nil
}

func bytes2Header(header [80]byte) (*wire.BlockHeader, error) {
	var bh wire.BlockHeader
	err := bh.Deserialize(bytes.NewReader(header[:]))
	if err != nil {
		return nil, fmt.Errorf("deserialize block header: %w", err)
	}
	return &bh, nil
}

func (bc *BlockChain) InsertL2Keystone(l2Keystone hemi.L2Keystone) error {
	bc.keystoneMtx.Lock()
	defer bc.keystoneMtx.Unlock()

	l2KeystoneAbrevHash := hemi.L2KeystoneAbbreviate(l2Keystone).Hash()

	log.Info("inserting l2 keystone", "l2KeystoneAbrevHash", hex.EncodeToString(l2KeystoneAbrevHash.CloneBytes()))

	if err := rawdb.WriteL2Keystone(bc.db, l2Keystone); err != nil {
		return err
	}

	return nil
}

func (bc *BlockChain) GetMostRecentKeystones(count uint) ([]hemi.L2Keystone, error) {
	bc.keystoneMtx.RLock()
	defer bc.keystoneMtx.RUnlock()

	return rawdb.ReadMostRecentL2Keystones(bc.db, count)
}

func (bc *BlockChain) GetKeystoneAndDescendants(hash []byte, count uint) ([]hemi.L2Keystone, error) {
	bc.keystoneMtx.RLock()
	defer bc.keystoneMtx.RUnlock()

	return rawdb.GetKeystoneAndDescendants(bc.db, hash, count)
}

func (bc *BlockChain) GetKeystoneByAbrevHash(hash []byte) (*hemi.L2Keystone, error) {
	bc.keystoneMtx.RLock()
	defer bc.keystoneMtx.RUnlock()

	return rawdb.ReadL2KeystoneByAbrevHash(bc.db, hash)
}

func (bc *BlockChain) DeleteKeystonesAboveHeight(height uint64) error {
	bc.keystoneMtx.RLock()
	defer bc.keystoneMtx.RUnlock()

	return rawdb.DeleteL2KeystonesAboveHeight(bc.db, height)
}

var (
	errNoTransactionOnBlock = errors.New("no transactions on block?")
)

func (bc *BlockChain) l2BlockNumberToKeystone(l2BlockNumber uint32) (*hemi.L2Keystone, error) {
	l2Block := bc.GetBlockByNumber(uint64(l2BlockNumber))
	if l2Block == nil {
		return nil, fmt.Errorf("could not get l2blockbynumber")
	}

	if len(l2Block.Transactions()) == 0 {
		return nil, errNoTransactionOnBlock
	}

	if l2Block.Transactions()[0].Type() != types.DepositTxType {
		return nil, fmt.Errorf("incorrect transaction type found: %d", l2Block.Transactions()[0].Type())
	}

	l1BlockNumber, err := bc.deriveL1BlockNumberFromData(l2Block.Time(), l2Block.Transactions()[0].Data(), l2Block.NumberU64())
	if err != nil {
		return nil, fmt.Errorf("could not derive l1 block number from data for l2 block %d: %s", l2BlockNumber, err)
	}

	l2Keystone := hemi.L2Keystone{
		Version:            uint8(1),
		L1BlockNumber:      uint32(l1BlockNumber),
		L2BlockNumber:      l2BlockNumber,
		ParentEPHash:       l2Block.ParentHash().Bytes(),
		PrevKeystoneEPHash: nil,
		StateRoot:          l2Block.Root().Bytes(),
		EPHash:             l2Block.Hash().Bytes(),
	}

	if l2Keystone.L2BlockNumber >= hemi.KeystoneHeaderPeriod {
		subResult := l2Keystone.L2BlockNumber - hemi.KeystoneHeaderPeriod

		// note that genesis does not have any transaction so we can't derive
		// l1 block info
		if subResult > 0 {
			prevKeystone, err := bc.l2BlockNumberToKeystone(subResult)
			if err != nil {
				return nil, fmt.Errorf("error getting previous keystone at block number %d: %s", subResult, err)
			}

			l2Keystone.PrevKeystoneEPHash = prevKeystone.EPHash
		}

	}

	return &l2Keystone, nil
}

func (bc *BlockChain) upsertKeystoneAtL2BlockNumber(l2BlockNumber uint32) (bool, error) {
	bc.keystoneBackfillMtx.Lock()
	defer bc.keystoneBackfillMtx.Unlock()

	l2Keystone, err := bc.l2BlockNumberToKeystone(l2BlockNumber)
	if err != nil {
		return false, fmt.Errorf("error getting l2keystone: %s", err)
	}

	l2KeystoneAbrev := hemi.L2KeystoneAbbreviate(*l2Keystone)

	_, err = bc.GetKeystoneByAbrevHash(l2KeystoneAbrev.Hash().CloneBytes())
	insertedNew := err != nil
	if err != nil {
		// there isn't a great way to determine if this is a "not found"
		// error, so assume it is.  thus debug log level when not nil
		log.Debug("error when finding keystone by abrev hash is not nil",
			"error", err)
	}

	if err := bc.InsertL2Keystone(*l2Keystone); err != nil {
		return false, err
	}

	return insertedNew, nil
}

func (bc *BlockChain) BackfillKeystones() error {
	bc.keystoneBackfillMtx.Lock()

	headL2Block := bc.CurrentBlock()
	if headL2Block == nil {
		bc.keystoneBackfillMtx.Unlock()
		return fmt.Errorf("could not find current head")
	}

	l2BlockNumber := headL2Block.Number.Uint64()
	if err := bc.DeleteKeystonesAboveHeight(l2BlockNumber); err != nil {
		bc.keystoneBackfillMtx.Unlock()
		return err
	}

	bc.keystoneBackfillMtx.Unlock()

	// we want to start backfilling at the unsafe block
	// we will continue to either the finalized block if it exists or genesis
	// if not
	finalizedBlockNumber := uint64(0)
	finalizedBlock := bc.CurrentFinalBlock()
	if finalizedBlock != nil {
		finalizedBlockNumber = finalizedBlock.Number.Uint64()
	}

	// this should not be the case
	if l2BlockNumber < finalizedBlockNumber {
		return fmt.Errorf("unsafe block behind finalized block? %d < %d", l2BlockNumber, finalizedBlockNumber)
	}

	log.Debug("will backfill", "start", l2BlockNumber, "end", finalizedBlockNumber)

	for {
		// note that genesis does not have any transaction so we can't derive
		// l1 block info
		if l2BlockNumber == 0 {
			break
		}

		// we upsert the keystone, and we make not if we inserted vs upserted
		// we use this a few lines below
		insertedNew, err := bc.upsertKeystoneAtL2BlockNumber(uint32(l2BlockNumber))
		if err != nil {
			return fmt.Errorf("error upserting keystone: %s", err)
		}

		if l2BlockNumber <= 0 {
			break
		}

		// if insertedNew is true then we have inserted a brand new keystone
		// (not upserted) if this is the case it MAY be due to missing keystones
		// so continue the for loop if we inserted a new one to handle
		// more missing ones

		bc.keystoneBackfillMtx.Lock()
		keystonesBackfilled := bc.keystonesBackfilled
		bc.keystoneBackfillMtx.Unlock()

		if keystonesBackfilled && l2BlockNumber < finalizedBlockNumber && !insertedNew {
			break
		}

		l2BlockNumber -= hemi.KeystoneHeaderPeriod
	}

	// we always want this to run to genesis once on startup to backfill
	// all keystones and validate that they are correct
	// once this initial backfill is done, then we can continue from
	// either the finalized block or the last known keystone
	bc.keystoneBackfillMtx.Lock()
	bc.keystonesBackfilled = true
	bc.keystoneBackfillMtx.Unlock()

	return nil
}

// note that below here was code all-but-copied from optimism to derive l1 block info
// from the l2 chain

const (
	l1InfoFuncBedrockSignature = "setL1BlockValues(uint64,uint64,uint256,bytes32,uint64,bytes32,uint256,uint256)"
	l1InfoFuncEcotoneSignature = "setL1BlockValuesEcotone()"
	l1InfoArguments            = 8
	l1InfoBedrockLen           = 4 + 32*l1InfoArguments
	l1InfoEcotoneLen           = 4 + 32*5 // after Ecotone upgrade, args are packed into 5 32-byte slots
	l1InfoIsthmusLen           = 4 + 32*5 + 4 + 8
)

var (
	l1InfoFuncBedrockBytes4          = crypto.Keccak256([]byte(l1InfoFuncBedrockSignature))[:4]
	l1InfoFuncEcotoneBytes4          = crypto.Keccak256([]byte(l1InfoFuncEcotoneSignature))[:4]
	l1InfoDepositerAddress           = common.HexToAddress("0xdeaddeaddeaddeaddeaddeaddeaddeaddead0001")
	l1BlockAddress                   = common.HexToAddress("0x4200000000000000000000000000000000000015")
	uint8EmptyPadding       [31]byte = [31]byte{}
	addressEmptyPadding     [12]byte = [12]byte{}
	uint64EmptyPadding      [24]byte = [24]byte{}
)

func validateSignature(potentialSignature []byte, expectedSignature []byte) ([]byte, error) {
	if !bytes.Equal(potentialSignature, expectedSignature) {
		return nil, errors.New("invalid function signature")
	}
	return potentialSignature, nil
}

func unmarshalBinaryEcotone(data []byte) (uint64, error) {
	if len(data) != l1InfoEcotoneLen {
		return 0, fmt.Errorf("data is unexpected length for ecootone: %d", len(data))
	}

	if _, err := validateSignature(data[:4], l1InfoFuncEcotoneBytes4); err != nil {
		return 0, err
	}

	offset := 4 + // signature
		4 + // base fee
		4 + // base fee scalar
		8 + // sequence number
		8 // time
	size := 8

	return binary.BigEndian.Uint64(data[offset : offset+size]), nil
}

func unmarshalBinaryBedrock(data []byte) (uint64, error) {
	if len(data) != l1InfoBedrockLen {
		return 0, fmt.Errorf("data is unexpected length for bedrock: %d", len(data))
	}

	if _, err := validateSignature(data[:4], l1InfoFuncBedrockBytes4); err != nil {
		return 0, err
	}

	offset := 4 + // signature
		(32 - 8) //padding

	size := 8

	return binary.BigEndian.Uint64(data[offset : offset+size]), nil
}

func unmarshalBinaryIsthmus(data []byte) (uint64, error) {
	if len(data) != l1InfoIsthmusLen {
		return 0, fmt.Errorf("data is unexpected length for bedrock: %d", len(data))
	}

	offset := 4 + // signature
		4 + // base fee scalar
		4 + // blob base fee scalar
		8 + // sequence number
		8 // time
	size := 8

	return binary.BigEndian.Uint64(data[offset : offset+size]), nil
}

func (bc *BlockChain) deriveL1BlockNumberFromData(l2BlockTime uint64, data []byte, l2BlockNumber uint64) (uint64, error) {
	if bc.chainConfig.IsIsthmus(l2BlockTime) {
		return unmarshalBinaryIsthmus(data)
	}

	if bc.chainConfig.IsEcotone(l2BlockTime) {
		return unmarshalBinaryEcotone(data)
	}

	return unmarshalBinaryBedrock(data)
}

func (bc *BlockChain) StateSizer() *state.SizeTracker {
	return bc.stateSizer
}
