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
	context2 "context"
	"errors"
	"fmt"
	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/database/tbcd"
	"github.com/hemilabs/heminetwork/service/tbc"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/lru"
	"github.com/ethereum/go-ethereum/common/mclock"
	"github.com/ethereum/go-ethereum/common/prque"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/consensus/misc/eip4844"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/state/snapshot"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/event"
	"github.com/ethereum/go-ethereum/internal/syncx"
	"github.com/ethereum/go-ethereum/internal/version"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/metrics"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/ethereum/go-ethereum/trie/triedb/hashdb"
	"github.com/ethereum/go-ethereum/trie/triedb/pathdb"
	"golang.org/x/exp/slices"
)

var (
	headBlockGauge          = metrics.NewRegisteredGauge("chain/head/block", nil)
	headHeaderGauge         = metrics.NewRegisteredGauge("chain/head/header", nil)
	headFastBlockGauge      = metrics.NewRegisteredGauge("chain/head/receipt", nil)
	headFinalizedBlockGauge = metrics.NewRegisteredGauge("chain/head/finalized", nil)
	headSafeBlockGauge      = metrics.NewRegisteredGauge("chain/head/safe", nil)

	chainInfoGauge = metrics.NewRegisteredGaugeInfo("chain/info", nil)

	accountReadTimer   = metrics.NewRegisteredTimer("chain/account/reads", nil)
	accountHashTimer   = metrics.NewRegisteredTimer("chain/account/hashes", nil)
	accountUpdateTimer = metrics.NewRegisteredTimer("chain/account/updates", nil)
	accountCommitTimer = metrics.NewRegisteredTimer("chain/account/commits", nil)

	storageReadTimer   = metrics.NewRegisteredTimer("chain/storage/reads", nil)
	storageHashTimer   = metrics.NewRegisteredTimer("chain/storage/hashes", nil)
	storageUpdateTimer = metrics.NewRegisteredTimer("chain/storage/updates", nil)
	storageCommitTimer = metrics.NewRegisteredTimer("chain/storage/commits", nil)

	snapshotAccountReadTimer = metrics.NewRegisteredTimer("chain/snapshot/account/reads", nil)
	snapshotStorageReadTimer = metrics.NewRegisteredTimer("chain/snapshot/storage/reads", nil)
	snapshotCommitTimer      = metrics.NewRegisteredTimer("chain/snapshot/commits", nil)

	triedbCommitTimer = metrics.NewRegisteredTimer("chain/triedb/commits", nil)

	blockInsertTimer     = metrics.NewRegisteredTimer("chain/inserts", nil)
	blockValidationTimer = metrics.NewRegisteredTimer("chain/validation", nil)
	blockExecutionTimer  = metrics.NewRegisteredTimer("chain/execution", nil)
	blockWriteTimer      = metrics.NewRegisteredTimer("chain/write", nil)

	blockReorgMeter     = metrics.NewRegisteredMeter("chain/reorg/executes", nil)
	blockReorgAddMeter  = metrics.NewRegisteredMeter("chain/reorg/add", nil)
	blockReorgDropMeter = metrics.NewRegisteredMeter("chain/reorg/drop", nil)

	blockPrefetchExecuteTimer   = metrics.NewRegisteredTimer("chain/prefetch/executes", nil)
	blockPrefetchInterruptMeter = metrics.NewRegisteredMeter("chain/prefetch/interrupts", nil)

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
)

// Used for communicating chain geometry when finding common ancestor between blocks for hVM state transition
type AncestorType int

const (
	bodyCacheLimit      = 256
	blockCacheLimit     = 256
	receiptsCacheLimit  = 32
	txLookupCacheLimit  = 1024
	maxFutureBlocks     = 256
	maxTimeFutureBlocks = 30
	TriesInMemory       = 128

	// BlockChainVersion ensures that an incompatible database forces a resync from scratch.
	//
	// Changelog:
	//
	// - Version 4
	//   The following incompatible database changes were added:
	//   * the `BlockNumber`, `TxHash`, `TxIndex`, `BlockHash` and `Index` fields of log are deleted
	//   * the `Bloom` field of receipt is deleted
	//   * the `BlockIndex` and `TxIndex` fields of txlookup are deleted
	// - Version 5
	//  The following incompatible database changes were added:
	//    * the `TxHash`, `GasCost`, and `ContractAddress` fields are no longer stored for a receipt
	//    * the `TxHash`, `GasCost`, and `ContractAddress` fields are computed by looking up the
	//      receipts' corresponding block
	// - Version 6
	//  The following incompatible database changes were added:
	//    * Transaction lookup information stores the corresponding block number instead of block hash
	// - Version 7
	//  The following incompatible database changes were added:
	//    * Use freezer as the ancient database to maintain all ancient data
	// - Version 8
	//  The following incompatible database changes were added:
	//    * New scheme for contract code in order to separate the codes and trie nodes
	BlockChainVersion uint64 = 8

	// Number of blocks behind the lightweight TBC canonical tip that the full TBC node is indexed to.
	// For example when a Bitcoin Attributes Deposited transaction adds headers 101 through 103, indexer
	// would move from 98 to 101.
	// TODO: Make this configurable as part of chain parameters?
	hVMIndexerTipLag = 2
)

// CacheConfig contains the configuration values for the trie database
// and state snapshot these are resident in a blockchain.
type CacheConfig struct {
	TrieCleanLimit      int           // Memory allowance (MB) to use for caching trie nodes in memory
	TrieCleanNoPrefetch bool          // Whether to disable heuristic state prefetching for followup blocks
	TrieDirtyLimit      int           // Memory limit (MB) at which to start flushing dirty trie nodes to disk
	TrieDirtyDisabled   bool          // Whether to disable trie write caching and GC altogether (archive node)
	TrieTimeLimit       time.Duration // Time limit after which to flush the current in-memory trie to disk
	SnapshotLimit       int           // Memory allowance (MB) to use for caching snapshot entries in memory
	Preimages           bool          // Whether to store preimage of trie key to the disk
	StateHistory        uint64        // Number of blocks from head whose state histories are reserved.
	StateScheme         string        // Scheme used to store ethereum states and merkle tree nodes on top

	SnapshotNoBuild bool // Whether the background generation is allowed
	SnapshotWait    bool // Wait for snapshot construction on startup. TODO(karalabe): This is a dirty hack for testing, nuke it
}

// triedbConfig derives the configures for trie database.
func (c *CacheConfig) triedbConfig() *trie.Config {
	config := &trie.Config{Preimages: c.Preimages}
	if c.StateScheme == rawdb.HashScheme {
		config.HashDB = &hashdb.Config{
			CleanCacheSize: c.TrieCleanLimit * 1024 * 1024,
		}
	}
	if c.StateScheme == rawdb.PathScheme {
		config.PathDB = &pathdb.Config{
			StateHistory:   c.StateHistory,
			CleanCacheSize: c.TrieCleanLimit * 1024 * 1024,
			DirtyCacheSize: c.TrieDirtyLimit * 1024 * 1024,
		}
	}
	return config
}

// defaultCacheConfig are the default caching values if none are specified by the
// user (also used during testing).
var defaultCacheConfig = &CacheConfig{
	TrieCleanLimit: 256,
	TrieDirtyLimit: 256,
	TrieTimeLimit:  5 * time.Minute,
	SnapshotLimit:  256,
	SnapshotWait:   true,
	StateScheme:    rawdb.HashScheme,
}

// DefaultCacheConfigWithScheme returns a deep copied default cache config with
// a provided trie node scheme.
func DefaultCacheConfigWithScheme(scheme string) *CacheConfig {
	config := *defaultCacheConfig
	config.StateScheme = scheme
	return &config
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
	cacheConfig *CacheConfig        // Cache configuration for pruning

	db            ethdb.Database                   // Low level persistent database to store final content in
	snaps         *snapshot.Tree                   // Snapshot tree for fast trie leaf access
	triegc        *prque.Prque[int64, common.Hash] // Priority queue mapping block numbers to tries to gc
	gcproc        time.Duration                    // Accumulates canonical block processing for trie dumping
	lastWrite     uint64                           // Last block when the state was flushed
	flushInterval atomic.Int64                     // Time interval (processing time) after which to flush a state
	triedb        *trie.Database                   // The database handler for maintaining trie nodes.
	stateCache    state.Database                   // State database to reuse between imports (contains state cache)
	txIndexer     *txIndexer                       // Transaction indexer, might be nil if not enabled

	hc            *HeaderChain
	rmLogsFeed    event.Feed
	chainFeed     event.Feed
	chainSideFeed event.Feed
	chainHeadFeed event.Feed
	logsFeed      event.Feed
	blockProcFeed event.Feed
	scope         event.SubscriptionScope
	genesisBlock  *types.Block

	// This mutex synchronizes chain write operations.
	// Readers don't need to take it, they can just read the database.
	chainmu *syncx.ClosableMutex

	currentBlock      atomic.Pointer[types.Header] // Current head of the chain
	currentSnapBlock  atomic.Pointer[types.Header] // Current head of snap-sync
	currentFinalBlock atomic.Pointer[types.Header] // Latest (consensus) finalized block
	currentSafeBlock  atomic.Pointer[types.Header] // Latest (consensus) safe block

	bodyCache     *lru.Cache[common.Hash, *types.Body]
	bodyRLPCache  *lru.Cache[common.Hash, rlp.RawValue]
	receiptsCache *lru.Cache[common.Hash, []*types.Receipt]
	blockCache    *lru.Cache[common.Hash, *types.Block]
	txLookupCache *lru.Cache[common.Hash, txLookup]

	// future blocks are blocks added for later processing
	futureBlocks *lru.Cache[common.Hash, *types.Block]

	wg            sync.WaitGroup
	quit          chan struct{} // shutdown signal, closed in Stop.
	stopping      atomic.Bool   // false if chain is running, true when stopped
	procInterrupt atomic.Bool   // interrupt signaler for block processing

	engine     consensus.Engine
	validator  Validator // Block and state validator interface
	prefetcher Prefetcher
	processor  Processor // Block transaction processor interface
	forker     *ForkChoice
	vmConfig   vm.Config

	hvmEnabled          bool
	tbcHeaderNode       *tbc.Server
	tbcHeaderNodeConfig *tbc.Config

	// A temporary holding pen for blocks that are being considered but not yet
	// written to disk to allow hVM consensus update functions to access these
	// to extract the geometry changes they represent.
	// TODO: consider refactor that allows these blocks to be passed directly
	// into the hVM consensus update functions to make this easier to reason about.
	tempBlocks  map[string]*types.Block
	tempHeaders map[string]*types.Header

	btcAttributesDepCacheBlockHash common.Hash
	btcAttributesDepCacheEntry     *types.BtcAttributesDepositedTx
}

// getHeaderModeTBCEVMHeader returns the EVM header for which the
// header-only TBC node represents the cumulative Bitcoin state knowledge
func (bc *BlockChain) getHeaderModeTBCEVMHeader() (*types.Header, error) {
	if !bc.hvmEnabled {
		return nil, fmt.Errorf("getHeaderModeTBCEVMHeader() called but hVM is not enabled")
	}

	stateId, err := bc.tbcHeaderNode.UpstreamStateId(context2.Background())
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
	return nil, fmt.Errorf(fmt.Sprintf("Unable to find EVM header corresponding to hash %x", stateBlockHash[:]))
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
	// Note genesis block cannot contain a Bitcoin Attributes Deposited tx.
	for cursor.Number.Uint64() > 1000 {
		header := bc.GetHeaderByNumber(cursor.Number.Uint64() - 1000)
		if !bc.chainConfig.IsHvm0(header.Time) {
			// Our tip is now less than 1000 blocks above activation height, descend manually
			break
		}

		cursor = header
	}

	// Walk back until we are either at genesis or we pass behind the hVM Phase 0 activation timestamp
	for {
		header := bc.GetHeaderByHash(cursor.ParentHash)
		if bc.chainConfig.IsHvm0(header.Time) && header.Number.Uint64() > 0 {
			cursor = header
			continue
		}
		break
	}

	return cursor, nil
}

// performFullHvmStateRestore is used to clear and completely regenerate
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
		err := bc.applyHvmHeaderConsensusUpdate(cursor)
		if err != nil {
			log.Crit(fmt.Sprintf("Failed to fully restore hVM state, encountered an error processing hVM"+
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
	log.Info("Resetting hVM header TBC node to genesis")
	if bc.tbcHeaderNode != nil {
		log.Info("Header-only TBC instance running, tearing down...")
		err := bc.tbcHeaderNode.ExternalHeaderTearDown()
		if err != nil {
			log.Crit("resetHvmHeaderNodeToGenesis failed when calling ExternalHeaderTearDown on TBC", "err", err)
		}
	} else {
		log.Info("Header-only TBC instance is not running, nothing to tear down.")
	}

	dataDir := bc.tbcHeaderNodeConfig.LevelDBHome

	path, _ := filepath.Abs(dataDir)
	log.Info(fmt.Sprintf("Full path: %s", path))

	if err := os.RemoveAll(dataDir); err != nil {
		log.Crit(fmt.Sprintf("ResetHvmHeaderNodeToGenesis unable to delete external header mode TBC "+
			"data directory %s", dataDir))
	}

	if _, err := os.Open(dataDir); os.IsNotExist(err) {
		log.Info(fmt.Sprintf("The data directory %s does not exist", dataDir))
	} else {
		log.Info(fmt.Sprintf("The data directory %s exists", dataDir))
	}

	log.Info("Deleted hVM header TBC node data directory", "dataDir", dataDir)

	bc.initHvmHeaderNode(bc.tbcHeaderNodeConfig)
	err := bc.tbcHeaderNode.SetUpstreamStateId(context2.Background(), &hVMGenesisUpstreamId)
	if err != nil {
		log.Crit("When resetting hVM header-only node to genesis, unable to set upstream state id to genesis state id")
	}
}

func (bc *BlockChain) initHvmHeaderNode(config *tbc.Config) {
	if config.ExternalHeaderMode != true {
		log.Crit("initHvmHeaderNode called with a TBC config that does not have ExternalHeaderMode set")
	}

	tbcHeaderNode, err := tbc.NewServer(config)
	if err != nil {
		log.Crit("initHvmHeaderNode unable to create new TBC server", "err", err)
	}
	err = tbcHeaderNode.ExternalHeaderSetup(context2.Background())
	if err != nil {
		log.Crit("initHvmHeaderNode unable to run ExternalHeaderSetup on TBC", "err", err)
	}

	bc.tbcHeaderNode = tbcHeaderNode
	bc.tbcHeaderNodeConfig = config
	bc.hvmEnabled = true
}

func (bc *BlockChain) SetupHvmHeaderNode(config *tbc.Config) {
	bc.initHvmHeaderNode(config)

	// Get the current state ID
	stateId, err := bc.tbcHeaderNode.UpstreamStateId(context2.Background())
	if err != nil {
		log.Crit("Unable to get upstream state ID from TBC header node", "err", err)
	}

	potentialBlockHash := common.BytesToHash(stateId[:])
	potentialHeader := bc.GetHeaderByHash(potentialBlockHash)

	if potentialHeader != nil {
		// TBC has already been progressed with EVM blocks prior
		log.Info(fmt.Sprintf("Setup hVM's header-only TBC node, it is currently at state representing block %s @ %d",
			potentialHeader.Hash().String, potentialHeader.Number.Uint64()))
	} else {
		// TBC's stateId doesn't correspond to a known block.
		// It is either in an invalid state, or it's in genesis configuration.

		_, bestHeader, err := bc.tbcHeaderNode.BlockHeaderBest(context2.Background())
		if err != nil {
			log.Crit("SetupHvmHeaderNode unable to get Best header on TBC", "err", err)
		}
		bestHeaderHash := bestHeader.BlockHash()
		genesisHash := config.EffectiveGenesisBlock.BlockHash()

		// TODO: Decide whether this check for genesis belongs in init instead of setup
		if bytes.Equal(bestHeaderHash[:], genesisHash[:]) {
			// TBC is in genesis state, set its state id to the genesis id
			err := bc.tbcHeaderNode.SetUpstreamStateId(context2.Background(), &hVMGenesisUpstreamId)
			if err != nil {
				log.Crit("SetupHvmHeaderNode unable to set upstream state id", "err", err)
			}
		} else {
			// TBC is in an invalid state
			log.Info(fmt.Sprintf("The hVM header-only TBC node has an invaid state on startup; statId=%x, "+
				"attempting full restore from hVM activation height", stateId))
			bc.performFullHvmHeaderStateRestore()
		}
	}
}

// NewBlockChain returns a fully initialised block chain using information
// available in the database. It initialises the default Ethereum Validator
// and Processor.
func NewBlockChain(db ethdb.Database, cacheConfig *CacheConfig, genesis *Genesis, overrides *ChainOverrides, engine consensus.Engine, vmConfig vm.Config, shouldPreserve func(header *types.Header) bool, txLookupLimit *uint64) (*BlockChain, error) {
	if cacheConfig == nil {
		cacheConfig = defaultCacheConfig
	}

	// Open trie database with provided config
	triedb := trie.NewDatabase(db, cacheConfig.triedbConfig())

	// Setup the genesis block, commit the provided genesis specification
	// to database if the genesis block is not present yet, or load the
	// stored one from database.
	chainConfig, genesisHash, genesisErr := SetupGenesisBlockWithOverride(db, triedb, genesis, overrides)
	if _, ok := genesisErr.(*params.ConfigCompatError); genesisErr != nil && !ok {
		return nil, genesisErr
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

	bc := &BlockChain{
		chainConfig:   chainConfig,
		cacheConfig:   cacheConfig,
		db:            db,
		triedb:        triedb,
		triegc:        prque.New[int64, common.Hash](nil),
		quit:          make(chan struct{}),
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
		vmConfig:      vmConfig,
	}
	bc.flushInterval.Store(int64(cacheConfig.TrieTimeLimit))
	bc.forker = NewForkChoice(bc, shouldPreserve)
	bc.stateCache = state.NewDatabaseWithNodeDB(bc.db, bc.triedb)
	bc.validator = NewBlockValidator(chainConfig, bc, engine)
	bc.prefetcher = newStatePrefetcher(chainConfig, bc, engine)
	bc.processor = NewStateProcessor(chainConfig, bc, engine)

	var err error
	bc.hc, err = NewHeaderChain(db, chainConfig, engine, bc.insertStopped)
	if err != nil {
		return nil, err
	}
	bc.genesisBlock = bc.GetBlockByNumber(0)
	if bc.genesisBlock == nil {
		return nil, ErrNoGenesis
	}

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
			// Head state is missing, before the state recovery, find out the
			// disk layer point of snapshot(if it's enabled). Make sure the
			// rewound point is lower than disk layer.
			var diskRoot common.Hash
			if bc.cacheConfig.SnapshotLimit > 0 {
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
	// The first thing the node will do is reconstruct the verification data for
	// the head block (ethash cache or clique voting snapshot). Might as well do
	// it in advance.
	bc.engine.VerifyHeader(bc, bc.CurrentHeader())

	// Check the current state of the block hashes and make sure that we do not have any of the bad blocks in our chain
	for hash := range BadHashes {
		if header := bc.GetHeaderByHash(hash); header != nil {
			// get the canonical block corresponding to the offending header's number
			headerByNumber := bc.GetHeaderByNumber(header.Number.Uint64())
			// make sure the headerByNumber (if present) is in our current canonical chain
			if headerByNumber != nil && headerByNumber.Hash() == header.Hash() {
				log.Error("Found bad hash, rewinding chain", "number", header.Number, "hash", header.ParentHash)
				if err := bc.SetHead(header.Number.Uint64() - 1); err != nil {
					return nil, err
				}
				log.Error("Chain rewind was successful, resuming normal operation")
			}
		}
	}

	// Load any existing snapshot, regenerating it if loading failed
	if bc.cacheConfig.SnapshotLimit > 0 {
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
			CacheSize:  bc.cacheConfig.SnapshotLimit,
			Recovery:   recover,
			NoBuild:    bc.cacheConfig.SnapshotNoBuild,
			AsyncBuild: !bc.cacheConfig.SnapshotWait,
		}
		bc.snaps, _ = snapshot.New(snapconfig, bc.db, bc.triedb, head.Root)
	}

	// Start future block processor.
	bc.wg.Add(1)
	go bc.updateFutureBlocks()

	// Rewind the chain in case of an incompatible config upgrade.
	if compat, ok := genesisErr.(*params.ConfigCompatError); ok {
		log.Warn("Rewinding chain to upgrade configuration", "err", compat)
		if compat.RewindToTime > 0 {
			bc.SetHeadWithTimestamp(compat.RewindToTime)
		} else {
			bc.SetHead(compat.RewindToBlock)
		}
		rawdb.WriteChainConfig(db, genesisHash, chainConfig)
	}
	// Start tx indexer if it's enabled.
	if txLookupLimit != nil {
		bc.txIndexer = newTxIndexer(*txLookupLimit, bc)
	}
	return bc, nil
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
	// Make sure the entire head block is available
	headBlock := bc.GetBlockByHash(head)
	if headBlock == nil {
		// Corrupt or empty database, init from scratch
		log.Warn("Head block missing, resetting chain", "hash", head)
		return bc.Reset()
	}
	// Everything seems to be fine, set as the head block
	bc.currentBlock.Store(headBlock.Header())
	headBlockGauge.Update(int64(headBlock.NumberU64()))

	// Restore the last known head header
	headHeader := headBlock.Header()
	if head := rawdb.ReadHeadHeaderHash(bc.db); head != (common.Hash{}) {
		if header := bc.GetHeaderByHash(head); header != nil {
			headHeader = header
		}
	}
	bc.hc.SetCurrentHeader(headHeader)

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

		headerTd = bc.GetTd(headHeader.Hash(), headHeader.Number.Uint64())
		blockTd  = bc.GetTd(headBlock.Hash(), headBlock.NumberU64())
	)
	if headHeader.Hash() != headBlock.Hash() {
		log.Info("Loaded most recent local header", "number", headHeader.Number, "hash", headHeader.Hash(), "td", headerTd, "age", common.PrettyAge(time.Unix(int64(headHeader.Time), 0)))
	}
	log.Info("Loaded most recent local block", "number", headBlock.Number(), "hash", headBlock.Hash(), "td", blockTd, "age", common.PrettyAge(time.Unix(int64(headBlock.Time()), 0)))
	if headBlock.Hash() != currentSnapBlock.Hash() {
		snapTd := bc.GetTd(currentSnapBlock.Hash(), currentSnapBlock.Number.Uint64())
		log.Info("Loaded most recent local snap block", "number", currentSnapBlock.Number, "hash", currentSnapBlock.Hash(), "td", snapTd, "age", common.PrettyAge(time.Unix(int64(currentSnapBlock.Time), 0)))
	}
	if currentFinalBlock != nil {
		finalTd := bc.GetTd(currentFinalBlock.Hash(), currentFinalBlock.Number.Uint64())
		log.Info("Loaded most recent local finalized block", "number", currentFinalBlock.Number, "hash", currentFinalBlock.Hash(), "td", finalTd, "age", common.PrettyAge(time.Unix(int64(currentFinalBlock.Time), 0)))
	}
	if pivot := rawdb.ReadLastPivotNumber(bc.db); pivot != nil {
		log.Info("Loaded last snap-sync pivot marker", "number", *pivot)
	}
	return nil
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
	block := bc.GetBlock(header.Hash(), header.Number.Uint64())
	if block == nil {
		// This should never happen. In practice, previously currentBlock
		// contained the entire block whereas now only a "marker", so there
		// is an ever so slight chance for a race we should handle.
		log.Error("Current block not found in database", "block", header.Number, "hash", header.Hash())
		return fmt.Errorf("current block missing: #%d [%x..]", header.Number, header.Hash().Bytes()[:4])
	}
	bc.chainHeadFeed.Send(ChainHeadEvent{Block: block})
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
	block := bc.GetBlock(header.Hash(), header.Number.Uint64())
	if block == nil {
		// This should never happen. In practice, previously currentBlock
		// contained the entire block whereas now only a "marker", so there
		// is an ever so slight chance for a race we should handle.
		log.Error("Current block not found in database", "block", header.Number, "hash", header.Hash())
		return fmt.Errorf("current block missing: #%d [%x..]", header.Number, header.Hash().Bytes()[:4])
	}
	bc.chainHeadFeed.Send(ChainHeadEvent{Block: block})
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

// unapplyHvmHeaderConsensusUpdate retrieves the block corresponding to
// the provided block header, extracts its Bitcoin Attributes Deposited
// transaction and, if it exists, removes the header information contained
// in it from the protocol's lightweight view of Bitcoin and verifies that
// TBC has been correctly returned to the canonical tip claimed by the
// previous block which contains a Bitcoin Attributes Deposited tx.
func (bc *BlockChain) unapplyHvmHeaderConsensusUpdate(header *types.Header) error {
	block := bc.getBlockFromDiskOrHoldingPen(header.Hash())
	if block == nil {
		return fmt.Errorf("unable to get block %s @ %d to unapply hVM consensus updates",
			header.Hash().String(), header.Number.Uint64())
	}

	// When we unapply the current block, TBC's state will reflect that of the
	// previous block
	prevBlock := bc.getHeaderFromDiskOrHoldingPen(header.ParentHash)
	stateTransitionTargetHash := [32]byte{}

	if bc.chainConfig.IsHvm0(header.Time) && !bc.chainConfig.IsHvm0(prevBlock.Time) {
		// Special case, we are unapplying the hVM state transition for the activation block,
		// so set the state transition target hash back to the genesis default
		copy(stateTransitionTargetHash[0:32], hVMGenesisUpstreamId[0:32])
	} else {
		// Previous block had hVM active
		copy(stateTransitionTargetHash[0:32], prevBlock.Hash().Bytes()[0:32])
	}

	btcAttrDep, err := block.Transactions().ExtractBtcAttrData()
	if err != nil {
		// Error implies that state of Bitcoin Attributes Deposited tx in the transaction list is invalid.
		// This should be impossible because any block which is being unapplied would have undergone the
		// same check previously and passed.
		// TODO: Bubble this error up and invalidate this previous block?
		log.Crit(fmt.Sprintf("Error while extracting Bitcoin Attributes Deposited transaction to unwind "+
			"hVM state application for block %s @ %d", header.Hash().String(), header.Number.Uint64()),
			"err", err)
	}

	if btcAttrDep == nil {
		log.Info(fmt.Sprintf("Nothing to unapply in hVM state for block %s @ %d; doesn't contain a Bitcoin "+
			"Attributes Deposited transaction", header.Hash().String(), header.Number.Uint64()))

		// There is no Bitcoin Attributes Deposited transaction in this block to unapply.
		// Even though we didn't make any changes, explicitly update TBC's state id to indicate that
		// TBC's current state is correct for previous after removing this block. The
		// stateTransitionTargetHash is already set to the previous block or the genesis upsteam ID
		// depending on whether previous parent had hVM Phase 0 active or not.
		if bc.chainConfig.IsHvm0(header.Time) {
			err := bc.tbcHeaderNode.SetUpstreamStateId(context2.Background(), &stateTransitionTargetHash)
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

	currentTipHeight, currentTip, err := bc.tbcHeaderNode.BlockHeaderBest(context2.Background())
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
	// TODO: Get this state more efficiently from HvmState contract in EVM?
	var expectedPreviousTipHash [32]byte
	cursorNum := header.Number.Uint64() - 1
	cursor := bc.getBlockFromDiskOrHoldingPen(header.ParentHash)
	for bc.chainConfig.IsHvm0(cursor.Time()) {
		oldBtcAttrDep, err := cursor.Transactions().ExtractBtcAttrData()
		if err != nil {
			// Error implies that state of Bitcoin Attributes Deposited tx in the transaction list is invalid.
			// This should be impossible because any block which is being unapplied would have undergone the
			// same check previously and passed.
			// TODO: Bubble this error up to invalidate the old block?
			log.Crit(fmt.Sprintf("Error while extracting Bitcoin Attributes Deposited transaction from "+
				"prior block %s @ %d when attempting to unwind hVM state application for block %s @ %d",
				cursor.Hash().String(), cursorNum, header.Hash().String(), header.Number.Uint64()), "err", err)
		}
		if oldBtcAttrDep != nil {
			// Found previous state
			expectedPreviousTipHash = oldBtcAttrDep.CanonicalTip
			break
		}
		cursor = bc.getBlockFromDiskOrHoldingPen(cursor.ParentHash())
	}
	if bytes.Equal(expectedPreviousTipHash[:], []byte{}) {
		genHash := bc.tbcHeaderNodeConfig.EffectiveGenesisBlock.BlockHash()
		copy(expectedPreviousTipHash[0:32], genHash[0:32])
		log.Info("when unapplying hVM changes for block %s @ %d, got to block %s @ %d with timestamp "+
			"%d which is before the hVM Phase 0 activation timestamp %d, so previous canonical tip should be "+
			"the genesis block %x", header.Hash().String(), header.Number.Uint64(), cursor.Hash().String(),
			cursor.NumberU64(), cursor.Time, bc.chainConfig.Hvm0Time, genHash[:])
	}

	// Get the actual header represented by the previous canonical tip hash
	expectedPreviousTipHashParsed, err := chainhash.NewHash(expectedPreviousTipHash[:])
	if err != nil {
		log.Warn(fmt.Sprintf("Unable to create blockhash from %x", expectedPreviousTipHash[:]))
	}

	expectedPreviousTip, expectedPreviousTipHeight, err :=
		bc.tbcHeaderNode.BlockHeaderByHash(context2.Background(), expectedPreviousTipHashParsed)

	if err != nil {
		// This should never happen, it means TBC doesn't have a header which either:
		// 1. Should have already been added to it when this older block was originally processed, or
		// 2. Is the genesis block TBC is configured with
		// TODO: TBC recovery from genesis
		log.Crit(fmt.Sprintf("when unapplying hVM changes for block %s @ %d, previous canonical tip "+
			"should be %x but TBC encountered an error when fetching that header", header.Hash().String(),
			header.Number.Uint64(), expectedPreviousTipHash[:]))
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

	reconstitutedHeaders, err := unflattenBTCHeaders(btcAttrDep.Headers)
	if err != nil {
		// This is a critical failure as the headers should be valid if the hVM consensus update we are
		// unapplying was able to be applied in the first place
		log.Crit(fmt.Sprintf("when unapplying hVM changes for block %s @ %d, unable to unflatten "+
			"one of the BTC headers from the block", header.Hash().String(), header.Number.Uint64()),
			"err", err)
	}

	rt, lastHeader, err := bc.tbcHeaderNode.RemoveExternalHeaders(
		context2.Background(), reconstitutedHeaders, expectedPreviousTip, &stateTransitionTargetHash)
	if err != nil {
		// This is a critical failure, not related to block validity
		// TODO: TBC recovery from genesis
		log.Crit(fmt.Sprintf("when unapplying hVM changes from block %s @ %d, unable to remove "+
			"%d headers and change the canonical tip from %s @ %d to %x @ %d", header.Hash().String(),
			header.Number.Uint64(), len(btcAttrDep.Headers), currentTipHash.String(), currentTipHeight,
			expectedPreviousTipHash[:], expectedPreviousTipHeight), "err", err)
	}
	lastHeaderHash := lastHeader.BlockHash()

	newHeight, newTip, err := bc.tbcHeaderNode.BlockHeaderBest(context2.Background())
	if err != nil {
		// TODO: TBC recovery from genesis
		log.Crit(fmt.Sprintf("when unapplying hVM changes from block %s @ %d, attempted to remove "+
			"%d headers and change the canonical tip from %s @ %d to %x @ %d, but TBC reports an error "+
			"getting the canonical tip after state transition", header.Hash().String(),
			header.Number.Uint64(), len(btcAttrDep.Headers), currentTipHash.String(), currentTipHeight,
			expectedPreviousTipHash[:], expectedPreviousTipHeight), "err", err)
	}

	newTipHash := newTip.BlockHash()

	if !bytes.Equal(newTipHash[:], expectedPreviousTipHash[:]) {
		// TODO: TBC recovery from genesis
		log.Crit(fmt.Sprintf("when unapplying hVM changes from block %s @ %d, attempted to remove "+
			"%d headers and change the canonical tip from %s @ %d to %x @ %d, but TBC reports that the "+
			"canonical tip after state transition is %x @ %d which is incorrect", header.Hash().String(),
			header.Number.Uint64(), len(btcAttrDep.Headers), currentTipHash.String(), currentTipHeight,
			expectedPreviousTipHash[:], expectedPreviousTipHeight, newTipHash[:], newHeight), "err", err)
	}

	log.Info(fmt.Sprintf("successfully unapplied hVM changes from block %s @ %d, removed %d headers "+
		"and changed the canonical tip from %s @ %d to %x @ %d, last header before removed chunk is %x, rt=%d",
		header.Hash().String(), header.Number.Uint64(), len(btcAttrDep.Headers), currentTipHash.String(),
		currentTipHeight, expectedPreviousTipHash[:], expectedPreviousTipHeight, lastHeaderHash[:], rt))

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

// applyHvmHeaderConsensusUpdate retrieves the block corresponding to
// the provided block header, extracts its Bitcoin Attributes Deposited
// transaction and, if it exists, applies the headers contained in it
// to the protocol's lightweight view of Bitcoin and verifies that the
// claimed canonical tip is correct.
func (bc *BlockChain) applyHvmHeaderConsensusUpdate(header *types.Header) error {
	block := bc.getBlockFromDiskOrHoldingPen(header.Hash())
	if block == nil {
		// Block not on disk or in holding pen
		return fmt.Errorf("unable to get block %s @ %d to apply hVM consensus updates",
			header.Hash().String(), header.Number.Uint64())
	}

	stateTransitionTargetHash := [32]byte{}
	copy(stateTransitionTargetHash[0:32], header.Hash().Bytes()[0:32])

	// Store the current TBC state hash so we can put it back if we revert our changes here
	previousStateTransitionHash, err := bc.tbcHeaderNode.UpstreamStateId(context2.Background())
	if err != nil {
		log.Crit("Unable to get upstream state id from TBC", "err", err)
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
		checkHash := check.Hash()
		if !bytes.Equal(checkHash[:], header.ParentHash[:]) {
			log.Crit(fmt.Sprintf("Applying hVM header update for block %s @ %d failed, "+
				"previous state id is %x but parent of updated block is %s @ %d",
				header.Hash().String(), header.Number.Uint64(), previousStateTransitionHash[:],
				header.ParentHash[:], header.Number.Uint64()-1))
		}
	}

	btcAttrDep, err := block.Transactions().ExtractBtcAttrData()
	if err != nil {
		// Error implies that state of Bitcoin Attributes Deposited tx in the transaction list is invalid
		// TODO: Bubble this error up to cause a block rejection instead
		log.Crit(fmt.Sprintf("Error while extracting Bitcoin Attributes Deposited transaction to process hVM state "+
			"application for applying block %s @ %d", header.Hash().String(), header.Number.Uint64()), "err", err)
	}

	if btcAttrDep == nil {
		log.Info(fmt.Sprintf("Nothing to apply in hVM state for block %s @ %d; doesn't contain a Bitcoin "+
			"Attributes Deposited transaction", header.Hash().String(), header.Number.Uint64()))

		// Even though we didn't make any changes, explicitly update TBC's state id to indicate that
		// TBC's current state is correct after processing this block if hVM Phase 0 is active at
		// this block's timestamp
		if bc.chainConfig.IsHvm0(header.Time) {
			err := bc.tbcHeaderNode.SetUpstreamStateId(context2.Background(), &stateTransitionTargetHash)
			if err != nil {
				// TODO: Recovery mode that resets TBC header mode to genesis configuration and rebuilds it from hVM activation block
				log.Crit(fmt.Sprintf("Error while updating the upstream state id in TBC with no corresponding "+
					"consensus state modifications for block %s @ %d", header.Hash().String(), header.Number.Uint64()), "err", err)
			}
		}
		return nil
	}

	if !bc.chainConfig.IsHvm0(header.Time) { // && btcAttrDep != nil per above check
		// TODO: Bubble this error up to cause a block rejection instead
		log.Crit(fmt.Sprintf("block %s @ %d has a Bitcoin Attributes Deposited transaction but its timestamp "+
			"%d is before the hVM Phase 0 activation height %d", header.Hash().String(), header.Number.Uint64(),
			header.Time, *bc.chainConfig.Hvm0Time))
	}

	prevHeight, prevTip, err := bc.tbcHeaderNode.BlockHeaderBest(context2.Background())
	if err != nil {
		// This is a critical TBC failure, not related to block validity
		// TODO: Recovery mode that resets TBC header mode to genesis configuration and rebuilds it from hVM activation block
		log.Crit(fmt.Sprintf("when processing block %s @ %d, unable to retrieve tip from lightweight TBC!",
			header.Hash().String(), header.Number.Uint64()), "err", err)
	}
	log.Info(fmt.Sprintf("before processing BTC headers from block %s @ %d, the lightweight TBC node's tip "+
		"is %s @ %d", header.Hash().String(), header.Number.Uint64(), prevTip.BlockHash().String(), prevHeight))

	prevTipHash := prevTip.BlockHash()

	headersToAdd := len(btcAttrDep.Headers)
	var lastHeader *[80]byte
	if headersToAdd > 0 {
		// BTC Attributes Deposited transaction communicates at least one new header, store the last one for reference
		lastHeader = &btcAttrDep.Headers[headersToAdd-1]

		reconstitutedHeaders, err := unflattenBTCHeaders(btcAttrDep.Headers)
		if err != nil {
			// TODO: Bubble this error up to cause a block rejection instead
			log.Crit(fmt.Sprintf("when unapplying hVM changes for block %s @ %d, unable to unflatten "+
				"one of the BTC headers from the block", header.Hash().String(), header.Number.Uint64()),
				"err", err)
		}

		it, cbh, lbh, _, err := bc.tbcHeaderNode.AddExternalHeaders(
			context2.Background(), reconstitutedHeaders, &stateTransitionTargetHash)
		if err != nil {
			// TODO: Bubble this error up to cause a block rejection instead
			log.Crit(fmt.Sprintf("block %s @ %d has a Bitcoin Attributes Deposited transaction which contains"+
				" %d Bitcoin headers, and adding these headers to the protocol's Bitcoin view caused an error",
				header.Hash().String(), header.Number.Uint64(), len(btcAttrDep.Headers)), "err", err)
		}

		cbHash := cbh.Hash[:]
		// Check that the Bitcoin Attributes Deposited transaction claims the correct canonical tip
		if !bytes.Equal(cbHash, btcAttrDep.CanonicalTip[:]) {
			// Canonical tip determined by TBC based on the new headers does not match canonical tip claimed by
			// Bitcoin Attributes Deposited transaction
			// TODO: Bubble this error up to cause a block rejection instead

			// Print out error, then remove the bad headers to return TBC to the correct state
			log.Error(fmt.Sprintf("block %s @ %d has a Bitcoin Attributes Deposited transaction which "+
				"claims that after adding %d headers ending with %x, the canonical tip should be %x, but after "+
				"adding the headers to TBC the canonical tip is %x", header.Hash().String(), header.Number.Uint64(),
				headersToAdd, lastHeader[:], btcAttrDep.CanonicalTip[:], cbHash[:]))

			// Remove the added headers and set the canonical tip and previous upstream state id back to
			// what it was prior to the invalid addition
			rt, removalParent, err := bc.tbcHeaderNode.RemoveExternalHeaders(
				context2.Background(), reconstitutedHeaders, prevTip, previousStateTransitionHash)

			if err != nil {
				// TODO: Recovery
				log.Crit(fmt.Sprintf("after adding headers ending with %x from the Bitcoin Attributes "+
					" Deposited transaction in block %s @ %d, unable to remove those headers from TBC's view",
					lastHeader[:], header.Hash().String(), header.Number), "err", err)
			}

			removalParentHash := removalParent.BlockHash()

			// TODO: Bubble this error up to cause a block rejection instead
			log.Crit(fmt.Sprintf("successfully removed headers applied from invalid block %s @ %d, last header "+
				"before removed section is %x. Removal type: %d", header.Hash().String(), header.Number.Uint64(),
				removalParentHash[:], rt))
		}

		lbHash := lbh.Hash[:]
		if !bytes.Equal(lbh.Header[:], lastHeader[:]) {
			// Indicates a bug in TBC, as TBC didn't add all the headers we passed in
			log.Crit(fmt.Sprintf("block %s @ %d has a Bitcoin Attributes Deposited transaction which "+
				"contains %d headers ending in %x, but after adding those headers to lightweight TBC, TBC's last "+
				"added block was %x", header.Hash().String(), header.Number.Uint64(), headersToAdd, lastHeader[:],
				lbHash[:]))
		}

		log.Info(fmt.Sprintf("Successfully added %d bitcoin headers from the Bitcoin Attributes Deposited tx "+
			"from block %s @ %d, current canonical tip is %x, former tip was %x @ %d, insertType=%d", headersToAdd,
			header.Hash().String(), header.Number.Uint64(), lbHash[:], prevTipHash[:], prevHeight, it))
		return nil
	} else {
		// No headers to add, make sure that claimed canonical in BTC Attributes Deposited matches TBC's current
		if !bytes.Equal(prevTipHash[:], btcAttrDep.CanonicalTip[:]) {
			// TODO: Bubble this error up to cause a block rejection instead
			log.Crit(fmt.Sprintf("block %s @ %d contains a Bitcoin Attributes Deposited transaction which "+
				"does not contain any headers, but claims the canonical tip should be %x when light TBC's tip "+
				"is %x", header.Hash().String(), header.Number.Uint64(), btcAttrDep.CanonicalTip[:], prevTipHash[:]))
		}
		return nil
	}
	// Catch-all because we don't have returns after log.Crits which are going to be replaced with appropriate recovery action
	return fmt.Errorf("unspecified error")
}

func (bc *BlockChain) IsHvmEnabled() bool {
	return bc.hvmEnabled
}

// GetBitcoinAttributesForNextBlock generates a new Bitcoin Attributes Deposited transaction which
// should be added to the next EVM block.
func (bc *BlockChain) GetBitcoinAttributesForNextBlock(timestamp uint64) (*types.BtcAttributesDepositedTx, error) {
	// Lock the chain mutex - all other code that modifies lightweight TBC node respects this mutex
	// and locking this resource ensures that we can safely modify the lightweight TBC node to ensure
	// the new the Bitcoin Attributes Deposited transaction we generate can be successfully applied
	// when it occurs in a block for real, and also to ensure the canonical tip we report matches what
	// canonical tip lightweight TBC will report after the specified headers are added.
	if !bc.chainmu.TryLock() {
		return nil, errChainStopped
	}
	defer bc.chainmu.Unlock()

	// Don't generate a Bitcoin Attributes deposited transaction unless we're building for a recent block.
	// XXX: Move this upstream?
	if timestamp-uint64(time.Now().Unix()) > 60*60 {
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

	lastTip := bc.CurrentBlock()
	if lastTip == nil {
		log.Crit("Unable to generate the Bitcoin Attributes Deposited transaction, as the current EVM tip " +
			"is unknown!")
	}
	lastTipHash := lastTip.Hash()

	log.Info(fmt.Sprintf("Generating Bitcoin Attributes Deposited transaction for a new block with timestamp "+
		"%d on top of prior block %s @ %d", timestamp, lastTip.Hash().String(), lastTip.Number.Uint64()))

	if bytes.Equal(bc.btcAttributesDepCacheBlockHash[:], lastTipHash[:]) {
		if bc.btcAttributesDepCacheEntry != nil {
			return bc.btcAttributesDepCacheEntry, nil
		}
	}

	// Sanity check: lightweight TBC node's state should always reflect lastTip when this is called.
	// If it doesn't, log the error and manually move the lightweight node to represent the current
	// tip so we can return valid data.
	currentTbcEvmTip, err := bc.getHeaderModeTBCEVMHeader()
	if err != nil {
		log.Crit(fmt.Sprintf("Unable to get the EVM block that lightweight TBC's state represents "+
			"while trying to generate a Bitcoin Attributes Deposited transaction for the next block after "+
			"%s @ %d", lastTip.Hash().String(), lastTip.Number.Uint64()), "err", err)
	}
	if currentTbcEvmTip != nil {
		if currentTbcEvmTip.Hash().Cmp(lastTip.Hash()) != 0 {
			log.Error(fmt.Sprintf("When attempting to generate a Bitcoin Attributes Deposited transaction "+
				"for the next block after %s @ %d, lightweight TBC represents an incorrect EVM state of %s @ %d",
				lastTip.Hash().String(), lastTip.Number.Uint64(), currentTbcEvmTip.Hash().String(),
				currentTbcEvmTip.Number.Uint64()))

			// Attempting to generate Bitcoin Attributes Deposited transaction for the block after current tip
			// but lightweight TBC's state isn't at the current tip, move it here manually
			err := bc.updateHvmHeaderConsensus(lastTip)
			if err != nil {
				log.Crit(fmt.Sprintf("When attempting to generate a Bitcoin Attributes Deposited transaction "+
					"for the next block after %s @ %d, lightweight TBC represented an incorrect EVM state of %s @ %d "+
					"and an error occurred trying to move its EVM state.",
					lastTip.Hash().String(), lastTip.Number.Uint64(), currentTbcEvmTip.Hash().String(),
					currentTbcEvmTip.Number.Uint64()))
			}
			// TODO: decide whether to move TBC back to the "bad" (non-tip) state after this calculation.
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

	originalTbcUpstreamId, err := bc.tbcHeaderNode.UpstreamStateId(context2.Background())
	if err != nil {
		log.Crit(fmt.Sprintf("Unable to get the upstream state id from TBC when creating the Bitcoin "+
			"Attributes Deposited transaction for the block after %s @ %d ", lastTip.Hash().String(),
			lastTip.Number.Uint64()), "err", err)
	}

	// Get current tips known by our lightweight and full TBC nodes
	lightTipHeight, lightTipHeader, err := bc.tbcHeaderNode.BlockHeaderBest(context2.Background())
	if err != nil {
		log.Crit(fmt.Sprintf("Unable to get the best block header from lightweight TBC node when attempting "+
			"to calculate the Bitcoin Attributes Deposited transaction for next block after %s @ %d",
			lastTip.Hash().String(), lastTip.Number.Uint64()), "err", err)
	}
	lightTipHash := lightTipHeader.BlockHash()

	fullTipHeight, fullTipHeader, err := vm.TBCFullNode.BlockHeaderBest(context2.Background())
	if err != nil {
		log.Crit(fmt.Sprintf("Unable to get the best block header from TBC full node when attempting "+
			"to calculate the Bitcoin Attributes Deposited transaction for next block after %s @ %d",
			lastTip.Hash().String(), lastTip.Number.Uint64()), "err", err)
	}
	fullTipHash := fullTipHeader.BlockHash()

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
		header, height, err := bc.tbcHeaderNode.BlockHeaderByHash(context2.Background(), &lightCursorHeader.PrevBlock)
		if err != nil {
			// Should never happen, implies lightweight TBC has a header before its current
			// canonical tip which it is unable to return, probably signals corruption.
			// TODO: Lightweight TBC recovery from genesis
			log.Crit(fmt.Sprintf("Unable to get header %x @ %d from lightweight TBC node when walking "+
				"backwards from %x @ %d", lightCursorHeader.PrevBlock[:], lightCursorHeight-1,
				lightCursorHash[:], lightCursorHeight), "err", err)
		}
		if height != lightCursorHeight-1 {
			// Should never happen, means lightweight TBC node is returning bad heights
			log.Crit(fmt.Sprintf("Lightweight TBC node returned an incorrect height for block %x: "+
				"expected %d but got %d", lightCursorHeader.PrevBlock[:], lightCursorHeight-1, height))
		}
		lightCursorHeader = header
		lightCursorHeight = height // same as lightCursorHeight - 1
		lightCursorHash = lightCursorHeader.BlockHash()
	}
	// Walk back the full cursor until we get to the same height if it's ahead
	for fullCursorHeight > lightCursorHeight {
		// Get height even though we could calculate it as a sanity check
		header, height, err := vm.TBCFullNode.BlockHeaderByHash(context2.Background(), &fullCursorHeader.PrevBlock)
		if err != nil {
			// Should never happen, implies full TBC node has a header before its current
			// canonical tip which it is unable to return, probably signals corruption.
			// TODO: Full TBC node recovery?
			log.Crit(fmt.Sprintf("Unable to get header %x @ %d from full TBC node when walking "+
				"backwards from %x @ %d", fullCursorHeader.PrevBlock[:], fullCursorHeight-1,
				fullCursorHash[:], fullCursorHeight), "err", err)
		}
		if height != fullCursorHeight-1 {
			// Should never happen, means full TBC node is returning bad heights
			log.Crit(fmt.Sprintf("Full TBC node returned an incorrect height for block %x: "+
				"expected %d but got %d", fullCursorHeader.PrevBlock[:], fullCursorHeight-1, height))
		}
		fullCursorHeader = header
		fullCursorHeight = height // same as fullCursorHeight - 1
		fullCursorHash = fullCursorHeader.BlockHash()
	}

	// Whether or not lightweight and full TBC nodes are on the same chain,
	// we will find their common ancestor (which will be the same as
	// one of the node's tips if they are on the same chain) which we can
	// use to only perform walk-back logic once rather than separately for
	// the different forking scenarios.
	var commonAncestorHash chainhash.Hash

	// Now the cursors for the lightweight and full node chains are at the same height.
	// If both cursors match, both chains' current tips are on the same chain.
	if bytes.Equal(fullCursorHash[:], lightCursorHash[:]) {
		// They match, so they are on the same chain.
		if lightTipHeight > fullTipHeight {
			// Lightweight TBC has consensus ahead of full tip, on same chain,
			// so nothing to do.
			//
			// We didn't check this until we got the block from both chains
			// at the lowest height of either tip, because there is an edge
			// edge case where lightweight tip could have been previously
			// advanced onto a fork that is higher than canonical block known
			// by the full node, but the full node still contains one or more
			// headers on its canonical chain that should be communicated to
			// the lightweight view.
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
			lHeader, lHeight, err := bc.tbcHeaderNode.BlockHeaderByHash(context2.Background(), &lightCursorHeader.PrevBlock)
			if err != nil {
				// Should never happen, implies lightweight TBC has a header before its current
				// canonical tip which it is unable to return, probably signals corruption.
				// TODO: Lightweight TBC recovery from genesis
				log.Crit(fmt.Sprintf("Unable to get header %x @ %d from lightweight TBC node when walking "+
					"backwards from %x @ %d", lightCursorHeader.PrevBlock[:], lightCursorHeight-1,
					lightCursorHash[:], lightCursorHeight), "err", err)
			}
			if lHeight != lightCursorHeight-1 {
				// Should never happen, means lightweight TBC node is returning bad heights
				log.Crit(fmt.Sprintf("Lightweight TBC node returned an incorrect height for block %x: "+
					"expected %d but got %d", lightCursorHeader.PrevBlock[:], lightCursorHeight-1, lHeight))
			}

			fHeader, fHeight, err := vm.TBCFullNode.BlockHeaderByHash(context2.Background(), &fullCursorHeader.PrevBlock)
			if err != nil {
				// Should never happen, implies full TBC node has a header before its current
				// canonical tip which it is unable to return, probably signals corruption.
				// TODO: Full TBC node recovery?
				log.Crit(fmt.Sprintf("Unable to get header %x @ %d from full TBC node when walking "+
					"backwards from %x @ %d", fullCursorHeader.PrevBlock[:], fullCursorHeight-1,
					fullCursorHash[:], fullCursorHeight), "err", err)
			}
			if fHeight != fullCursorHeight-1 {
				// Should never happen, means full TBC node is returning bad heights
				log.Crit(fmt.Sprintf("Full TBC node returned an incorrect height for block %x: "+
					"expected %d but got %d", fullCursorHeader.PrevBlock[:], fullCursorHeight-1, fHeight))
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
		tHeader, tHeight, err := vm.TBCFullNode.BlockHeaderByHash(context2.Background(), &cursorHeader.PrevBlock)
		if err != nil {
			// Should never happen, implies full TBC node has a header before its current
			// canonical tip which it is unable to return, probably signals corruption.
			// TODO: Full TBC node recovery?
			log.Crit(fmt.Sprintf("Unable to get header %x @ %d from full TBC node when walking "+
				"backwards from %x @ %d", cursorHeader.PrevBlock[:], cursorHeight-1,
				cursorHash[:], cursorHeight), "err", err)
		}
		if tHeight != cursorHeight-1 {
			// Should never happen, means full TBC node is returning bad heights
			log.Crit(fmt.Sprintf("Full TBC node returned an incorrect height for block %x: "+
				"expected %d but got %d", cursorHeader.PrevBlock[:], cursorHeight-1, tHeight))
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
		return nil, nil
	}

	var headersToAdd []wire.BlockHeader
	// Check that none of the headers we are going to add are already known by lightweight TBC.
	// This is possible in an edge case where we are communicating a reorg, as lightweight
	// TBC could know some blocks on the fork since the common ancestor which we didn't
	// yet check for. Note headersToTip is in reverse order.
	for index := len(headersToTip) - 1; index >= 0; index-- {
		headerToAdd := headersToTip[index]
		headerToAddHash := headerToAdd.BlockHash()
		_, _, err := bc.tbcHeaderNode.BlockHeaderByHash(context2.Background(), &headerToAddHash)
		if err != nil { // Error means header was not found
			// TODO: Make sure the error is a NotFoundError, not some other failure
			headersToAdd = append(headersToAdd, headerToAdd)
		}
	}

	// It's possible that all headers were already known by lightweight TBC if it is
	// fully aware of the alternate chain in a chain-split scenario.
	if len(headersToAdd) == 0 {
		return nil, nil
	}

	// Trim headersToAdd to the maximum number of headers we are allowed to include.
	// if len(headersToAdd) > types.MaximumBtcHeadersInTx {
	// 	headersToAdd = headersToAdd[0:types.MaximumBtcHeadersInTx]
	// }
	if len(headersToAdd) > 3 {
		headersToAdd = headersToAdd[0:3] // Temporarily limit to 3 at generation level, not validation level
	}

	// Walk up headersToAdd, and truncate blocks that TBC Full Node does not have complete information for
	for i := 0; i < len(headersToAdd); i++ {
		hashToCheck := headersToAdd[i].BlockHash()
		headerAvailable, err := vm.TBCFullNode.FullBlockAvailable(context2.Background(), &hashToCheck)
		if err != nil {
			log.Crit(fmt.Sprintf("Generating Bitcoin Attributes Deposited transaction for the next block after "+
				"%s @ %d, but TBC full node was unable to determine whether the full block for hash %s is available",
				lastTip.Hash().String(), lastTip.Number.Uint64(), hashToCheck.String()), "err", err)
		}

		if !headerAvailable {
			// Header is not available; if this is the first block then return nothing, otherwise truncate
			if i == 0 {
				// No blocks to add
				return nil, nil
			} else {
				log.Info(fmt.Sprintf("Generating Bitcoin Attributes Deposited transaction for the next block "+
					"after %s @ %d, and TBC Full Node does not have the full block for %s, so removing from headers "+
					"to add to hVM's lightweight view", lastTip.Hash().String(), lastTip.Number.Uint64(),
					hashToCheck.String()))

				headersToAdd = headersToAdd[0 : i-1]
				break
			}
		}
	}

	// Serialize headers to bytes
	headersToAddSerialized, err := types.SerializeHeadersToArray(headersToAdd)
	if err != nil {
		log.Crit(fmt.Sprintf("Unable to serialize Bitcoin headers to create Bitcoin Attributes Deposited "+
			"transaction for the block after %s @ %d", lastTip.Hash().String(), lastTip.Number.Uint64()), "err", err)
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

	_, canonical, _, _, err := bc.tbcHeaderNode.AddExternalHeaders(
		context2.Background(),
		msgHeaders,
		&hVMDummyUpstreamId)

	if err != nil {
		first := headersToAdd[0].BlockHash()
		last := headersToAdd[len(headersToAdd)-1].BlockHash()
		log.Crit(fmt.Sprintf("Unable to add %d external headers %x to %x to lightweight TBC view on top "+
			"of prior canonical tip %x @ %d!", len(*headersToAddSerialized), first[:], last[:], lightTipHash,
			lightTipHeight), "err", err)
		return nil, err
	}

	// Revert lightweight TBC's view back to what it was before we started.
	rt, prevHeader, err := bc.tbcHeaderNode.RemoveExternalHeaders(context2.Background(), msgHeaders, lightTipHeader, originalTbcUpstreamId)
	if err != nil {
		first := headersToAdd[0].BlockHash()
		last := headersToAdd[len(headersToAdd)-1].BlockHash()
		log.Crit(fmt.Sprintf("Unable to remove %d external headers %x to %x from lightweight TBC view after "+
			"they were temporarily added when creating the Bitcoin Attributes Deposited transaction for the block "+
			"after %s @ %d", len(*headersToAddSerialized), first[:], last[:], lastTip.Hash().String(),
			lastTip.Number.Uint64()), "err", err)
	}

	log.Info(fmt.Sprintf("Successfully removed %d block headers from lightweight TBC view after temporarily "+
		"adding them when generating the Bitcoin Attributes Deposited transaction for the block after %s @ %d. "+
		"RemoveType=%d, prevHeader=%x", len(*headersToAddSerialized), lastTip.Hash().String(), lastTip.Number.Uint64(),
		rt, prevHeader.Hash[:]))

	canonHashAfterDepTx := canonical.BlockHash()
	btcAttrDepTx, err := types.MakeBtcAttributesDepositedTx(canonHashAfterDepTx, headersToAdd)
	if err != nil {
		log.Crit(fmt.Sprintf("Unable to construct a Bitcoin Attributes Deposited tx containing %d headers "+
			"with canonical hash %x for placement in the block after %s @ %d", len(headersToAdd),
			canonHashAfterDepTx[:], lastTip.Hash().String(), lastTip.Number.Uint64()), "err", err)
	}

	// Store the calculated Bitcoin Attributes Deposited transaction so we don't need to recalculate
	// it on subsequent calls to build on top of the same parent.
	bc.btcAttributesDepCacheBlockHash = lastTip.Hash()
	bc.btcAttributesDepCacheEntry = btcAttrDepTx

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
			return nil, fmt.Errorf(fmt.Sprintf("headersBetweenBlocks could not retrieve header %s @ %d",
				cursor.ParentHash.String(), cursor.Number.Uint64()-1))
		}
		path[index] = cursorTmp
		cursor = cursorTmp
	}

	return path, nil
}

func (bc *BlockChain) walkHvmHeaderConsensusForward(currentHead *types.Header, newHead *types.Header) error {
	// Can't walk forwards from a block that is the same height or higher than the destination
	if currentHead.Number.Uint64() >= newHead.Number.Uint64() {
		return fmt.Errorf(fmt.Sprintf("Cannot walk hVM consensus forewards from "+
			"%s @ %d to %s @ %d - bad geometry", currentHead.Hash().String(), currentHead.Number.Uint64(),
			newHead.Hash().String(), newHead.Number.Uint64()))
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
		err := bc.applyHvmHeaderConsensusUpdate(headers[index])
		if err != nil {
			// TODO: Invalidate the failing block OR attempt to recover hVM state from genesis
			return fmt.Errorf("unable to apply the hVM header state transition for block %s @ %d, err: %v",
				headers[index].Hash().String(), headers[index].Number.Uint64(), err)
		}
	}

	return nil
}

func (bc *BlockChain) walkHvmHeaderConsensusBack(currentHead *types.Header, newHead *types.Header) error {
	// Can't walk backwards from a block that is the same height or lower than the destination
	if currentHead.Number.Uint64() <= newHead.Number.Uint64() {
		return fmt.Errorf(fmt.Sprintf("Cannot walk hVM consensus backwards from "+
			"%s @ %d to %s @ %d - bad geometry", currentHead.Hash().String(), currentHead.Number.Uint64(),
			newHead.Hash().String(), newHead.Number.Uint64()))
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
			return fmt.Errorf("walking backwards from block %s @ %d, reached block %s @ %d but "+
				"was expecting the block at index %d to be %s which is the new head we are unwinding to",
				currentHead.Hash().String(), currentHead.Number.Uint64(), cursor.Hash().String(),
				cursor.Number.Uint64(), cursor.Number.Uint64(), newHead.Hash().String())
		}

		err := bc.unapplyHvmHeaderConsensusUpdate(cursor)
		if err != nil {
			log.Crit(fmt.Sprintf("Unable to unapply the hVM header %s @ %d",
				cursor.Hash().String(), cursor.Number.Uint64()), "err", err)
		}
		newCursor := bc.getHeaderFromDiskOrHoldingPen(cursor.ParentHash)
		if newCursor == nil {
			log.Crit(fmt.Sprintf("Unable to get header for block %s @ %d",
				cursor.ParentHash.String(), cursor.Number.Uint64()-1))
		}
		cursor = newCursor
	}

	// We expect hVM to have an upstream state id corresponding to newHead, sanity check it
	upstreamStateId, err := bc.tbcHeaderNode.UpstreamStateId(context2.Background())
	if err != nil {
		return err
	}
	if !bytes.Equal(upstreamStateId[:], newHead.Hash().Bytes()[:]) {
		return fmt.Errorf("after walking backwards from block %s @ %d to %s @ %d, expected TBC "+
			"upstream state id to be %s but got %x instead", currentHead.Hash().String(), currentHead.Number.Uint64(),
			newHead.Hash().String(), newHead.Number.Uint64(), newHead.Hash().String(), upstreamStateId[:])
	}

	return nil
}

func (bc *BlockChain) updateFullTBCToLightweight() error {
	// Update TBC Full Node's indexing to represent lightweight view minus 2 BTC blocks
	lightTipHeight, lightTipHeader, err := bc.tbcHeaderNode.BlockHeaderBest(context2.Background())
	if err != nil {
		return err
	}
	lightTipHash := lightTipHeader.BlockHash()

	cursorHeight, cursorHeader := lightTipHeight, lightTipHeader
	cursorHash := cursorHeader.BlockHash()

	// Special case to fix an issue with testnet3 difficulty bomb - when difficulty is low, give a longer tip lag
	// TODO: Review logic before updating public testnet
	effectiveHVMIndexerTipLag := uint64(hVMIndexerTipLag)
	lowDiffThreshold := blockchain.CalcWork(436469756) // = 0x1a03fffc = difficulty of 4194304
	tipDiff := blockchain.CalcWork(cursorHeader.Bits)
	if tipDiff.Cmp(lowDiffThreshold) <= 0 {
		effectiveHVMIndexerTipLag = 100 // Lag 100 blocks during low difficulty
	}

	// walk back hVMIndexerTipLag blocks from tip
	// On initial init when we have less than hVMIndexerTipLag previous blocks (right after
	// hVM0 phase transition), correct indexer behavior is to remain at the genesis-configured
	// height until walking backwards the specified number of lag blocks doesn't surpass
	// configured genesis.
	if cursorHeight-effectiveHVMIndexerTipLag > bc.tbcHeaderNodeConfig.GenesisHeightOffset {
		for i := uint64(0); i < effectiveHVMIndexerTipLag; i++ {
			head, height, err := bc.tbcHeaderNode.BlockHeaderByHash(context2.Background(), &cursorHeader.PrevBlock)
			if err != nil {
				log.Crit(fmt.Sprintf("an error occurred walking back Bitcoin headers from lightweight "+
					"TBC tip %s @ %d, unable to get header %s @ %d", lightTipHash.String(), lightTipHeight,
					cursorHeader.PrevBlock.String(), cursorHeight-1))
			}
			cursorHeader, cursorHeight = head, height // Storing them temporarily for verbose logging
			cursorHash = cursorHeader.BlockHash()
		}
	}

	// Check that the TBC Full Node has sufficient chain knowledge to sync to this height.
	// TODO: More intelligent handling of this in the future - adding to queue and processing later
	// rather than busy-waiting here
	available, err := vm.TBCBlocksAvailableToHeader(context2.Background(), cursorHeader)
	if err != nil {
		return err
	}

	for !available {
		available, err = vm.TBCBlocksAvailableToHeader(context2.Background(), cursorHeader)
		if err != nil {
			return err
		}
		log.Info(fmt.Sprintf("TBC Full Node does not yet have all full blocks up to Bitcoin block %s "+
			" which is required to index up to according to lightweight TBC node", cursorHash.String()))
		time.Sleep(250 * time.Millisecond)
	}

	// This single indexer function handles any reorgs required to move the TBC full node to the specified index
	err = vm.TBCIndexToHeader(cursorHeader)
	if err != nil {
		// TODO: Recovery?
		log.Crit(fmt.Sprintf("Unable to move TBC Full Node indexes to BTC block %x @ %d",
			cursorHash[:], cursorHeight), "err", err)
	}

	return nil
}

// updateHvmHeaderConsensus must be called each time when the canonical
// tip is changed. This method determines the change in chain geometry
// that the switch to the new block represents, and modifies the
// external-header-mode TBC instance's Bitcoin header knowledge to
// account for only information contained in the canonical chain ending
// at the new head.
func (bc *BlockChain) updateHvmHeaderConsensus(newHead *types.Header) error {
	if !bc.hvmEnabled {
		log.Warn("updateHvmHeaderConsensus called but hVM is disabled")
		return nil
	}

	log.Info(fmt.Sprintf("updateHvmHeaderConsensus called with new head: %s @ %d",
		newHead.Hash().String(), newHead.Number.Uint64()))

	if !bc.chainConfig.IsHvm0(newHead.Time) {
		log.Info(fmt.Sprintf("New head %s @ %d does not have hVM Phase 0 active yet.", newHead.Hash().String(), newHead.Number.Uint64()))
		return nil
	}

	// We store the EVM block which was last applied to update hVM
	// independently in order to gracefully handle updates to EVM
	// blockchain state that occurred without TBC's knowledge.
	// In the future, this may also be used for some kind of
	// snap sync of TBC state or similar.
	currentHeadHashRaw, err := bc.tbcHeaderNode.UpstreamStateId(context2.Background())
	log.Info(fmt.Sprintf("current upstream state id from TBC is %x", currentHeadHashRaw[:]))

	if bytes.Equal(currentHeadHashRaw[:], tbcd.DefaultUpstreamStateId[:]) {
		// TODO: Full TBC recovery from genesis
		log.Crit("hVM's header-only TBC node reported a default upstream state id, " +
			"indicating it was modified without a proper corresponding EVM block to identify its state.")
	}

	if bytes.Equal(currentHeadHashRaw[:], newHead.Hash().Bytes()[:]) {
		log.Info(fmt.Sprintf("updateHvmHeaderConsensus called to update chain to new head %x but lightweight "+
			"TBC node's state already reflects this block, no-op", currentHeadHashRaw[:]))
		return nil
	}

	var currentHead *types.Header
	currentHeadHash := common.BytesToHash(currentHeadHashRaw[:])

	if bytes.Equal(currentHeadHashRaw[:], hVMGenesisUpstreamId[:]) {
		log.Info(fmt.Sprintf("Current head from lightweight TBC upstream ID is the hVM Genesis Upstream ID"))
		// Upstream id is genesis, so this should be the first hVM block
		currentHead = bc.getHeaderFromDiskOrHoldingPen(newHead.ParentHash)
		currentHeadHash = currentHead.Hash()
		if bc.chainConfig.IsHvm0(currentHead.Time) {
			log.Crit(fmt.Sprintf("When updating hVM state transition for block %s @ %d, the upstream id is the "+
				" hVMGenesisUpstreamId, but the parent at time %d should have hVM Phase 0 activated!",
				newHead.Hash().String(), newHead.Number.Uint64(), currentHead.Time))
		}
	} else {
		log.Info(fmt.Sprintf("Getting header %x from disk or holding pen", currentHeadHash[:]))
		currentHead = bc.getHeaderFromDiskOrHoldingPen(currentHeadHash)
	}

	if currentHead == nil {
		log.Error(fmt.Sprintf("currentHead is nil, but should have been %x", currentHeadHash[:]))
	} else {
		log.Info(fmt.Sprintf("Going to look for ancestor of %d @ %s and %d @ %s", newHead.Hash().String(),
			newHead.Number.Uint64(), currentHead.Hash().String(), currentHead.Number.Uint64()))
	}

	log.Info(fmt.Sprintf("updateHvmHeaderConsensus found current head hash: %x", currentHeadHashRaw[:]))

	// Get common ancestor between newHead and currentHead
	ancestor, err := bc.findCommonAncestor(newHead, currentHead)
	if err != nil || ancestor == nil {
		log.Crit(fmt.Sprintf("Unable to find common ancestor between %s @ %d and %s @ %d,"+
			" cannot transition hVM's header knowledge to the correct state",
			newHead.Hash().String(), newHead.Number.Uint64(),
			currentHead.Hash().String(), currentHead.Number.Uint64()), "err", err)
	}

	log.Info(fmt.Sprintf("Common ancestor between %s @ %d and %s @ %d is %s @ %d",
		currentHead.Hash().String(), currentHead.Number.Uint64(), newHead.Hash().String(),
		newHead.Number.Uint64(), ancestor.Hash().String(), ancestor.Number.Uint64()))

	// If currentHead is direct parent, then just apply state change from newHead
	if newHead.ParentHash.Cmp(currentHead.Hash()) == 0 {
		err := bc.applyHvmHeaderConsensusUpdate(newHead)
		if err != nil {
			// TODO: This is where we should invalidate the block OR attempt to recover hVM state from genesis
			// depending on the nature of the error. For now, crit.
			log.Crit(fmt.Sprintf("Encountered an error applying hVM header state transition for block %s @ %d",
				newHead.Hash().String(), newHead.Number.Uint64()), "err", err)
		}
		log.Info(fmt.Sprintf("Successfully applied hVM header state transition for single block %s @ %d",
			newHead.Hash().String(), newHead.Number.Uint64()))
	} else if bytes.Equal(currentHead.Hash().Bytes(), ancestor.Hash().Bytes()) {
		// If currentHead is the ancestor, then we are walking directly forwards.
		err := bc.walkHvmHeaderConsensusForward(currentHead, newHead)
		if err != nil {
			// TODO: depending on error either recover hVM state from genesis or mark blocks invalid
			log.Crit("Unable to walk hVM consensus forwards", "err", err)
		}

	} else if bytes.Equal(newHead.Hash().Bytes(), ancestor.Hash().Bytes()) {
		// Otherwise if newHead is the ancestor, then we are walking directly backwards.
		err := bc.walkHvmHeaderConsensusBack(currentHead, newHead)
		if err != nil {
			// TODO: depending on error either recover hVM state from genesis or mark blocks invalid
			log.Crit("Unable to walk hVM consensus backwards", "err", err)
		}
	} else {
		// Finally if neither newHead or currentHead is the ancestor, then we are in a fork and need to walk
		// backwards from currentHead until we reach ancestor, then forward to newHead.

		// First, walk backwards from currentHead to common ancestor
		err := bc.walkHvmHeaderConsensusBack(currentHead, ancestor)
		if err != nil {
			// TODO: depending on error either recover hVM state from genesis or mark blocks invalid
			log.Crit("Unable to walk hVM consensus backwards", "err", err)
		}
		// Then, walk forwards from the common ancestor
		err = bc.walkHvmHeaderConsensusForward(ancestor, newHead)
		if err != nil {
			// TODO: depending on error either recover hVM state from genesis or mark blocks invalid
			log.Crit("Unable to walk hVM consensus backwards", "err", err)
		}
	}

	// Now make sure TBC indexer represents this final state
	err = bc.updateFullTBCToLightweight()
	if err != nil {
		log.Crit("Unable to update full TBC node according to lightweight", "err", err)
		return err
	}
	// canonHeight, canonHeader, err := bc.tbcHeaderNode.BlockHeaderBest(context2.Background())
	// if err != nil {
	// 	canonHeaderHash := canonHeader.BlockHash()
	// 	log.Crit(fmt.Sprintf("Unable to progress TBC indexers to represent the canonical state of the lightweight "+
	// 		"header TBC node which has canonical tip %x @ %d", canonHeaderHash[:], canonHeight), "err", err)
	// }
	// chbh := canonHeader.BlockHash()
	// log.Info("updateHvmHeaderConsensus moving TBC indexer to %x for block %s @ %d", chbh[:],
	// 	newHead.Hash().String(), newHead.Number.Uint64())
	// err = vm.TBCIndexToHeader(canonHeader)
	// if err != nil {
	// 	canonHeaderHash := canonHeader.BlockHash()
	// 	log.Crit(fmt.Sprintf("Encountered an error progressing TBC indexers to represent the canonical state of "+
	// 		"the lightweight header TBC node which has canonical tip %x @ %d", canonHeaderHash[:], canonHeight),
	// 		"err", err)
	// }

	return nil
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

	// Track the block number of the requested root hash
	var rootNumber uint64 // (no root == always 0)

	// Retrieve the last pivot block to short circuit rollbacks beyond it and the
	// current freezer limit to start nuking id underflown
	pivot := rawdb.ReadLastPivotNumber(bc.db)
	frozen, _ := bc.db.Ancients()

	updateFn := func(db ethdb.KeyValueWriter, header *types.Header) (*types.Header, bool) {
		// Rewind the blockchain, ensuring we don't end up with a stateless head
		// block. Note, depth equality is permitted to allow using SetHead as a
		// chain reparation mechanism without deleting any data!
		if currentBlock := bc.CurrentBlock(); currentBlock != nil && header.Number.Uint64() <= currentBlock.Number.Uint64() {
			newHeadBlock := bc.GetBlock(header.Hash(), header.Number.Uint64())
			if newHeadBlock == nil {
				log.Error("Gap in the chain, rewinding to genesis", "number", header.Number, "hash", header.Hash())
				newHeadBlock = bc.genesisBlock
			} else {
				// Block exists. Keep rewinding until either we find one with state
				// or until we exceed the optional threshold root hash
				beyondRoot := (root == common.Hash{}) // Flag whether we're beyond the requested root (no root, always true)

				for {
					// If a root threshold was requested but not yet crossed, check
					if root != (common.Hash{}) && !beyondRoot && newHeadBlock.Root() == root {
						beyondRoot, rootNumber = true, newHeadBlock.NumberU64()
					}
					if !bc.HasState(newHeadBlock.Root()) && !bc.stateRecoverable(newHeadBlock.Root()) {
						log.Trace("Block state missing, rewinding further", "number", newHeadBlock.NumberU64(), "hash", newHeadBlock.Hash())
						if pivot == nil || newHeadBlock.NumberU64() > *pivot {
							parent := bc.GetBlock(newHeadBlock.ParentHash(), newHeadBlock.NumberU64()-1)
							if parent != nil {
								newHeadBlock = parent
								continue
							}
							log.Error("Missing block in the middle, aiming genesis", "number", newHeadBlock.NumberU64()-1, "hash", newHeadBlock.ParentHash())
							newHeadBlock = bc.genesisBlock
						} else {
							log.Trace("Rewind passed pivot, aiming genesis", "number", newHeadBlock.NumberU64(), "hash", newHeadBlock.Hash(), "pivot", *pivot)
							newHeadBlock = bc.genesisBlock
						}
					}
					if beyondRoot || newHeadBlock.NumberU64() == 0 {
						if !bc.HasState(newHeadBlock.Root()) && bc.stateRecoverable(newHeadBlock.Root()) {
							// Rewind to a block with recoverable state. If the state is
							// missing, run the state recovery here.
							if err := bc.triedb.Recover(newHeadBlock.Root()); err != nil {
								log.Crit("Failed to rollback state", "err", err) // Shouldn't happen
							}
							log.Debug("Rewound to block with state", "number", newHeadBlock.NumberU64(), "hash", newHeadBlock.Hash())
						}
						break
					}
					log.Debug("Skipping block with threshold state", "number", newHeadBlock.NumberU64(), "hash", newHeadBlock.Hash(), "root", newHeadBlock.Root())
					newHeadBlock = bc.GetBlock(newHeadBlock.ParentHash(), newHeadBlock.NumberU64()-1) // Keep rewinding
				}
			}
			rawdb.WriteHeadBlockHash(db, newHeadBlock.Hash())

			// Degrade the chain markers if they are explicitly reverted.
			// In theory we should update all in-memory markers in the
			// last step, however the direction of SetHead is from high
			// to low, so it's safe to update in-memory markers directly.
			bc.currentBlock.Store(newHeadBlock.Header())
			headBlockGauge.Update(int64(newHeadBlock.NumberU64()))

			log.Info(fmt.Sprintf("Updating hVM header consensus in setHeadBeyondRoot updateFn to %s @ %d",
				newHeadBlock.Header().Hash().String(), newHeadBlock.Number().Uint64()))
			err := bc.updateHvmHeaderConsensus(newHeadBlock.Header())
			if err != nil {
				log.Crit(fmt.Sprintf("Unable to udpate hVM header consensus in setHeadBeyondRoot updateFn to %s @ %d",
					newHeadBlock.Header().Hash(), newHeadBlock.Number().Uint64()), "err", err)
			}

			// The head state is missing, which is only possible in the path-based
			// scheme. This situation occurs when the chain head is rewound below
			// the pivot point. In this scenario, there is no possible recovery
			// approach except for rerunning a snap sync. Do nothing here until the
			// state syncer picks it up.
			if !bc.HasState(newHeadBlock.Root()) {
				log.Info("Chain is stateless, wait state sync", "number", newHeadBlock.Number(), "hash", newHeadBlock.Hash())
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
			// Truncate all relative data(header, total difficulty, body, receipt
			// and canonical hash) from ancient store.
			if _, err := bc.db.TruncateHead(num); err != nil {
				log.Crit("Failed to truncate ancient data", "number", num, "err", err)
			}
			// Remove the hash <-> number mapping from the active store.
			rawdb.DeleteHeaderNumber(db, hash)
		} else {
			// Remove relative body and receipts from the active store.
			// The header, total difficulty and canonical hash will be
			// removed in the hc.SetHead function.
			rawdb.DeleteBody(db, hash, num)
			rawdb.DeleteReceipts(db, hash, num)
		}
		// Todo(rjl493456442) txlookup, bloombits, etc
	}
	// If SetHead was only called as a chain reparation method, try to skip
	// touching the header chain altogether, unless the freezer is broken
	if repair {
		if target, force := updateFn(bc.db, bc.CurrentBlock()); force {
			bc.hc.SetHead(target.Number.Uint64(), updateFn, delFn)
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
	bc.futureBlocks.Purge()

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
	rawdb.WriteTd(batch, genesis.Hash(), genesis.NumberU64(), genesis.Difficulty())
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
	return nil
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
	err := bc.updateHvmHeaderConsensus(block.Header())
	if err != nil {
		log.Crit(fmt.Sprintf("Unable to update hVM header consensus to block %s @ %d in writeHeadBlock()",
			block.Hash().String(), block.Number().Uint64()), "err", err)
	}
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
	close(bc.quit)
	bc.StopInsert()

	// Now wait for all chain modifications to end and persistent goroutines to exit.
	//
	// Note: Close waits for the mutex to become available, i.e. any running chain
	// modification will have exited when Close returns. Since we also called StopInsert,
	// the mutex should become available quickly. It cannot be taken again after Close has
	// returned.
	bc.chainmu.Close()
	bc.wg.Wait()
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
		if !bc.cacheConfig.TrieDirtyDisabled {
			triedb := bc.triedb

			for _, offset := range []uint64{0, 1, TriesInMemory - 1} {
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
	// Close the trie database, release all the held resources as the last step.
	if err := bc.triedb.Close(); err != nil {
		log.Error("Failed to close trie database", "err", err)
	}
	log.Info("Blockchain stopped")
}

// StopInsert interrupts all insertion methods, causing them to return
// errInsertionInterrupted as soon as possible. Insertion is permanently disabled after
// calling this method.
func (bc *BlockChain) StopInsert() {
	bc.procInterrupt.Store(true)
}

// insertStopped returns true after StopInsert has been called.
func (bc *BlockChain) insertStopped() bool {
	return bc.procInterrupt.Load()
}

func (bc *BlockChain) procFutureBlocks() {
	blocks := make([]*types.Block, 0, bc.futureBlocks.Len())
	for _, hash := range bc.futureBlocks.Keys() {
		if block, exist := bc.futureBlocks.Peek(hash); exist {
			blocks = append(blocks, block)
		}
	}
	if len(blocks) > 0 {
		slices.SortFunc(blocks, func(a, b *types.Block) int {
			return a.Number().Cmp(b.Number())
		})
		// Insert one by one as chain insertion needs contiguous ancestry between blocks
		for i := range blocks {
			bc.InsertChain(blocks[i : i+1])
		}
	}
}

// WriteStatus status of write
type WriteStatus byte

const (
	NonStatTy WriteStatus = iota
	CanonStatTy
	SideStatTy
)

// InsertReceiptChain attempts to complete an already existing header chain with
// transaction and receipt data.
func (bc *BlockChain) InsertReceiptChain(blockChain types.Blocks, receiptChain []types.Receipts, ancientLimit uint64) (int, error) {
	// We don't require the chainMu here since we want to maximize the
	// concurrency of header insertion and receipt insertion.
	bc.wg.Add(1)
	defer bc.wg.Done()

	var (
		ancientBlocks, liveBlocks     types.Blocks
		ancientReceipts, liveReceipts []types.Receipts
	)
	// Do a sanity check that the provided chain is actually ordered and linked
	for i, block := range blockChain {
		if i != 0 {
			prev := blockChain[i-1]
			if block.NumberU64() != prev.NumberU64()+1 || block.ParentHash() != prev.Hash() {
				log.Error("Non contiguous receipt insert",
					"number", block.Number(), "hash", block.Hash(), "parent", block.ParentHash(),
					"prevnumber", prev.Number(), "prevhash", prev.Hash())
				return 0, fmt.Errorf("non contiguous insert: item %d is #%d [%x..], item %d is #%d [%x..] (parent [%x..])",
					i-1, prev.NumberU64(), prev.Hash().Bytes()[:4],
					i, block.NumberU64(), block.Hash().Bytes()[:4], block.ParentHash().Bytes()[:4])
			}
		}
		if block.NumberU64() <= ancientLimit {
			ancientBlocks, ancientReceipts = append(ancientBlocks, block), append(ancientReceipts, receiptChain[i])
		} else {
			liveBlocks, liveReceipts = append(liveBlocks, block), append(liveReceipts, receiptChain[i])
		}

		// Here we also validate that blob transactions in the block do not contain a sidecar.
		// While the sidecar does not affect the block hash / tx hash, sending blobs within a block is not allowed.
		for txIndex, tx := range block.Transactions() {
			if tx.Type() == types.BlobTxType && tx.BlobTxSidecar() != nil {
				return 0, fmt.Errorf("block #%d contains unexpected blob sidecar in tx at index %d", block.NumberU64(), txIndex)
			}
		}
	}

	var (
		stats = struct{ processed, ignored int32 }{}
		start = time.Now()
		size  = int64(0)
	)

	// updateHead updates the head snap sync block if the inserted blocks are better
	// and returns an indicator whether the inserted blocks are canonical.
	updateHead := func(head *types.Block) bool {
		if !bc.chainmu.TryLock() {
			return false
		}
		defer bc.chainmu.Unlock()

		// Rewind may have occurred, skip in that case.
		if bc.CurrentHeader().Number.Cmp(head.Number()) >= 0 {
			reorg, err := bc.forker.ReorgNeeded(bc.CurrentSnapBlock(), head.Header())
			if err != nil {
				log.Warn("Reorg failed", "err", err)
				return false
			} else if !reorg {
				return false
			}
			rawdb.WriteHeadFastBlockHash(bc.db, head.Hash())
			bc.currentSnapBlock.Store(head.Header())
			headFastBlockGauge.Update(int64(head.NumberU64()))
			return true
		}
		return false
	}
	// writeAncient writes blockchain and corresponding receipt chain into ancient store.
	//
	// this function only accepts canonical chain data. All side chain will be reverted
	// eventually.
	writeAncient := func(blockChain types.Blocks, receiptChain []types.Receipts) (int, error) {
		first := blockChain[0]
		last := blockChain[len(blockChain)-1]

		// Ensure genesis is in ancients.
		if first.NumberU64() == 1 {
			if frozen, _ := bc.db.Ancients(); frozen == 0 {
				td := bc.genesisBlock.Difficulty()
				writeSize, err := rawdb.WriteAncientBlocks(bc.db, []*types.Block{bc.genesisBlock}, []types.Receipts{nil}, td)
				if err != nil {
					log.Error("Error writing genesis to ancients", "err", err)
					return 0, err
				}
				size += writeSize
				log.Info("Wrote genesis to ancients")
			}
		}
		// Before writing the blocks to the ancients, we need to ensure that
		// they correspond to the what the headerchain 'expects'.
		// We only check the last block/header, since it's a contiguous chain.
		if !bc.HasHeader(last.Hash(), last.NumberU64()) {
			return 0, fmt.Errorf("containing header #%d [%x..] unknown", last.Number(), last.Hash().Bytes()[:4])
		}

		// Write all chain data to ancients.
		td := bc.GetTd(first.Hash(), first.NumberU64())
		writeSize, err := rawdb.WriteAncientBlocks(bc.db, blockChain, receiptChain, td)
		if err != nil {
			log.Error("Error importing chain data to ancients", "err", err)
			return 0, err
		}
		size += writeSize

		// Sync the ancient store explicitly to ensure all data has been flushed to disk.
		if err := bc.db.Sync(); err != nil {
			return 0, err
		}
		// Update the current snap block because all block data is now present in DB.
		previousSnapBlock := bc.CurrentSnapBlock().Number.Uint64()
		if !updateHead(blockChain[len(blockChain)-1]) {
			// We end up here if the header chain has reorg'ed, and the blocks/receipts
			// don't match the canonical chain.
			if _, err := bc.db.TruncateHead(previousSnapBlock + 1); err != nil {
				log.Error("Can't truncate ancient store after failed insert", "err", err)
			}
			return 0, errSideChainReceipts
		}

		// Delete block data from the main database.
		var (
			batch       = bc.db.NewBatch()
			canonHashes = make(map[common.Hash]struct{})
		)
		for _, block := range blockChain {
			canonHashes[block.Hash()] = struct{}{}
			if block.NumberU64() == 0 {
				continue
			}
			rawdb.DeleteCanonicalHash(batch, block.NumberU64())
			rawdb.DeleteBlockWithoutNumber(batch, block.Hash(), block.NumberU64())
		}
		// Delete side chain hash-to-number mappings.
		for _, nh := range rawdb.ReadAllHashesInRange(bc.db, first.NumberU64(), last.NumberU64()) {
			if _, canon := canonHashes[nh.Hash]; !canon {
				rawdb.DeleteHeader(batch, nh.Hash, nh.Number)
			}
		}
		if err := batch.Write(); err != nil {
			return 0, err
		}
		stats.processed += int32(len(blockChain))
		return 0, nil
	}

	// writeLive writes blockchain and corresponding receipt chain into active store.
	writeLive := func(blockChain types.Blocks, receiptChain []types.Receipts) (int, error) {
		var (
			skipPresenceCheck = false
			batch             = bc.db.NewBatch()
		)
		for i, block := range blockChain {
			// Short circuit insertion if shutting down or processing failed
			if bc.insertStopped() {
				return 0, errInsertionInterrupted
			}
			// Short circuit if the owner header is unknown
			if !bc.HasHeader(block.Hash(), block.NumberU64()) {
				return i, fmt.Errorf("containing header #%d [%x..] unknown", block.Number(), block.Hash().Bytes()[:4])
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
			rawdb.WriteBody(batch, block.Hash(), block.NumberU64(), block.Body())
			rawdb.WriteReceipts(batch, block.Hash(), block.NumberU64(), receiptChain[i])

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
		updateHead(blockChain[len(blockChain)-1])
		return 0, nil
	}

	// Write downloaded chain data and corresponding receipt chain data
	if len(ancientBlocks) > 0 {
		if n, err := writeAncient(ancientBlocks, ancientReceipts); err != nil {
			if err == errInsertionInterrupted {
				return 0, nil
			}
			return n, err
		}
	}
	if len(liveBlocks) > 0 {
		if n, err := writeLive(liveBlocks, liveReceipts); err != nil {
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
func (bc *BlockChain) writeBlockWithoutState(block *types.Block, td *big.Int) (err error) {
	if bc.insertStopped() {
		return errInsertionInterrupted
	}
	batch := bc.db.NewBatch()
	rawdb.WriteTd(batch, block.Hash(), block.NumberU64(), td)
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
		if err := bc.reorg(current, block); err != nil {
			return err
		}
	}
	bc.writeHeadBlock(block)
	return nil
}

// writeBlockWithState writes block, metadata and corresponding state data to the
// database.
func (bc *BlockChain) writeBlockWithState(block *types.Block, receipts []*types.Receipt, state *state.StateDB) error {
	// Calculate the total difficulty of the block
	ptd := bc.GetTd(block.ParentHash(), block.NumberU64()-1)
	if ptd == nil {
		return consensus.ErrUnknownAncestor
	}
	// Make sure no inconsistent state is leaked during insertion
	externTd := new(big.Int).Add(block.Difficulty(), ptd)

	// Irrelevant of the canonical status, write the block itself to the database.
	//
	// Note all the components of block(td, hash->number map, header, body, receipts)
	// should be written atomically. BlockBatch is used for containing all components.
	blockBatch := bc.db.NewBatch()
	rawdb.WriteTd(blockBatch, block.Hash(), block.NumberU64(), externTd)
	rawdb.WriteBlock(blockBatch, block)
	rawdb.WriteReceipts(blockBatch, block.Hash(), block.NumberU64(), receipts)
	rawdb.WritePreimages(blockBatch, state.Preimages())
	if err := blockBatch.Write(); err != nil {
		log.Crit("Failed to write block into disk", "err", err)
	}
	// Commit all cached state changes into underlying memory database.
	root, err := state.Commit(block.NumberU64(), bc.chainConfig.IsEIP158(block.Number()))
	if err != nil {
		return err
	}
	// If node is running in path mode, skip explicit gc operation
	// which is unnecessary in this mode.
	if bc.triedb.Scheme() == rawdb.PathScheme {
		return nil
	}
	// If we're running an archive node, always flush
	if bc.cacheConfig.TrieDirtyDisabled {
		return bc.triedb.Commit(root, false)
	}
	// Full but not archive node, do proper garbage collection
	bc.triedb.Reference(root, common.Hash{}) // metadata reference to keep trie alive
	bc.triegc.Push(root, -int64(block.NumberU64()))

	// Flush limits are not considered for the first TriesInMemory blocks.
	current := block.NumberU64()
	if current <= TriesInMemory {
		return nil
	}
	// If we exceeded our memory allowance, flush matured singleton nodes to disk
	var (
		_, nodes, imgs = bc.triedb.Size() // all memory is contained within the nodes return for hashdb
		limit          = common.StorageSize(bc.cacheConfig.TrieDirtyLimit) * 1024 * 1024
	)
	if nodes > limit || imgs > 4*1024*1024 {
		bc.triedb.Cap(limit - ethdb.IdealBatchSize)
	}
	// Find the next state trie we need to commit
	chosen := current - TriesInMemory
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
			if chosen < bc.lastWrite+TriesInMemory && bc.gcproc >= 2*flushInterval {
				log.Info("State in memory for too long, committing", "time", bc.gcproc, "allowance", flushInterval, "optimum", float64(chosen-bc.lastWrite)/TriesInMemory)
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

// WriteBlockAndSetHead writes the given block and all associated state to the database,
// and applies the block as the new chain head.
func (bc *BlockChain) WriteBlockAndSetHead(block *types.Block, receipts []*types.Receipt, logs []*types.Log, state *state.StateDB, emitHeadEvent bool) (status WriteStatus, err error) {
	if !bc.chainmu.TryLock() {
		return NonStatTy, errChainStopped
	}
	defer bc.chainmu.Unlock()

	return bc.writeBlockAndSetHead(block, receipts, logs, state, emitHeadEvent)
}

// writeBlockAndSetHead is the internal implementation of WriteBlockAndSetHead.
// This function expects the chain mutex to be held.
func (bc *BlockChain) writeBlockAndSetHead(block *types.Block, receipts []*types.Receipt, logs []*types.Log, state *state.StateDB, emitHeadEvent bool) (status WriteStatus, err error) {
	if err := bc.writeBlockWithState(block, receipts, state); err != nil {
		return NonStatTy, err
	}
	currentBlock := bc.CurrentBlock()
	reorg, err := bc.forker.ReorgNeeded(currentBlock, block.Header())
	if err != nil {
		return NonStatTy, err
	}
	if reorg {
		// Reorganise the chain if the parent is not the head block
		if block.ParentHash() != currentBlock.Hash() {
			if err := bc.reorg(currentBlock, block); err != nil {
				return NonStatTy, err
			}
		}
		status = CanonStatTy
	} else {
		status = SideStatTy
	}
	// Set new head.
	if status == CanonStatTy {
		bc.writeHeadBlock(block)
		log.Info(fmt.Sprintf("Updating hVM header consensus to block %s @ %d in writeBlockAndSetHead()",
			block.Hash().String(), block.Number().Uint64()))
		// Update lightweight TBC header view of Bitcoin to account for this new tip
		err := bc.updateHvmHeaderConsensus(block.Header())
		if err != nil {
			// TODO: Recovery of lightweight TBC
			log.Crit(fmt.Sprintf("Unable to update hVM header consensus to block %s @ %d in writeBlockAndSetHead()",
				block.Hash().String(), block.Number().Uint64()), "err", err)
		}
		err = bc.updateFullTBCToLightweight()
		if err != nil {
			log.Crit(fmt.Sprintf("Unable to update full TBC node indexers to reflect EVM block %s @ %d",
				block.Hash().String(), block.NumberU64()))
		}
		log.Info(fmt.Sprintf("Updated full TBC node indexers to reflect EVM block %s @ %d",
			block.Hash().String(), block.NumberU64()))
	} else {
		log.Info(fmt.Sprintf("In writeBlockAndSetHead, EVM block %s @ %d is not Canon, not updating hVM state",
			block.Hash().String(), block.NumberU64()))
	}
	bc.futureBlocks.Remove(block.Hash())

	if status == CanonStatTy {
		bc.chainFeed.Send(ChainEvent{Block: block, Hash: block.Hash(), Logs: logs})
		if len(logs) > 0 {
			bc.logsFeed.Send(logs)
		}
		// In theory, we should fire a ChainHeadEvent when we inject
		// a canonical block, but sometimes we can insert a batch of
		// canonical blocks. Avoid firing too many ChainHeadEvents,
		// we will fire an accumulated ChainHeadEvent and disable fire
		// event here.
		if emitHeadEvent {
			bc.chainHeadFeed.Send(ChainHeadEvent{Block: block})
		}
	} else {
		bc.chainSideFeed.Send(ChainSideEvent{Block: block})
	}
	return status, nil
}

// addFutureBlock checks if the block is within the max allowed window to get
// accepted for future processing, and returns an error if the block is too far
// ahead and was not added.
//
// TODO after the transition, the future block shouldn't be kept. Because
// it's not checked in the Geth side anymore.
func (bc *BlockChain) addFutureBlock(block *types.Block) error {
	max := uint64(time.Now().Unix() + maxTimeFutureBlocks)
	if block.Time() > max {
		return fmt.Errorf("future block timestamp %v > allowed %v", block.Time(), max)
	}
	if block.Difficulty().Cmp(common.Big0) == 0 {
		// Never add PoS blocks into the future queue
		return nil
	}
	bc.futureBlocks.Add(block.Hash(), block)
	return nil
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
	bc.blockProcFeed.Send(true)
	defer bc.blockProcFeed.Send(false)

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
	return bc.insertChain(chain, true)
}

// insertChain is the internal implementation of InsertChain, which assumes that
// 1) chains are contiguous, and 2) The chain mutex is held.
//
// This method is split out so that import batches that require re-injecting
// historical blocks can do so without releasing the lock, which could lead to
// racey behaviour. If a sidechain import is in progress, and the historic state
// is imported, but then new canon-head is added before the actual sidechain
// completes, then the historic state could be pruned again
func (bc *BlockChain) insertChain(chain types.Blocks, setHead bool) (int, error) {
	// If the chain is terminating, don't even bother starting up.
	if bc.insertStopped() {
		return 0, nil
	}

	// Start a parallel signature recovery (signer will fluke on fork transition, minimal perf loss)
	SenderCacher.RecoverFromBlocks(types.MakeSigner(bc.chainConfig, chain[0].Number(), chain[0].Time()), chain)

	var (
		stats     = insertStats{startTime: mclock.Now()}
		lastCanon *types.Block
	)
	// Fire a single chain head event if we've progressed the chain
	defer func() {
		if lastCanon != nil && bc.CurrentBlock().Hash() == lastCanon.Hash() {
			bc.chainHeadFeed.Send(ChainHeadEvent{lastCanon})
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
		var (
			reorg   bool
			current = bc.CurrentBlock()
		)
		for block != nil && bc.skipBlock(err, it) {
			reorg, err = bc.forker.ReorgNeeded(current, block.Header())
			if err != nil {
				return it.index, err
			}
			if reorg {
				// Switch to import mode if the forker says the reorg is necessary
				// and also the block is not on the canonical chain.
				// In eth2 the forker always returns true for reorg decision (blindly trusting
				// the external consensus engine), but in order to prevent the unnecessary
				// reorgs when importing known blocks, the special case is handled here.
				if block.NumberU64() > current.Number.Uint64() || bc.GetCanonicalHash(block.NumberU64()) != block.Hash() {
					break
				}
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
				return it.index, err
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
			return bc.insertSideChain(block, it)
		} else {
			// We're post-merge and the parent is pruned, try to recover the parent state
			log.Debug("Pruned ancestor", "number", block.Number(), "hash", block.Hash())
			_, err := bc.recoverAncestors(block)
			return it.index, err
		}
	// First block is future, shove it (and all children) to the future queue (unknown ancestor)
	case errors.Is(err, consensus.ErrFutureBlock) || (errors.Is(err, consensus.ErrUnknownAncestor) && bc.futureBlocks.Contains(it.first().ParentHash())):
		for block != nil && (it.index == 0 || errors.Is(err, consensus.ErrUnknownAncestor)) {
			log.Debug("Future block, postponing import", "number", block.Number(), "hash", block.Hash())
			if err := bc.addFutureBlock(block); err != nil {
				return it.index, err
			}
			block, err = it.next()
		}
		stats.queued += it.processed()
		stats.ignored += it.remaining()

		// If there are any still remaining, mark as ignored
		return it.index, err

	// Some other error(except ErrKnownBlock) occurred, abort.
	// ErrKnownBlock is allowed here since some known blocks
	// still need re-execution to generate snapshots that are missing
	case err != nil && !errors.Is(err, ErrKnownBlock):
		bc.futureBlocks.Remove(block.Hash())
		stats.ignored += len(it.chain)
		bc.reportBlock(block, nil, err)
		return it.index, err
	}
	// No validation errors for the first block (or chain prefix skipped)
	var activeState *state.StateDB
	defer func() {
		// The chain importer is starting and stopping trie prefetchers. If a bad
		// block or other error is hit however, an early return may not properly
		// terminate the background threads. This defer ensures that we clean up
		// and dangling prefetcher, without defering each and holding on live refs.
		if activeState != nil {
			activeState.StopPrefetcher()
		}
	}()

	// When this function is over, clear all temp blocks
	defer clear(bc.tempBlocks)
	defer clear(bc.tempHeaders)

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
		// If the header is a banned one, straight out abort
		if BadHashes[block.Hash()] {
			bc.reportBlock(block, nil, ErrBannedHash)
			return it.index, ErrBannedHash
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
				return it.index, err
			}
			stats.processed++

			// We can assume that logs are empty here, since the only way for consecutive
			// Clique blocks to have the same state is if there are no transactions.
			lastCanon = block
			continue
		}

		// Retrieve the parent block and it's state to execute on top
		start := time.Now()
		parent := it.previous()
		if parent == nil {
			parent = bc.GetHeader(block.ParentHash(), block.NumberU64()-1)
		}
		statedb, err := state.New(parent.Root, bc.stateCache, bc.snaps)
		if err != nil {
			return it.index, err
		}

		// Enable prefetching to pull in trie node paths while processing transactions
		statedb.StartPrefetcher("chain")
		activeState = statedb

		// If we have a followup block, run that against the current state to pre-cache
		// transactions and probabilistically some of the account/storage trie nodes.
		var followupInterrupt atomic.Bool
		if !bc.cacheConfig.TrieCleanNoPrefetch {
			if followup, err := it.peek(); followup != nil && err == nil {
				throwaway, _ := state.New(parent.Root, bc.stateCache, bc.snaps)

				go func(start time.Time, followup *types.Block, throwaway *state.StateDB) {
					bc.prefetcher.Prefetch(followup, throwaway, bc.vmConfig, &followupInterrupt)

					blockPrefetchExecuteTimer.Update(time.Since(start))
					if followupInterrupt.Load() {
						blockPrefetchInterruptMeter.Mark(1)
					}
				}(time.Now(), followup, throwaway)
			}
		}

		// Process block using the parent state as reference point
		pstart := time.Now()
		// TODO:  Evaluate scenarios where very old blocks could require significant work to walk TBC correctly to validate
		// TODO: if full-node TBC progression fails because it doesn't know of block yet, queue this EVM block for processing later
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

		var tbcHeader *types.Header    // Original EVM tip that lightweight TBC knowledge represents to revert to when necessary
		var indexedState *tbc.SyncInfo // Original state of TBC Full Node to revert to when necessary
		isHvmActivated := false
		isFirstHvmBlock := false
		log.Info(fmt.Sprintf("Processing block %s @ %d", block.Hash().String(), block.NumberU64()))
		if bc.hvmEnabled {
			var parent *types.Header

			if bc.chainConfig.IsHvm0(block.Time()) {
				log.Info(fmt.Sprintf("For block %s @ %d, hVM is activated",
					block.Hash().String(), block.NumberU64()))
				isHvmActivated = true
				indexedState = vm.GetTBCFullNodeSyncStatus()
				if block.NumberU64() != 0 {
					log.Info(fmt.Sprintf("Block != 0, getting parent by hash %s", block.ParentHash()))
					parent = bc.GetHeaderByHash(block.ParentHash())
					if !bc.chainConfig.IsHvm0(parent.Time) {
						// Parent is not hVM0, meaning this block is first activation
						log.Info(fmt.Sprintf("Block %s @ %d is the hVM activation block",
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
			// The full TBC node *doesn't* need any intermediate hop to parent consensus, since it's only to provide
			// linear indexed state based on a particular Bitcoin tip which is dictated by the lightweight TBC node.
			// The lightweight TBC node *does* need to be adjusted to a specific pre-state based on this block's
			// parent to ensure that this block communicates data which is correct in the context of it's parent,
			// otherwise different nodes could disagree on the validity of this block's Bitcoin Attributes Deposited tx
			// for lightweight consensus update based on different lightweight Bitcoin views.
			// The updateHvmHeaderConsensus() method does handle underlying reorganizations of TBC's EVM state
			// including reversing down a fork and up a new branch to the EVM header we specify, but moving the
			// geometry here gives us more control here to know why an error occurred and in the future use various
			// recovery mechanisms depending on the issue.
			if isHvmActivated && !isFirstHvmBlock {
				if tbcHeader.Hash().Cmp(parent.Hash()) != 0 {
					log.Info(fmt.Sprintf("Lightweight TBC at block %s @ %d, moving to parent %s @ %d",
						tbcHeader.Hash().String(), tbcHeader.Number.Uint64(),
						parent.Hash().String(), parent.Number.Uint64()))
					err := bc.updateHvmHeaderConsensus(parent)
					if err != nil {
						log.Crit(fmt.Sprintf("Unable to move lightweight TBC node to parent %s @ %d",
							parent.Hash().String(), parent.Number.Uint64()), "err", err)
					}
				} else {
					log.Info(fmt.Sprintf("Lightweight TBC is already at parent %s @ %d",
						parent.Hash().String(), parent.Number.Uint64()))
				}
			}

			// Do an extra sanity check that lightweight TBC node is in the correct state, after above logic which
			// should have moved it to the correct state based on the parent of the block we're processing.
			// Incorrect state represents either data corruption or an issue with the reorg logic.
			// TODO on incorrect state attempt automated recovery of lightweight TBC state instead of log.Crit() exit
			if isHvmActivated && !isFirstHvmBlock {
				log.Info(fmt.Sprintf("Verifying before applying block %s @ %d, lightweight TBC's state is "+
					"correctly set to direct parent %s @ %d", block.Hash().String(), block.NumberU64(),
					parent.Hash().String(), parent.Number.Uint64()))
				representedBlock, err := bc.getHeaderModeTBCEVMHeader()
				if err != nil {
					log.Crit(fmt.Sprintf("Error, unable to fetch the EVM tip which lightweight TBC state "+
						"currently represents!"), "err", err)
				}
				if representedBlock.Hash().Cmp(parent.Hash()) != 0 {
					stateId, err := bc.tbcHeaderNode.UpstreamStateId(context2.Background())
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
				// Process this block's hVM updates
				err := bc.updateHvmHeaderConsensus(block.Header())
				if err != nil {
					// TODO: ban block instead
					log.Crit(fmt.Sprintf("TBC lightweight node unable to update lightweight TBC node to block "+
						"to process %s @ %d", block.Header().Hash().String(), block.Header().Number.Uint64()))
				}

				err = bc.updateFullTBCToLightweight()
				if err != nil {
					log.Crit(fmt.Sprintf("when processing block %s @ %d, an error occurred getting lightweight"+
						" TBC's best block", block.Hash().String(), block.NumberU64()))
				}
				si := vm.TBCFullNode.Synced(context2.Background())
				log.Info(fmt.Sprintf("Lightweight TBC is at canonical BTC block %s @ %d "+
					"(UTXOs: %s @ %d, TXs: %s @ %d)", si.BlockHeader.Hash.String(), si.BlockHeader.Height,
					si.Utxo.Hash.String(), si.Utxo.Height, si.Tx.Hash.String(), si.Tx.Height))
			}
		}

		receipts, logs, usedGas, err := bc.processor.Process(block, statedb, bc.vmConfig)
		if err != nil {
			bc.reportBlock(block, receipts, err)
			followupInterrupt.Store(true)
			return it.index, err
		}

		log.Info(fmt.Sprintf("Performed EVM processing of block %s @ %d",
			block.Hash().String(), block.NumberU64()))
		ptime := time.Since(pstart)

		vstart := time.Now()
		if err := bc.validator.ValidateState(block, statedb, receipts, usedGas); err != nil {
			bc.reportBlock(block, receipts, err)
			followupInterrupt.Store(true)
			return it.index, err
		}
		vtime := time.Since(vstart)
		proctime := time.Since(start) // processing + validation

		// Update the metrics touched during block processing and validation
		accountReadTimer.Update(statedb.AccountReads)                   // Account reads are complete(in processing)
		storageReadTimer.Update(statedb.StorageReads)                   // Storage reads are complete(in processing)
		snapshotAccountReadTimer.Update(statedb.SnapshotAccountReads)   // Account reads are complete(in processing)
		snapshotStorageReadTimer.Update(statedb.SnapshotStorageReads)   // Storage reads are complete(in processing)
		accountUpdateTimer.Update(statedb.AccountUpdates)               // Account updates are complete(in validation)
		storageUpdateTimer.Update(statedb.StorageUpdates)               // Storage updates are complete(in validation)
		accountHashTimer.Update(statedb.AccountHashes)                  // Account hashes are complete(in validation)
		storageHashTimer.Update(statedb.StorageHashes)                  // Storage hashes are complete(in validation)
		triehash := statedb.AccountHashes + statedb.StorageHashes       // The time spent on tries hashing
		trieUpdate := statedb.AccountUpdates + statedb.StorageUpdates   // The time spent on tries update
		trieRead := statedb.SnapshotAccountReads + statedb.AccountReads // The time spent on account read
		trieRead += statedb.SnapshotStorageReads + statedb.StorageReads // The time spent on storage read
		blockExecutionTimer.Update(ptime - trieRead)                    // The time spent on EVM processing
		blockValidationTimer.Update(vtime - (triehash + trieUpdate))    // The time spent on block validation

		// Write the block to the chain and get the status.
		var (
			wstart = time.Now()
			status WriteStatus
		)
		if !setHead {
			// Don't set the head, only insert the block
			log.Info(fmt.Sprintf("Writing block %s @ %d to disk but not setting as head.", block.Hash().String(),
				block.NumberU64()))
			// Because this block is not canonical, revert lightweight and full TBC nodes to former state
			if tbcHeader != nil {
				err := bc.updateHvmHeaderConsensus(tbcHeader)
				if err != nil {
					// TODO: Recover lightweight TBC state from genesis
					log.Crit(fmt.Sprintf("Unable to revert lightweight TBC node to represent state at "+
						"block %s @ %d.", tbcHeader.Hash().String(), tbcHeader.Number.Uint64()), "err", err)
				} else {
					log.Info(fmt.Sprintf("Successfully reverted lightweight TBC node to represent state at "+
						"block %s @ %d.", tbcHeader.Hash().String(), tbcHeader.Number.Uint64()))
				}
			}
			if indexedState != nil {
				// TODO: temporarily disabled, make sure that setting canonical block always does this.
				// err := vm.TBCRestoreIndexersToPoint(indexedState)
				// if err != nil {
				// 	// TODO: Recovery of TBC full node?
				//	log.Crit(fmt.Sprintf("Unable to restore TBC full node to previous indexed state "+
				//		"of UTXO Indexer=%x@%d, Tx Indexer=%x@%d", indexedState.Utxo.Hash[:], indexedState.Utxo.Height,
				//		indexedState.Tx.Hash[:], indexedState.Tx.Height))
				//}
			}
			err = bc.writeBlockWithState(block, receipts, statedb)
		} else {
			log.Info(fmt.Sprintf("Writing block %s @ %d to disk and setting as head, leaving lightweight and "+
				"full node TBC states progressed", block.Hash().String(), block.NumberU64()))
			status, err = bc.writeBlockAndSetHead(block, receipts, logs, statedb, false)
		}
		followupInterrupt.Store(true)
		if err != nil {
			return it.index, err
		}
		// Update the metrics touched during block commit
		accountCommitTimer.Update(statedb.AccountCommits)   // Account commits are complete, we can mark them
		storageCommitTimer.Update(statedb.StorageCommits)   // Storage commits are complete, we can mark them
		snapshotCommitTimer.Update(statedb.SnapshotCommits) // Snapshot commits are complete, we can mark them
		triedbCommitTimer.Update(statedb.TrieDBCommits)     // Trie database commits are complete, we can mark them

		blockWriteTimer.Update(time.Since(wstart) - statedb.AccountCommits - statedb.StorageCommits - statedb.SnapshotCommits - statedb.TrieDBCommits)
		blockInsertTimer.UpdateSince(start)

		// Report the import stats before returning the various results
		stats.processed++
		stats.usedGas += usedGas

		var snapDiffItems, snapBufItems common.StorageSize
		if bc.snaps != nil {
			snapDiffItems, snapBufItems = bc.snaps.Size()
		}
		trieDiffNodes, trieBufNodes, _ := bc.triedb.Size()
		stats.report(chain, it.index, snapDiffItems, snapBufItems, trieDiffNodes, trieBufNodes, setHead)

		if !setHead {
			// After merge we expect few side chains. Simply count
			// all blocks the CL gives us for GC processing time
			bc.gcproc += proctime

			return it.index, nil // Direct block insertion of a single block
		}
		switch status {
		case CanonStatTy:
			log.Debug("Inserted new block", "number", block.Number(), "hash", block.Hash(),
				"uncles", len(block.Uncles()), "txs", len(block.Transactions()), "gas", block.GasUsed(),
				"elapsed", common.PrettyDuration(time.Since(start)),
				"root", block.Root())

			lastCanon = block

			// Only count canonical blocks for GC processing time
			bc.gcproc += proctime

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

	// Any blocks remaining here? The only ones we care about are the future ones
	if block != nil && errors.Is(err, consensus.ErrFutureBlock) {
		if err := bc.addFutureBlock(block); err != nil {
			return it.index, err
		}
		block, err = it.next()

		for ; block != nil && errors.Is(err, consensus.ErrUnknownAncestor); block, err = it.next() {
			if err := bc.addFutureBlock(block); err != nil {
				return it.index, err
			}
			stats.queued++
		}
	}
	stats.ignored += it.remaining()

	return it.index, err
}

// insertSideChain is called when an import batch hits upon a pruned ancestor
// error, which happens when a sidechain with a sufficiently old fork-block is
// found.
//
// The method writes all (header-and-body-valid) blocks to disk, then tries to
// switch over to the new chain if the TD exceeded the current chain.
// insertSideChain is only used pre-merge.
func (bc *BlockChain) insertSideChain(block *types.Block, it *insertIterator) (int, error) {
	var (
		externTd  *big.Int
		lastBlock = block
		current   = bc.CurrentBlock()
	)
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

				// Collect the TD of the block. Since we know it's a canon one,
				// we can get it directly, and not (like further below) use
				// the parent and then add the block on top
				externTd = bc.GetTd(block.Hash(), block.NumberU64())
				continue
			}
			if canonical != nil && canonical.Root() == block.Root() {
				// This is most likely a shadow-state attack. When a fork is imported into the
				// database, and it eventually reaches a block height which is not pruned, we
				// just found that the state already exist! This means that the sidechain block
				// refers to a state which already exists in our canon chain.
				//
				// If left unchecked, we would now proceed importing the blocks, without actually
				// having verified the state of the previous blocks.
				log.Warn("Sidechain ghost-state attack detected", "number", block.NumberU64(), "sideroot", block.Root(), "canonroot", canonical.Root())

				// If someone legitimately side-mines blocks, they would still be imported as usual. However,
				// we cannot risk writing unverified blocks to disk when they obviously target the pruning
				// mechanism.
				return it.index, errors.New("sidechain ghost-state attack")
			}
		}
		if externTd == nil {
			externTd = bc.GetTd(block.ParentHash(), block.NumberU64()-1)
		}
		externTd = new(big.Int).Add(externTd, block.Difficulty())

		if !bc.HasBlock(block.Hash(), block.NumberU64()) {
			start := time.Now()
			if err := bc.writeBlockWithoutState(block, externTd); err != nil {
				return it.index, err
			}
			log.Debug("Injected sidechain block", "number", block.Number(), "hash", block.Hash(),
				"diff", block.Difficulty(), "elapsed", common.PrettyDuration(time.Since(start)),
				"txs", len(block.Transactions()), "gas", block.GasUsed(), "uncles", len(block.Uncles()),
				"root", block.Root())
		}
		lastBlock = block
	}
	// At this point, we've written all sidechain blocks to database. Loop ended
	// either on some other error or all were processed. If there was some other
	// error, we can ignore the rest of those blocks.
	//
	// If the externTd was larger than our local TD, we now need to reimport the previous
	// blocks to regenerate the required state
	reorg, err := bc.forker.ReorgNeeded(current, lastBlock.Header())
	if err != nil {
		return it.index, err
	}
	if !reorg {
		localTd := bc.GetTd(current.Hash(), current.Number.Uint64())
		log.Info("Sidechain written to disk", "start", it.first().NumberU64(), "end", it.previous().Number, "sidetd", externTd, "localtd", localTd)
		return it.index, err
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
				return 0, err
			}
			break
		}
		hashes = append(hashes, parent.Hash())
		numbers = append(numbers, parent.Number.Uint64())

		parent = bc.GetHeader(parent.ParentHash, parent.Number.Uint64()-1)
	}
	if parent == nil {
		return it.index, errors.New("missing parent")
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
			if _, err := bc.insertChain(blocks, true); err != nil {
				return 0, err
			}
			blocks, memory = blocks[:0], 0

			// If the chain is terminating, stop processing blocks
			if bc.insertStopped() {
				log.Debug("Abort during blocks processing")
				return 0, nil
			}
		}
	}
	if len(blocks) > 0 {
		log.Info("Importing sidechain segment", "start", blocks[0].NumberU64(), "end", blocks[len(blocks)-1].NumberU64())
		return bc.insertChain(blocks, true)
	}
	return 0, nil
}

// recoverAncestors finds the closest ancestor with available state and re-execute
// all the ancestor blocks since that.
// recoverAncestors is only used post-merge.
// We return the hash of the latest block that we could correctly validate.
func (bc *BlockChain) recoverAncestors(block *types.Block) (common.Hash, error) {
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
		if _, err := bc.insertChain(types.Blocks{b}, false); err != nil {
			return b.ParentHash(), err
		}
	}
	return block.Hash(), nil
}

// collectLogs collects the logs that were generated or removed during
// the processing of a block. These logs are later announced as deleted or reborn.
func (bc *BlockChain) collectLogs(b *types.Block, removed bool) []*types.Log {
	var blobGasPrice *big.Int
	excessBlobGas := b.ExcessBlobGas()
	if excessBlobGas != nil {
		blobGasPrice = eip4844.CalcBlobFee(*excessBlobGas)
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
	return logs
}

// reorg takes two blocks, an old chain and a new chain and will reconstruct the
// blocks and inserts them to be part of the new canonical chain and accumulates
// potential missing transactions and post an event about them.
// Note the new head block won't be processed here, callers need to handle it
// externally.
func (bc *BlockChain) reorg(oldHead *types.Header, newHead *types.Block) error {
	var (
		newChain    types.Blocks
		oldChain    types.Blocks
		commonBlock *types.Block

		deletedTxs []common.Hash
		addedTxs   []common.Hash
	)
	oldBlock := bc.GetBlock(oldHead.Hash(), oldHead.Number.Uint64())
	if oldBlock == nil {
		return errors.New("current head block missing")
	}
	newBlock := newHead

	// Reduce the longer chain to the same number as the shorter one
	if oldBlock.NumberU64() > newBlock.NumberU64() {
		// Old chain is longer, gather all transactions and logs as deleted ones
		for ; oldBlock != nil && oldBlock.NumberU64() != newBlock.NumberU64(); oldBlock = bc.GetBlock(oldBlock.ParentHash(), oldBlock.NumberU64()-1) {
			oldChain = append(oldChain, oldBlock)
			for _, tx := range oldBlock.Transactions() {
				deletedTxs = append(deletedTxs, tx.Hash())
			}
		}
	} else {
		// New chain is longer, stash all blocks away for subsequent insertion
		for ; newBlock != nil && newBlock.NumberU64() != oldBlock.NumberU64(); newBlock = bc.GetBlock(newBlock.ParentHash(), newBlock.NumberU64()-1) {
			newChain = append(newChain, newBlock)
		}
	}
	if oldBlock == nil {
		return errInvalidOldChain
	}
	if newBlock == nil {
		return errInvalidNewChain
	}
	// Both sides of the reorg are at the same number, reduce both until the common
	// ancestor is found
	for {
		// If the common ancestor was found, bail out
		if oldBlock.Hash() == newBlock.Hash() {
			commonBlock = oldBlock
			break
		}
		// Remove an old block as well as stash away a new block
		oldChain = append(oldChain, oldBlock)
		for _, tx := range oldBlock.Transactions() {
			deletedTxs = append(deletedTxs, tx.Hash())
		}
		newChain = append(newChain, newBlock)

		// Step back with both chains
		oldBlock = bc.GetBlock(oldBlock.ParentHash(), oldBlock.NumberU64()-1)
		if oldBlock == nil {
			return errInvalidOldChain
		}
		newBlock = bc.GetBlock(newBlock.ParentHash(), newBlock.NumberU64()-1)
		if newBlock == nil {
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
		logFn(msg, "number", commonBlock.Number(), "hash", commonBlock.Hash(),
			"drop", len(oldChain), "dropfrom", oldChain[0].Hash(), "add", len(newChain), "addfrom", newChain[0].Hash())
		blockReorgAddMeter.Mark(int64(len(newChain)))
		blockReorgDropMeter.Mark(int64(len(oldChain)))
		blockReorgMeter.Mark(1)
	} else if len(newChain) > 0 {
		// Special case happens in the post merge stage that current head is
		// the ancestor of new head while these two blocks are not consecutive
		log.Info("Extend chain", "add", len(newChain), "number", newChain[0].Number(), "hash", newChain[0].Hash())
		blockReorgAddMeter.Mark(int64(len(newChain)))
	} else {
		// len(newChain) == 0 && len(oldChain) > 0
		// rewind the canonical chain to a lower point.
		log.Error("Impossible reorg, please file an issue", "oldnum", oldBlock.Number(), "oldhash", oldBlock.Hash(), "oldblocks", len(oldChain), "newnum", newBlock.Number(), "newhash", newBlock.Hash(), "newblocks", len(newChain))
	}
	// Insert the new chain(except the head block(reverse order)),
	// taking care of the proper incremental order.
	for i := len(newChain) - 1; i >= 1; i-- {
		// Insert the block in the canonical way, re-writing history
		bc.writeHeadBlock(newChain[i])

		// Collect the new added transactions.
		for _, tx := range newChain[i].Transactions() {
			addedTxs = append(addedTxs, tx.Hash())
		}
	}

	// Delete useless indexes right now which includes the non-canonical
	// transaction indexes, canonical chain indexes which above the head.
	indexesBatch := bc.db.NewBatch()
	for _, tx := range types.HashDifference(deletedTxs, addedTxs) {
		rawdb.DeleteTxLookupEntry(indexesBatch, tx)
	}

	// Delete all hash markers that are not part of the new canonical chain.
	// Because the reorg function does not handle new chain head, all hash
	// markers greater than or equal to new chain head should be deleted.
	number := commonBlock.NumberU64()
	if len(newChain) > 1 {
		number = newChain[1].NumberU64()
	}
	for i := number + 1; ; i++ {
		hash := rawdb.ReadCanonicalHash(bc.db, i)
		if hash == (common.Hash{}) {
			break
		}
		rawdb.DeleteCanonicalHash(indexesBatch, i)
	}
	if err := indexesBatch.Write(); err != nil {
		log.Crit("Failed to delete useless indexes", "err", err)
	}

	// Send out events for logs from the old canon chain, and 'reborn'
	// logs from the new canon chain. The number of logs can be very
	// high, so the events are sent in batches of size around 512.

	// Deleted logs + blocks:
	var deletedLogs []*types.Log
	for i := len(oldChain) - 1; i >= 0; i-- {
		// Also send event for blocks removed from the canon chain.
		bc.chainSideFeed.Send(ChainSideEvent{Block: oldChain[i]})

		// Collect deleted logs for notification
		if logs := bc.collectLogs(oldChain[i], true); len(logs) > 0 {
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

	// New logs:
	var rebirthLogs []*types.Log
	for i := len(newChain) - 1; i >= 1; i-- {
		if logs := bc.collectLogs(newChain[i], false); len(logs) > 0 {
			rebirthLogs = append(rebirthLogs, logs...)
		}
		if len(rebirthLogs) > 512 {
			bc.logsFeed.Send(rebirthLogs)
			rebirthLogs = nil
		}
	}
	if len(rebirthLogs) > 0 {
		bc.logsFeed.Send(rebirthLogs)
	}
	return nil
}

// InsertBlockWithoutSetHead executes the block, runs the necessary verification
// upon it and then persist the block and the associate state into the database.
// The key difference between the InsertChain is it won't do the canonical chain
// updating. It relies on the additional SetCanonical call to finalize the entire
// procedure.
func (bc *BlockChain) InsertBlockWithoutSetHead(block *types.Block) error {
	if !bc.chainmu.TryLock() {
		return errChainStopped
	}
	defer bc.chainmu.Unlock()

	log.Info(fmt.Sprintf("InsertBlockWithoutSetHead called for block %s @ %d",
		block.Hash().String(), block.NumberU64()))
	_, err := bc.insertChain(types.Blocks{block}, false)
	return err
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
		if latestValidHash, err := bc.recoverAncestors(head); err != nil {
			return latestValidHash, err
		}
		log.Info("Recovered head state", "number", head.Number(), "hash", head.Hash())
	}
	// Run the reorg if necessary and set the given block as new head.
	start := time.Now()
	if head.ParentHash() != bc.CurrentBlock().Hash() {
		if err := bc.reorg(bc.CurrentBlock(), head); err != nil {
			return common.Hash{}, err
		}
	}
	bc.writeHeadBlock(head)

	log.Info(fmt.Sprintf("Updating hVM header consensus to block %s @ %d in SetCanonical()",
		head.Hash().String(), head.Number().Uint64()))
	err := bc.updateHvmHeaderConsensus(head.Header())
	if err != nil {
		log.Crit(fmt.Sprintf("Unable to update hVM header consensus to block %s @ %d in SetCanonical()",
			head.Hash().String(), head.Number().Uint64()), "err", err)
	}

	// Emit events
	logs := bc.collectLogs(head, false)
	bc.chainFeed.Send(ChainEvent{Block: head, Hash: head.Hash(), Logs: logs})
	if len(logs) > 0 {
		bc.logsFeed.Send(logs)
	}
	bc.chainHeadFeed.Send(ChainHeadEvent{Block: head})

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

func (bc *BlockChain) updateFutureBlocks() {
	futureTimer := time.NewTicker(5 * time.Second)
	defer futureTimer.Stop()
	defer bc.wg.Done()
	for {
		select {
		case <-futureTimer.C:
			bc.procFutureBlocks()
		case <-bc.quit:
			return
		}
	}
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
func (bc *BlockChain) reportBlock(block *types.Block, receipts types.Receipts, err error) {
	rawdb.WriteBadBlock(bc.db, block)
	log.Error(summarizeBadBlock(block, receipts, bc.Config(), err))
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
	_, err := bc.hc.InsertHeaderChain(chain, start, bc.forker)
	return 0, err
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

// GetTrieFlushInterval gets the in-memory tries flush interval
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
