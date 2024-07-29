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

package vm

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"fmt"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/database"
	"math/big"
	"reflect"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/txscript"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/math"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/crypto/blake2b"
	"github.com/ethereum/go-ethereum/crypto/bls12381"
	"github.com/ethereum/go-ethereum/crypto/bn256"
	"github.com/ethereum/go-ethereum/crypto/kzg4844"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
	"github.com/hemilabs/heminetwork/service/tbc"
	"golang.org/x/crypto/ripemd160"
	"golang.org/x/exp/slices"
)

// PrecompiledContract is the basic interface for native Go contracts. The implementation
// requires a deterministic gas count based on the input size of the Run method of the
// contract.
type PrecompiledContract interface {
	RequiredGas(input []byte) uint64 // RequiredPrice calculates the contract gas use
	// Run TODO: Refactor and have a separate signature for hVM calls?
	Run(input []byte, blockContext common.Hash) ([]byte, error) // Run runs the precompiled contract
}

type hVMQueryKey [32]byte

var TBCFullNode *tbc.Server
var tbcChainParams *chaincfg.Params

// TODO: Cache this on-disk at some point, will need to persist restarts to correctly provide execution traces for old txs
var hvmQueryMap = make(map[hVMQueryKey][]byte)

var HvmNullBlockHash = make([]byte, 32)

func GetTBCFullNodeSyncStatus() *tbc.SyncInfo {
	syncInfo := TBCFullNode.Synced(context.Background())
	return &syncInfo
}

// SetupTBCFullNode Sets up the TBC full node that will be available for precompiles
func SetupTBCFullNode(ctx context.Context, cfg *tbc.Config) error {
	switch cfg.Network {
	case "mainnet":
		tbcChainParams = &chaincfg.MainNetParams
	case "testnet3":
		tbcChainParams = &chaincfg.TestNet3Params
	case "localnet":
		tbcChainParams = &chaincfg.RegressionNetParams
	default:
		log.Crit("TBC configured with an unknown network!", "network", cfg.Network)
	}

	tbcNode, err := tbc.NewServer(cfg)
	if err != nil {
		log.Crit("Unable to create TBC node!", "err", err)
		return err
	}

	go func() {
		err := tbcNode.Run(ctx)
		if err != nil && err != context.Canceled {
			panic(err)
		}
	}()

	TBCFullNode = tbcNode

	return nil
}

// Very expensive but only needed for recovery.
// If needed for other things in the future, update TBC to efficiently handle this query.
func getCanonicalHeaderAtHeight(height uint64) *wire.BlockHeader {
	height, header, err := TBCFullNode.BlockHeaderBest(context.Background())
	if err != nil {
		// TODO: Recovery?
		log.Crit("Unable to get best block header from TBC Full Node!")
	}

	cursor := header
	cursorHeight := height
	// Walk back best tip until we get to the destination height
	for cursorHeight > height {
		prevHeader, prevHeight, err := TBCFullNode.BlockHeaderByHash(context.Background(), &cursor.PrevBlock)
		if err != nil {
			// TODO: Recovery?
			log.Crit("Unable to get block %x from TBC Full Node!", cursor.PrevBlock[:])
		}
		cursor = prevHeader
		cursorHeight = prevHeight // pedantic
	}

	return cursor
}

// TODO: Refactor this, IsEqual was creating issues
func hashEquals(a chainhash.Hash, b chainhash.Hash) bool {
	return bytes.Equal(a[:], b[:])
}

// Walks backwards from both headers to find a common ancestor.
// Returns common ancestor header, a boolean for whether there was a fork or one of the passed
// in headers was an ancestor of the other
// TODO: Refactor this, also could return height to make some upstream uses easier
func findCommonAncestor(a *tbc.HashHeight, b *tbc.HashHeight) (*wire.BlockHeader, bool, error) {
	if a.Hash.IsEqual(&b.Hash) {
		header, _, err := TBCFullNode.BlockHeaderByHash(context.Background(), &a.Hash)
		if err != nil {
			return nil, false, err
		}
		return header, false, nil // They are same, no fork
	}

	lowerHeight := a.Height
	higherHash := b.Hash
	lowerHash := a.Hash
	if b.Height < lowerHeight {
		lowerHeight = b.Height
		higherHash = a.Hash
		lowerHash = b.Hash
	}

	highCursorHeader, highCursorHeight, err := TBCFullNode.BlockHeaderByHash(context.Background(), &higherHash)
	if err != nil {
		return nil, false, err
	}

	lowCursorHeader, lowCursorHeight, err := TBCFullNode.BlockHeaderByHash(context.Background(), &lowerHash)
	if err != nil {
		return nil, false, err
	}

	// TODO: Redundant heights
	for highCursorHeight > lowCursorHeight {
		highCursorHeader, highCursorHeight, err = TBCFullNode.BlockHeaderByHash(context.Background(), &highCursorHeader.PrevBlock)
		if err != nil {
			return nil, false, err
		}
	}

	// If the cursors are now equal then one was the ancestor
	if hashEquals(lowCursorHeader.BlockHash(), highCursorHeader.BlockHash()) {
		return lowCursorHeader, false, nil // No fork
	}

	// Cursors are at the same height but on different forks, walk both of them back until they match
	// TODO can just do this for loop and ignore the if condition above
	for !hashEquals(lowCursorHeader.BlockHash(), highCursorHeader.BlockHash()) {
		lowCursorHeader, lowCursorHeight, err = TBCFullNode.BlockHeaderByHash(context.Background(), &lowCursorHeader.PrevBlock)
		if err != nil {
			return nil, false, err
		}
		highCursorHeader, highCursorHeight, err = TBCFullNode.BlockHeaderByHash(context.Background(), &highCursorHeader.PrevBlock)
		if err != nil {
			return nil, false, err
		}
	}

	// Now the cursors match
	return lowCursorHeader, true, nil // There was a fork
}

// Moves the Tx indexer to the specified header. This does not
// assume that the move to header is straight - it will determine
// whether a fork is required and handle it appropriately.
// This should only be used when recovering from a desync between
// the indexers, otherwise always use moveIndexersToHeight
// TODO: Dedup with moveTxIndexerToUtxo & TBCIndexToHeader logic somehow?
func moveTxIndexerToHeader(header *wire.BlockHeader) error {
	tIndexInfo, err := TBCFullNode.TxIndexHash(context.Background())
	headerHash := header.BlockHash()
	if err != nil {
		// Critical error
		log.Crit(fmt.Sprintf("Unable to move TBC full node Tx indexer to block %x; unable to get TxIndexHash",
			headerHash[:]), "err", err)
	}

	if hashEquals(tIndexInfo.Hash, header.BlockHash()) {
		// already done
		return nil
	}

	targetHash := header.BlockHash()
	_, targetHeight, err := TBCFullNode.BlockHeaderByHash(context.Background(), &targetHash)
	if err != nil {
		// Passed in header is not available
		return err
	}

	targetHH := &tbc.HashHeight{
		Height: targetHeight,
		Hash:   targetHash,
	}

	ancestor, isFork, err := findCommonAncestor(tIndexInfo, targetHH)
	if err != nil {
		// Critical error
		log.Crit(fmt.Sprintf("Unable to find common ancestor between tx indexer tip %x and best header %x",
			tIndexInfo.Hash[:], targetHH.Hash[:]))
	}
	ancestorHash := ancestor.BlockHash()

	if !isFork {
		// Tx indexer only needs to move in one direction, and TxIndexer will figure out which
		err = TBCFullNode.TxIndexer(context.Background(), &targetHH.Hash)
		if err != nil {
			log.Error("Unable to move Tx indexer from current hash %x to requested hash %x",
				tIndexInfo.Hash[:], targetHH.Hash[:])
			return err
		}
	} else {
		// Tx indexer needs to first unwind to the ancestor, and then wind to the requested target
		err = TBCFullNode.TxIndexer(context.Background(), &ancestorHash)
		if err != nil {
			log.Error("While indexing over a fork, unable to unwind Tx indexer from current hash "+
				"%x to requested hash %x", tIndexInfo.Hash[:], ancestorHash[:])
			return err
		}
		// We unwound to common ancestor, now need to wind forward
		err = TBCFullNode.TxIndexer(context.Background(), &targetHH.Hash)
		if err != nil {
			log.Error("While indexing over a fork, unable to wind Tx indexer from current hash "+
				"%x to requested hash %x", ancestorHash[:], targetHH.Hash[:])
		}
	}

	// Successful
	return nil
}

// Moves the UTXO indexer to the specified header. This does not
// assume that the move to header is straight - it will determine
// whether a fork is required and handle it appropriately.
// This should only be used when recovering from a desync between
// the indexers, otherwise always use moveIndexersToHeight
// TODO: Dedup with moveTxIndexerToHeader / TBCIndexToHeader logic somehow?
func moveUtxoIndexerToHeader(header *wire.BlockHeader) error {
	uIndexInfo, err := TBCFullNode.UtxoIndexHash(context.Background())
	headerHash := header.BlockHash()
	if err != nil {
		// Critical error
		log.Crit(fmt.Sprintf("Unable to move TBC full node UTXO indexer to block %x; unable to get UtxoIndexHash",
			headerHash[:]), "err", err)
	}

	if hashEquals(uIndexInfo.Hash, header.BlockHash()) {
		// already done
		return nil
	}

	targetHash := header.BlockHash()
	_, targetHeight, err := TBCFullNode.BlockHeaderByHash(context.Background(), &targetHash)
	if err != nil {
		// Passed in header is not available
		return err
	}

	targetHH := &tbc.HashHeight{
		Height: targetHeight,
		Hash:   targetHash,
	}

	ancestor, isFork, err := findCommonAncestor(uIndexInfo, targetHH)
	if err != nil {
		// Critical error
		log.Crit(fmt.Sprintf("Unable to find common ancestor between utxo indexer tip %x and best header %x",
			uIndexInfo.Hash[:], targetHH.Hash[:]))
	}
	ancestorHash := ancestor.BlockHash()

	if !isFork {
		// UTXO indexer only needs to move in one direction, and UtxoIndexer will figure out which
		err = TBCFullNode.UtxoIndexer(context.Background(), &targetHH.Hash)
		if err != nil {
			log.Error("Unable to move UTXO indexer from current hash %x to requested hash %x",
				uIndexInfo.Hash[:], targetHH.Hash[:])
			return err
		}
	} else {
		// UTXO indexer needs to first unwind to the ancestor, and then wind to the requested target
		err = TBCFullNode.UtxoIndexer(context.Background(), &ancestorHash)
		if err != nil {
			log.Error("While indexing over a fork, unable to unwind UTXO indexer from current hash "+
				"%x to requested hash %x", uIndexInfo.Hash[:], ancestorHash[:])
			return err
		}
		// We unwound to common ancestor, now need to wind forward
		err = TBCFullNode.UtxoIndexer(context.Background(), &targetHH.Hash)
		if err != nil {
			log.Error("While indexing over a fork, unable to wind UTXO indexer from current hash "+
				"%x to requested hash %x", ancestorHash[:], targetHH.Hash[:])
		}
	}

	// Successful
	return nil
}

// fixMismatchedIndexesIfRequired checks if the UTXO and TX indexers do not match,
// and if they don't walks both of them back to the highest common ancestor.
// This should only ever be required if something like an unclean
// shutdown resulted in TBC's indexers being off.
func fixMismatchedIndexesIfRequired() error {
	uIndexInfo, err := TBCFullNode.UtxoIndexHash(context.Background())
	if err != nil {
		log.Crit("Unable to get UtxoIndexHash", "err", err)
	}
	tIndexInfo, err := TBCFullNode.TxIndexHash(context.Background())
	if err != nil {
		log.Crit("Unable to get TxIndexHash", "err", err)
	}

	if !hashEquals(uIndexInfo.Hash, tIndexInfo.Hash) {
		// Find the common ancestor
		ancestor, _, err := findCommonAncestor(uIndexInfo, tIndexInfo)
		if err != nil {
			log.Error(fmt.Sprintf("Unable to find common ancestor between Utxo and Tx indexers! "+
				"Utxo indexed to: %x, Tx indexed to: %x", uIndexInfo.Hash[:], tIndexInfo.Hash[:]))
		}

		ancestorHash := ancestor.BlockHash()
		log.Info(fmt.Sprintf("Fixing mismatched UTXO and Tx indexes, UTXO indexer @ %x, "+
			"Tx indexer @ %x, common ancestor @ %x", uIndexInfo.Hash[:], tIndexInfo.Hash[:], ancestorHash[:]))

		ancestorHeader, _, err := TBCFullNode.BlockHeaderByHash(context.Background(), &ancestorHash)

		// Rewind both to common ancestor
		err = moveUtxoIndexerToHeader(ancestorHeader)
		if err != nil {
			log.Crit(fmt.Sprintf("Unable to repair indexer desync by moving UTXO indexer "+
				"from %x to common ancestor %x", uIndexInfo.Hash[:], ancestorHash[:]))
		}
		err = moveTxIndexerToHeader(ancestorHeader)
		if err != nil {
			log.Crit(fmt.Sprintf("Unable to repair indexer desync by moving Tx indexer "+
				"from %x to common ancestor %x", tIndexInfo.Hash[:], ancestorHash[:]))
		}
	}

	return nil
}

// TBCIndexToHeader is a convenience pass-through to TBCIndexToHashHeight with
// a Bitcoin header provided.
func TBCIndexToHeader(header *wire.BlockHeader) error {
	targetHash := header.BlockHash()
	_, targetHeight, err := TBCFullNode.BlockHeaderByHash(context.Background(), &targetHash)
	if err != nil {
		// Passed in header is not available
		return err
	}

	hh := tbc.HashHeight{
		Hash:   header.BlockHash(),
		Height: targetHeight,
	}

	return TBCIndexToHashHeight(&hh)
}

// TBCRestoreIndexersToPoint attempts to move the TBC Full Node's UTXO
// and Tx indexers back to their respective points from a prior SyncInfo.
// Under normal operation the UTXO and Tx index tips should always be
// the same, but this method will restore UTXO and Tx indexers to different
// states if specified by the passed-in Syncinfo.
func TBCRestoreIndexersToPoint(point *tbc.SyncInfo) error {
	utxoPoint := point.Utxo
	utxoHeader, _, err := TBCFullNode.BlockHeaderByHash(context.Background(), &utxoPoint.Hash)
	if err != nil {
		return err
	}
	err = moveUtxoIndexerToHeader(utxoHeader)
	if err != nil {
		return err
	}

	txPoint := point.Tx
	txHeader, _, err := TBCFullNode.BlockHeaderByHash(context.Background(), &txPoint.Hash)
	if err != nil {
		return err
	}
	err = moveTxIndexerToHeader(txHeader)
	if err != nil {
		return err
	}
	return nil
}

// TBCIndexToHashHeight first checks to make sure the UTXO and Tx indexers
// are the same (and if not, moves both to the lowest indexed height of either)
// and then moves the indexer to the specified target hash and height,
// unwinding and winding if the move from current indexer state to new
// target state involves a reorganization.
func TBCIndexToHashHeight(targetHH *tbc.HashHeight) error {
	log.Info("TBCIndexToHashHight called with target", "target", targetHH.String())
	// Check for indexer desync and attempt to fix.
	err := fixMismatchedIndexesIfRequired()
	if err != nil {
		log.Crit(fmt.Sprintf("Unable to fix mismatched indexes"))
	}

	targetHash := targetHH.Hash

	// Already checked for indexer desync so if we got here UTXO and Tx indexes are the same
	tIndexInfo, err := TBCFullNode.TxIndexHash(context.Background())
	if err != nil {
		// Critical error
		log.Crit("Unable to move TBC full node indexers to block %x; unable to get TxIndexHash", "err", err)
	}

	if hashEquals(tIndexInfo.Hash, targetHash) {
		// already done
		return nil
	}

	ancestor, isFork, err := findCommonAncestor(tIndexInfo, targetHH)
	if err != nil {
		// Critical error
		log.Crit(fmt.Sprintf("Unable to find common ancestor between indexers tip %x and best header %x",
			tIndexInfo.Hash[:], targetHH.Hash[:]))
	}
	ancestorHash := ancestor.BlockHash()

	if !isFork {
		// Indexers only needs to move in one direction, and the indexer will figure out which
		err = TBCFullNode.SyncIndexersToHash(context.Background(), &targetHH.Hash)
		if err != nil {
			log.Error("Unable to move indexers from current hash %x to requested hash %x",
				tIndexInfo.Hash[:], targetHH.Hash[:])
			return err
		}
	} else {
		// Indexers need to first unwind to the ancestor, and then wind to the requested target
		err = TBCFullNode.SyncIndexersToHash(context.Background(), &ancestorHash)
		if err != nil {
			log.Error("While indexing over a fork, unable to unwind indexers from current hash "+
				"%x to requested hash %x", tIndexInfo.Hash[:], ancestorHash[:])
			return err
		}
		// We unwound to common ancestor, now need to wind forward
		err = TBCFullNode.SyncIndexersToHash(context.Background(), &targetHH.Hash)
		if err != nil {
			log.Error("While indexing over a fork, unable to wind indexers from current hash "+
				"%x to requested hash %x", ancestorHash[:], targetHH.Hash[:])
		}
	}

	// Successful
	return nil
}

func hashHeightForHeader(ctx context.Context, header *wire.BlockHeader) (*tbc.HashHeight, error) {
	hash := header.BlockHash()
	_, height, err := TBCFullNode.BlockHeaderByHash(ctx, &hash)
	if err != nil {
		return nil, err
	}

	return &tbc.HashHeight{Hash: hash, Height: height}, nil
}

// TBCBlocksAvailableToHeader Checks whether the TBC full node has all of the blocks required to index to the
// specified header from its current location.
//
// This function assumes that any blocks below the current indexed tip are available, otherwise the indexers
// would have been unable to reach that tip previously.
//
// This function will always return true if the specified header is a direct ancestor of current indexed tip,
// including if they are equal.
//
// If this function is called with a header that requires a reorg, it finds the common ancestor and returns
// whether all blocks required to index after walking back to that common ancestor are available.
//
// If TBC's UTXO and Tx indexers are not in the same state, this function will determine whether all blocks
// are available based on the commnon ancestor of the misaligned indexer tips (such that reconciling the
// indexer tips and then moving to the specified endingHeader would have all required blocks.
func TBCBlocksAvailableToHeader(ctx context.Context, endingHeader *wire.BlockHeader) (bool, error) {
	syncInfo := TBCFullNode.Synced(ctx)
	utxoSync := syncInfo.Utxo
	txSync := syncInfo.Tx

	// When both indexers are at the same header, this will be that header.
	// If the indexers are at different positions, this will be the common
	// ancestor they share, which we know we could walk back to since the
	// blocks were available to index to the two different tips
	commonIndexTip, _, err := findCommonAncestor(&utxoSync, &txSync)
	if err != nil {
		if errors.As(err, &database.ErrNotFound) {
			return false, nil
		}
		return false, err
	}
	tipHH, err := hashHeightForHeader(ctx, commonIndexTip)
	if err != nil {
		if errors.As(err, &database.ErrNotFound) {
			return false, nil
		}
		return false, err
	}
	targetHH, err := hashHeightForHeader(ctx, endingHeader)
	if err != nil {
		if errors.As(err, &database.ErrNotFound) {
			return false, nil
		}
		return false, err
	}

	// Find common ancestor between current common index ancestor tip and target header
	ancestorToTarget, _, err := findCommonAncestor(tipHH, targetHH)
	if err != nil {
		if errors.As(err, &database.ErrNotFound) {
			return false, nil
		}
		return false, err
	}
	ancestorToTargetHash := ancestorToTarget.BlockHash()
	_, ancestorHeight, err := TBCFullNode.BlockHeaderByHash(ctx, &ancestorToTargetHash)
	if err != nil {
		if errors.As(err, &database.ErrNotFound) {
			return false, nil
		}
		return false, err
	}

	// Whether or not moving to the target requires unwinding, the only blocks that
	// could be missing are the ones that would have to be indexed after the rewind,
	// so we only need to check for all blocks from the ancestor to the target.
	// Walk backwards from the target down to the ancestor, as generally if blocks
	// are missing they will be towards the end so top down will find more efficiently.
	// TODO: make more efficient by adding a cheap check in TBC for a full block being available.
	endingHash := endingHeader.BlockHash()
	cursor, height, err := TBCFullNode.BlockHeaderByHash(ctx, &endingHash)
	if err != nil {
		return false, err
	}
	cursorHash := endingHash

	// Walk backwards until our cursor matches the ancestor
	for !bytes.Equal(cursorHash[:], ancestorToTargetHash[:]) {
		available, err := TBCFullNode.FullBlockAvailable(ctx, &cursorHash)
		if err != nil {
			return false, err
		}
		if !available {
			return false, nil
		}

		cursor, height, err = TBCFullNode.BlockHeaderByHash(ctx, &cursor.PrevBlock)
		if err != nil {
			if errors.As(err, &database.ErrNotFound) {
				return false, nil
			}
			return false, err
		}
		if height < ancestorHeight {
			// Somehow walking backwards got to a lower block than the ancestor we are looking for.
			// Should never happen, would imply that the current indexed tip and target are not
			// on the same chain graph
			return false, fmt.Errorf("TBCBlocksAvailableToHeader failed walking backwards from"+
				" %x looking for %x, walked to height=%d but ancestorHeight=%d", endingHash[:],
				ancestorToTargetHash[:], height, ancestorHeight)
		}
		cursorHash = cursor.PrevBlock
	}

	// Above for loop exited meaning all blocks from the target back to common ancestor with
	// indexer were successfully fetched from database
	return true, nil
}

// PrecompiledContractsHomestead contains the default set of pre-compiled Ethereum
// contracts used in the Frontier and Homestead releases.
var PrecompiledContractsHomestead = map[common.Address]PrecompiledContract{
	common.BytesToAddress([]byte{1}): &ecrecover{},
	common.BytesToAddress([]byte{2}): &sha256hash{},
	common.BytesToAddress([]byte{3}): &ripemd160hash{},
	common.BytesToAddress([]byte{4}): &dataCopy{},
}

// PrecompiledContractsByzantium contains the default set of pre-compiled Ethereum
// contracts used in the Byzantium release.
var PrecompiledContractsByzantium = map[common.Address]PrecompiledContract{
	common.BytesToAddress([]byte{1}): &ecrecover{},
	common.BytesToAddress([]byte{2}): &sha256hash{},
	common.BytesToAddress([]byte{3}): &ripemd160hash{},
	common.BytesToAddress([]byte{4}): &dataCopy{},
	common.BytesToAddress([]byte{5}): &bigModExp{eip2565: false},
	common.BytesToAddress([]byte{6}): &bn256AddByzantium{},
	common.BytesToAddress([]byte{7}): &bn256ScalarMulByzantium{},
	common.BytesToAddress([]byte{8}): &bn256PairingByzantium{},
}

// PrecompiledContractsIstanbul contains the default set of pre-compiled Ethereum
// contracts used in the Istanbul release.
var PrecompiledContractsIstanbul = map[common.Address]PrecompiledContract{
	common.BytesToAddress([]byte{1}): &ecrecover{},
	common.BytesToAddress([]byte{2}): &sha256hash{},
	common.BytesToAddress([]byte{3}): &ripemd160hash{},
	common.BytesToAddress([]byte{4}): &dataCopy{},
	common.BytesToAddress([]byte{5}): &bigModExp{eip2565: false},
	common.BytesToAddress([]byte{6}): &bn256AddIstanbul{},
	common.BytesToAddress([]byte{7}): &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{8}): &bn256PairingIstanbul{},
	common.BytesToAddress([]byte{9}): &blake2F{},
}

// PrecompiledContractsBerlin contains the default set of pre-compiled Ethereum
// contracts used in the Berlin release.
var PrecompiledContractsBerlin = map[common.Address]PrecompiledContract{
	common.BytesToAddress([]byte{1}): &ecrecover{},
	common.BytesToAddress([]byte{2}): &sha256hash{},
	common.BytesToAddress([]byte{3}): &ripemd160hash{},
	common.BytesToAddress([]byte{4}): &dataCopy{},
	common.BytesToAddress([]byte{5}): &bigModExp{eip2565: true},
	common.BytesToAddress([]byte{6}): &bn256AddIstanbul{},
	common.BytesToAddress([]byte{7}): &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{8}): &bn256PairingIstanbul{},
	common.BytesToAddress([]byte{9}): &blake2F{},
}

// PrecompiledContractsCancun contains the default set of pre-compiled Ethereum
// contracts used in the Cancun release.
var PrecompiledContractsCancun = map[common.Address]PrecompiledContract{
	common.BytesToAddress([]byte{1}):    &ecrecover{},
	common.BytesToAddress([]byte{2}):    &sha256hash{},
	common.BytesToAddress([]byte{3}):    &ripemd160hash{},
	common.BytesToAddress([]byte{4}):    &dataCopy{},
	common.BytesToAddress([]byte{5}):    &bigModExp{eip2565: true},
	common.BytesToAddress([]byte{6}):    &bn256AddIstanbul{},
	common.BytesToAddress([]byte{7}):    &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{8}):    &bn256PairingIstanbul{},
	common.BytesToAddress([]byte{9}):    &blake2F{},
	common.BytesToAddress([]byte{0x0a}): &kzgPointEvaluation{},
}

// PrecompiledContractsBLS contains the set of pre-compiled Ethereum
// contracts specified in EIP-2537. These are exported for testing purposes.
var PrecompiledContractsBLS = map[common.Address]PrecompiledContract{
	common.BytesToAddress([]byte{10}): &bls12381G1Add{},
	common.BytesToAddress([]byte{11}): &bls12381G1Mul{},
	common.BytesToAddress([]byte{12}): &bls12381G1MultiExp{},
	common.BytesToAddress([]byte{13}): &bls12381G2Add{},
	common.BytesToAddress([]byte{14}): &bls12381G2Mul{},
	common.BytesToAddress([]byte{15}): &bls12381G2MultiExp{},
	common.BytesToAddress([]byte{16}): &bls12381Pairing{},
	common.BytesToAddress([]byte{17}): &bls12381MapG1{},
	common.BytesToAddress([]byte{18}): &bls12381MapG2{},
}

var hvmContractsToAddress = map[reflect.Type][]byte{
	reflect.TypeOf(&btcBalAddr{}):         {0x40},
	reflect.TypeOf(&btcUtxosAddrList{}):   {0x41},
	reflect.TypeOf(&btcTxByTxid{}):        {0x42},
	reflect.TypeOf(&btcTxConfirmations{}): {0x43},
	reflect.TypeOf(&btcLastHeader{}):      {0x44},
	reflect.TypeOf(&btcHeaderN{}):         {0x45},
	reflect.TypeOf(&btcAddrToScript{}):    {0x46},
}

var PrecompiledContractsHvm0 = map[common.Address]PrecompiledContract{
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcBalAddr{})]):         &btcBalAddr{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcUtxosAddrList{})]):   &btcUtxosAddrList{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcTxByTxid{})]):        &btcTxByTxid{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcTxConfirmations{})]): &btcTxConfirmations{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcLastHeader{})]):      &btcLastHeader{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcHeaderN{})]):         &btcHeaderN{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcAddrToScript{})]):    &btcAddrToScript{},
}

var (
	PrecompiledAddressesCancun    []common.Address
	PrecompiledAddressesBerlin    []common.Address
	PrecompiledAddressesIstanbul  []common.Address
	PrecompiledAddressesByzantium []common.Address
	PrecompiledAddressesHomestead []common.Address
	PrecompiledAddressesHvm0      []common.Address
)

func init() {
	for k := range PrecompiledContractsHomestead {
		PrecompiledAddressesHomestead = append(PrecompiledAddressesHomestead, k)
	}
	for k := range PrecompiledContractsByzantium {
		PrecompiledAddressesByzantium = append(PrecompiledAddressesByzantium, k)
	}
	for k := range PrecompiledContractsIstanbul {
		PrecompiledAddressesIstanbul = append(PrecompiledAddressesIstanbul, k)
	}
	for k := range PrecompiledContractsBerlin {
		PrecompiledAddressesBerlin = append(PrecompiledAddressesBerlin, k)
	}
	for k := range PrecompiledContractsCancun {
		PrecompiledAddressesCancun = append(PrecompiledAddressesCancun, k)
	}
	for k := range PrecompiledContractsHvm0 {
		// TODO: Does this assume bad indexes? Does this even need to be done?
		PrecompiledAddressesHvm0 = append(PrecompiledAddressesHvm0, k)
	}
}

func activeUpstreamPrecompiles(rules params.Rules) []common.Address {
	switch {
	case rules.IsCancun:
		return PrecompiledAddressesCancun
	case rules.IsBerlin:
		return PrecompiledAddressesBerlin
	case rules.IsIstanbul:
		return PrecompiledAddressesIstanbul
	case rules.IsByzantium:
		return PrecompiledAddressesByzantium
	default:
		return PrecompiledAddressesHomestead
	}
}

// ActivePrecompiles returns the precompiles enabled with the current configuration.
func ActivePrecompiles(rules params.Rules) []common.Address {
	// For now, Hemi upgrades can be performed out-of-sync with upstream updates.
	// As a result, this code is modified to select upstream precompiles, and then
	// Layer on Hemi-specific precompile lists.
	// Original ActivePrecompiles logic moved to activeUpstreamPrecompiles.
	// TODO: Make this more efficient if necessary

	nonHvmPrecompiles := activeUpstreamPrecompiles(rules)

	switch {
	case rules.IsHvm0:
		return append(nonHvmPrecompiles, PrecompiledAddressesHvm0...)
	default:
		return nonHvmPrecompiles
	}
}

// calculateHVMQueryKey constructs an hVMQueryKey which is used to cache hVM responses.
// Each key is (precompile_input + precompile_address_byte + containing_header_hash)
// This query key is unique for a specific precompile called with specific input argument contained in a specific block
func calculateHVMQueryKey(input []byte, precompileAddress byte, blockContext common.Hash) (hVMQueryKey, error) {
	if bytes.Equal(blockContext[:], HvmNullBlockHash) {
		return hVMQueryKey(make([]byte, 32)), fmt.Errorf("cannot create a hVM Query Key for a null containing block")
	}
	h := sha256.New()
	v := append(blockContext[:], precompileAddress)
	v = append(v, input...)
	_, err := h.Write(v)
	if err != nil {
		return [32]byte{}, err
	}
	hs := h.Sum(nil)
	var c [32]byte
	copy(c[0:32], hs[0:32])
	var k hVMQueryKey
	k = c
	return k, nil
}

func isValidBlock(blockContext common.Hash) bool {
	return !bytes.Equal(blockContext[:], HvmNullBlockHash)
}

// RunPrecompiledContract runs and evaluates the output of a precompiled contract.
// It returns
// - the returned bytes,
// - the _remaining_ gas,
// - any error that occurred
func RunPrecompiledContract(p PrecompiledContract, input []byte, suppliedGas uint64, blockContext common.Hash) (ret []byte, remainingGas uint64, err error) {
	gasCost := p.RequiredGas(input)
	if suppliedGas < gasCost {
		return nil, 0, ErrOutOfGas
	}
	suppliedGas -= gasCost
	output, err := p.Run(input, blockContext)
	return output, suppliedGas, err
}

type btcBalAddr struct{}

func (c *btcBalAddr) RequiredGas(input []byte) uint64 {
	return params.BtcAddrBal
}

func (c *btcBalAddr) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// TODO: 24 to global variable
	if input == nil || len(input) < 24 {
		log.Debug("btcBalAddr run called with nil or too small input", "input", input)
		return nil, nil
	}
	if TBCFullNode == nil {
		log.Crit("hVM Precompile called but the TBC Full Node is not setup")
	}

	var k hVMQueryKey
	if isValidBlock(blockContext) {
		k, err := calculateHVMQueryKey(input, hvmContractsToAddress[reflect.TypeOf(c)][0], blockContext)
		if err != nil {
			log.Crit("Unable to calculate hVM Query Key!", "input", input, "blockContext", blockContext)
		}
		cachedResult, exists := hvmQueryMap[k]
		if exists {
			log.Debug(fmt.Sprintf("btcTxConfirmations returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	addr := string(input)
	log.Debug("btcBalAddr called", "address", addr)
	if TBCFullNode == nil {
		log.Crit("TBCIndexer is nil!")
	}

	bal, err := TBCFullNode.BalanceByAddress(context.Background(), addr)

	if err != nil {
		// TODO: Error handling
		log.Error("hVM Error: Unable to process balance of address", "address", addr, "err", err)
		return nil, err
	}

	resp := make([]byte, 8)
	binary.BigEndian.PutUint64(resp, bal)
	log.Debug("btcBalAddr returning data", "returnedData", fmt.Sprintf("%x", resp))
	if isValidBlock(blockContext) {
		hvmQueryMap[k] = resp
	}
	return resp, nil
}

type btcTxConfirmations struct{}

func (c *btcTxConfirmations) RequiredGas(input []byte) uint64 {
	return params.BtcTxConf
}

func (c *btcTxConfirmations) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if input == nil || len(input) != 32 {
		log.Debug("btcTxConfirmations run called with nil or != 32 input", "input", fmt.Sprintf("%x", input))
	}
	log.Debug("btcTxConfirmations called", "txid", input)
	if TBCFullNode == nil {
		log.Crit("TBCIndexer is nil!")
	}

	var k hVMQueryKey
	if isValidBlock(blockContext) {
		k, err := calculateHVMQueryKey(input, hvmContractsToAddress[reflect.TypeOf(c)][0], blockContext)
		if err != nil {
			log.Error("Unable to calculate hVM Query Key!",
				"input", fmt.Sprintf("%x", input),
				"blockContext", fmt.Sprintf("%x", blockContext))
		}
		cachedResult, exists := hvmQueryMap[k]
		if exists {
			log.Debug(fmt.Sprintf("btcTxConfirmations returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	var txid = make([]byte, 32)
	copy(txid[0:32], input[0:32])
	slices.Reverse(txid)
	// txidMade := [32]byte(txid)
	txHash := chainhash.Hash{}
	err := txHash.SetBytes(txid[:])
	if err != nil {
		log.Warn("Unable to lookup tx confirmations by Txid; unable to convert txid %x to chainhash!", "txid", txid, "err", err)
	}

	_, blockHash, err := TBCFullNode.TxById(context.Background(), &txHash)
	if err != nil {
		log.Error("Unable to lookup transaction confirmations by txid", "txid", txid, "err", err)
		return nil, err
	}

	// TODO: Canonical check, needs upstream TBC modification.
	// For now hVM has an edge case where confirmation value from a forked chain could be returned.

	_, height, err := TBCFullNode.BlockHeaderByHash(context.Background(), blockHash)
	if err != nil {
		log.Error(fmt.Sprintf("Unable to get block header by hash %x", blockHash[:]))
		return nil, err
	}

	heightBest, _, err := TBCFullNode.BlockHeaderBest(context.Background())
	if err != nil {
		log.Error("Unable to get best block header")
		return nil, err
	}

	resp := make([]byte, 4)
	binary.BigEndian.PutUint32(resp, uint32(heightBest-height+1))

	log.Debug("txidConfirmations returning data", "returnedData", fmt.Sprintf("%x", resp))

	if isValidBlock(blockContext) {
		hvmQueryMap[k] = resp
	}
	return resp, nil
}

type btcAddrToScript struct{}

func (c *btcAddrToScript) RequiredGas(input []byte) uint64 {
	return params.BtcAddrToScript
}

func (c *btcAddrToScript) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if input == nil || len(input) < 24 {
		log.Debug("btcAddrToScript run called with nil or too small input", "input", fmt.Sprintf("%x", input))
		return nil, nil
	}
	if TBCFullNode == nil {
		log.Crit("TBCIndexer is nil!")
	}

	var k hVMQueryKey
	if isValidBlock(blockContext) {
		k, err := calculateHVMQueryKey(input, hvmContractsToAddress[reflect.TypeOf(c)][0], blockContext)
		if err != nil {
			log.Error("Unable to calculate hVM Query Key!",
				"input", fmt.Sprintf("%x", input),
				"blockContext", fmt.Sprintf("%x", blockContext))
		}
		cachedResult, exists := hvmQueryMap[k]
		if exists {
			log.Debug(fmt.Sprintf("btcAddrToScript returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	addressStr := string(input)
	log.Debug("btcAddrToScript called", "address", addressStr)

	addr, err := btcutil.DecodeAddress(addressStr, tbcChainParams)
	if err != nil {
		log.Error("In btcAddrToScript call, unable to decode address", "addressStr", addressStr)
		return nil, err
	}

	script, err := txscript.PayToAddrScript(addr)
	if err != nil {
		log.Error("In btcAddrToScript call, unable to convert address to pay script", "addressStr", addressStr)
		return nil, err
	}

	resp := make([]byte, 0)
	resp = append(resp, script[:]...)
	log.Debug("btcAddrToScript returning data", "returnedData", fmt.Sprintf("%x", resp))
	if isValidBlock(blockContext) {
		hvmQueryMap[k] = resp
	}
	return resp, nil
}

type btcLastHeader struct{}

func (c *btcLastHeader) RequiredGas(input []byte) uint64 {
	return params.BtcLastHeader
}

func (c *btcLastHeader) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// No input validation
	if TBCFullNode == nil {
		log.Crit("TBCIndexer is nil!")
	}

	var k hVMQueryKey
	if isValidBlock(blockContext) {
		k, err := calculateHVMQueryKey(input, hvmContractsToAddress[reflect.TypeOf(c)][0], blockContext)
		if err != nil {
			log.Error("Unable to calculate hVM Query Key!",
				"input", fmt.Sprintf("%x", input),
				"blockContext", fmt.Sprintf("%x", blockContext))
		}
		cachedResult, exists := hvmQueryMap[k]
		if exists {
			log.Debug(fmt.Sprintf("btcTxConfirmations returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	height, bestHeader, err := TBCFullNode.BlockHeaderBest(context.Background())

	if err != nil {
		log.Error("Unable to lookup best header!")
		return nil, err
	}

	hash := bestHeader.BlockHash()
	prevHash := bestHeader.PrevBlock
	merkle := bestHeader.MerkleRoot

	var hashReverse = make([]byte, 32)
	copy(hashReverse[0:32], hash[0:32])
	slices.Reverse(hashReverse)

	var prevHashReverse = make([]byte, 32)
	copy(prevHashReverse[0:32], prevHash[0:32])
	slices.Reverse(prevHashReverse)

	var merkleReverse = make([]byte, 32)
	copy(merkleReverse[0:32], merkle[0:32])
	slices.Reverse(merkleReverse)

	// TODO: serialize header directly instead
	resp := make([]byte, 4)
	binary.BigEndian.PutUint32(resp, uint32(height))
	resp = append(resp, hashReverse[:]...)
	resp = binary.BigEndian.AppendUint32(resp, uint32(bestHeader.Version))
	resp = append(resp, prevHashReverse[:]...)
	resp = append(resp, merkleReverse[:]...)
	resp = binary.BigEndian.AppendUint32(resp, uint32(bestHeader.Timestamp.Unix()))
	resp = binary.BigEndian.AppendUint32(resp, bestHeader.Bits)
	resp = binary.BigEndian.AppendUint32(resp, bestHeader.Nonce)

	log.Debug("btcLastHeader returning data", "returnedData", fmt.Sprintf("%x", resp))
	if isValidBlock(blockContext) {
		hvmQueryMap[k] = resp
	}
	return resp, nil
}

type btcHeaderN struct{}

func (c *btcHeaderN) RequiredGas(input []byte) uint64 {
	return params.BtcHeaderN
}

func (c *btcHeaderN) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if input == nil || len(input) != 4 {
		log.Debug("btcHeaderN run called with nil or != 4 input", "input", fmt.Sprintf("%x", input))
		return nil, fmt.Errorf("btcHeaderN called with nill or != 4 input")
	}

	var k hVMQueryKey
	if isValidBlock(blockContext) {
		k, err := calculateHVMQueryKey(input, hvmContractsToAddress[reflect.TypeOf(c)][0], blockContext)
		if err != nil {
			log.Error("Unable to calculate hVM Query Key!",
				"input", fmt.Sprintf("%x", input),
				"blockContext", fmt.Sprintf("%x", blockContext))
		}
		cachedResult, exists := hvmQueryMap[k]
		if exists {
			log.Info(fmt.Sprintf("btcTxConfirmations returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	height := (uint32(input[0]&0xFF) << 24) |
		(uint32(input[1]&0xFF) << 16) |
		(uint32(input[2]&0xFF) << 8) |
		uint32(input[3]&0xFF)

	log.Debug("btcHeaderN called", "height", height)
	if TBCFullNode == nil {
		log.Crit("TBCIndexer is nil!")
	}

	headers, err := TBCFullNode.BlockHeadersByHeight(context.Background(), uint64(height))

	if err != nil || len(headers) == 0 {
		log.Warn("Unable to lookup header!", "height", height)
		return nil, nil
	}

	// TODO: Canonical check
	bestHeader := headers[0]

	hash := bestHeader.BlockHash()
	prevHash := bestHeader.PrevBlock
	merkle := bestHeader.MerkleRoot

	var hashReverse = make([]byte, 32)
	copy(hashReverse[0:32], hash[0:32])
	slices.Reverse(hashReverse)

	var prevHashReverse = make([]byte, 32)
	copy(prevHashReverse[0:32], prevHash[0:32])
	slices.Reverse(prevHashReverse)

	var merkleReverse = make([]byte, 32)
	copy(merkleReverse[0:32], merkle[0:32])
	slices.Reverse(merkleReverse)

	resp := make([]byte, 4)
	binary.BigEndian.PutUint32(resp, uint32(height))
	resp = append(resp, hashReverse[:]...)
	resp = binary.BigEndian.AppendUint32(resp, uint32(bestHeader.Version))
	resp = append(resp, prevHashReverse[:]...)
	resp = append(resp, merkleReverse[:]...)
	resp = binary.BigEndian.AppendUint32(resp, uint32(bestHeader.Timestamp.Unix()))
	resp = binary.BigEndian.AppendUint32(resp, bestHeader.Bits)
	resp = binary.BigEndian.AppendUint32(resp, bestHeader.Nonce)

	log.Debug("btcHeaderN returning data", "returnedData", fmt.Sprintf("%x", resp))
	if isValidBlock(blockContext) {
		hvmQueryMap[k] = resp
	}
	return resp, nil
}

type btcUtxosAddrList struct{}

func (c *btcUtxosAddrList) RequiredGas(input []byte) uint64 {
	return params.BtcUtxosAddrList
}

func (c *btcUtxosAddrList) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// TODO: Move to variable, check addr min length + 4 bytes
	if len(input) < 28 {
		return nil, nil
	}

	var k hVMQueryKey
	if isValidBlock(blockContext) {
		k, err := calculateHVMQueryKey(input, hvmContractsToAddress[reflect.TypeOf(c)][0], blockContext)
		if err != nil {
			log.Error("Unable to calculate hVM Query Key!",
				"input", fmt.Sprintf("%x", input),
				"blockContext", fmt.Sprintf("%x", blockContext))
		}
		cachedResult, exists := hvmQueryMap[k]
		if exists {
			log.Info(fmt.Sprintf("btcTxConfirmations returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	addrEnd := len(input) - 4
	addr := string(input)[0:addrEnd]
	pg := (uint32(input[addrEnd]&0xFF) << 16) |
		(uint32(input[addrEnd+1]&0xFF) << 8) |
		uint32(input[addrEnd+2]&0xFF)
	pgSize := uint32(input[addrEnd+3])

	if pgSize == 0 {
		pgSize = 10 // TODO review default here
	}

	log.Debug("btcUtxosAddrList run called", "addr", addr, "pg", pg, "pgSize", pgSize)

	if TBCFullNode == nil {
		log.Crit("No TBC indexer available, cannot perform hVM precompile call!")
	}

	utxos, err := TBCFullNode.UtxosByAddress(context.Background(), addr, uint64(pg), uint64(pgSize))

	if err != nil {
		log.Warn("Unable to lookup UTXOs for address!", "addr", addr)
		return nil, nil
	}

	resp := make([]byte, 1)
	resp[0] = byte(len(utxos) & 0xFF)

	for _, utxo := range utxos {
		txid := utxo.ScriptHashSlice()
		slices.Reverse(txid)
		resp = append(resp, txid...) // TODO: Rename ScriptHash/ScriptHashSlice in TBC to TxID[...]
		resp = binary.BigEndian.AppendUint16(resp, uint16(utxo.OutputIndex()))
		resp = binary.BigEndian.AppendUint64(resp, utxo.Value())
		log.Debug("btcUtxosAddrList adding output to returned data",
			"txid", fmt.Sprintf("%x", utxo.ScriptHashSlice()), "outputIndex", utxo.OutputIndex(),
			"value", utxo.Value())
	}

	log.Debug("btcUtxosAddrList returning data", "returnedData", fmt.Sprintf("%x", resp))
	if isValidBlock(blockContext) {
		hvmQueryMap[k] = resp
	}
	return resp, nil
}

type btcTxByTxid struct{}

func (c *btcTxByTxid) RequiredGas(input []byte) uint64 {
	// TODO: Gas based on returned size and/or enabled fields
	return params.BtcTxByTxid
}

func (c *btcTxByTxid) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// TODO: Move to variable
	if len(input) != 36 { // 4 bytes bitflag, 32 bytes txid. TODO: Allow 32-byte input (just TxID) and assume some default bitflag values?
		return nil, nil
	}

	var k hVMQueryKey
	if isValidBlock(blockContext) {
		k, err := calculateHVMQueryKey(input, hvmContractsToAddress[reflect.TypeOf(c)][0], blockContext)
		if err != nil {
			log.Error("Unable to calculate hVM Query Key!",
				"input", fmt.Sprintf("%x", input),
				"blockContext", fmt.Sprintf("%x", blockContext))
		}
		cachedResult, exists := hvmQueryMap[k]
		if exists {
			log.Info(fmt.Sprintf("btcTxConfirmations returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	var txid = make([]byte, 32)
	copy(txid[0:32], input[0:32])
	slices.Reverse(txid)

	bitflag1 := input[32]
	includeTxHash := bitflag1&(0x01<<7) != 0
	includeContainingBlock := bitflag1&(0x01<<6) != 0
	includeVersion := bitflag1&(0x01<<5) != 0
	includeSizes := bitflag1&(0x01<<4) != 0 // Size, vsize, weight
	includeLockTime := bitflag1&(0x01<<3) != 0
	includeInputs := bitflag1&(0x01<<2) != 0
	includeInputSource := bitflag1&(0x01<<1) != 0
	includeInputScriptSig := bitflag1&(0x01) != 0

	bitflag2 := input[33]
	includeInputSeq := bitflag2&(0x01<<7) != 0
	includeOutputs := bitflag2&(0x01<<6) != 0
	includeOutputScript := bitflag2&(0x01<<5) != 0
	includeOutputAddress := bitflag2&(0x01<<4) != 0
	includeUnspendableOutputs := bitflag2&(0x01<<3) != 0
	includeOutputSpent := bitflag2&(0x01<<2) != 0
	includeOutputSpentBy := bitflag2&(0x01<<1) != 0
	// One unused bit for future, possibly meta-protocol info like Ordinals

	bitflag3 := input[34] // Gives size limits for data which could get unexpectedly expensive to return
	// Two free bits here
	maxInputsExponent := (bitflag3 & (0x07 << 3)) >> 3 // bits xxXXXxxx used as 2^(X), b00=2^0=1, b01=2^1=2, ... up to 2^6=64 inputs
	maxOutputsExponent := bitflag3 & (0x07)            // bits xxxxxXXX used as 2^(X), b00=2^0=1, b01=2^1=2, ... up to 2^6=64 outputs

	maxInputs := 0x01 << maxInputsExponent
	maxOutputs := 0x01 << maxOutputsExponent

	bitflag4 := input[35]
	// Four free bits here
	maxInputScriptSigSizeExponent := (bitflag4 & (0x03 << 2)) >> 2 // bits xxxxXXxx used as 2^(4+X), b00=2^(4+0)=16, b01=2^(4+1)=32, ... up to 128 bytes
	maxOutputScriptSizeExponent := bitflag4 & (0x03)               // bits xxxxxxXX used as 2^(4+X), b00=2^(4+0)=16, b01=2^(4+1)=32, ... up to 128 bytes

	maxInputScriptSigSize := 0x01 << (4 + maxInputScriptSigSizeExponent)
	maxOutputScriptSize := 0x01 << (4 + maxOutputScriptSizeExponent)

	log.Debug("btcTxByTxid called", "includeTxHash", includeTxHash,
		"includeContainingBlock", includeContainingBlock, "includeVersion", includeVersion,
		"includeSizes", includeSizes, "includeLockTime", includeLockTime, "includeInputs", includeInputs,
		"includeInputSource", includeInputSource, "includeInputScriptSig", includeInputScriptSig,
		"includeInputSeq", includeInputSeq, "includeInputAddress", includeOutputs,
		"includeOutputScript", includeOutputScript, "includeOutputAddress", includeOutputAddress,
		"includeUnspendableOutputs", includeUnspendableOutputs, "includeOutputSpent", includeOutputSpent,
		"includeOutputSpentBy", includeOutputSpentBy, "maxInputsExponent", maxInputsExponent,
		"maxOutputsExponent", maxOutputsExponent, "maxInputScriptSigSizeExponent", maxInputScriptSigSizeExponent,
		"maxOutputScriptSizeExponent", maxOutputScriptSizeExponent, "maxInputs", maxInputs, "maxOutputs", maxOutputs,
		"maxInputScriptSigSize", maxInputScriptSigSize, "maxOutputScriptSize", maxOutputScriptSize)

	ch := chainhash.Hash{}
	err := ch.SetBytes(txid)
	if err != nil {
		log.Warn("Unable to lookup tx by txid; unable to convert txid %x to chainhash", "txid", txid)
	}

	tx, block, err := TBCFullNode.TxById(context.Background(), &ch)
	if err != nil || tx == nil {
		log.Error("Unable to lookup tx by txid", "txid", fmt.Sprintf("%x", txid))
		return nil, nil
	}

	resp := make([]byte, 0)

	if includeTxHash {
		// TODO: Not yet implemented
	}

	// TODO: Canonical check
	if includeContainingBlock {
		blockHash := make([]byte, 0)
		blockHash = append(blockHash, block[:]...)
		slices.Reverse(blockHash)
		resp = append(resp, blockHash...)
	}

	if includeVersion {
		resp = binary.BigEndian.AppendUint32(resp, uint32(tx.Version))
	}

	if includeSizes {
		resp = binary.BigEndian.AppendUint32(resp, uint32(tx.SerializeSize()))
		resp = binary.BigEndian.AppendUint32(resp, uint32(tx.SerializeSizeStripped()))
	}

	if includeLockTime {
		resp = binary.BigEndian.AppendUint32(resp, tx.LockTime)
	}

	if includeInputs {
		resp = binary.BigEndian.AppendUint16(resp, uint16(len(tx.TxIn)))
		for count, in := range tx.TxIn {
			if count >= maxInputs {
				// Caller needs to check # of inputs compared to claimed length to detect inputs were chopped
				break
			}
			// Always include input value - Review if this is desired behavior because of extra lookup cost
			prevIn := in.PreviousOutPoint
			pih := chainhash.Hash{}
			err := pih.SetBytes(prevIn.Hash[:])
			if err != nil {
				log.Warn("Unable to lookup Tx by Txid; unable to convert txid %x to chainhash!", "txid", txid)
				return nil, nil
			}
			sourceTx, _, err := TBCFullNode.TxById(context.Background(), &pih)

			if err != nil {
				log.Warn("unable to lookup input transaction",
					"prevInTxID", fmt.Sprintf("%x", prevIn.Hash), "prevInTxIndex", prevIn.Index)
				return nil, nil
			}
			value := sourceTx.TxOut[prevIn.Index].Value

			resp = binary.BigEndian.AppendUint64(resp, uint64(value))
			if includeInputSource {
				prevInHash := prevIn.Hash
				slices.Reverse(prevInHash[:])
				resp = append(resp, prevInHash[:]...)
				resp = binary.BigEndian.AppendUint16(resp, uint16(prevIn.Index)) // TODO: Check outputs cannot exceed 2^16-1
			}
			if includeInputScriptSig {
				choppedInputScript := make([]byte, 0)
				choppedInputScript = append(choppedInputScript, in.SignatureScript...)
				if len(choppedInputScript) > maxInputScriptSigSize {
					choppedInputScript = choppedInputScript[0:maxInputScriptSigSize]
				}
				resp = binary.BigEndian.AppendUint16(resp, uint16(len(in.SignatureScript)))
				resp = append(resp, choppedInputScript...)
			}
			//
			// TODO: respect max inputs setting
			if includeInputSeq {
				resp = binary.BigEndian.AppendUint32(resp, in.Sequence)
			}
		}
	}

	if includeOutputs {
		var unspendable int
		for _, out := range tx.TxOut {
			if txscript.IsUnspendable(out.PkScript) {
				unspendable++
			}
		}

		outLen := len(tx.TxOut)
		if !includeUnspendableOutputs {
			outLen -= unspendable
		}

		count := 0
		resp = binary.BigEndian.AppendUint16(resp, uint16(outLen))
		for idx, out := range tx.TxOut {
			if count >= maxOutputs {
				// Caller needs to check # of outputs compared to claimed length to detect outputs were chopped
				break
			}
			unspendable := txscript.IsUnspendable(out.PkScript)
			if unspendable && !includeUnspendableOutputs {
				continue
			}
			resp = binary.BigEndian.AppendUint64(resp, uint64(out.Value))
			if includeOutputScript {
				choppedOutputScript := make([]byte, 0)
				choppedOutputScript = append(choppedOutputScript, out.PkScript...)
				if len(choppedOutputScript) > maxOutputScriptSize {
					choppedOutputScript = choppedOutputScript[0:maxOutputScriptSize]
				}
				resp = binary.BigEndian.AppendUint16(resp, uint16(len(out.PkScript)))
				resp = append(resp, choppedOutputScript...)
			}
			if includeOutputAddress {
				// TODO
				// addrBytes := []byte(*out.)
				// resp = append(resp, byte(len(addrBytes)))
				// resp = append(resp, addrBytes...) // TODO: right now this is just ASCII->Bytes, consider changing to Base58 decode? Could be flag option
			}
			if includeOutputSpent {
				spentBool, err := TBCFullNode.ScriptHashAvailableToSpend(context.Background(), &ch, uint32(idx))

				if err != nil {
					log.Warn("Unable to lookup output spend status", "txid", txid)
					return nil, nil
				}

				spent := byte(0)
				if spentBool {
					// Could not look up Outpoint in UTXO table, therefore spent
					spent = byte(1)
				}

				resp = append(resp, spent)
				if includeOutputSpentBy {
					// If not spent, do not include spender TxID
					if spent == 1 {
						// TODO
						// TxID then input index
						// resp = append(resp, out.SpendTx...)
						// resp = binary.BigEndian.AppendUint16(resp, uint16(out.SpendIndex))
					}
				}
			}
			count++
		}
	}

	log.Debug("btcTxByTxid returning data", "returnedData", fmt.Sprintf("%x", resp))
	if isValidBlock(blockContext) {
		hvmQueryMap[k] = resp
	}
	return resp, nil
}

// ECRECOVER implemented as a native contract.
type ecrecover struct{}

func (c *ecrecover) RequiredGas(input []byte) uint64 {
	return params.EcrecoverGas
}

func (c *ecrecover) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	const ecRecoverInputLength = 128

	input = common.RightPadBytes(input, ecRecoverInputLength)
	// "input" is (hash, v, r, s), each 32 bytes
	// but for ecrecover we want (r, s, v)

	r := new(big.Int).SetBytes(input[64:96])
	s := new(big.Int).SetBytes(input[96:128])
	v := input[63] - 27

	// tighter sig s values input homestead only apply to tx sigs
	if !allZero(input[32:63]) || !crypto.ValidateSignatureValues(v, r, s, false) {
		return nil, nil
	}
	// We must make sure not to modify the 'input', so placing the 'v' along with
	// the signature needs to be done on a new allocation
	sig := make([]byte, 65)
	copy(sig, input[64:128])
	sig[64] = v
	// v needs to be at the end for libsecp256k1
	pubKey, err := crypto.Ecrecover(input[:32], sig)
	// make sure the public key is a valid one
	if err != nil {
		return nil, nil
	}

	// the first byte of pubkey is bitcoin heritage
	return common.LeftPadBytes(crypto.Keccak256(pubKey[1:])[12:], 32), nil
}

// SHA256 implemented as a native contract.
type sha256hash struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
//
// This method does not require any overflow checking as the input size gas costs
// required for anything significant is so high it's impossible to pay for.
func (c *sha256hash) RequiredGas(input []byte) uint64 {
	return uint64(len(input)+31)/32*params.Sha256PerWordGas + params.Sha256BaseGas
}
func (c *sha256hash) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	h := sha256.Sum256(input)
	return h[:], nil
}

// RIPEMD160 implemented as a native contract.
type ripemd160hash struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
//
// This method does not require any overflow checking as the input size gas costs
// required for anything significant is so high it's impossible to pay for.
func (c *ripemd160hash) RequiredGas(input []byte) uint64 {
	return uint64(len(input)+31)/32*params.Ripemd160PerWordGas + params.Ripemd160BaseGas
}
func (c *ripemd160hash) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	ripemd := ripemd160.New()
	ripemd.Write(input)
	return common.LeftPadBytes(ripemd.Sum(nil), 32), nil
}

// data copy implemented as a native contract.
type dataCopy struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
//
// This method does not require any overflow checking as the input size gas costs
// required for anything significant is so high it's impossible to pay for.
func (c *dataCopy) RequiredGas(input []byte) uint64 {
	return uint64(len(input)+31)/32*params.IdentityPerWordGas + params.IdentityBaseGas
}
func (c *dataCopy) Run(in []byte, blockContext common.Hash) ([]byte, error) {
	return common.CopyBytes(in), nil
}

// bigModExp implements a native big integer exponential modular operation.
type bigModExp struct {
	eip2565 bool
}

var (
	big1      = big.NewInt(1)
	big3      = big.NewInt(3)
	big4      = big.NewInt(4)
	big7      = big.NewInt(7)
	big8      = big.NewInt(8)
	big16     = big.NewInt(16)
	big20     = big.NewInt(20)
	big32     = big.NewInt(32)
	big64     = big.NewInt(64)
	big96     = big.NewInt(96)
	big480    = big.NewInt(480)
	big1024   = big.NewInt(1024)
	big3072   = big.NewInt(3072)
	big199680 = big.NewInt(199680)
)

// modexpMultComplexity implements bigModexp multComplexity formula, as defined in EIP-198
//
//	def mult_complexity(x):
//		if x <= 64: return x ** 2
//		elif x <= 1024: return x ** 2 // 4 + 96 * x - 3072
//		else: return x ** 2 // 16 + 480 * x - 199680
//
// where is x is max(length_of_MODULUS, length_of_BASE)
func modexpMultComplexity(x *big.Int) *big.Int {
	switch {
	case x.Cmp(big64) <= 0:
		x.Mul(x, x) // x ** 2
	case x.Cmp(big1024) <= 0:
		// (x ** 2 // 4 ) + ( 96 * x - 3072)
		x = new(big.Int).Add(
			new(big.Int).Div(new(big.Int).Mul(x, x), big4),
			new(big.Int).Sub(new(big.Int).Mul(big96, x), big3072),
		)
	default:
		// (x ** 2 // 16) + (480 * x - 199680)
		x = new(big.Int).Add(
			new(big.Int).Div(new(big.Int).Mul(x, x), big16),
			new(big.Int).Sub(new(big.Int).Mul(big480, x), big199680),
		)
	}
	return x
}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bigModExp) RequiredGas(input []byte) uint64 {
	var (
		baseLen = new(big.Int).SetBytes(getData(input, 0, 32))
		expLen  = new(big.Int).SetBytes(getData(input, 32, 32))
		modLen  = new(big.Int).SetBytes(getData(input, 64, 32))
	)
	if len(input) > 96 {
		input = input[96:]
	} else {
		input = input[:0]
	}
	// Retrieve the head 32 bytes of exp for the adjusted exponent length
	var expHead *big.Int
	if big.NewInt(int64(len(input))).Cmp(baseLen) <= 0 {
		expHead = new(big.Int)
	} else {
		if expLen.Cmp(big32) > 0 {
			expHead = new(big.Int).SetBytes(getData(input, baseLen.Uint64(), 32))
		} else {
			expHead = new(big.Int).SetBytes(getData(input, baseLen.Uint64(), expLen.Uint64()))
		}
	}
	// Calculate the adjusted exponent length
	var msb int
	if bitlen := expHead.BitLen(); bitlen > 0 {
		msb = bitlen - 1
	}
	adjExpLen := new(big.Int)
	if expLen.Cmp(big32) > 0 {
		adjExpLen.Sub(expLen, big32)
		adjExpLen.Mul(big8, adjExpLen)
	}
	adjExpLen.Add(adjExpLen, big.NewInt(int64(msb)))
	// Calculate the gas cost of the operation
	gas := new(big.Int).Set(math.BigMax(modLen, baseLen))
	if c.eip2565 {
		// EIP-2565 has three changes
		// 1. Different multComplexity (inlined here)
		// in EIP-2565 (https://eips.ethereum.org/EIPS/eip-2565):
		//
		// def mult_complexity(x):
		//    ceiling(x/8)^2
		//
		//where is x is max(length_of_MODULUS, length_of_BASE)
		gas = gas.Add(gas, big7)
		gas = gas.Div(gas, big8)
		gas.Mul(gas, gas)

		gas.Mul(gas, math.BigMax(adjExpLen, big1))
		// 2. Different divisor (`GQUADDIVISOR`) (3)
		gas.Div(gas, big3)
		if gas.BitLen() > 64 {
			return math.MaxUint64
		}
		// 3. Minimum price of 200 gas
		if gas.Uint64() < 200 {
			return 200
		}
		return gas.Uint64()
	}
	gas = modexpMultComplexity(gas)
	gas.Mul(gas, math.BigMax(adjExpLen, big1))
	gas.Div(gas, big20)

	if gas.BitLen() > 64 {
		return math.MaxUint64
	}
	return gas.Uint64()
}

func (c *bigModExp) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	var (
		baseLen = new(big.Int).SetBytes(getData(input, 0, 32)).Uint64()
		expLen  = new(big.Int).SetBytes(getData(input, 32, 32)).Uint64()
		modLen  = new(big.Int).SetBytes(getData(input, 64, 32)).Uint64()
	)
	if len(input) > 96 {
		input = input[96:]
	} else {
		input = input[:0]
	}
	// Handle a special case when both the base and mod length is zero
	if baseLen == 0 && modLen == 0 {
		return []byte{}, nil
	}
	// Retrieve the operands and execute the exponentiation
	var (
		base = new(big.Int).SetBytes(getData(input, 0, baseLen))
		exp  = new(big.Int).SetBytes(getData(input, baseLen, expLen))
		mod  = new(big.Int).SetBytes(getData(input, baseLen+expLen, modLen))
		v    []byte
	)
	switch {
	case mod.BitLen() == 0:
		// Modulo 0 is undefined, return zero
		return common.LeftPadBytes([]byte{}, int(modLen)), nil
	case base.BitLen() == 1: // a bit length of 1 means it's 1 (or -1).
		//If base == 1, then we can just return base % mod (if mod >= 1, which it is)
		v = base.Mod(base, mod).Bytes()
	default:
		v = base.Exp(base, exp, mod).Bytes()
	}
	return common.LeftPadBytes(v, int(modLen)), nil
}

// newCurvePoint unmarshals a binary blob into a bn256 elliptic curve point,
// returning it, or an error if the point is invalid.
func newCurvePoint(blob []byte) (*bn256.G1, error) {
	p := new(bn256.G1)
	if _, err := p.Unmarshal(blob); err != nil {
		return nil, err
	}
	return p, nil
}

// newTwistPoint unmarshals a binary blob into a bn256 elliptic curve point,
// returning it, or an error if the point is invalid.
func newTwistPoint(blob []byte) (*bn256.G2, error) {
	p := new(bn256.G2)
	if _, err := p.Unmarshal(blob); err != nil {
		return nil, err
	}
	return p, nil
}

// runBn256Add implements the Bn256Add precompile, referenced by both
// Byzantium and Istanbul operations.
func runBn256Add(input []byte) ([]byte, error) {
	x, err := newCurvePoint(getData(input, 0, 64))
	if err != nil {
		return nil, err
	}
	y, err := newCurvePoint(getData(input, 64, 64))
	if err != nil {
		return nil, err
	}
	res := new(bn256.G1)
	res.Add(x, y)
	return res.Marshal(), nil
}

// bn256Add implements a native elliptic curve point addition conforming to
// Istanbul consensus rules.
type bn256AddIstanbul struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bn256AddIstanbul) RequiredGas(input []byte) uint64 {
	return params.Bn256AddGasIstanbul
}

func (c *bn256AddIstanbul) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	return runBn256Add(input)
}

// bn256AddByzantium implements a native elliptic curve point addition
// conforming to Byzantium consensus rules.
type bn256AddByzantium struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bn256AddByzantium) RequiredGas(input []byte) uint64 {
	return params.Bn256AddGasByzantium
}

func (c *bn256AddByzantium) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	return runBn256Add(input)
}

// runBn256ScalarMul implements the Bn256ScalarMul precompile, referenced by
// both Byzantium and Istanbul operations.
func runBn256ScalarMul(input []byte) ([]byte, error) {
	p, err := newCurvePoint(getData(input, 0, 64))
	if err != nil {
		return nil, err
	}
	res := new(bn256.G1)
	res.ScalarMult(p, new(big.Int).SetBytes(getData(input, 64, 32)))
	return res.Marshal(), nil
}

// bn256ScalarMulIstanbul implements a native elliptic curve scalar
// multiplication conforming to Istanbul consensus rules.
type bn256ScalarMulIstanbul struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bn256ScalarMulIstanbul) RequiredGas(input []byte) uint64 {
	return params.Bn256ScalarMulGasIstanbul
}

func (c *bn256ScalarMulIstanbul) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	return runBn256ScalarMul(input)
}

// bn256ScalarMulByzantium implements a native elliptic curve scalar
// multiplication conforming to Byzantium consensus rules.
type bn256ScalarMulByzantium struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bn256ScalarMulByzantium) RequiredGas(input []byte) uint64 {
	return params.Bn256ScalarMulGasByzantium
}

func (c *bn256ScalarMulByzantium) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	return runBn256ScalarMul(input)
}

var (
	// true32Byte is returned if the bn256 pairing check succeeds.
	true32Byte = []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1}

	// false32Byte is returned if the bn256 pairing check fails.
	false32Byte = make([]byte, 32)

	// errBadPairingInput is returned if the bn256 pairing input is invalid.
	errBadPairingInput = errors.New("bad elliptic curve pairing size")
)

// runBn256Pairing implements the Bn256Pairing precompile, referenced by both
// Byzantium and Istanbul operations.
func runBn256Pairing(input []byte) ([]byte, error) {
	// Handle some corner cases cheaply
	if len(input)%192 > 0 {
		return nil, errBadPairingInput
	}
	// Convert the input into a set of coordinates
	var (
		cs []*bn256.G1
		ts []*bn256.G2
	)
	for i := 0; i < len(input); i += 192 {
		c, err := newCurvePoint(input[i : i+64])
		if err != nil {
			return nil, err
		}
		t, err := newTwistPoint(input[i+64 : i+192])
		if err != nil {
			return nil, err
		}
		cs = append(cs, c)
		ts = append(ts, t)
	}
	// Execute the pairing checks and return the results
	if bn256.PairingCheck(cs, ts) {
		return true32Byte, nil
	}
	return false32Byte, nil
}

// bn256PairingIstanbul implements a pairing pre-compile for the bn256 curve
// conforming to Istanbul consensus rules.
type bn256PairingIstanbul struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bn256PairingIstanbul) RequiredGas(input []byte) uint64 {
	return params.Bn256PairingBaseGasIstanbul + uint64(len(input)/192)*params.Bn256PairingPerPointGasIstanbul
}

func (c *bn256PairingIstanbul) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	return runBn256Pairing(input)
}

// bn256PairingByzantium implements a pairing pre-compile for the bn256 curve
// conforming to Byzantium consensus rules.
type bn256PairingByzantium struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bn256PairingByzantium) RequiredGas(input []byte) uint64 {
	return params.Bn256PairingBaseGasByzantium + uint64(len(input)/192)*params.Bn256PairingPerPointGasByzantium
}

func (c *bn256PairingByzantium) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	return runBn256Pairing(input)
}

type blake2F struct{}

func (c *blake2F) RequiredGas(input []byte) uint64 {
	// If the input is malformed, we can't calculate the gas, return 0 and let the
	// actual call choke and fault.
	if len(input) != blake2FInputLength {
		return 0
	}
	return uint64(binary.BigEndian.Uint32(input[0:4]))
}

const (
	blake2FInputLength        = 213
	blake2FFinalBlockBytes    = byte(1)
	blake2FNonFinalBlockBytes = byte(0)
)

var (
	errBlake2FInvalidInputLength = errors.New("invalid input length")
	errBlake2FInvalidFinalFlag   = errors.New("invalid final flag")
)

func (c *blake2F) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Make sure the input is valid (correct length and final flag)
	if len(input) != blake2FInputLength {
		return nil, errBlake2FInvalidInputLength
	}
	if input[212] != blake2FNonFinalBlockBytes && input[212] != blake2FFinalBlockBytes {
		return nil, errBlake2FInvalidFinalFlag
	}
	// Parse the input into the Blake2b call parameters
	var (
		rounds = binary.BigEndian.Uint32(input[0:4])
		final  = input[212] == blake2FFinalBlockBytes

		h [8]uint64
		m [16]uint64
		t [2]uint64
	)
	for i := 0; i < 8; i++ {
		offset := 4 + i*8
		h[i] = binary.LittleEndian.Uint64(input[offset : offset+8])
	}
	for i := 0; i < 16; i++ {
		offset := 68 + i*8
		m[i] = binary.LittleEndian.Uint64(input[offset : offset+8])
	}
	t[0] = binary.LittleEndian.Uint64(input[196:204])
	t[1] = binary.LittleEndian.Uint64(input[204:212])

	// Execute the compression function, extract and return the result
	blake2b.F(&h, m, t, final, rounds)

	output := make([]byte, 64)
	for i := 0; i < 8; i++ {
		offset := i * 8
		binary.LittleEndian.PutUint64(output[offset:offset+8], h[i])
	}
	return output, nil
}

var (
	errBLS12381InvalidInputLength          = errors.New("invalid input length")
	errBLS12381InvalidFieldElementTopBytes = errors.New("invalid field element top bytes")
	errBLS12381G1PointSubgroup             = errors.New("g1 point is not on correct subgroup")
	errBLS12381G2PointSubgroup             = errors.New("g2 point is not on correct subgroup")
)

// bls12381G1Add implements EIP-2537 G1Add precompile.
type bls12381G1Add struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381G1Add) RequiredGas(input []byte) uint64 {
	return params.Bls12381G1AddGas
}

func (c *bls12381G1Add) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 G1Add precompile.
	// > G1 addition call expects `256` bytes as an input that is interpreted as byte concatenation of two G1 points (`128` bytes each).
	// > Output is an encoding of addition operation result - single G1 point (`128` bytes).
	if len(input) != 256 {
		return nil, errBLS12381InvalidInputLength
	}
	var err error
	var p0, p1 *bls12381.PointG1

	// Initialize G1
	g := bls12381.NewG1()

	// Decode G1 point p_0
	if p0, err = g.DecodePoint(input[:128]); err != nil {
		return nil, err
	}
	// Decode G1 point p_1
	if p1, err = g.DecodePoint(input[128:]); err != nil {
		return nil, err
	}

	// Compute r = p_0 + p_1
	r := g.New()
	g.Add(r, p0, p1)

	// Encode the G1 point result into 128 bytes
	return g.EncodePoint(r), nil
}

// bls12381G1Mul implements EIP-2537 G1Mul precompile.
type bls12381G1Mul struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381G1Mul) RequiredGas(input []byte) uint64 {
	return params.Bls12381G1MulGas
}

func (c *bls12381G1Mul) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 G1Mul precompile.
	// > G1 multiplication call expects `160` bytes as an input that is interpreted as byte concatenation of encoding of G1 point (`128` bytes) and encoding of a scalar value (`32` bytes).
	// > Output is an encoding of multiplication operation result - single G1 point (`128` bytes).
	if len(input) != 160 {
		return nil, errBLS12381InvalidInputLength
	}
	var err error
	var p0 *bls12381.PointG1

	// Initialize G1
	g := bls12381.NewG1()

	// Decode G1 point
	if p0, err = g.DecodePoint(input[:128]); err != nil {
		return nil, err
	}
	// Decode scalar value
	e := new(big.Int).SetBytes(input[128:])

	// Compute r = e * p_0
	r := g.New()
	g.MulScalar(r, p0, e)

	// Encode the G1 point into 128 bytes
	return g.EncodePoint(r), nil
}

// bls12381G1MultiExp implements EIP-2537 G1MultiExp precompile.
type bls12381G1MultiExp struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381G1MultiExp) RequiredGas(input []byte) uint64 {
	// Calculate G1 point, scalar value pair length
	k := len(input) / 160
	if k == 0 {
		// Return 0 gas for small input length
		return 0
	}
	// Lookup discount value for G1 point, scalar value pair length
	var discount uint64
	if dLen := len(params.Bls12381MultiExpDiscountTable); k < dLen {
		discount = params.Bls12381MultiExpDiscountTable[k-1]
	} else {
		discount = params.Bls12381MultiExpDiscountTable[dLen-1]
	}
	// Calculate gas and return the result
	return (uint64(k) * params.Bls12381G1MulGas * discount) / 1000
}

func (c *bls12381G1MultiExp) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 G1MultiExp precompile.
	// G1 multiplication call expects `160*k` bytes as an input that is interpreted as byte concatenation of `k` slices each of them being a byte concatenation of encoding of G1 point (`128` bytes) and encoding of a scalar value (`32` bytes).
	// Output is an encoding of multiexponentiation operation result - single G1 point (`128` bytes).
	k := len(input) / 160
	if len(input) == 0 || len(input)%160 != 0 {
		return nil, errBLS12381InvalidInputLength
	}
	var err error
	points := make([]*bls12381.PointG1, k)
	scalars := make([]*big.Int, k)

	// Initialize G1
	g := bls12381.NewG1()

	// Decode point scalar pairs
	for i := 0; i < k; i++ {
		off := 160 * i
		t0, t1, t2 := off, off+128, off+160
		// Decode G1 point
		if points[i], err = g.DecodePoint(input[t0:t1]); err != nil {
			return nil, err
		}
		// Decode scalar value
		scalars[i] = new(big.Int).SetBytes(input[t1:t2])
	}

	// Compute r = e_0 * p_0 + e_1 * p_1 + ... + e_(k-1) * p_(k-1)
	r := g.New()
	g.MultiExp(r, points, scalars)

	// Encode the G1 point to 128 bytes
	return g.EncodePoint(r), nil
}

// bls12381G2Add implements EIP-2537 G2Add precompile.
type bls12381G2Add struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381G2Add) RequiredGas(input []byte) uint64 {
	return params.Bls12381G2AddGas
}

func (c *bls12381G2Add) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 G2Add precompile.
	// > G2 addition call expects `512` bytes as an input that is interpreted as byte concatenation of two G2 points (`256` bytes each).
	// > Output is an encoding of addition operation result - single G2 point (`256` bytes).
	if len(input) != 512 {
		return nil, errBLS12381InvalidInputLength
	}
	var err error
	var p0, p1 *bls12381.PointG2

	// Initialize G2
	g := bls12381.NewG2()
	r := g.New()

	// Decode G2 point p_0
	if p0, err = g.DecodePoint(input[:256]); err != nil {
		return nil, err
	}
	// Decode G2 point p_1
	if p1, err = g.DecodePoint(input[256:]); err != nil {
		return nil, err
	}

	// Compute r = p_0 + p_1
	g.Add(r, p0, p1)

	// Encode the G2 point into 256 bytes
	return g.EncodePoint(r), nil
}

// bls12381G2Mul implements EIP-2537 G2Mul precompile.
type bls12381G2Mul struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381G2Mul) RequiredGas(input []byte) uint64 {
	return params.Bls12381G2MulGas
}

func (c *bls12381G2Mul) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 G2MUL precompile logic.
	// > G2 multiplication call expects `288` bytes as an input that is interpreted as byte concatenation of encoding of G2 point (`256` bytes) and encoding of a scalar value (`32` bytes).
	// > Output is an encoding of multiplication operation result - single G2 point (`256` bytes).
	if len(input) != 288 {
		return nil, errBLS12381InvalidInputLength
	}
	var err error
	var p0 *bls12381.PointG2

	// Initialize G2
	g := bls12381.NewG2()

	// Decode G2 point
	if p0, err = g.DecodePoint(input[:256]); err != nil {
		return nil, err
	}
	// Decode scalar value
	e := new(big.Int).SetBytes(input[256:])

	// Compute r = e * p_0
	r := g.New()
	g.MulScalar(r, p0, e)

	// Encode the G2 point into 256 bytes
	return g.EncodePoint(r), nil
}

// bls12381G2MultiExp implements EIP-2537 G2MultiExp precompile.
type bls12381G2MultiExp struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381G2MultiExp) RequiredGas(input []byte) uint64 {
	// Calculate G2 point, scalar value pair length
	k := len(input) / 288
	if k == 0 {
		// Return 0 gas for small input length
		return 0
	}
	// Lookup discount value for G2 point, scalar value pair length
	var discount uint64
	if dLen := len(params.Bls12381MultiExpDiscountTable); k < dLen {
		discount = params.Bls12381MultiExpDiscountTable[k-1]
	} else {
		discount = params.Bls12381MultiExpDiscountTable[dLen-1]
	}
	// Calculate gas and return the result
	return (uint64(k) * params.Bls12381G2MulGas * discount) / 1000
}

func (c *bls12381G2MultiExp) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 G2MultiExp precompile logic
	// > G2 multiplication call expects `288*k` bytes as an input that is interpreted as byte concatenation of `k` slices each of them being a byte concatenation of encoding of G2 point (`256` bytes) and encoding of a scalar value (`32` bytes).
	// > Output is an encoding of multiexponentiation operation result - single G2 point (`256` bytes).
	k := len(input) / 288
	if len(input) == 0 || len(input)%288 != 0 {
		return nil, errBLS12381InvalidInputLength
	}
	var err error
	points := make([]*bls12381.PointG2, k)
	scalars := make([]*big.Int, k)

	// Initialize G2
	g := bls12381.NewG2()

	// Decode point scalar pairs
	for i := 0; i < k; i++ {
		off := 288 * i
		t0, t1, t2 := off, off+256, off+288
		// Decode G1 point
		if points[i], err = g.DecodePoint(input[t0:t1]); err != nil {
			return nil, err
		}
		// Decode scalar value
		scalars[i] = new(big.Int).SetBytes(input[t1:t2])
	}

	// Compute r = e_0 * p_0 + e_1 * p_1 + ... + e_(k-1) * p_(k-1)
	r := g.New()
	g.MultiExp(r, points, scalars)

	// Encode the G2 point to 256 bytes.
	return g.EncodePoint(r), nil
}

// bls12381Pairing implements EIP-2537 Pairing precompile.
type bls12381Pairing struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381Pairing) RequiredGas(input []byte) uint64 {
	return params.Bls12381PairingBaseGas + uint64(len(input)/384)*params.Bls12381PairingPerPairGas
}

func (c *bls12381Pairing) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 Pairing precompile logic.
	// > Pairing call expects `384*k` bytes as an inputs that is interpreted as byte concatenation of `k` slices. Each slice has the following structure:
	// > - `128` bytes of G1 point encoding
	// > - `256` bytes of G2 point encoding
	// > Output is a `32` bytes where last single byte is `0x01` if pairing result is equal to multiplicative identity in a pairing target field and `0x00` otherwise
	// > (which is equivalent of Big Endian encoding of Solidity values `uint256(1)` and `uin256(0)` respectively).
	k := len(input) / 384
	if len(input) == 0 || len(input)%384 != 0 {
		return nil, errBLS12381InvalidInputLength
	}

	// Initialize BLS12-381 pairing engine
	e := bls12381.NewPairingEngine()
	g1, g2 := e.G1, e.G2

	// Decode pairs
	for i := 0; i < k; i++ {
		off := 384 * i
		t0, t1, t2 := off, off+128, off+384

		// Decode G1 point
		p1, err := g1.DecodePoint(input[t0:t1])
		if err != nil {
			return nil, err
		}
		// Decode G2 point
		p2, err := g2.DecodePoint(input[t1:t2])
		if err != nil {
			return nil, err
		}

		// 'point is on curve' check already done,
		// Here we need to apply subgroup checks.
		if !g1.InCorrectSubgroup(p1) {
			return nil, errBLS12381G1PointSubgroup
		}
		if !g2.InCorrectSubgroup(p2) {
			return nil, errBLS12381G2PointSubgroup
		}

		// Update pairing engine with G1 and G2 points
		e.AddPair(p1, p2)
	}
	// Prepare 32 byte output
	out := make([]byte, 32)

	// Compute pairing and set the result
	if e.Check() {
		out[31] = 1
	}
	return out, nil
}

// decodeBLS12381FieldElement decodes BLS12-381 elliptic curve field element.
// Removes top 16 bytes of 64 byte input.
func decodeBLS12381FieldElement(in []byte) ([]byte, error) {
	if len(in) != 64 {
		return nil, errors.New("invalid field element length")
	}
	// check top bytes
	for i := 0; i < 16; i++ {
		if in[i] != byte(0x00) {
			return nil, errBLS12381InvalidFieldElementTopBytes
		}
	}
	out := make([]byte, 48)
	copy(out[:], in[16:])
	return out, nil
}

// bls12381MapG1 implements EIP-2537 MapG1 precompile.
type bls12381MapG1 struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381MapG1) RequiredGas(input []byte) uint64 {
	return params.Bls12381MapG1Gas
}

func (c *bls12381MapG1) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 Map_To_G1 precompile.
	// > Field-to-curve call expects `64` bytes an an input that is interpreted as a an element of the base field.
	// > Output of this call is `128` bytes and is G1 point following respective encoding rules.
	if len(input) != 64 {
		return nil, errBLS12381InvalidInputLength
	}

	// Decode input field element
	fe, err := decodeBLS12381FieldElement(input)
	if err != nil {
		return nil, err
	}

	// Initialize G1
	g := bls12381.NewG1()

	// Compute mapping
	r, err := g.MapToCurve(fe)
	if err != nil {
		return nil, err
	}

	// Encode the G1 point to 128 bytes
	return g.EncodePoint(r), nil
}

// bls12381MapG2 implements EIP-2537 MapG2 precompile.
type bls12381MapG2 struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381MapG2) RequiredGas(input []byte) uint64 {
	return params.Bls12381MapG2Gas
}

func (c *bls12381MapG2) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 Map_FP2_TO_G2 precompile logic.
	// > Field-to-curve call expects `128` bytes an an input that is interpreted as a an element of the quadratic extension field.
	// > Output of this call is `256` bytes and is G2 point following respective encoding rules.
	if len(input) != 128 {
		return nil, errBLS12381InvalidInputLength
	}

	// Decode input field element
	fe := make([]byte, 96)
	c0, err := decodeBLS12381FieldElement(input[:64])
	if err != nil {
		return nil, err
	}
	copy(fe[48:], c0)
	c1, err := decodeBLS12381FieldElement(input[64:])
	if err != nil {
		return nil, err
	}
	copy(fe[:48], c1)

	// Initialize G2
	g := bls12381.NewG2()

	// Compute mapping
	r, err := g.MapToCurve(fe)
	if err != nil {
		return nil, err
	}

	// Encode the G2 point to 256 bytes
	return g.EncodePoint(r), nil
}

// kzgPointEvaluation implements the EIP-4844 point evaluation precompile.
type kzgPointEvaluation struct{}

// RequiredGas estimates the gas required for running the point evaluation precompile.
func (b *kzgPointEvaluation) RequiredGas(input []byte) uint64 {
	return params.BlobTxPointEvaluationPrecompileGas
}

const (
	blobVerifyInputLength           = 192  // Max input length for the point evaluation precompile.
	blobCommitmentVersionKZG  uint8 = 0x01 // Version byte for the point evaluation precompile.
	blobPrecompileReturnValue       = "000000000000000000000000000000000000000000000000000000000000100073eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"
)

var (
	errBlobVerifyInvalidInputLength = errors.New("invalid input length")
	errBlobVerifyMismatchedVersion  = errors.New("mismatched versioned hash")
	errBlobVerifyKZGProof           = errors.New("error verifying kzg proof")
)

// Run executes the point evaluation precompile.
func (b *kzgPointEvaluation) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) != blobVerifyInputLength {
		return nil, errBlobVerifyInvalidInputLength
	}
	// versioned hash: first 32 bytes
	var versionedHash common.Hash
	copy(versionedHash[:], input[:])

	var (
		point kzg4844.Point
		claim kzg4844.Claim
	)
	// Evaluation point: next 32 bytes
	copy(point[:], input[32:])
	// Expected output: next 32 bytes
	copy(claim[:], input[64:])

	// input kzg point: next 48 bytes
	var commitment kzg4844.Commitment
	copy(commitment[:], input[96:])
	if kZGToVersionedHash(commitment) != versionedHash {
		return nil, errBlobVerifyMismatchedVersion
	}

	// Proof: next 48 bytes
	var proof kzg4844.Proof
	copy(proof[:], input[144:])

	if err := kzg4844.VerifyProof(commitment, point, claim, proof); err != nil {
		return nil, fmt.Errorf("%w: %v", errBlobVerifyKZGProof, err)
	}

	return common.Hex2Bytes(blobPrecompileReturnValue), nil
}

// kZGToVersionedHash implements kzg_to_versioned_hash from EIP-4844
func kZGToVersionedHash(kzg kzg4844.Commitment) common.Hash {
	h := sha256.Sum256(kzg[:])
	h[0] = blobCommitmentVersionKZG

	return h
}
