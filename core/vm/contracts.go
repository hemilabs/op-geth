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
	"maps"
	"math"
	"math/big"
	"math/bits"
	"os"
	"reflect"
	"sync"
	"time"

	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/wire"
	"github.com/hemilabs/heminetwork/database"
	"github.com/holiman/uint256"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/txscript"
	"github.com/consensys/gnark-crypto/ecc"
	bls12381 "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fp"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	patched_big "github.com/ethereum/go-bigmodexpfix/src/math/big"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/bitutil"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/crypto/blake2b"
	"github.com/ethereum/go-ethereum/crypto/bn256"
	"github.com/ethereum/go-ethereum/crypto/kzg4844"
	"github.com/ethereum/go-ethereum/crypto/secp256r1"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
	"github.com/hemilabs/heminetwork/service/tbc"
	"golang.org/x/crypto/ripemd160"
	"golang.org/x/exp/slices"
)

const (
	MIN_BTC_ADDRESS_LENGTH = 24
	BTC_TXID_LENGTH_BYTES  = 32

	btcBalAddrAddr           = byte(0x40)
	btcUtxosAddrListAddr     = byte(0x41)
	btcTxByTxidAddr          = byte(0x42)
	btcTxConfirmationsAddr   = byte(0x43)
	btcLastHeaderAddr        = byte(0x44)
	btcHeaderNAddr           = byte(0x45)
	btcAddrToScriptAddr      = byte(0x46)
	btcInputByTxidAddr       = byte(0x47)
	btcOutputByTxidAddr      = byte(0x48)
	btcTxGetInputWitnessAddr = byte(0x49)
)

func isHvmPrecompileCall(precompile common.Address) bool {
	return slices.Contains([]common.Address{
		common.BytesToAddress([]byte{btcBalAddrAddr}),
		common.BytesToAddress([]byte{btcUtxosAddrListAddr}),
		common.BytesToAddress([]byte{btcTxByTxidAddr}),
		common.BytesToAddress([]byte{btcTxConfirmationsAddr}),
		common.BytesToAddress([]byte{btcLastHeaderAddr}),
		common.BytesToAddress([]byte{btcHeaderNAddr}),
		common.BytesToAddress([]byte{btcAddrToScriptAddr}),
		common.BytesToAddress([]byte{btcInputByTxidAddr}),
		common.BytesToAddress([]byte{btcOutputByTxidAddr}),
		common.BytesToAddress([]byte{btcTxGetInputWitnessAddr}),
	}, precompile)
}

// PrecompiledContract is the basic interface for native Go contracts. The implementation
// requires a deterministic gas count based on the input size of the Run method of the
// contract.
type PrecompiledContract interface {
	RequiredGas(input []byte) uint64 // RequiredPrice calculates the contract gas use
	// Run includes a blockContext so that hVM calls can be attributed correctly to their containing block (or lack thereof)
	Run(input []byte, blockContext common.Hash) ([]byte, error) // Run runs the precompiled contract
	Name() string
}

type hVMQueryKey [32]byte

var TBCFullNodeConfig *tbc.Config
var TBCFullNodeCtxCancel context.CancelFunc

var TBCFullNode *tbc.Server
var tbcChainParams *chaincfg.Params

var TBCUpstreamTip *wire.BlockHeader

// TODO: Refactor all exported TBC methods to always use this context instead of allowing one to be passed in?
var MainCtx context.Context

// TODO: Eventually store this on-disk so old transaction execution can be simulated if required.
// Does not affect transaction execution validity, only useful for performance improvements on repeated calls
// and re-computation of hVM calls in historical transactions in already processed blocks.
var hvmQueryMap = make(map[hVMQueryKey][]byte)

var HvmNullBlockHash = make([]byte, 32)

// Clayton note: update me
func ZKMode() bool {
	return zkMode()
}

func zkMode() bool {
	return os.Getenv("TMP_ZKMODE") == "true"
}

func GetTBCFullNodeSyncStatus() *tbc.SyncInfo {
	syncInfo := TBCFullNode.Synced(MainCtx)
	return &syncInfo
}

// TODO: Better way to shut down current TBC instance and start up a new one without hard-coded waiting times
func RestartTBCFullNode(ctx context.Context) error {
	TBCFullNodeCtxCancel()
	time.Sleep(5000 * time.Millisecond)
	err := SetupTBCFullNode(ctx, TBCFullNodeConfig)
	time.Sleep(5000 * time.Millisecond)
	return err
}

// SetupTBCFullNode Sets up the TBC full node that will be available for hVM precompiles
func SetupTBCFullNode(ctx context.Context, cfg *tbc.Config) error {
	cfg.HemiIndex = true

	MainCtx = ctx

	tbcFullNodeContext, cancel := context.WithCancel(ctx)

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
		err := tbcNode.Run(tbcFullNodeContext)
		if err != nil && !errors.Is(err, context.Canceled) {
			panic(err)
		}
	}()

	TBCFullNode = tbcNode

	TBCFullNodeConfig = cfg
	TBCFullNodeCtxCancel = cancel

	return nil
}

// Equality function which can be used to compare hashes in-line without needing to store in a variable
// to get pointer for using the built-in IsEqual function.
// TODO: review, better way to compare hashes where this is called?
func hashEquals(a chainhash.Hash, b chainhash.Hash) bool {
	return bytes.Equal(a[:], b[:])
}

// FindCommonAncestor walks backwards from both headers to find a common ancestor.
// Returns common ancestor header, a boolean for whether there was a fork or one of the passed
// in headers was an ancestor of the other
// Returns:
//   - *wire.BlockHeader The common ancestor if it was successfully found
//   - uint64 The height of the common ancestor if the ancestor was successfully found
//   - *chainhash.Hash The hash of the first block header encountered which was not found
//   - bool Whether there is a fork/reorg
func FindCommonAncestor(a *tbc.HashHeight, b *tbc.HashHeight) (*wire.BlockHeader, uint64, *chainhash.Hash, bool, error) {
	emptyChainHash := &chainhash.Hash{}

	// If either of the hashes are empty, then assume common ancestor is genesis
	if a.Hash.IsEqual(emptyChainHash) || b.Hash.IsEqual(emptyChainHash) {
		gh, err := TBCFullNode.BlockHeadersByHeight(MainCtx, 0)
		if err != nil {
			// Should always be able to find genesis
			log.Crit("Unable to query TBC for the genesis block", "err", err)
		}
		if len(gh) != 1 {
			log.Crit("Should be exactly one genesis header in TBC")
		}
		return gh[0], 0, nil, false, nil
	}

	if a.Hash.IsEqual(&b.Hash) {
		header, height, err := TBCFullNode.BlockHeaderByHash(MainCtx, a.Hash)
		if err != nil {
			return nil, 0, &a.Hash, false, err
		}
		return header, height, nil, false, nil // They are same, no fork
	}

	lowerHeight := a.Height
	higherHash := b.Hash
	lowerHash := a.Hash
	if b.Height < lowerHeight {
		lowerHeight = b.Height
		higherHash = a.Hash
		lowerHash = b.Hash
	}

	highCursorHeader, highCursorHeight, err := TBCFullNode.BlockHeaderByHash(MainCtx, higherHash)
	if err != nil {
		return nil, 0, &higherHash, false, err
	}

	lowCursorHeader, lowCursorHeight, err := TBCFullNode.BlockHeaderByHash(MainCtx, lowerHash)
	if err != nil {
		return nil, 0, &lowerHash, false, err
	}

	for highCursorHeight > lowCursorHeight {
		prevBlockHash := highCursorHeader.PrevBlock // Temp variable so we can return hash as not found on error
		highCursorHeader, highCursorHeight, err = TBCFullNode.BlockHeaderByHash(MainCtx, prevBlockHash)
		if err != nil {
			return nil, 0, &prevBlockHash, false, err
		}
	}

	// If the cursors are now equal then one was the ancestor
	if hashEquals(lowCursorHeader.BlockHash(), highCursorHeader.BlockHash()) {
		return lowCursorHeader, lowCursorHeight, nil, false, nil // No fork, note low and high cursor heights are same here
	}

	// Cursors are at the same height but on different forks, walk both of them back until they match
	for !hashEquals(lowCursorHeader.BlockHash(), highCursorHeader.BlockHash()) {
		lowCursorPrevBlock := lowCursorHeader.PrevBlock // Temp variable so we can return hash as not found on error
		lowCursorHeader, lowCursorHeight, err = TBCFullNode.BlockHeaderByHash(MainCtx, lowCursorPrevBlock)
		if err != nil {
			return nil, 0, &lowCursorPrevBlock, false, err
		}

		highCursorPrevBlock := highCursorHeader.PrevBlock // Temp variable so we can return hash as not found on error
		highCursorHeader, highCursorHeight, err = TBCFullNode.BlockHeaderByHash(MainCtx, highCursorPrevBlock)
		if err != nil {
			return nil, 0, &highCursorPrevBlock, false, err
		}
	}

	// Now the cursors match, but we had to walk both chains back meaning there was a fork
	return lowCursorHeader, lowCursorHeight, nil, true, nil
}

// TBCIndexToHashHeight first checks to make sure the UTXO and Tx indexers
// are the same (and if not, moves both to the lowest indexed height of either)
// and then moves the indexer to the specified target hash and height,
// unwinding and winding if the move from current indexer state to new
// target state involves a reorganization.
func TBCIndexToHashHeight(targetHH *tbc.HashHeight) error {
	log.Info("TBCIndexToHashHight called with target", "target", targetHH.String())
	// Check for indexer desync and attempt to fix.
	FixMismatchedIndexesIfRequired(MainCtx)

	targetHash := targetHH.Hash

	// Already checked for (and fixed if required) indexer desync so if we got here UTXO and Tx indexes are the same,
	// and we can use one of them for the rest of this function
	tIndexInfo, err := TBCFullNode.TxIndexHash(MainCtx)
	if err != nil {
		// Critical error as this is likely a downstream bug or data corruption with full TBC node
		log.Crit(fmt.Sprintf("Unable to move TBC full node indexers to block %s @ %d; unable to get TxIndexHash",
			targetHH.Hash.String(), targetHH.Height), "err", err)
	}

	if hashEquals(tIndexInfo.Hash, targetHash) {
		// already done
		return nil
	}

	ancestor, _, missingHeader, isFork, err := FindCommonAncestor(tIndexInfo, targetHH)
	if err != nil {
		if missingHeader != nil {
			// This function should only be called after upstream caller ensures that TBC full node has the correct
			// information to perform the requested indexer update, but return an error so upstream can decide how
			// to handle.
			log.Error(fmt.Sprintf("Unable to find common ancestor between indexers tip %s @ %d and best header"+
				" %s @ %d, encountered a missing header %s", tIndexInfo.Hash.String(), tIndexInfo.Height,
				targetHH.Hash.String(), targetHH.Height, missingHeader.String()), "err", err)
			panic("Clayton change me")
			// return consensus.ErrFullTBCMissingBTCHeader
		} else {
			// An error without a missing header indicated, fail with crit
			log.Crit(fmt.Sprintf("Unable to find common ancestor between indexers tip %s @ %d and best header"+
				" %s @ %d, but no missing header in the path identified", tIndexInfo.Hash.String(), tIndexInfo.Height,
				targetHH.Hash.String(), targetHH.Height), "err", err)
		}
	}

	ancestorHash := ancestor.BlockHash()

	if !isFork {
		// Indexers only needs to move in one direction, and the indexer will figure out which
		log.Debug(fmt.Sprintf("Moving full TBC indexers forward from %s to %s @ %d", ancestor.BlockHash().String(),
			targetHH.Hash.String(), targetHH.Height))

		err = TBCFullNode.SyncIndexersToHash(MainCtx, targetHH.Hash)
		if err != nil {
			// Upstream caller should have checked that the TBC full node had the required block information to perform
			// this indexer update, but bubble the error upstream to handle rather than assuming a critical error here.
			log.Error(fmt.Sprintf("Unable to move indexers from current hash %s to requested hash %s",
				ancestor.BlockHash().String(), targetHH.Hash.String()), "err", err)
			return err
		}

		log.Debug(fmt.Sprintf("Successfully moved TBC indexers forward to %s @ %d without traversing a fork",
			targetHH.Hash.String(), targetHH.Height))
	} else {
		// Indexers need to first unwind to the ancestor, and then wind to the requested target
		log.Debug(fmt.Sprintf("Moving full TBC indexers backward from %s @ %d to %s",
			tIndexInfo.Hash.String(), tIndexInfo.Height, ancestor.BlockHash().String()))

		err = TBCFullNode.SyncIndexersToHash(MainCtx, ancestorHash)
		if err != nil {
			// Being unable to unwind the indexers to a previous point in the chain should never happen as all
			// data should be available, so this indicates either a bug or data corruption.
			log.Crit(fmt.Sprintf("While indexing over a fork, unable to unwind indexers from current hash "+
				"%s to requested hash %s", tIndexInfo.Hash.String(), ancestor.BlockHash().String()), "err", err)
			return err
		}

		// We unwound to common ancestor, now need to wind forward
		log.Debug(fmt.Sprintf("Moving full TBC indexers forward from %s to %s @ %d", ancestor.BlockHash().String(),
			targetHH.Hash.String(), targetHH.Height))
		err = TBCFullNode.SyncIndexersToHash(MainCtx, targetHH.Hash)
		if err != nil {
			// Was able to unwind to common ancestor but unable to wind forward to requested target, attempt to
			//restore indexers to their original state
			log.Error(fmt.Sprintf("While indexing over a fork, unable to wind indexers forward from common "+
				"ancestor %s to requested tip %s, attempting to restore TBC full node indexers to previous state "+
				"%s @ %d", ancestor.BlockHash().String(), targetHH.Hash.String(), tIndexInfo.Hash.String(),
				tIndexInfo.Height), "err", err)

			errDuringFix := TBCFullNode.SyncIndexersToHash(MainCtx, tIndexInfo.Hash)
			if errDuringFix != nil {
				// Unable to undo our previous unwind, this should never happen as all data should be available
				// so this indicates either a bug or data corruption
				log.Crit(fmt.Sprintf("While indexing over a fork, encountered an error indexing forward from "+
					"common ancestor %s, and was unable to restore previous state by undoing unwind by indexing back "+
					"to original tip %s @ %d", ancestor.BlockHash().String(), tIndexInfo.Hash.String(),
					tIndexInfo.Height))
			}

			log.Error(fmt.Sprintf("Restored indexer to original state at tip %s @ %d after encoutering error "+
				" winding indexers forward to requested tip %s @ %d", tIndexInfo.Hash.String(), tIndexInfo.Height,
				targetHH.Hash.String(), targetHH.Height))

			// Upstream caller should have checked that the TBC full node had the required block information to perform
			// this indexer update, but bubble the error upstream to handle rather than assuming a critical error here,
			// same as if we encounter an error indexing forward when there is not a fork.
			return err
		}

		log.Debug(fmt.Sprintf("Successfully moved TBC indexers forward to %s @ %d after traversing a fork",
			targetHH.Hash.String(), targetHH.Height))
	}

	// Successful
	return nil
}

// FixMismatchedIndexesIfRequired moves both utxo and tx index to the utxo
// index's hash
func FixMismatchedIndexesIfRequired(ctx context.Context) {
	uIndexInfo, err := TBCFullNode.UtxoIndexHash(ctx)
	if err != nil {
		log.Crit("Unable to get UtxoIndexHash", "err", err)
	}

	log.Info("going to sync indexers to utxo hash")
	err = TBCFullNode.SyncIndexersToHash(ctx, uIndexInfo.Hash)
	if err != nil {
		tIndexInfo, err := TBCFullNode.TxIndexHash(ctx)
		if err != nil {
			log.Crit("Unable to get TxIndexHash", "err", err)
		}

		log.Crit(fmt.Sprintf("Unable to move tx indexer up to utxo indexer "+
			"utxo: %s @ %d, tx: %s @ %d", uIndexInfo.Hash.String(),
			uIndexInfo.Height, tIndexInfo.Hash.String(), tIndexInfo.Height), "err", err)
	}
}

// TBCIndexToHeader is a convenience pass-through to TBCIndexToHashHeight with
// a Bitcoin header provided, and also updates the known upstream consensus tip
// that index advancement is based on.
func TBCIndexToHeader(header *wire.BlockHeader, upstreamTip *wire.BlockHeader) error {
	targetHash := header.BlockHash()
	_, targetHeight, err := TBCFullNode.BlockHeaderByHash(MainCtx, targetHash)
	if err != nil {
		// Passed in header is not available
		return err
	}

	bh := header.BlockHash()

	hh := tbc.HashHeight{
		Hash:   bh,
		Height: targetHeight,
	}

	err = TBCIndexToHashHeight(&hh)
	if err != nil {
		log.Error(fmt.Sprintf("Unable to advance TBC index to header %s with upstream tip %s",
			header.BlockHash().String(), upstreamTip.BlockHash().String()))
		return err
	} else {
		// Indexing was successful, now update upstream tip
		TBCUpstreamTip = upstreamTip
		return nil
	}
}

func hashHeightForHeader(ctx context.Context, header *wire.BlockHeader) (*tbc.HashHeight, error) {
	hash := header.BlockHash()
	_, height, err := TBCFullNode.BlockHeaderByHash(ctx, hash)
	if err != nil {
		return nil, err
	}

	return &tbc.HashHeight{Hash: hash, Height: height}, nil
}

// TBCAttemptBlockRefetch attempts to fetch a specific block
func TBCAttemptBlockRefetch(ctx context.Context, header *wire.BlockHeader) {
	bh := header.BlockHash()
	log.Info(fmt.Sprintf("Attempting to refetch block %s for TBC full node over P2P", bh.String()))

	block, err := TBCFullNode.DownloadBlockFromRandomPeers(ctx, bh, 8)
	if err != nil {
		log.Error(fmt.Sprintf("Encountered error attempting to refetch block %s", bh.String()), "err", err)
	}

	if block != nil {
		log.Info(fmt.Sprintf("Attempt to refetch block %s returned the requested block indicating a refetch "+
			"was not required", bh.String()))
		return
	}

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
// are available based on the common ancestor of the misaligned indexer tips (such that reconciling the
// indexer tips and then moving to the specified endingHeader would have all required blocks).
// Returns:
//   - bool: Whether all blocks (headers AND full blocks) are available between the current indexed tip and the
//     specified tip header, including blocks required for a reorg from indexed tip to ending header if relevant
//   - *[]wire.BlockHeader A list of headers which are known but for which the full block is not available
//   - *chainhash.Hash The first hash of the block for which a header was not found, if relevant
//
// Does NOT return an error if one or more blocks are not found, only if an unexpected error occurs
func TBCBlocksAvailableToHeader(ctx context.Context, endingHeader *wire.BlockHeader) (bool, *[]wire.BlockHeader, *chainhash.Hash, error) {
	syncInfo := TBCFullNode.Synced(ctx)
	utxoSync := syncInfo.Utxo
	txSync := syncInfo.Tx

	missingFullBlocks := make([]wire.BlockHeader, 0)

	log.Info(fmt.Sprintf("TBCBlocksAvailableToHeader called with endingHeader=%s, UTXOs synced to: "+
		"%s and Txs synced to: %s", endingHeader.BlockHash().String(), utxoSync.Hash.String(), txSync.Hash.String()))

	// When both indexers are at the same header, this will be that header.
	// If the indexers are at different positions, this will be the common
	// ancestor they share, which we know we could walk back to since the
	// blocks were available to index to the two different tips
	commonIndexTip, commonIndexTipHeight, missingHeaderHashIndexerAncestorSearch, _, err := FindCommonAncestor(&utxoSync, &txSync)
	if err != nil {
		if errors.As(err, &database.ErrNotFound) {
			// A header wasn't found when looking for the common ancestor.
			return false, nil, missingHeaderHashIndexerAncestorSearch, nil
		}
		return false, nil, nil, err
	}

	tipHH := &tbc.HashHeight{Hash: commonIndexTip.BlockHash(), Height: commonIndexTipHeight}

	targetHH, err := hashHeightForHeader(ctx, endingHeader)
	if err != nil {
		if errors.As(err, &database.ErrNotFound) {
			endingHeaderHash := endingHeader.BlockHash()
			log.Warn(fmt.Sprintf("Header %s not found", endingHeaderHash.String()), "err", err)
			// TBC full node does not know about the ending header
			return false, nil, &endingHeaderHash, nil
		}
		return false, nil, nil, err
	}

	// Find common ancestor between current common index ancestor tip and target header
	ancestorToTarget, _, missingHeaderHashTargetAncestorSearch, _, err := FindCommonAncestor(tipHH, targetHH)
	if err != nil {
		if errors.As(err, &database.ErrNotFound) {
			return false, nil, missingHeaderHashTargetAncestorSearch, nil
		}
		return false, nil, nil, err
	}

	ancestorToTargetHash := ancestorToTarget.BlockHash()
	_, ancestorHeight, err := TBCFullNode.BlockHeaderByHash(ctx, ancestorToTargetHash)
	if err != nil {
		if errors.As(err, &database.ErrNotFound) {
			// Should be impossible, as if the ancestor header is not available FindCommonAncestor
			// would have returned an error already.
			return false, nil, &ancestorToTargetHash, nil
		}
		return false, nil, nil, err
	}

	// Whether or not moving to the target requires unwinding, the only blocks that
	// could be missing are the ones that would have to be indexed after the rewind,
	// so we only need to check for all blocks from the ancestor to the target.
	// Walk backwards from the target down to the ancestor.
	// TODO: make more efficient by adding a cheap check in TBC for a full block being available.
	cursor := endingHeader
	cursorHash := targetHH.Hash
	height := targetHH.Height

	// Walk backwards until our cursor matches the ancestor
	missingCount := 0
	for !bytes.Equal(cursorHash[:], ancestorToTargetHash[:]) {
		log.Trace(fmt.Sprintf("Cursor of %s does not match ancestorToTarget of %s, continuing to walk backwards",
			cursorHash.String(), ancestorToTargetHash.String()))

		available, err := TBCFullNode.FullBlockAvailable(ctx, cursorHash)
		if err != nil {
			log.Warn(fmt.Sprintf("Got error while getting full block for cursor %s", cursorHash.String()),
				"err", err)

			// Even though this error is for something other than the block not being available, return the list of
			// missing full blocks as there could have previously been one or more missing full blocks identified.
			return false, &missingFullBlocks, nil, err
		}

		if !available {
			missingCount++

			if missingCount < 5 {
				log.Trace(fmt.Sprintf("Full block for cursor %s not available",
					cursorHash.String()))
			} else if missingCount == 5 {
				log.Trace(fmt.Sprintf("More than 5 full blocks missing, not printing additional missing blocks"))
			}

			missingFullBlocks = append(missingFullBlocks, *cursor)
			// Do not return yet, so we can collect potentially multiple missing full blocks
		}

		prevBlockHash := cursor.PrevBlock // Temp variable to allow returning it on error since cursor is overwritten
		cursor, height, err = TBCFullNode.BlockHeaderByHash(ctx, cursor.PrevBlock)
		if err != nil {
			// Should be impossible as a missing header would have been identified when finding the
			// common ancestor between target and lowest indexed tip.
			if errors.As(err, &database.ErrNotFound) {
				return false, nil, &prevBlockHash, nil
			}
			log.Warn(fmt.Sprintf("Unable to get block header for cursor's previous block %s, got error other "+
				"than database not found", cursor.PrevBlock.String()), "err", err)
			return false, nil, nil, err
		}
		if height < ancestorHeight {
			// Somehow walking backwards got to a lower block than the ancestor we are looking for.
			// Should never happen, would mean that the current indexed tip and target are not
			// on the same chain graph but FindCommonAncestor reported a common ancestor.
			log.Error(fmt.Sprintf(""))
			return false, nil, nil, fmt.Errorf("TBCBlocksAvailableToHeader failed walking backwards from "+
				"%s @ %d looking for %s @ %d, walked to height=%d", targetHH.Hash.String(),
				targetHH.Height, ancestorToTarget.BlockHash().String(), ancestorHeight, height)
		}
		cursorHash = cursor.BlockHash()
	}

	// If missingFullBlocks is empty then the previous loop was able to find all full blocks
	// in the path up to the target ending tip. Otherwise, one or more full blocks are not
	// currently available in TBC.
	if len(missingFullBlocks) > 0 {
		// No error to bubble up, just a list of missing full blocks which must be acquired
		// before indexing to the specified target tip will be possible.
		return false, &missingFullBlocks, nil, nil
	} else {
		// No missing blocks, and a missing block header would have been returned earlier.
		return true, nil, nil, nil
	}
}

// PrecompiledContracts contains the precompiled contracts supported at the given fork.
type PrecompiledContracts map[common.Address]PrecompiledContract

// PrecompiledContractsHomestead contains the default set of pre-compiled Ethereum
// contracts used in the Frontier and Homestead releases.
var PrecompiledContractsHomestead = PrecompiledContracts{
	common.BytesToAddress([]byte{0x1}): &ecrecover{},
	common.BytesToAddress([]byte{0x2}): &sha256hash{},
	common.BytesToAddress([]byte{0x3}): &ripemd160hash{},
	common.BytesToAddress([]byte{0x4}): &dataCopy{},
}

// PrecompiledContractsByzantium contains the default set of pre-compiled Ethereum
// contracts used in the Byzantium release.
var PrecompiledContractsByzantium = PrecompiledContracts{
	common.BytesToAddress([]byte{0x1}): &ecrecover{},
	common.BytesToAddress([]byte{0x2}): &sha256hash{},
	common.BytesToAddress([]byte{0x3}): &ripemd160hash{},
	common.BytesToAddress([]byte{0x4}): &dataCopy{},
	common.BytesToAddress([]byte{0x5}): &bigModExp{eip2565: false, eip7823: false, eip7883: false},
	common.BytesToAddress([]byte{0x6}): &bn256AddByzantium{},
	common.BytesToAddress([]byte{0x7}): &bn256ScalarMulByzantium{},
	common.BytesToAddress([]byte{0x8}): &bn256PairingByzantium{},
}

// PrecompiledContractsIstanbul contains the default set of pre-compiled Ethereum
// contracts used in the Istanbul release.
var PrecompiledContractsIstanbul = PrecompiledContracts{
	common.BytesToAddress([]byte{0x1}): &ecrecover{},
	common.BytesToAddress([]byte{0x2}): &sha256hash{},
	common.BytesToAddress([]byte{0x3}): &ripemd160hash{},
	common.BytesToAddress([]byte{0x4}): &dataCopy{},
	common.BytesToAddress([]byte{0x5}): &bigModExp{eip2565: false, eip7823: false, eip7883: false},
	common.BytesToAddress([]byte{0x6}): &bn256AddIstanbul{},
	common.BytesToAddress([]byte{0x7}): &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{0x8}): &bn256PairingIstanbul{},
	common.BytesToAddress([]byte{0x9}): &blake2F{},
}

// PrecompiledContractsBerlin contains the default set of pre-compiled Ethereum
// contracts used in the Berlin release.
var PrecompiledContractsBerlin = PrecompiledContracts{
	common.BytesToAddress([]byte{0x1}): &ecrecover{},
	common.BytesToAddress([]byte{0x2}): &sha256hash{},
	common.BytesToAddress([]byte{0x3}): &ripemd160hash{},
	common.BytesToAddress([]byte{0x4}): &dataCopy{},
	common.BytesToAddress([]byte{0x5}): &bigModExp{eip2565: true, eip7823: false, eip7883: false},
	common.BytesToAddress([]byte{0x6}): &bn256AddIstanbul{},
	common.BytesToAddress([]byte{0x7}): &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{0x8}): &bn256PairingIstanbul{},
	common.BytesToAddress([]byte{0x9}): &blake2F{},
}

// PrecompiledContractsCancun contains the default set of pre-compiled Ethereum
// contracts used in the Cancun release.
var PrecompiledContractsCancun = PrecompiledContracts{
	common.BytesToAddress([]byte{0x1}): &ecrecover{},
	common.BytesToAddress([]byte{0x2}): &sha256hash{},
	common.BytesToAddress([]byte{0x3}): &ripemd160hash{},
	common.BytesToAddress([]byte{0x4}): &dataCopy{},
	common.BytesToAddress([]byte{0x5}): &bigModExp{eip2565: true, eip7823: false, eip7883: false},
	common.BytesToAddress([]byte{0x6}): &bn256AddIstanbul{},
	common.BytesToAddress([]byte{0x7}): &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{0x8}): &bn256PairingIstanbul{},
	common.BytesToAddress([]byte{0x9}): &blake2F{},
	common.BytesToAddress([]byte{0xa}): &kzgPointEvaluation{},
}

// PrecompiledContractsPrague contains the set of pre-compiled Ethereum
// contracts used in the Prague release.
var PrecompiledContractsPrague = PrecompiledContracts{
	common.BytesToAddress([]byte{0x01}): &ecrecover{},
	common.BytesToAddress([]byte{0x02}): &sha256hash{},
	common.BytesToAddress([]byte{0x03}): &ripemd160hash{},
	common.BytesToAddress([]byte{0x04}): &dataCopy{},
	common.BytesToAddress([]byte{0x05}): &bigModExp{eip2565: true, eip7823: false, eip7883: false},
	common.BytesToAddress([]byte{0x06}): &bn256AddIstanbul{},
	common.BytesToAddress([]byte{0x07}): &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{0x08}): &bn256PairingIstanbul{},
	common.BytesToAddress([]byte{0x09}): &blake2F{},
	common.BytesToAddress([]byte{0x0a}): &kzgPointEvaluation{},
	common.BytesToAddress([]byte{0x0b}): &bls12381G1Add{},
	common.BytesToAddress([]byte{0x0c}): &bls12381G1MultiExp{},
	common.BytesToAddress([]byte{0x0d}): &bls12381G2Add{},
	common.BytesToAddress([]byte{0x0e}): &bls12381G2MultiExp{},
	common.BytesToAddress([]byte{0x0f}): &bls12381Pairing{},
	common.BytesToAddress([]byte{0x10}): &bls12381MapG1{},
	common.BytesToAddress([]byte{0x11}): &bls12381MapG2{},
}

var PrecompiledContractsBLS = PrecompiledContractsPrague

var PrecompiledContractsVerkle = PrecompiledContractsBerlin

// PrecompiledContractsOsaka contains the set of pre-compiled Ethereum
// contracts used in the Osaka release.
var PrecompiledContractsOsaka = PrecompiledContracts{
	common.BytesToAddress([]byte{0x01}): &ecrecover{},
	common.BytesToAddress([]byte{0x02}): &sha256hash{},
	common.BytesToAddress([]byte{0x03}): &ripemd160hash{},
	common.BytesToAddress([]byte{0x04}): &dataCopy{},
	common.BytesToAddress([]byte{0x05}): &bigModExp{eip2565: true, eip7823: true, eip7883: true},
	common.BytesToAddress([]byte{0x06}): &bn256AddIstanbul{},
	common.BytesToAddress([]byte{0x07}): &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{0x08}): &bn256PairingIstanbul{},
	common.BytesToAddress([]byte{0x09}): &blake2F{},
	common.BytesToAddress([]byte{0x0a}): &kzgPointEvaluation{},
	common.BytesToAddress([]byte{0x0b}): &bls12381G1Add{},
	common.BytesToAddress([]byte{0x0c}): &bls12381G1MultiExp{},
	common.BytesToAddress([]byte{0x0d}): &bls12381G2Add{},
	common.BytesToAddress([]byte{0x0e}): &bls12381G2MultiExp{},
	common.BytesToAddress([]byte{0x0f}): &bls12381Pairing{},
	common.BytesToAddress([]byte{0x10}): &bls12381MapG1{},
	common.BytesToAddress([]byte{0x11}): &bls12381MapG2{},

	common.BytesToAddress([]byte{0x1, 0x00}): &p256Verify{},
}

// PrecompiledContractsP256Verify contains the precompiled Ethereum
// contract specified in EIP-7212. This is exported for testing purposes.
var PrecompiledContractsP256Verify = PrecompiledContracts{
	common.BytesToAddress([]byte{0x1, 0x00}): &p256Verify{},
}

// PrecompiledContractsFjord contains the default set of pre-compiled Ethereum
// contracts used in the Fjord release.
var PrecompiledContractsFjord = map[common.Address]PrecompiledContract{
	common.BytesToAddress([]byte{1}):          &ecrecover{},
	common.BytesToAddress([]byte{2}):          &sha256hash{},
	common.BytesToAddress([]byte{3}):          &ripemd160hash{},
	common.BytesToAddress([]byte{4}):          &dataCopy{},
	common.BytesToAddress([]byte{5}):          &bigModExp{eip2565: true},
	common.BytesToAddress([]byte{6}):          &bn256AddIstanbul{},
	common.BytesToAddress([]byte{7}):          &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{8}):          &bn256PairingIstanbul{},
	common.BytesToAddress([]byte{9}):          &blake2F{},
	common.BytesToAddress([]byte{0x0a}):       &kzgPointEvaluation{},
	common.BytesToAddress([]byte{0x01, 0x00}): &p256VerifyFjord{},
}

// PrecompiledContractsGranite contains the default set of pre-compiled Ethereum
// contracts used in the Granite release.
var PrecompiledContractsGranite = map[common.Address]PrecompiledContract{
	common.BytesToAddress([]byte{1}):          &ecrecover{},
	common.BytesToAddress([]byte{2}):          &sha256hash{},
	common.BytesToAddress([]byte{3}):          &ripemd160hash{},
	common.BytesToAddress([]byte{4}):          &dataCopy{},
	common.BytesToAddress([]byte{5}):          &bigModExp{eip2565: true},
	common.BytesToAddress([]byte{6}):          &bn256AddIstanbul{},
	common.BytesToAddress([]byte{7}):          &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{8}):          &bn256PairingGranite{},
	common.BytesToAddress([]byte{9}):          &blake2F{},
	common.BytesToAddress([]byte{0x0a}):       &kzgPointEvaluation{},
	common.BytesToAddress([]byte{0x01, 0x00}): &p256VerifyFjord{},
}

var PrecompiledContractsIsthmus = map[common.Address]PrecompiledContract{
	common.BytesToAddress([]byte{1}):          &ecrecover{},
	common.BytesToAddress([]byte{2}):          &sha256hash{},
	common.BytesToAddress([]byte{3}):          &ripemd160hash{},
	common.BytesToAddress([]byte{4}):          &dataCopy{},
	common.BytesToAddress([]byte{5}):          &bigModExp{eip2565: true},
	common.BytesToAddress([]byte{6}):          &bn256AddIstanbul{},
	common.BytesToAddress([]byte{7}):          &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{8}):          &bn256PairingGranite{},
	common.BytesToAddress([]byte{9}):          &blake2F{},
	common.BytesToAddress([]byte{0x0a}):       &kzgPointEvaluation{},
	common.BytesToAddress([]byte{0x0b}):       &bls12381G1Add{},
	common.BytesToAddress([]byte{0x0c}):       &bls12381G1MultiExpIsthmus{},
	common.BytesToAddress([]byte{0x0d}):       &bls12381G2Add{},
	common.BytesToAddress([]byte{0x0e}):       &bls12381G2MultiExpIsthmus{},
	common.BytesToAddress([]byte{0x0f}):       &bls12381PairingIsthmus{},
	common.BytesToAddress([]byte{0x10}):       &bls12381MapG1{},
	common.BytesToAddress([]byte{0x11}):       &bls12381MapG2{},
	common.BytesToAddress([]byte{0x01, 0x00}): &p256VerifyFjord{},
}

var PrecompiledContractsJovian = map[common.Address]PrecompiledContract{
	common.BytesToAddress([]byte{1}):          &ecrecover{},
	common.BytesToAddress([]byte{2}):          &sha256hash{},
	common.BytesToAddress([]byte{3}):          &ripemd160hash{},
	common.BytesToAddress([]byte{4}):          &dataCopy{},
	common.BytesToAddress([]byte{5}):          &bigModExp{eip2565: true},
	common.BytesToAddress([]byte{6}):          &bn256AddIstanbul{},
	common.BytesToAddress([]byte{7}):          &bn256ScalarMulIstanbul{},
	common.BytesToAddress([]byte{8}):          &bn256PairingJovian{},
	common.BytesToAddress([]byte{9}):          &blake2F{},
	common.BytesToAddress([]byte{0x0a}):       &kzgPointEvaluation{},
	common.BytesToAddress([]byte{0x0b}):       &bls12381G1Add{},
	common.BytesToAddress([]byte{0x0c}):       &bls12381G1MultiExpJovian{},
	common.BytesToAddress([]byte{0x0d}):       &bls12381G2Add{},
	common.BytesToAddress([]byte{0x0e}):       &bls12381G2MultiExpJovian{},
	common.BytesToAddress([]byte{0x0f}):       &bls12381PairingJovian{},
	common.BytesToAddress([]byte{0x10}):       &bls12381MapG1{},
	common.BytesToAddress([]byte{0x11}):       &bls12381MapG2{},
	common.BytesToAddress([]byte{0x01, 0x00}): &p256VerifyFjord{},
}

var hvmContractsToAddress = map[reflect.Type][]byte{
	reflect.TypeOf(&btcBalAddr{}):           {btcBalAddrAddr},
	reflect.TypeOf(&btcUtxosAddrList{}):     {btcUtxosAddrListAddr},
	reflect.TypeOf(&btcTxByTxid{}):          {btcTxByTxidAddr},
	reflect.TypeOf(&btcTxConfirmations{}):   {btcTxConfirmationsAddr},
	reflect.TypeOf(&btcLastHeader{}):        {btcLastHeaderAddr},
	reflect.TypeOf(&btcHeaderN{}):           {btcHeaderNAddr},
	reflect.TypeOf(&btcAddrToScript{}):      {btcAddrToScriptAddr},
	reflect.TypeOf(&btcInputByTxid{}):       {btcInputByTxidAddr},
	reflect.TypeOf(&btcOutputByTxid{}):      {btcOutputByTxidAddr},
	reflect.TypeOf(&btcTxGetInputWitness{}): {btcTxGetInputWitnessAddr},
}

var PrecompiledContractsHvm0 = map[common.Address]PrecompiledContract{
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcBalAddr{})]):           &btcBalAddr{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcUtxosAddrList{})]):     &btcUtxosAddrList{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcTxByTxid{})]):          &btcTxByTxid{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcTxConfirmations{})]):   &btcTxConfirmations{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcLastHeader{})]):        &btcLastHeader{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcHeaderN{})]):           &btcHeaderN{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcAddrToScript{})]):      &btcAddrToScript{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcInputByTxid{})]):       &btcInputByTxid{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcOutputByTxid{})]):      &btcOutputByTxid{},
	common.BytesToAddress(hvmContractsToAddress[reflect.TypeOf(&btcTxGetInputWitness{})]): &btcTxGetInputWitness{},
}

var (
	PrecompiledAddressesJovian    []common.Address
	PrecompiledAddressesIsthmus   []common.Address
	PrecompiledAddressesGranite   []common.Address
	PrecompiledAddressesFjord     []common.Address
	PrecompiledAddressesOsaka     []common.Address
	PrecompiledAddressesPrague    []common.Address
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
		PrecompiledAddressesHvm0 = append(PrecompiledAddressesHvm0, k)
	}

	for k := range PrecompiledContractsPrague {
		PrecompiledAddressesPrague = append(PrecompiledAddressesPrague, k)
	}
	for k := range PrecompiledContractsOsaka {
		PrecompiledAddressesOsaka = append(PrecompiledAddressesOsaka, k)
	}
	for k := range PrecompiledContractsFjord {
		PrecompiledAddressesFjord = append(PrecompiledAddressesFjord, k)
	}
	for k := range PrecompiledContractsGranite {
		PrecompiledAddressesGranite = append(PrecompiledAddressesGranite, k)
	}
	for k := range PrecompiledContractsIsthmus {
		PrecompiledAddressesIsthmus = append(PrecompiledAddressesIsthmus, k)
	}
	for k := range PrecompiledContractsJovian {
		PrecompiledAddressesJovian = append(PrecompiledAddressesJovian, k)
	}
}

func activePrecompiledContracts(rules params.Rules) PrecompiledContracts {
	// note: the order of these switch cases is important
	switch {
	case rules.IsOptimismJovian:
		return PrecompiledContractsJovian
	case rules.IsOptimismIsthmus:
		return PrecompiledContractsIsthmus
	case rules.IsOptimismGranite:
		return PrecompiledContractsGranite
	case rules.IsOptimismFjord:
		return PrecompiledContractsFjord
	case rules.IsVerkle:
		return PrecompiledContractsVerkle
	case rules.IsOsaka:
		return PrecompiledContractsOsaka
	case rules.IsPrague:
		return PrecompiledContractsPrague
	case rules.IsCancun:
		return PrecompiledContractsCancun
	case rules.IsBerlin:
		return PrecompiledContractsBerlin
	case rules.IsIstanbul:
		return PrecompiledContractsIstanbul
	case rules.IsByzantium:
		return PrecompiledContractsByzantium
	default:
		return PrecompiledContractsHomestead
	}
}

// ActivePrecompiledContracts returns a copy of precompiled contracts enabled with the current configuration.
func ActivePrecompiledContracts(rules params.Rules) PrecompiledContracts {
	precompiles := maps.Clone(activePrecompiledContracts(rules))

	switch {
	case rules.IsHvm0:
		for k, v := range PrecompiledContractsHvm0 {
			precompiles[k] = v
		}
		return precompiles
	default:
		return precompiles
	}
}

// ActivePrecompiles returns the precompiles enabled with the current configuration.
func activePrecompiles(rules params.Rules) []common.Address {
	switch {
	case rules.IsOptimismJovian:
		return PrecompiledAddressesJovian
	case rules.IsOptimismIsthmus:
		return PrecompiledAddressesIsthmus
	case rules.IsOptimismGranite:
		return PrecompiledAddressesGranite
	case rules.IsOptimismFjord:
		return PrecompiledAddressesFjord
	case rules.IsOsaka:
		return PrecompiledAddressesOsaka
	case rules.IsPrague:
		return PrecompiledAddressesPrague
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
func ActivePrecompiles(rules params.Rules) []common.Address {
	// For now, Hemi upgrades can be performed out-of-sync with upstream updates.
	// As a result, this code is modified to select upstream precompiles, and then
	// Layer on Hemi-specific precompile lists.
	// Original ActivePrecompiles logic moved to activeUpstreamPrecompiles.

	nonHvmPrecompiles := activePrecompiles(rules)

	switch {
	case rules.IsHvm0:
		if rules.IsPrague && !rules.IsOptimismJovian {
			return append([]common.Address{}, PrecompiledAddressesHvm0...)
		}
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

type ZKPrecompileProof interface {
	Verify() error
	Result() []byte
	StateRoot() []byte
}

// check that Verify(), commit to StateRoot that is the correct state root
// of zk trie at this point in the chain
// StateRoot is in journal.  Verify() == correct journal outputs
// when you run precompile, verify that state root is the same is the sta
// mock zk trie
// get state root from evm state, given current execution context

var proofsMtx sync.Mutex
var proofs map[string]map[string]ZKPrecompileProof = map[string]map[string]ZKPrecompileProof{}

func proofKey(precompile common.Address, calldata []byte, stateRoot []byte) string {
	return fmt.Sprintf("%X-%X", precompile, calldata)
}

func AddProof(blockExecutionContextHash common.Hash, precompile common.Address, calldata []byte, proof ZKPrecompileProof) {
	key := proofKey(precompile, calldata, proof.StateRoot())

	proofsMtx.Lock()
	defer proofsMtx.Unlock()

	log.Info("adding proofs for block hash", "block hash", blockExecutionContextHash.Hex())

	if proofs[blockExecutionContextHash.Hex()] == nil {
		proofs[blockExecutionContextHash.Hex()] = map[string]ZKPrecompileProof{}
	}

	proofs[blockExecutionContextHash.Hex()][key] = proof
}

var ErrPrecompileProofNotFound = errors.New("could not find precompile proof")

func ProofForPrecompileCall(precompile common.Address, calldata []byte, stateRoot []byte) (ZKPrecompileProof, error) {
	key := proofKey(precompile, calldata, stateRoot)

	proofsMtx.Lock()
	defer proofsMtx.Unlock()

	for _, v := range proofs {
		foundProof := v[key]
		if foundProof != nil {
			return foundProof, nil
		}
	}

	return nil, ErrPrecompileProofNotFound
}

func RemoveProofsForBlockHash(h common.Hash) {
	proofsMtx.Lock()
	defer proofsMtx.Unlock()

	log.Info("proofs: removing for block hash", "block hash", h.Hex())

	// Clayton note: verify this is the correct spot
	delete(proofs, h.Hex())
}

// RunPrecompiledContract runs and evaluates the output of a precompiled contract.
// It returns
// - the returned bytes,
// - the _remaining_ gas,
// - any error that occurred
func RunPrecompiledContract(p PrecompiledContract, input []byte, suppliedGas uint64, blockContext *common.Hash, logger *tracing.Hooks) (ret []byte, remainingGas uint64, err error) {
	gasCost := p.RequiredGas(input)
	if suppliedGas < gasCost {
		return nil, 0, ErrOutOfGas
	}
	if logger != nil && logger.OnGasChange != nil {
		logger.OnGasChange(suppliedGas, suppliedGas-gasCost, tracing.GasChangeCallPrecompiledContract)
	}
	suppliedGas -= gasCost
	if precompile := hvmContractsToAddress[reflect.TypeOf(p)]; precompile != nil && zkMode() && isHvmPrecompileCall(common.BytesToAddress(precompile)) {
		// add back in block context
		// update map to be mapping of block execution context hash --> proofs for that execution
		// at the end of execution (should be the function where it's created, double-check), we can delete it from the map based on the hash
		// in this precompile function, panic()
		result, err := ProofForPrecompileCall(common.BytesToAddress(precompile), input, []byte{})
		if errors.Is(err, ErrPrecompileProofNotFound) {
			panic(err)
		}

		if err := result.Verify(); err != nil {
			panic(err) // should not happen, as we call Verify() upon insertion
		}

		// Clayton note: check result.StateRoot() here
		// if !bytes.Equal(result.StateRoot(), something) ... error!

		return result.Result(), suppliedGas, err
	}
	output, err := p.Run(input, common.Hash{})
	return output, suppliedGas, err
}

type btcBalAddr struct{}

func (c *btcBalAddr) Name() string {
	return "BTC Balance Address"
}

func (c *btcBalAddr) RequiredGas(input []byte) uint64 {
	return params.BtcAddrBal
}

func (c *btcBalAddr) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if input == nil || len(input) < MIN_BTC_ADDRESS_LENGTH {
		log.Debug("btcBalAddr run called with nil or too small address as input", "input", input)
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
			log.Debug(fmt.Sprintf("btcBalAddr returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	addr := string(input)
	log.Debug("btcBalAddr called", "address", addr)

	bal, err := TBCFullNode.BalanceByAddress(MainCtx, addr)

	if err != nil {
		log.Error("hVM Error: Unable to process balance of address", "address", addr, "err", err)
		return nil, nil
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

func (c *btcTxConfirmations) Name() string {
	return "BTC TX Confirmations"
}

func (c *btcTxConfirmations) RequiredGas(input []byte) uint64 {
	return params.BtcTxConf
}

func (c *btcTxConfirmations) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if input == nil || len(input) != BTC_TXID_LENGTH_BYTES {
		log.Debug("btcTxConfirmations run called with nil or input that is not the length of a BTC TxId",
			"input", fmt.Sprintf("%x", input))
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

	txHash := chainhash.Hash{}
	err := txHash.SetBytes(txid[:])
	if err != nil {
		log.Warn("Unable to lookup tx confirmations by Txid; unable to convert txid %x to chainhash!", "txid", txid, "err", err)
	}

	// This only returns information about the canonical chain
	blockHash, err := TBCFullNode.BlockHashByTxId(MainCtx, txHash)
	if err != nil {
		log.Error("Unable to lookup transaction confirmations by txid", "txid", txid, "err", err)
		return nil, err
	}

	if blockHash == nil {
		log.Crit("block hash is nil")
	}

	_, height, err := TBCFullNode.BlockHeaderByHash(MainCtx, *blockHash)
	if err != nil {
		log.Error(fmt.Sprintf("Unable to get block header by hash %x", blockHash[:]))
		return nil, err
	}

	_, heightBest, err := TBCFullNode.BlockHeaderByHash(MainCtx, TBCUpstreamTip.BlockHash())
	if err != nil {
		log.Error("hVM precompile unable to get header of upstream best tip", "err", err)
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

func (c *btcAddrToScript) Name() string {
	return "BTC Addr to Script"
}

func (c *btcAddrToScript) RequiredGas(input []byte) uint64 {
	return params.BtcAddrToScript
}

func (c *btcAddrToScript) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if input == nil || len(input) < MIN_BTC_ADDRESS_LENGTH {
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

func (c *btcLastHeader) Name() string {
	return "BTC Last Header"
}

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
			log.Debug(fmt.Sprintf("btcLastHeader returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	// Assumes UTXO and Tx indexers are in sync when hVM precompile calls are performed
	utxoIndex, err := TBCFullNode.UtxoIndexHash(MainCtx)
	if err != nil {
		log.Error("hVM precompile unable to get UTXO indexer status", "err", err)
	}

	// Get header and height that UTXO indexer (and assumed Tx indexer) is synced to
	bestHeader, height, err := TBCFullNode.BlockHeaderByHash(MainCtx, utxoIndex.Hash)

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

func (c *btcHeaderN) Name() string {
	return "BTC Header N"
}

func (c *btcHeaderN) RequiredGas(input []byte) uint64 {
	return params.BtcHeaderN
}

func (c *btcHeaderN) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if input == nil || len(input) != 4 {
		log.Debug("btcHeaderN run called with nil or != 4 input", "input", fmt.Sprintf("%x", input))
		return nil, fmt.Errorf("btcHeaderN called with nill or != 4 input")
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
			log.Debug(fmt.Sprintf("btcHeaderN returning cached result for query of "+
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

	headers, err := TBCFullNode.BlockHeadersByHeight(MainCtx, uint64(height))
	if err != nil || len(headers) == 0 {
		log.Warn("Unable to lookup header!", "height", height)
		return nil, nil
	}

	indexOfCanonicalHeader := -1

	// Find which (if any) header at specified height is represented by the Tx Index (so is part of hVM's view)
	for i, header := range headers {
		headerHash := header.BlockHash()
		canonical, err := TBCFullNode.BlockInTxIndex(MainCtx, headerHash)
		if err != nil {
			log.Error(fmt.Sprintf("Unable to lookup whether header %s is in the tx index!",
				headerHash.String()), "err", err)
			// Don't return as this could be an error on a non-canonical block
		}
		if canonical {
			indexOfCanonicalHeader = i
			break
		}
	}

	if indexOfCanonicalHeader == -1 {
		// No canonical header at height found
		log.Warn(fmt.Sprintf("hVM unable to find any canonical header at height %d", height))
		return nil, nil
	}

	bestHeader := headers[indexOfCanonicalHeader]

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

func (c *btcUtxosAddrList) Name() string {
	return "BTC UTXOs Address List"
}

func (c *btcUtxosAddrList) RequiredGas(input []byte) uint64 {
	return params.BtcUtxosAddrList
}

func (c *btcUtxosAddrList) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Must be an address plus 4 bytes for pagination info
	if len(input) < MIN_BTC_ADDRESS_LENGTH+4 {
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
			log.Info(fmt.Sprintf("btcUtxosAddrList returning cached result for query of "+
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
		pgSize = 10 // Default to 10 items per page
	}

	log.Debug("btcUtxosAddrList run called", "addr", addr, "pg", pg, "pgSize", pgSize)

	if TBCFullNode == nil {
		log.Crit("No TBC indexer available, cannot perform hVM precompile call!")
	}

	utxos, err := TBCFullNode.UtxosByAddress(MainCtx, false, addr, uint64(pg), uint64(pgSize))

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

type btcInputByTxid struct{}

func (c *btcInputByTxid) Name() string {
	return "BTC Input by TXID"
}

func (c *btcInputByTxid) RequiredGas(input []byte) uint64 {
	// TODO: Gas based on returned size and/or enabled fields
	return params.BtcInputByTxid
}

func (c *btcInputByTxid) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) != BTC_TXID_LENGTH_BYTES+4 { // 32 bytes txid, 2 bytes for input index
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
			log.Info(fmt.Sprintf("btcInputByTxid returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	var txid = make([]byte, 32)
	copy(txid[0:32], input[0:32])
	slices.Reverse(txid)

	txidEnd := len(input) - 4
	inputIdx := (uint32(input[txidEnd+1]&0xFF) << 8) |
		uint32(input[txidEnd+2]&0xFF)

	maxInputScriptSigSize := (uint32(input[txidEnd+3]&0xFF) << 8) |
		uint32(input[txidEnd+4]&0xFF)

	log.Debug(fmt.Sprintf("Looking up input %d for txid %x", inputIdx, txid))

	ch := chainhash.Hash{}
	err := ch.SetBytes(txid)
	if err != nil {
		log.Warn("Unable to lookup tx by txid; unable to convert txid %x to chainhash", "txid", txid)
	}

	tx, err := TBCFullNode.TxById(MainCtx, ch)
	if err != nil || tx == nil {
		log.Error("Unable to lookup tx by txid", "txid", fmt.Sprintf("%x", txid))
		return nil, nil
	}

	if inputIdx >= uint32(len(tx.TxIn)) {
		log.Warn(fmt.Sprintf("hVM call requested input %d but tx %x only has %d inputs", inputIdx, txid, len(tx.TxIn)))
		return nil, nil
	}
	resp := make([]byte, 0)

	in := tx.TxIn[inputIdx]

	if in.Witness == nil || len(in.Witness) == 0 {
		resp = binary.BigEndian.AppendUint16(resp, uint16(0))
	} else {
		witnessElements := len(in.Witness)
		if witnessElements > math.MaxUint16 {
			// If caller sees 65535 witness elements, then it may have exactly that amount or more
			witnessElements = math.MaxUint16
		}
		resp = binary.BigEndian.AppendUint16(resp, uint16(witnessElements))
	}

	prevIn := in.PreviousOutPoint
	pih := chainhash.Hash{}
	err = pih.SetBytes(prevIn.Hash[:])
	if err != nil {
		log.Warn("Unable to lookup Tx by Txid; unable to convert txid %x to chainhash!", "txid", txid)
		return nil, nil
	}

	sourceTx, err := TBCFullNode.TxById(MainCtx, pih)
	if err != nil {
		log.Warn("unable to lookup input transaction",
			"prevInTxID", fmt.Sprintf("%x", prevIn.Hash), "prevInTxIndex", prevIn.Index)
		return nil, nil
	}
	value := sourceTx.TxOut[prevIn.Index].Value

	resp = binary.BigEndian.AppendUint64(resp, uint64(value))

	prevInHash := prevIn.Hash
	slices.Reverse(prevInHash[:])
	resp = append(resp, prevInHash[:]...)

	prevInIndex := prevIn.Index
	if prevInIndex > math.MaxUint16 {
		prevInIndex = math.MaxUint16
	}

	resp = binary.BigEndian.AppendUint16(resp, uint16(prevInIndex))

	choppedInputScript := make([]byte, 0)
	choppedInputScript = append(choppedInputScript, in.SignatureScript...)
	if len(choppedInputScript) > int(maxInputScriptSigSize) {
		choppedInputScript = choppedInputScript[0:maxInputScriptSigSize]
	}

	sigScriptLength := len(in.SignatureScript)
	if sigScriptLength > math.MaxUint16 {
		sigScriptLength = math.MaxUint16
	}

	resp = binary.BigEndian.AppendUint16(resp, uint16(sigScriptLength))
	resp = append(resp, choppedInputScript...)
	resp = binary.BigEndian.AppendUint32(resp, in.Sequence)

	if isValidBlock(blockContext) {
		hvmQueryMap[k] = resp
	}

	return resp, nil
}

type btcOutputByTxid struct{}

func (c *btcOutputByTxid) Name() string {
	return "BTC Output by TXID"
}

func (c *btcOutputByTxid) RequiredGas(input []byte) uint64 {
	// TODO: Gas based on returned size and/or enabled fields in future hVM version
	return params.BtcOutputByTxid
}

func (c *btcOutputByTxid) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) != BTC_TXID_LENGTH_BYTES+4 { // 32 bytes txid, 2 bytes for output index
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
			log.Info(fmt.Sprintf("btcOutputByTxid returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	var txid = make([]byte, 32)
	copy(txid[0:32], input[0:32])
	slices.Reverse(txid)

	txidEnd := len(input) - 4
	outputIdx := (uint32(input[txidEnd+1]&0xFF) << 8) |
		uint32(input[txidEnd+2]&0xFF)
	maxOutputScriptSize := (uint32(input[txidEnd+3]&0xFF) << 8) |
		uint32(input[txidEnd+4]&0xFF)

	log.Info(fmt.Sprintf("Looking up output %d for txid %x", outputIdx, txid))

	ch := chainhash.Hash{}
	err := ch.SetBytes(txid)
	if err != nil {
		log.Warn("Unable to lookup tx by txid; unable to convert txid %x to chainhash", "txid", txid)
	}

	tx, err := TBCFullNode.TxById(MainCtx, ch)
	if err != nil || tx == nil {
		log.Error("Unable to lookup tx by txid", "txid", fmt.Sprintf("%x", txid))
		return nil, nil
	}

	if outputIdx >= uint32(len(tx.TxOut)) {
		log.Warn(fmt.Sprintf("hVM call requested output %d but tx %x only has %d outputs", outputIdx, txid, len(tx.TxOut)))
		return nil, nil
	}
	resp := make([]byte, 0)

	out := tx.TxOut[outputIdx]

	resp = binary.BigEndian.AppendUint64(resp, uint64(out.Value))

	choppedOutputScript := make([]byte, 0)
	choppedOutputScript = append(choppedOutputScript, out.PkScript...)

	if len(choppedOutputScript) > int(maxOutputScriptSize) {
		choppedOutputScript = choppedOutputScript[0:maxOutputScriptSize]
	}

	pkScriptLength := len(out.PkScript)
	if pkScriptLength > math.MaxUint16 {
		pkScriptLength = math.MaxUint16
	}

	resp = binary.BigEndian.AppendUint16(resp, uint16(pkScriptLength))
	resp = append(resp, choppedOutputScript...)

	spentBool, err := TBCFullNode.ScriptHashAvailableToSpend(MainCtx, ch, outputIdx)
	if err != nil {
		log.Warn("Unable to lookup output spend status", "txid", txid, "err", err)
		return nil, nil
	}

	spent := byte(0)
	if spentBool {
		spent = byte(1)
	}
	resp = append(resp, spent)

	if isValidBlock(blockContext) {
		hvmQueryMap[k] = resp
	}

	return resp, nil
}

type btcTxGetInputWitness struct{}

func (c *btcTxGetInputWitness) Name() string {
	return "BTC TX Get Input Witness"
}

func (c *btcTxGetInputWitness) RequiredGas(input []byte) uint64 {
	// TODO: Gas based on returned size and/or enabled fields in future hVM version
	return params.BtcTxGetInputWitness
}

func (c *btcTxGetInputWitness) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) != BTC_TXID_LENGTH_BYTES+6 { // 32 bytes txid, 2 bytes for output index
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
			log.Debug(fmt.Sprintf("btcTxGetInputWitness returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	var txid = make([]byte, 32)
	copy(txid[0:32], input[0:32])
	slices.Reverse(txid)

	txidEnd := len(input) - 6
	inputIdx := (uint32(input[txidEnd+1]&0xFF) << 8) |
		uint32(input[txidEnd+2]&0xFF)
	inputWitnessIndex := (uint32(input[txidEnd+3]&0xFF) << 8) |
		uint32(input[txidEnd+4]&0xFF)
	maxWitnessLength := (uint32(input[txidEnd+5]&0xFF) << 8) |
		uint32(input[txidEnd+6]&0xFF)

	log.Debug(fmt.Sprintf("Looking up witness %d for input %d in txid %x", inputWitnessIndex, inputIdx, txid))

	ch := chainhash.Hash{}
	err := ch.SetBytes(txid)
	if err != nil {
		log.Warn("Unable to lookup tx by txid; unable to convert txid %x to chainhash", "txid", txid)
	}

	tx, err := TBCFullNode.TxById(MainCtx, ch)
	if err != nil || tx == nil {
		log.Error("Unable to lookup tx by txid", "txid", fmt.Sprintf("%x", txid))
		return nil, nil
	}

	if inputIdx >= uint32(len(tx.TxIn)) {
		log.Warn(fmt.Sprintf("hVM call requested input %d but tx %x only has %d inputs", inputIdx, txid, len(tx.TxIn)))
		return nil, nil
	}
	resp := make([]byte, 0)

	in := tx.TxIn[inputIdx]

	if in.Witness == nil || len(in.Witness) == 0 {
		return nil, nil // No witness data in transaction input
	}

	if inputWitnessIndex >= uint32(len(in.Witness)) {
		return nil, nil // No witness at requested index
	}

	choppedWitness := make([]byte, 0)
	choppedWitness = append(choppedWitness, in.Witness[inputWitnessIndex]...)

	if len(choppedWitness) > int(maxWitnessLength) {
		choppedWitness = choppedWitness[0:maxWitnessLength]
	}

	witnessLength := len(in.Witness[inputWitnessIndex])
	if witnessLength > math.MaxUint16 {
		witnessLength = math.MaxUint16
	}

	resp = binary.BigEndian.AppendUint16(resp, uint16(witnessLength))
	resp = append(resp, choppedWitness...)

	if isValidBlock(blockContext) {
		hvmQueryMap[k] = resp
	}

	return resp, nil
}

type btcTxByTxid struct{}

func (c *btcTxByTxid) Name() string {
	return "BTC TX by TXID"
}

func (c *btcTxByTxid) RequiredGas(input []byte) uint64 {
	// TODO: Gas based on returned size and/or enabled fields in future hVM version
	return params.BtcTxByTxid
}

func (c *btcTxByTxid) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) != BTC_TXID_LENGTH_BYTES+4 { // 4 bytes bitflag, 32 bytes txid. TODO: Allow 32-byte input (just TxID) and assume some default bitflag values?
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
			log.Trace(fmt.Sprintf("btcTxByTxid returning cached result for query of "+
				"%x in context %x, cached result=%x", input, blockContext, cachedResult))
			return cachedResult, nil
		}
	}

	var txid = make([]byte, 32)
	copy(txid[0:32], input[0:32])
	slices.Reverse(txid)

	log.Debug(fmt.Sprintf("Looking up txid %x", txid))

	bitflag1 := input[32]
	includeContainingBlock := bitflag1&(0x01<<6) != 0
	includeVersion := bitflag1&(0x01<<5) != 0
	includeSizes := bitflag1&(0x01<<4) != 0 // Size, stripped size
	includeLockTime := bitflag1&(0x01<<3) != 0
	includeInputs := bitflag1&(0x01<<2) != 0
	includeInputSource := bitflag1&(0x01<<1) != 0
	includeInputScriptSig := bitflag1&(0x01) != 0

	bitflag2 := input[33]
	includeInputSeq := bitflag2&(0x01<<7) != 0
	includeWitnessArraySize := bitflag1&(0x01<<6) != 0
	includeOutputs := bitflag2&(0x01<<5) != 0
	includeOutputScript := bitflag2&(0x01<<4) != 0
	includeUnspendableOutputs := bitflag2&(0x01<<3) != 0
	includeOutputSpent := bitflag2&(0x01<<2) != 0

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

	ch := chainhash.Hash{}
	err := ch.SetBytes(txid)
	if err != nil {
		log.Warn("Unable to lookup tx by txid; unable to convert txid %x to chainhash", "txid", txid)
	}

	tx, err := TBCFullNode.TxById(MainCtx, ch)
	if err != nil || tx == nil {
		log.Error("Unable to lookup tx by txid", "txid", fmt.Sprintf("%x", txid))
		return nil, nil
	}

	block, err := TBCFullNode.BlockHashByTxId(MainCtx, ch)
	if err != nil || block == nil {
		log.Error("Unable to lookup block containing tx by txid", "txid", fmt.Sprintf("%x", txid))
		return nil, nil
	}

	resp := make([]byte, 0)

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
		txInLen := len(tx.TxIn)
		if txInLen > math.MaxUint16 {
			txInLen = math.MaxUint16
		}

		resp = binary.BigEndian.AppendUint16(resp, uint16(txInLen))
		for count, in := range tx.TxIn {
			if count >= maxInputs {
				// Caller needs to check # of inputs compared to claimed length to detect inputs were chopped
				break
			}

			if includeWitnessArraySize {
				if in.Witness == nil || len(in.Witness) == 0 {
					resp = binary.BigEndian.AppendUint16(resp, uint16(0))
				} else {
					witnessElements := len(in.Witness)
					if witnessElements > math.MaxUint16 {
						// If caller sees 65535 witness elements, then it may have exactly that amount or more
						witnessElements = math.MaxUint16
					}
					resp = binary.BigEndian.AppendUint16(resp, uint16(witnessElements))
				}
			}

			// Always include input value - Review if this is desired behavior because of extra lookup cost
			prevIn := in.PreviousOutPoint
			pih := chainhash.Hash{}
			err := pih.SetBytes(prevIn.Hash[:])
			if err != nil {
				log.Warn("Unable to lookup Tx by Txid; unable to convert txid %x to chainhash!", "txid", txid)
				return nil, nil
			}

			sourceTx, err := TBCFullNode.TxById(MainCtx, pih)
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

				resp = binary.BigEndian.AppendUint32(resp, prevIn.Index)
			}
			if includeInputScriptSig {
				choppedInputScript := make([]byte, 0)
				choppedInputScript = append(choppedInputScript, in.SignatureScript...)
				if len(choppedInputScript) > maxInputScriptSigSize {
					choppedInputScript = choppedInputScript[0:maxInputScriptSigSize]
				}
				sigScriptLength := len(in.SignatureScript)
				if sigScriptLength > math.MaxUint16 {
					sigScriptLength = math.MaxUint16
				}
				resp = binary.BigEndian.AppendUint16(resp, uint16(sigScriptLength))
				resp = append(resp, choppedInputScript...)
			}

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

		if outLen > math.MaxUint16 {
			outLen = math.MaxUint16
		}

		resp = binary.BigEndian.AppendUint16(resp, uint16(outLen))
		for idx, out := range tx.TxOut {
			if count >= maxOutputs {
				// Caller needs to check # of outputs compared to claimed length to detect outputs were chopped
				break
			}
			isUnspendable := txscript.IsUnspendable(out.PkScript)
			if isUnspendable && !includeUnspendableOutputs {
				continue
			}
			resp = binary.BigEndian.AppendUint64(resp, uint64(out.Value))
			if includeOutputScript {
				choppedOutputScript := make([]byte, 0)
				choppedOutputScript = append(choppedOutputScript, out.PkScript...)
				if len(choppedOutputScript) > maxOutputScriptSize {
					choppedOutputScript = choppedOutputScript[0:maxOutputScriptSize]
				}

				pkScriptLen := len(out.PkScript)
				if pkScriptLen > math.MaxUint16 {
					pkScriptLen = math.MaxUint16
				}

				resp = binary.BigEndian.AppendUint16(resp, uint16(pkScriptLen))
				resp = append(resp, choppedOutputScript...)
			}

			if includeOutputSpent {
				spentBool, err := TBCFullNode.ScriptHashAvailableToSpend(MainCtx, ch, uint32(idx))

				if err != nil {
					log.Warn("Unable to lookup output spend status", "txid", txid, "err", err)
					// return nil, nil
					spentBool = false
				}

				spent := byte(0)
				if spentBool {
					// Could not look up Outpoint in UTXO table, therefore spent
					spent = byte(1)
				}

				resp = append(resp, spent)
			}
			count++
		}
	}

	log.Info("btcTxByTxid returning data", "returnedData", fmt.Sprintf("%x", resp))
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
	if bitutil.TestBytes(input[32:63]) || !crypto.ValidateSignatureValues(v, r, s, false) {
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

func (c *ecrecover) Name() string {
	return "ECREC"
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

func (c *sha256hash) Name() string {
	return "SHA256"
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

func (c *ripemd160hash) Name() string {
	return "RIPEMD160"
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

func (c *dataCopy) Name() string {
	return "ID"
}

// bigModExp implements a native big integer exponential modular operation.
type bigModExp struct {
	eip2565 bool
	eip7823 bool
	eip7883 bool
}

// byzantiumMultComplexity implements the bigModexp multComplexity formula, as defined in EIP-198.
//
//	def mult_complexity(x):
//		if x <= 64: return x ** 2
//		elif x <= 1024: return x ** 2 // 4 + 96 * x - 3072
//		else: return x ** 2 // 16 + 480 * x - 199680
//
// where is x is max(length_of_MODULUS, length_of_BASE)
// returns MaxUint64 if an overflow occurred.
func byzantiumMultComplexity(x uint64) uint64 {
	switch {
	case x <= 64:
		return x * x
	case x <= 1024:
		// x^2 / 4 + 96*x - 3072
		return x*x/4 + 96*x - 3072

	default:
		// For large x, use uint256 arithmetic to avoid overflow
		// x^2 / 16 + 480*x - 199680

		// xSqr = x^2 / 16
		carry, xSqr := bits.Mul64(x, x)
		if carry != 0 {
			return math.MaxUint64
		}
		xSqr = xSqr >> 4

		// Calculate 480 * x (can't overflow if x^2 didn't overflow)
		x480 := x * 480
		// Calculate 480 * x - 199680 (will not underflow, since x > 1024)
		x480 = x480 - 199680

		// xSqr + x480
		sum, carry := bits.Add64(xSqr, x480, 0)
		if carry != 0 {
			return math.MaxUint64
		}
		return sum
	}
}

// berlinMultComplexity implements the multiplication complexity formula for Berlin.
//
// def mult_complexity(x):
//
//	ceiling(x/8)^2
//
// where is x is max(length_of_MODULUS, length_of_BASE)
func berlinMultComplexity(x uint64) uint64 {
	// x = (x + 7) / 8
	x, carry := bits.Add64(x, 7, 0)
	if carry != 0 {
		return math.MaxUint64
	}
	x /= 8

	// x^2
	carry, x = bits.Mul64(x, x)
	if carry != 0 {
		return math.MaxUint64
	}
	return x
}

// osakaMultComplexity implements the multiplication complexity formula for Osaka.
//
// For x <= 32: returns 16
// For x > 32: returns 2 * ceiling(x/8)^2
func osakaMultComplexity(x uint64) uint64 {
	if x <= 32 {
		return 16
	}
	// For x > 32, return 2 * berlinMultComplexity(x)
	result := berlinMultComplexity(x)
	carry, result := bits.Mul64(result, 2)
	if carry != 0 {
		return math.MaxUint64
	}
	return result
}

// modexpIterationCount calculates the number of iterations for the modexp precompile.
// This is the adjusted exponent length used in gas calculation.
func modexpIterationCount(expLen uint64, expHead uint256.Int, multiplier uint64) uint64 {
	var iterationCount uint64

	// For large exponents (expLen > 32), add (expLen - 32) * multiplier
	if expLen > 32 {
		carry, count := bits.Mul64(expLen-32, multiplier)
		if carry > 0 {
			return math.MaxUint64
		}
		iterationCount = count
	}
	// Add the MSB position - 1 if expHead is non-zero
	if bitLen := expHead.BitLen(); bitLen > 0 {
		count, carry := bits.Add64(iterationCount, uint64(bitLen-1), 0)
		if carry > 0 {
			return math.MaxUint64
		}
		iterationCount = count
	}

	return max(iterationCount, 1)
}

// byzantiumModexpGas calculates the gas cost for the modexp precompile using Byzantium rules.
func byzantiumModexpGas(baseLen, expLen, modLen uint64, expHead uint256.Int) uint64 {
	const (
		multiplier = 8
		divisor    = 20
	)

	maxLen := max(baseLen, modLen)
	multComplexity := byzantiumMultComplexity(maxLen)
	if multComplexity == math.MaxUint64 {
		return math.MaxUint64
	}
	iterationCount := modexpIterationCount(expLen, expHead, multiplier)

	// Calculate gas: (multComplexity * iterationCount) / divisor
	carry, gas := bits.Mul64(iterationCount, multComplexity)
	gas /= divisor
	if carry != 0 {
		return math.MaxUint64
	}
	return gas
}

// berlinModexpGas calculates the gas cost for the modexp precompile using Berlin rules.
func berlinModexpGas(baseLen, expLen, modLen uint64, expHead uint256.Int) uint64 {
	const (
		multiplier = 8
		divisor    = 3
		minGas     = 200
	)

	maxLen := max(baseLen, modLen)
	multComplexity := berlinMultComplexity(maxLen)
	if multComplexity == math.MaxUint64 {
		return math.MaxUint64
	}
	iterationCount := modexpIterationCount(expLen, expHead, multiplier)

	// Calculate gas: (multComplexity * iterationCount) / divisor
	carry, gas := bits.Mul64(iterationCount, multComplexity)
	gas /= divisor
	if carry != 0 {
		return math.MaxUint64
	}
	return max(gas, minGas)
}

// osakaModexpGas calculates the gas cost for the modexp precompile using Osaka rules.
func osakaModexpGas(baseLen, expLen, modLen uint64, expHead uint256.Int) uint64 {
	const (
		multiplier = 16
		minGas     = 500
	)

	maxLen := max(baseLen, modLen)
	multComplexity := osakaMultComplexity(maxLen)
	if multComplexity == math.MaxUint64 {
		return math.MaxUint64
	}
	iterationCount := modexpIterationCount(expLen, expHead, multiplier)

	// Calculate gas: multComplexity * iterationCount
	carry, gas := bits.Mul64(iterationCount, multComplexity)
	if carry != 0 {
		return math.MaxUint64
	}
	return max(gas, minGas)
}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bigModExp) RequiredGas(input []byte) uint64 {
	// Parse input lengths
	baseLenBig := new(uint256.Int).SetBytes(getData(input, 0, 32))
	expLenBig := new(uint256.Int).SetBytes(getData(input, 32, 32))
	modLenBig := new(uint256.Int).SetBytes(getData(input, 64, 32))

	// Convert to uint64, capping at max value
	baseLen := baseLenBig.Uint64()
	if !baseLenBig.IsUint64() {
		baseLen = math.MaxUint64
	}
	expLen := expLenBig.Uint64()
	if !expLenBig.IsUint64() {
		expLen = math.MaxUint64
	}
	modLen := modLenBig.Uint64()
	if !modLenBig.IsUint64() {
		modLen = math.MaxUint64
	}

	// Skip the header
	if len(input) > 96 {
		input = input[96:]
	} else {
		input = input[:0]
	}

	// Retrieve the head 32 bytes of exp for the adjusted exponent length
	var expHead uint256.Int
	if uint64(len(input)) > baseLen {
		if expLen > 32 {
			expHead.SetBytes(getData(input, baseLen, 32))
		} else {
			// TODO: Check that if expLen < baseLen, then getData will return an empty slice
			expHead.SetBytes(getData(input, baseLen, expLen))
		}
	}

	// Choose the appropriate gas calculation based on the EIP flags
	if c.eip7883 {
		return osakaModexpGas(baseLen, expLen, modLen, expHead)
	} else if c.eip2565 {
		return berlinModexpGas(baseLen, expLen, modLen, expHead)
	} else {
		return byzantiumModexpGas(baseLen, expLen, modLen, expHead)
	}
}

func (c *bigModExp) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	var (
		baseLenBig       = new(big.Int).SetBytes(getData(input, 0, 32))
		expLenBig        = new(big.Int).SetBytes(getData(input, 32, 32))
		modLenBig        = new(big.Int).SetBytes(getData(input, 64, 32))
		baseLen          = baseLenBig.Uint64()
		expLen           = expLenBig.Uint64()
		modLen           = modLenBig.Uint64()
		inputLenOverflow = max(baseLenBig.BitLen(), expLenBig.BitLen(), modLenBig.BitLen()) > 64
	)
	if len(input) > 96 {
		input = input[96:]
	} else {
		input = input[:0]
	}

	// enforce size cap for inputs
	if c.eip7823 && (inputLenOverflow || max(baseLen, expLen, modLen) > 1024) {
		return nil, errors.New("one or more of base/exponent/modulus length exceeded 1024 bytes")
	}
	// Handle a special case when both the base and mod length is zero
	if baseLen == 0 && modLen == 0 {
		return []byte{}, nil
	}
	// Retrieve the operands and execute the exponentiation
	var (
		base = new(patched_big.Int).SetBytes(getData(input, 0, baseLen))
		exp  = new(patched_big.Int).SetBytes(getData(input, baseLen, expLen))
		mod  = new(patched_big.Int).SetBytes(getData(input, baseLen+expLen, modLen))
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

func (c *bigModExp) Name() string {
	return "MODEXP"
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

// bn256AddIstanbul implements a native elliptic curve point addition conforming to
// Istanbul consensus rules.
type bn256AddIstanbul struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bn256AddIstanbul) RequiredGas(input []byte) uint64 {
	return params.Bn256AddGasIstanbul
}

func (c *bn256AddIstanbul) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	return runBn256Add(input)
}

func (c *bn256AddIstanbul) Name() string {
	return "BN254_ADD"
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

func (c *bn256AddByzantium) Name() string {
	return "BN254_ADD"
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

func (c *bn256ScalarMulIstanbul) Name() string {
	return "BN254_MUL"
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

func (c *bn256ScalarMulByzantium) Name() string {
	return "BN254_MUL"
}

var (
	// true32Byte is returned if the bn256 pairing check succeeds.
	true32Byte = []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1}

	// false32Byte is returned if the bn256 pairing check fails.
	false32Byte = make([]byte, 32)

	// errBadPairingInput is returned if the bn256 pairing input is invalid.
	errBadPairingInput = errors.New("bad elliptic curve pairing size")

	// errBadPairingInputSize is returned if the bn256 pairing input size is invalid.
	errBadPairingInputSize = errors.New("bad elliptic curve pairing input size")
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

// bn256PairingGranite implements a pairing pre-compile for the bn256 curve
// conforming to Granite consensus rules.
type bn256PairingGranite struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bn256PairingGranite) RequiredGas(input []byte) uint64 {
	return new(bn256PairingIstanbul).RequiredGas(input)
}

func (c *bn256PairingGranite) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) > int(params.Bn256PairingMaxInputSizeGranite) {
		return nil, errBadPairingInputSize
	}
	return runBn256Pairing(input)
}

func (c *bn256PairingGranite) Name() string {
	return "BN254_PAIRING"
}

type bn256PairingJovian struct{}

func (c *bn256PairingJovian) RequiredGas(input []byte) uint64 {
	return new(bn256PairingIstanbul).RequiredGas(input)
}

func (c *bn256PairingJovian) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) > int(params.Bn256PairingMaxInputSizeJovian) {
		return nil, errBadPairingInputSize
	}
	return runBn256Pairing(input)
}

func (c *bn256PairingJovian) Name() string {
	return "BN254_PAIRING"
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

func (c *bn256PairingIstanbul) Name() string {
	return "BN254_PAIRING"
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

func (c *bn256PairingByzantium) Name() string {
	return "BN254_PAIRING"
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

func (c *blake2F) Name() string {
	return "BLAKE2F"
}

var (
	errBLS12381InvalidInputLength          = errors.New("invalid input length")
	errBLS12381InvalidFieldElementTopBytes = errors.New("invalid field element top bytes")
	errBLS12381G1PointSubgroup             = errors.New("g1 point is not on correct subgroup")
	errBLS12381G2PointSubgroup             = errors.New("g2 point is not on correct subgroup")
	errBLS12381MaxG1Size                   = errors.New("g1 msm input size exceeds maximum")
	errBLS12381MaxG2Size                   = errors.New("g2 msm input size exceeds maximum")
	errBLS12381MaxPairingSize              = errors.New("pairing input size exceeds maximum")
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
	var p0, p1 *bls12381.G1Affine

	// Decode G1 point p_0
	if p0, err = decodePointG1(input[:128]); err != nil {
		return nil, err
	}
	// Decode G1 point p_1
	if p1, err = decodePointG1(input[128:]); err != nil {
		return nil, err
	}

	// No need to check the subgroup here, as specified by EIP-2537

	// Compute r = p_0 + p_1
	p0.Add(p0, p1)

	// Encode the G1 point result into 128 bytes
	return encodePointG1(p0), nil
}

type bls12381G1MultiExpIsthmus struct {
}

func (c *bls12381G1MultiExpIsthmus) RequiredGas(input []byte) uint64 {
	return new(bls12381G1MultiExp).RequiredGas(input)
}

func (c *bls12381G1MultiExpIsthmus) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) > int(params.Bls12381G1MulMaxInputSizeIsthmus) {
		return nil, errBLS12381MaxG1Size
	}

	return new(bls12381G1MultiExp).Run(input, blockContext)
}
func (c *bls12381G1MultiExpIsthmus) Name() string {
	return "BLS12_G1MSM"
}

type bls12381G1MultiExpJovian struct {
}

func (c *bls12381G1MultiExpJovian) RequiredGas(input []byte) uint64 {
	return new(bls12381G1MultiExp).RequiredGas(input)
}

func (c *bls12381G1MultiExpJovian) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) > int(params.Bls12381G1MulMaxInputSizeJovian) {
		return nil, errBLS12381MaxG1Size
	}

	return new(bls12381G1MultiExp).Run(input, blockContext)
}

func (c *bls12381G1MultiExpJovian) Name() string {
	return "BLS12_G1MSM"
}

// bls12381G1MultiExp implements EIP-2537 G1MultiExp precompile for Prague (no size limits).
func (c *bls12381G1Add) Name() string {
	return "BLS12_G1ADD"
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
	if dLen := len(params.Bls12381G1MultiExpDiscountTable); k < dLen {
		discount = params.Bls12381G1MultiExpDiscountTable[k-1]
	} else {
		discount = params.Bls12381G1MultiExpDiscountTable[dLen-1]
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
	points := make([]bls12381.G1Affine, k)
	scalars := make([]fr.Element, k)

	// Decode point scalar pairs
	for i := 0; i < k; i++ {
		off := 160 * i
		t0, t1, t2 := off, off+128, off+160
		// Decode G1 point
		p, err := decodePointG1(input[t0:t1])
		if err != nil {
			return nil, err
		}
		// 'point is on curve' check already done,
		// Here we need to apply subgroup checks.
		if !p.IsInSubGroup() {
			return nil, errBLS12381G1PointSubgroup
		}
		points[i] = *p
		// Decode scalar value
		scalars[i] = *new(fr.Element).SetBytes(input[t1:t2])
	}

	// Compute r = e_0 * p_0 + e_1 * p_1 + ... + e_(k-1) * p_(k-1)
	r := new(bls12381.G1Affine)
	r.MultiExp(points, scalars, ecc.MultiExpConfig{})

	// Encode the G1 point to 128 bytes
	return encodePointG1(r), nil
}

func (c *bls12381G1MultiExp) Name() string {
	return "BLS12_G1MSM"
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
	var p0, p1 *bls12381.G2Affine

	// Decode G2 point p_0
	if p0, err = decodePointG2(input[:256]); err != nil {
		return nil, err
	}
	// Decode G2 point p_1
	if p1, err = decodePointG2(input[256:]); err != nil {
		return nil, err
	}

	// No need to check the subgroup here, as specified by EIP-2537

	// Compute r = p_0 + p_1
	r := new(bls12381.G2Affine)
	r.Add(p0, p1)

	// Encode the G2 point into 256 bytes
	return encodePointG2(r), nil
}

func (c *bls12381G2Add) Name() string {
	return "BLS12_G2ADD"
}

type bls12381G2MultiExpIsthmus struct {
}

func (c *bls12381G2MultiExpIsthmus) RequiredGas(input []byte) uint64 {
	return new(bls12381G2MultiExp).RequiredGas(input)
}

func (c *bls12381G2MultiExpIsthmus) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) > int(params.Bls12381G2MulMaxInputSizeIsthmus) {
		return nil, errBLS12381MaxG2Size
	}

	return new(bls12381G2MultiExp).Run(input, blockContext)
}

func (c *bls12381G2MultiExpIsthmus) Name() string {
	return "BLS12_G2MSM"
}

type bls12381G2MultiExpJovian struct {
}

func (c *bls12381G2MultiExpJovian) RequiredGas(input []byte) uint64 {
	return new(bls12381G2MultiExp).RequiredGas(input)
}

func (c *bls12381G2MultiExpJovian) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) > int(params.Bls12381G2MulMaxInputSizeJovian) {
		return nil, errBLS12381MaxG2Size
	}

	return new(bls12381G2MultiExp).Run(input, blockContext)
}

func (c *bls12381G2MultiExpJovian) Name() string {
	return "BLS12_G2MSM"
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
	if dLen := len(params.Bls12381G2MultiExpDiscountTable); k < dLen {
		discount = params.Bls12381G2MultiExpDiscountTable[k-1]
	} else {
		discount = params.Bls12381G2MultiExpDiscountTable[dLen-1]
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
	points := make([]bls12381.G2Affine, k)
	scalars := make([]fr.Element, k)

	// Decode point scalar pairs
	for i := 0; i < k; i++ {
		off := 288 * i
		t0, t1, t2 := off, off+256, off+288
		// Decode G2 point
		p, err := decodePointG2(input[t0:t1])
		if err != nil {
			return nil, err
		}
		// 'point is on curve' check already done,
		// Here we need to apply subgroup checks.
		if !p.IsInSubGroup() {
			return nil, errBLS12381G2PointSubgroup
		}
		points[i] = *p
		// Decode scalar value
		scalars[i] = *new(fr.Element).SetBytes(input[t1:t2])
	}

	// Compute r = e_0 * p_0 + e_1 * p_1 + ... + e_(k-1) * p_(k-1)
	r := new(bls12381.G2Affine)
	r.MultiExp(points, scalars, ecc.MultiExpConfig{})

	// Encode the G2 point to 256 bytes.
	return encodePointG2(r), nil
}

func (c *bls12381G2MultiExp) Name() string {
	return "BLS12_G2MSM"
}

type bls12381PairingIsthmus struct {
}

func (c *bls12381PairingIsthmus) RequiredGas(input []byte) uint64 {
	return new(bls12381Pairing).RequiredGas(input)
}

func (c *bls12381PairingIsthmus) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) > int(params.Bls12381PairingMaxInputSizeIsthmus) {
		return nil, errBLS12381MaxPairingSize
	}

	return new(bls12381Pairing).Run(input, blockContext)
}

func (c *bls12381PairingIsthmus) Name() string {
	return "BLS12_PAIRING_CHECK"
}

type bls12381PairingJovian struct {
}

func (c *bls12381PairingJovian) RequiredGas(input []byte) uint64 {
	return new(bls12381Pairing).RequiredGas(input)
}

func (c *bls12381PairingJovian) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	if len(input) > int(params.Bls12381PairingMaxInputSizeJovian) {
		return nil, errBLS12381MaxPairingSize
	}

	return new(bls12381Pairing).Run(input, blockContext)
}

func (c *bls12381PairingJovian) Name() string {
	return "BLS12_PAIRING_CHECK"
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

	var (
		p []bls12381.G1Affine
		q []bls12381.G2Affine
	)

	// Decode pairs
	for i := 0; i < k; i++ {
		off := 384 * i
		t0, t1, t2 := off, off+128, off+384

		// Decode G1 point
		p1, err := decodePointG1(input[t0:t1])
		if err != nil {
			return nil, err
		}
		// Decode G2 point
		p2, err := decodePointG2(input[t1:t2])
		if err != nil {
			return nil, err
		}

		// 'point is on curve' check already done,
		// Here we need to apply subgroup checks.
		if !p1.IsInSubGroup() {
			return nil, errBLS12381G1PointSubgroup
		}
		if !p2.IsInSubGroup() {
			return nil, errBLS12381G2PointSubgroup
		}
		p = append(p, *p1)
		q = append(q, *p2)
	}
	// Prepare 32 byte output
	out := make([]byte, 32)

	// Compute pairing and set the result
	ok, err := bls12381.PairingCheck(p, q)
	if err == nil && ok {
		out[31] = 1
	}
	return out, nil
}

func (c *bls12381Pairing) Name() string {
	return "BLS12_PAIRING_CHECK"
}

func decodePointG1(in []byte) (*bls12381.G1Affine, error) {
	if len(in) != 128 {
		return nil, errors.New("invalid g1 point length")
	}
	// decode x
	x, err := decodeBLS12381FieldElement(in[:64])
	if err != nil {
		return nil, err
	}
	// decode y
	y, err := decodeBLS12381FieldElement(in[64:])
	if err != nil {
		return nil, err
	}
	elem := bls12381.G1Affine{X: x, Y: y}
	if !elem.IsOnCurve() {
		return nil, errors.New("invalid point: not on curve")
	}

	return &elem, nil
}

// decodePointG2 given encoded (x, y) coordinates in 256 bytes returns a valid G2 Point.
func decodePointG2(in []byte) (*bls12381.G2Affine, error) {
	if len(in) != 256 {
		return nil, errors.New("invalid g2 point length")
	}
	x0, err := decodeBLS12381FieldElement(in[:64])
	if err != nil {
		return nil, err
	}
	x1, err := decodeBLS12381FieldElement(in[64:128])
	if err != nil {
		return nil, err
	}
	y0, err := decodeBLS12381FieldElement(in[128:192])
	if err != nil {
		return nil, err
	}
	y1, err := decodeBLS12381FieldElement(in[192:])
	if err != nil {
		return nil, err
	}

	p := bls12381.G2Affine{X: bls12381.E2{A0: x0, A1: x1}, Y: bls12381.E2{A0: y0, A1: y1}}
	if !p.IsOnCurve() {
		return nil, errors.New("invalid point: not on curve")
	}
	return &p, err
}

// decodeBLS12381FieldElement decodes BLS12-381 elliptic curve field element.
// Removes top 16 bytes of 64 byte input.
func decodeBLS12381FieldElement(in []byte) (fp.Element, error) {
	if len(in) != 64 {
		return fp.Element{}, errors.New("invalid field element length")
	}
	// check top bytes
	for i := 0; i < 16; i++ {
		if in[i] != byte(0x00) {
			return fp.Element{}, errBLS12381InvalidFieldElementTopBytes
		}
	}
	var res [48]byte
	copy(res[:], in[16:])

	return fp.BigEndian.Element(&res)
}

// encodePointG1 encodes a point into 128 bytes.
func encodePointG1(p *bls12381.G1Affine) []byte {
	out := make([]byte, 128)
	fp.BigEndian.PutElement((*[fp.Bytes]byte)(out[16:]), p.X)
	fp.BigEndian.PutElement((*[fp.Bytes]byte)(out[64+16:]), p.Y)
	return out
}

// encodePointG2 encodes a point into 256 bytes.
func encodePointG2(p *bls12381.G2Affine) []byte {
	out := make([]byte, 256)
	// encode x
	fp.BigEndian.PutElement((*[fp.Bytes]byte)(out[16:16+48]), p.X.A0)
	fp.BigEndian.PutElement((*[fp.Bytes]byte)(out[80:80+48]), p.X.A1)
	// encode y
	fp.BigEndian.PutElement((*[fp.Bytes]byte)(out[144:144+48]), p.Y.A0)
	fp.BigEndian.PutElement((*[fp.Bytes]byte)(out[208:208+48]), p.Y.A1)
	return out
}

// bls12381MapG1 implements EIP-2537 MapG1 precompile.
type bls12381MapG1 struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381MapG1) RequiredGas(input []byte) uint64 {
	return params.Bls12381MapG1Gas
}

func (c *bls12381MapG1) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 Map_To_G1 precompile.
	// > Field-to-curve call expects an `64` bytes input that is interpreted as an element of the base field.
	// > Output of this call is `128` bytes and is G1 point following respective encoding rules.
	if len(input) != 64 {
		return nil, errBLS12381InvalidInputLength
	}

	// Decode input field element
	fe, err := decodeBLS12381FieldElement(input)
	if err != nil {
		return nil, err
	}

	// Compute mapping
	r := bls12381.MapToG1(fe)

	// Encode the G1 point to 128 bytes
	return encodePointG1(&r), nil
}

func (c *bls12381MapG1) Name() string {
	return "BLS12_MAP_FP_TO_G1"
}

// bls12381MapG2 implements EIP-2537 MapG2 precompile.
type bls12381MapG2 struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (c *bls12381MapG2) RequiredGas(input []byte) uint64 {
	return params.Bls12381MapG2Gas
}

func (c *bls12381MapG2) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Implements EIP-2537 Map_FP2_TO_G2 precompile logic.
	// > Field-to-curve call expects an `128` bytes input that is interpreted as an element of the quadratic extension field.
	// > Output of this call is `256` bytes and is G2 point following respective encoding rules.
	if len(input) != 128 {
		return nil, errBLS12381InvalidInputLength
	}

	// Decode input field element
	c0, err := decodeBLS12381FieldElement(input[:64])
	if err != nil {
		return nil, err
	}
	c1, err := decodeBLS12381FieldElement(input[64:])
	if err != nil {
		return nil, err
	}

	// Compute mapping
	r := bls12381.MapToG2(bls12381.E2{A0: c0, A1: c1})

	// Encode the G2 point to 256 bytes
	return encodePointG2(&r), nil
}

func (c *bls12381MapG2) Name() string {
	return "BLS12_MAP_FP2_TO_G2"
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

func (b *kzgPointEvaluation) Name() string {
	return "KZG_POINT_EVALUATION"
}

// kZGToVersionedHash implements kzg_to_versioned_hash from EIP-4844
func kZGToVersionedHash(kzg kzg4844.Commitment) common.Hash {
	h := sha256.Sum256(kzg[:])
	h[0] = blobCommitmentVersionKZG

	return h
}

// P256VERIFY (secp256r1 signature verification)
// implemented as a native contract.
//
// This is used in the OP Stack from Fjord until the implementation of Ethereum's Osaka fork, after
// which the p256Verify precompile is used instead to maintain Ethereum equivalence.
type p256VerifyFjord struct {
	p256Verify
}

// RequiredGas returns the gas required to execute the precompiled contract
func (c *p256VerifyFjord) RequiredGas(input []byte) uint64 {
	return params.P256VerifyGasFjord
}

// P256VERIFY (secp256r1 signature verification)
// implemented as a native contract
type p256Verify struct{}

// RequiredGas returns the gas required to execute the precompiled contract
func (c *p256Verify) RequiredGas(input []byte) uint64 {
	return params.P256VerifyGas
}

// Run executes the precompiled contract with given 160 bytes of param, returning the output and the used gas
func (c *p256Verify) Run(input []byte, blockContext common.Hash) ([]byte, error) {
	// Required input length is 160 bytes
	const p256VerifyInputLength = 160
	if len(input) != p256VerifyInputLength {
		return nil, nil
	}

	// Extract hash, r, s, x, y from the input.
	hash := input[0:32]
	r, s := new(big.Int).SetBytes(input[32:64]), new(big.Int).SetBytes(input[64:96])
	x, y := new(big.Int).SetBytes(input[96:128]), new(big.Int).SetBytes(input[128:160])

	// Verify the signature.
	if secp256r1.Verify(hash, r, s, x, y) {
		return true32Byte, nil
	}
	return nil, nil
}

func (c *p256Verify) Name() string {
	return "P256VERIFY"
}
