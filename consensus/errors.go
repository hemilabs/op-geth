// Copyright 2017 The go-ethereum Authors
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

package consensus

import "errors"

var (
	// ErrUnknownAncestor is returned when validating a block requires an ancestor
	// that is unknown.
	ErrUnknownAncestor = errors.New("unknown ancestor")

	// ErrPrunedAncestor is returned when validating a block requires an ancestor
	// that is known, but the state of which is not available.
	ErrPrunedAncestor = errors.New("pruned ancestor")

	// ErrFutureBlock is returned when a block's timestamp is in the future according
	// to the current node.
	ErrFutureBlock = errors.New("block in the future")

	// ErrInvalidNumber is returned if a block's number doesn't equal its parent's
	// plus one.
	ErrInvalidNumber = errors.New("invalid block number")

	// ErrInvalidTerminalBlock is returned if a block is invalid wrt. the terminal
	// total difficulty.
	ErrInvalidTerminalBlock = errors.New("invalid terminal block")

	// ErrMissingBTCFullBlocks is returned if a block contains an hVM state transition
	// that requires indexing over blocks that the full TBC node does not (yet) have
	ErrMissingBTCFullBlocks = errors.New("missing btc full blocks")

	// ErrInvalidHVMBlockFormat is returned if a block which should have hVM Phase 0 active
	// is formatted in a way which makes it internally invalid (data of block itself
	// is the problem, not predicated on contextual hVM state)
	ErrInvalidHVMBlockFormat = errors.New("invalid hvm block format")

	// ErrCorruptHVMHeaderOnlyModeState is returned if an error occurs which indicates
	// that the header-only lightweight TBC node used by hVM is likely in a corrupted
	// state which could be recovered by rebuilding it.
	ErrCorruptHVMHeaderOnlyModeState = errors.New("corrupt hvm header only mode state")

	// ErrInvalidHVMHeaders is returned if a block contains a Bitcoin Attributes Deposited
	// transaction that attempts to add BTC headers which don't fit on the previous HVM
	// lightweight view of Bitcoin consensus
	ErrInvalidHVMHeaders = errors.New("invalid hvm headers")

	// ErrBadTraversalGeometry is returned if moving from one state to another cannot
	// find the expected path or the actual path is not expected (such as a reorg in a
	// function that should only be called for state transitions between states without
	// a reorg).
	ErrBadTraversalGeometry = errors.New("bad traversal geometry")

	// ErrFullTBCMissingFullBTCBlock is returned when the full TBC node cannot be advanced
	// to the requested state as it is missing one or more full blocks required to do
	// so. This error is generally temporary, and either a forced refetch or waiting
	// for TBC to receive the block from peers normally will allow the same progression
	// to occur correctly in the future.
	ErrFullTBCMissingFullBTCBlock = errors.New("missing full btc block")

	// ErrFullTBCMissingBTCHeader is returned when the full TBC node cannot be advanced
	// to the requested state as it is missing one or more block headers required to do so.
	// This error can be temporary and resolve itself automatically as TBC full node
	// continues to sync, which will allow the sama progression to occur correctly in the future.
	ErrFullTBCMissingBTCHeader = errors.New("missing btc header in full tbc")
)
