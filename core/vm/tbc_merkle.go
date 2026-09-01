// Copyright 2026 The go-ethereum Authors
// Copyright 2026 Hemi Labs, Inc.
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
	"errors"
	"fmt"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
)

// ErrBTCBlockMerkleMismatch is returned by CheckBTCBlockMerkleRoot when a block body's transactions do
// not hash to the merkle root committed in the block header.
var ErrBTCBlockMerkleMismatch = errors.New("btc block body does not match header merkle root")

// ErrBTCBlockDuplicateTx is returned by CheckBTCBlockMerkleRoot when a block body contains the same
// transaction twice. Such a body is consensus-invalid in Bitcoin but, via the CVE-2012-2459 merkle
// malleability, hashes to the SAME root as the genuine block, so it would otherwise pass the merkle
// binding below.
var ErrBTCBlockDuplicateTx = errors.New("btc block contains a duplicate transaction")

// CheckBTCBlockMerkleRoot verifies that the transactions in a Bitcoin block body hash to the merkle
// root committed in the block's header, reusing btcd's EXACT (txid-based, non-witness) merkle routine
// so it cannot drift from Bitcoin's consensus rule.
//
// This binds a gossiped block body to its header's committed merkle root before the body is stored, so a
// body of substituted transactions cannot be admitted under a real consensus-chain header hash. Because
// the header commits to the merkle root and the root is a cryptographic hash over the txids, a body that
// passes this check is the genuine body of that header — a peer cannot substitute transactions without
// changing the root and thus the header hash.
//
// It also rejects a body whose first transaction is not a coinbase (closing the 64-byte leaf/node ambiguity.
//
// It is otherwise NOT a full block sanity check: it does not re-verify PoW (done separately by
// CheckBTCHeaderPoW), nor sizes, nor timestamps, nor any coinbase property BEYOND "txs[0] is a
// coinbase" — not its script length, not its value, not that there is exactly one.
//
// Returns nil if the body matches the header; ErrBTCBlockMerkleMismatch on a non-coinbase first
// transaction or (wrapped with both roots) on a root mismatch; ErrBTCBlockDuplicateTx on a repeated transaction; and a plain error for a structurally
// unusable body (nil block, or zero transactions — a real Bitcoin block always carries at least the
// coinbase, and the merkle routine is undefined for an empty transaction set).
func CheckBTCBlockMerkleRoot(block *wire.MsgBlock) error {
	if block == nil {
		return errors.New("btc block is nil")
	}
	if len(block.Transactions) == 0 {
		return errors.New("btc block has no transactions")
	}
	txs := btcutil.NewBlock(block).Transactions()
	// Require a coinbase first.
	if !blockchain.IsCoinBase(txs[0]) {
		return fmt.Errorf("%w: first transaction is not a coinbase", ErrBTCBlockMerkleMismatch)
	}
	// Reject duplicate transactions. A body that repeats a tx hashes to the SAME merkle root as the
	// genuine block (CVE-2012-2459), so it would pass the binding below; it is consensus-invalid in
	// Bitcoin and must be rejected here.
	seen := make(map[chainhash.Hash]struct{}, len(txs))
	for _, tx := range txs {
		if _, dup := seen[*tx.Hash()]; dup {
			return fmt.Errorf("%w: %s", ErrBTCBlockDuplicateTx, tx.Hash())
		}
		seen[*tx.Hash()] = struct{}{}
	}
	// witness=false: the header's MerkleRoot commits to the txid-based tree (the witness merkle root is
	// committed separately in the coinbase, not in the header).
	got := blockchain.CalcMerkleRoot(txs, false)
	want := block.Header.MerkleRoot
	if !got.IsEqual(&want) {
		return fmt.Errorf("%w: header %s, computed %s", ErrBTCBlockMerkleMismatch, want, got)
	}
	return nil
}
