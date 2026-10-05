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

package rawdb

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/core/types"
)

// TestWriteBadBlockDiscardsUndecodableHistory checks that a stored bad block whose
// header cannot be decoded back from RLP (here: slotNumber set while the preceding
// optional blockAccessListHash is nil, which encodes an empty placeholder that does
// not decode into a hash) is discarded instead of crashing the node on the next
// WriteBadBlock call, matching upstream go-ethereum.
func TestWriteBadBlockDiscardsUndecodableHistory(t *testing.T) {
	db := NewMemoryDatabase()
	slot := uint64(7)
	poison := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(1), Difficulty: big.NewInt(0), Extra: []byte{}, SlotNumber: &slot})
	WriteBadBlock(db, poison)
	if blocks := ReadAllBadBlocks(db); len(blocks) != 0 {
		t.Fatalf("expected the undecodable history to read back as empty, got %d entries", len(blocks))
	}
	// Must not log.Crit (which exits the process); the poisoned history is replaced.
	good := types.NewBlockWithHeader(&types.Header{Number: big.NewInt(2), Difficulty: big.NewInt(0), Extra: []byte{}})
	WriteBadBlock(db, good)
	blocks := ReadAllBadBlocks(db)
	if len(blocks) != 1 || blocks[0].Hash() != good.Hash() {
		t.Fatalf("expected exactly the new bad block to be stored, got %d entries", len(blocks))
	}
}
