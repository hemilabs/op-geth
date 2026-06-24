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

package vm

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/ethereum/go-ethereum/common"
)

// BlockAvailableByCommonHash is a best-effort peer-fetch helper (not a consensus path), so when the full
// node is not initialized it must degrade to "available" (skip the futile peer request) rather than
// log.Crit-ing like the precompiles or nil-dereferencing TBCFullNode. This pins that guard against a
// true->false flip or its removal.
func TestBlockAvailableByCommonHashNilFullNode(t *testing.T) {
	orig := TBCFullNode
	TBCFullNode = nil
	defer func() { TBCFullNode = orig }()

	var available bool
	require.NotPanics(t, func() {
		available = BlockAvailableByCommonHash(common.Hash{0x01})
	}, "must not nil-deref TBCFullNode when the full node is not initialized")
	require.True(t, available, "with no full node, the helper must return true (skip the peer request), not false")
}
