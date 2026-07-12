// Copyright 2024 The go-ethereum Authors
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

// Context-free proof-of-work check for Bitcoin headers entering the hVM lightweight
// consensus view. The contextual-difficulty validator (tbc_difficulty.go) checks that a header's Bits is
// correct per Bitcoin's retarget schedule; this check additionally verifies that the header actually did
// the work its Bits claim, by requiring hash <= target (target in the valid [1, PowLimit] range) —
// reusing btcd's exact consensus routine. Being context-free (needs only the header), it is not subject
// to the effective-genesis floor defer — the caller enforces it on every header in an enforced batch.

import (
	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/wire"
)

// CheckBTCHeaderBatchPoWForNetwork verifies the proof-of-work of every header in the batch against the
// chain params for the given TBC network name (the caller passes the lightweight node's own configured
// network, matching ValidateBTCHeaderBatchForNetwork). Returns the first failure as a btcd RuleError
// (ErrHighHash for an unmet target, ErrUnexpectedDifficulty for an out-of-range target), which the caller
// maps to the same consensus reject as a contextual RuleError. An unknown network or nil header fails
// closed to ErrBTCHeaderContextUnavailable (recoverable; never a silent accept).
func CheckBTCHeaderBatchPoWForNetwork(network string, headers []*wire.BlockHeader) error {
	params, err := paramsForNetwork(network)
	if err != nil {
		return ErrBTCHeaderContextUnavailable
	}
	for _, h := range headers {
		if e := checkBTCHeaderPoWWith(h, params); e != nil {
			return e
		}
	}
	return nil
}

// CheckBTCHeaderPoW verifies a single header's proof-of-work (hash <= target, target in the valid
// [1, PowLimit] range) against the full node's configured chain params — the same global tbcChainParams
// that ValidateBTCHeaderContext uses for the gossip-ingest path. Context-free (needs only the header), so
// it applies to every gossiped header regardless of the effective-genesis floor. Returns nil on valid
// PoW, a btcd RuleError on a genuine PoW failure (forged-Bits/zero-PoW), or
// ErrBTCHeaderContextUnavailable when params are not yet configured (fail-closed-to-skip — the caller
// must not treat this as a PoW failure or drop the header on it). Mirrors ValidateBTCHeaderContext.
func CheckBTCHeaderPoW(hdr *wire.BlockHeader) error {
	if hdr == nil || tbcChainParams == nil {
		return ErrBTCHeaderContextUnavailable
	}
	return checkBTCHeaderPoWWith(hdr, tbcChainParams)
}

// checkBTCHeaderPoWWith drives btcd's exact proof-of-work check (via the exported CheckProofOfWork, which
// reads only MsgBlock().Header) by wrapping the header in a header-only block. The exported wrapper always
// performs the hash<=target check. Split out so tests inject params directly (mirroring the contextual validator
// split). A nil header/params fails closed.
func checkBTCHeaderPoWWith(hdr *wire.BlockHeader, params *chaincfg.Params) error {
	if hdr == nil || params == nil {
		return ErrBTCHeaderContextUnavailable
	}
	return blockchain.CheckProofOfWork(btcutil.NewBlock(&wire.MsgBlock{Header: *hdr}), params.PowLimit)
}
