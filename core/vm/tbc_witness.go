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

// In the current version of op-geth+tbc, witness data is not used and should never be stored/used.
// A future network upgrade will add witness support at which point this code can be removed.

package vm

import (
	"context"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/metrics"
	"golang.org/x/time/rate"
)

// hvmWitnessObservedCounter counts transactions read out of the embedded full node that carried
// witness data. On a store filled only from Bitcoin P2P this is always zero, because TBC never
// solicits witness bytes.
var hvmWitnessObservedCounter = metrics.NewRegisteredCounter("vm/hvm/btc/witness_observed", nil)

// witnessObservedLogLimiter throttles the per-observation Warn. Same shape and budget as the hVM
// gossip reject limiters in eth/protocols/eth/handlers.go.
var witnessObservedLogLimiter = rate.NewLimiter(rate.Every(5*time.Second), 4)

// txByIdNoWitness fetches a Bitcoin transaction from the embedded full node and returns it with all
// input witness data removed, so hVM precompile output cannot be influenced by witness bytes which
// are in the database for any reason.
//
// On a witness-free store this is a no-op: the returned transaction is the very pointer
// TBCFullNode.TxById returned.
func txByIdNoWitness(ctx context.Context, txId chainhash.Hash) (*wire.MsgTx, error) {
	tx, err := TBCFullNode.TxById(ctx, txId)
	if err != nil {
		return nil, err
	}
	return stripTxWitness(tx, &txId), nil
}

// stripTxWitness returns tx with every input's witness cleared. A nil tx is returned unchanged so
// callers that tolerate a nil transaction keep doing so. txId is used only for logging and may be
// nil.
func stripTxWitness(tx *wire.MsgTx, txId *chainhash.Hash) *wire.MsgTx {
	if tx == nil {
		return nil
	}

	observed := false
	for _, in := range tx.TxIn {
		if in == nil {
			continue
		}
		if len(in.Witness) != 0 {
			observed = true
			break
		}
	}
	if !observed {
		// The only path a witness-free store ever takes: return the transaction untouched.
		return tx
	}

	hvmWitnessObservedCounter.Inc(1)
	if witnessObservedLogLimiter.Allow() {
		id := "unknown"
		if txId != nil {
			id = txId.String()
		}
		log.Warn("hVM: Bitcoin transaction in the local store carries segwit witness data; "+
			"stripping it.", "txid", id, "inputs", len(tx.TxIn))
	}

	// Deep-copy every field except witness, mirroring wire.MsgTx.Copy's aliasing guarantees so no
	// byte slice is shared with the caller's transaction.
	//
	// One deliberate deviation, matching Copy(): a non-nil EMPTY script becomes nil in the copy (the
	// len() > 0 guards below).
	cpy := &wire.MsgTx{
		Version:  tx.Version,
		LockTime: tx.LockTime,
		TxIn:     make([]*wire.TxIn, 0, len(tx.TxIn)),
		TxOut:    make([]*wire.TxOut, 0, len(tx.TxOut)),
	}
	for _, in := range tx.TxIn {
		if in == nil {
			// Unreachable, defense-in-depth against future codebase changes.
			continue
		}
		var sigScript []byte
		if len(in.SignatureScript) > 0 {
			sigScript = make([]byte, len(in.SignatureScript))
			copy(sigScript, in.SignatureScript)
		}
		cpy.TxIn = append(cpy.TxIn, &wire.TxIn{
			PreviousOutPoint: in.PreviousOutPoint,
			SignatureScript:  sigScript,
			Sequence:         in.Sequence,
			// Witness deliberately left nil: never allocated, never copied.
		})
	}
	for _, out := range tx.TxOut {
		if out == nil {
			// Preserve the index; appending a nil keeps output numbering intact.
			cpy.TxOut = append(cpy.TxOut, nil)
			continue
		}
		var pkScript []byte
		if len(out.PkScript) > 0 {
			pkScript = make([]byte, len(out.PkScript))
			copy(pkScript, out.PkScript)
		}
		cpy.TxOut = append(cpy.TxOut, &wire.TxOut{
			Value:    out.Value,
			PkScript: pkScript,
		})
	}
	return cpy
}

// StripBlockWitness clears witness data from every transaction of a Bitcoin block, returning
// the number of transactions that carried any.
func StripBlockWitness(blk *wire.MsgBlock) int {
	if blk == nil {
		return 0
	}
	n := 0
	for _, tx := range blk.Transactions {
		if tx == nil {
			continue
		}
		carried := false
		for _, in := range tx.TxIn {
			// A nil *TxIn cannot come off the wire -- btcd's decoder never produces one -- but it CAN
			// come from a JSON-decoded block. heminetwork's tbcapi BlockInsert takes a
			// *wire.MsgBlock straight out of json.Unmarshal, and JSON can express "TxIn":[null].
			if in == nil {
				continue
			}
			if len(in.Witness) != 0 {
				in.Witness = nil
				carried = true
			}
		}
		if carried {
			n++
		}
	}
	return n
}
