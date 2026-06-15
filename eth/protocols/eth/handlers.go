// Copyright 2021 The go-ethereum Authors
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

package eth

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/metrics"
	"github.com/ethereum/go-ethereum/p2p/tracker"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/trie"
	"golang.org/x/time/rate"
)

// requestTracker is a singleton tracker for eth/66 and newer request times.
var requestTracker = tracker.New(ProtocolName, 5*time.Minute)

func handleGetBlockHeaders(backend Backend, msg Decoder, peer *Peer) error {
	// Decode the complex header query
	var query GetBlockHeadersPacket
	if err := msg.Decode(&query); err != nil {
		return err
	}
	response := ServiceGetBlockHeadersQuery(backend.Chain(), query.GetBlockHeadersRequest, peer)
	return peer.ReplyBlockHeadersRLP(query.RequestId, response)
}

// ServiceGetBlockHeadersQuery assembles the response to a header query. It is
// exposed to allow external packages to test protocol behavior.
func ServiceGetBlockHeadersQuery(chain *core.BlockChain, query *GetBlockHeadersRequest, peer *Peer) []rlp.RawValue {
	if query.Amount == 0 {
		return nil
	}
	if query.Skip == 0 {
		// The fast path: when the request is for a contiguous segment of headers.
		return serviceContiguousBlockHeaderQuery(chain, query)
	} else {
		return serviceNonContiguousBlockHeaderQuery(chain, query, peer)
	}
}

func serviceNonContiguousBlockHeaderQuery(chain *core.BlockChain, query *GetBlockHeadersRequest, peer *Peer) []rlp.RawValue {
	hashMode := query.Origin.Hash != (common.Hash{})
	first := true
	maxNonCanonical := uint64(100)

	// Gather headers until the fetch or network limits is reached
	var (
		bytes   common.StorageSize
		headers []rlp.RawValue
		unknown bool
		lookups int
	)
	for !unknown && len(headers) < int(query.Amount) && bytes < softResponseLimit &&
		len(headers) < maxHeadersServe && lookups < 2*maxHeadersServe {
		lookups++
		// Retrieve the next header satisfying the query
		var origin *types.Header
		if hashMode {
			if first {
				first = false
				origin = chain.GetHeaderByHash(query.Origin.Hash)
				if origin != nil {
					query.Origin.Number = origin.Number.Uint64()
				}
			} else {
				origin = chain.GetHeader(query.Origin.Hash, query.Origin.Number)
			}
		} else {
			origin = chain.GetHeaderByNumber(query.Origin.Number)
		}
		if origin == nil {
			break
		}
		if rlpData, err := rlp.EncodeToBytes(origin); err != nil {
			log.Crit("Unable to encode our own headers", "err", err)
		} else {
			headers = append(headers, rlp.RawValue(rlpData))
			bytes += common.StorageSize(len(rlpData))
		}
		// Advance to the next header of the query
		switch {
		case hashMode && query.Reverse:
			// Hash based traversal towards the genesis block
			ancestor := query.Skip + 1
			if ancestor == 0 {
				unknown = true
			} else {
				query.Origin.Hash, query.Origin.Number = chain.GetAncestor(query.Origin.Hash, query.Origin.Number, ancestor, &maxNonCanonical)
				unknown = (query.Origin.Hash == common.Hash{})
			}
		case hashMode && !query.Reverse:
			// Hash based traversal towards the leaf block
			var (
				current = origin.Number.Uint64()
				next    = current + query.Skip + 1
			)
			if next <= current {
				infos, _ := json.MarshalIndent(peer.Peer.Info(), "", "  ")
				peer.Log().Warn("GetBlockHeaders skip overflow attack", "current", current, "skip", query.Skip, "next", next, "attacker", infos)
				unknown = true
			} else {
				if header := chain.GetHeaderByNumber(next); header != nil {
					nextHash := header.Hash()
					expOldHash, _ := chain.GetAncestor(nextHash, next, query.Skip+1, &maxNonCanonical)
					if expOldHash == query.Origin.Hash {
						query.Origin.Hash, query.Origin.Number = nextHash, next
					} else {
						unknown = true
					}
				} else {
					unknown = true
				}
			}
		case query.Reverse:
			// Number based traversal towards the genesis block
			current := query.Origin.Number
			ancestor := current - (query.Skip + 1)
			if ancestor >= current { // check for underflow
				unknown = true
			} else {
				query.Origin.Number = ancestor
			}

		case !query.Reverse:
			current := query.Origin.Number
			next := current + query.Skip + 1
			if next <= current { // check for overflow
				unknown = true
			} else {
				query.Origin.Number = next
			}
		}
	}
	return headers
}

func serviceContiguousBlockHeaderQuery(chain *core.BlockChain, query *GetBlockHeadersRequest) []rlp.RawValue {
	count := query.Amount
	if count > maxHeadersServe {
		count = maxHeadersServe
	}
	if query.Origin.Hash == (common.Hash{}) {
		// Number mode, just return the canon chain segment. The backend
		// delivers in [N, N-1, N-2..] descending order, so we need to
		// accommodate for that.
		from := query.Origin.Number
		if !query.Reverse {
			from = from + count - 1
		}
		headers := chain.GetHeadersFrom(from, count)
		if !query.Reverse {
			for i, j := 0, len(headers)-1; i < j; i, j = i+1, j-1 {
				headers[i], headers[j] = headers[j], headers[i]
			}
		}
		return headers
	}
	// Hash mode.
	var (
		headers []rlp.RawValue
		hash    = query.Origin.Hash
		header  = chain.GetHeaderByHash(hash)
	)
	if header != nil {
		rlpData, _ := rlp.EncodeToBytes(header)
		headers = append(headers, rlpData)
	} else {
		// We don't even have the origin header
		return headers
	}
	num := header.Number.Uint64()
	if !query.Reverse {
		// Theoretically, we are tasked to deliver header by hash H, and onwards.
		// However, if H is not canon, we will be unable to deliver any descendants of
		// H.
		if canonHash := chain.GetCanonicalHash(num); canonHash != hash {
			// Not canon, we can't deliver descendants
			return headers
		}
		descendants := chain.GetHeadersFrom(num+count-1, count-1)
		for i, j := 0, len(descendants)-1; i < j; i, j = i+1, j-1 {
			descendants[i], descendants[j] = descendants[j], descendants[i]
		}
		headers = append(headers, descendants...)
		return headers
	}
	{ // Last mode: deliver ancestors of H
		for i := uint64(1); i < count; i++ {
			header = chain.GetHeaderByHash(header.ParentHash)
			if header == nil {
				break
			}
			rlpData, _ := rlp.EncodeToBytes(header)
			headers = append(headers, rlpData)
		}
		return headers
	}
}

func handleGetBlockBodies(backend Backend, msg Decoder, peer *Peer) error {
	// Decode the block body retrieval message
	var query GetBlockBodiesPacket
	if err := msg.Decode(&query); err != nil {
		return err
	}
	response := ServiceGetBlockBodiesQuery(backend.Chain(), query.GetBlockBodiesRequest)
	return peer.ReplyBlockBodiesRLP(query.RequestId, response)
}

// ServiceGetBlockBodiesQuery assembles the response to a body query. It is
// exposed to allow external packages to test protocol behavior.
func ServiceGetBlockBodiesQuery(chain *core.BlockChain, query GetBlockBodiesRequest) []rlp.RawValue {
	// Gather blocks until the fetch or network limits is reached
	var (
		bytes  int
		bodies []rlp.RawValue
	)
	for lookups, hash := range query {
		if bytes >= softResponseLimit || len(bodies) >= maxBodiesServe ||
			lookups >= 2*maxBodiesServe {
			break
		}
		if data := chain.GetBodyRLP(hash); len(data) != 0 {
			bodies = append(bodies, data)
			bytes += len(data)
		}
	}
	return bodies
}

func handleGetBTCBlocks(backend Backend, msg Decoder, peer *Peer) error {
	// Decode the block body retrieval message
	var query GetBTCBlocksPacket
	if err := msg.Decode(&query); err != nil {
		log.Error("Unable to decode GetBTCBlocksPacket", "err", err)
		return fmt.Errorf("%w: message %v: %v", errDecode, msg, err)
	}
	response := ServiceGetBTCBlocksQuery(backend.Chain(), query.GetBTCBlocksRequest)

	return peer.ReplyBTCBlocksPacket(query.RequestId, response)
}

func ServiceGetBTCBlocksQuery(chain *core.BlockChain, query GetBTCBlocksRequest) []*common.BitcoinBlock {
	// A node started without hVM (HvmEnabled=false) never initializes the full TBC node, so
	// vm.TBCFullNode is nil; calling BlockByHash below would nil-deref and crash the process. Serve no
	// blocks instead (the caller replies with an empty set), as a node with no matching blocks would.
	// Mirrors the nil-guard every hVM precompile has (core/vm/contracts.go).
	if vm.TBCFullNode == nil {
		log.Debug("ignoring GetBtcBlocks query: hVM/TBC full node not enabled on this node")
		return nil
	}

	// Gather Bitcoin blocks until the fetch or network limits is reached
	var (
		bytesCount int
		blocks     []*common.BitcoinBlock
	)

	log.Info("P2P requested BTC blocks", "numBlocks", len(query))

	for lookups, hash := range query {
		if bytesCount >= softResponseLimitBTC || len(blocks) >= maxBtcBlocksServe ||
			lookups >= 2*maxBtcBlocksServe {
			break
		}

		var ch chainhash.Hash
		err := ch.SetBytes(hash.Bytes())
		if err != nil {
			log.Error(fmt.Sprintf("Unable to convert hash %s to a chainhash", hash.String()), "err", err)
			continue // Keep searching for other valid blocks
		}

		block, err := vm.TBCFullNode.BlockByHash(vm.MainCtx, ch)
		if err != nil {
			log.Error(fmt.Sprintf("did not find BTC block %s requested by peer", hash.String()), "err", err)
			continue
		}
		if block == nil {
			log.Error(fmt.Sprintf("did not encounter error when looking up BTC block %s but block is nil", hash.String()))
			continue
		}
		var blockBuf bytes.Buffer

		// Note that this might not always be congruent with BTC wire format in the future
		err = block.MsgBlock().Serialize(&blockBuf)
		if err != nil {
			log.Error(fmt.Sprintf("error serializing BTC block %s for peer", hash.String()), "err", err)
			continue
		}

		blockBytes := blockBuf.Bytes()
		if len(blockBytes) != 0 {
			btcBlock := common.BytesToBitcoinBlock(blockBytes)
			blocks = append(blocks, &btcBlock)
			bytesCount += len(blockBytes)
		}
	}

	return blocks
}

func handleGetReceipts68(backend Backend, msg Decoder, peer *Peer) error {
	// Decode the block receipts retrieval message
	var query GetReceiptsPacket
	if err := msg.Decode(&query); err != nil {
		return err
	}
	response := ServiceGetReceiptsQuery68(backend.Chain(), query.GetReceiptsRequest)
	return peer.ReplyReceiptsRLP(query.RequestId, response)
}

func handleGetReceipts69(backend Backend, msg Decoder, peer *Peer) error {
	// Decode the block receipts retrieval message
	var query GetReceiptsPacket
	if err := msg.Decode(&query); err != nil {
		return err
	}
	response := serviceGetReceiptsQuery69(backend.Chain(), query.GetReceiptsRequest)
	return peer.ReplyReceiptsRLP(query.RequestId, response)
}

// ServiceGetReceiptsQuery68 assembles the response to a receipt query. It is
// exposed to allow external packages to test protocol behavior.
func ServiceGetReceiptsQuery68(chain *core.BlockChain, query GetReceiptsRequest) []rlp.RawValue {
	// Gather state data until the fetch or network limits is reached
	var (
		bytes    int
		receipts []rlp.RawValue
	)
	for lookups, hash := range query {
		if bytes >= softResponseLimit || len(receipts) >= maxReceiptsServe ||
			lookups >= 2*maxReceiptsServe {
			break
		}
		// Retrieve the requested block's receipts
		results := chain.GetReceiptsRLP(hash)
		if results == nil {
			if header := chain.GetHeaderByHash(hash); header == nil || header.ReceiptHash != types.EmptyRootHash {
				continue
			}
		} else {
			body := chain.GetBodyRLP(hash)
			if body == nil {
				continue
			}
			var err error
			results, err = blockReceiptsToNetwork68(results, body)
			if err != nil {
				log.Error("Error in block receipts conversion", "hash", hash, "err", err)
				continue
			}
		}
		receipts = append(receipts, results)
		bytes += len(results)
	}
	return receipts
}

// serviceGetReceiptsQuery69 assembles the response to a receipt query.
// It does not send the bloom filters for the receipts
func serviceGetReceiptsQuery69(chain *core.BlockChain, query GetReceiptsRequest) []rlp.RawValue {
	// Gather state data until the fetch or network limits is reached
	var (
		bytes    int
		receipts []rlp.RawValue
	)
	for lookups, hash := range query {
		if bytes >= softResponseLimit || len(receipts) >= maxReceiptsServe ||
			lookups >= 2*maxReceiptsServe {
			break
		}
		// Retrieve the requested block's receipts
		results := chain.GetReceiptsRLP(hash)
		if results == nil {
			if header := chain.GetHeaderByHash(hash); header == nil || header.ReceiptHash != types.EmptyRootHash {
				continue
			}
		} else {
			body := chain.GetBodyRLP(hash)
			if body == nil {
				continue
			}
			var err error
			results, err = blockReceiptsToNetwork69(results, body)
			if err != nil {
				log.Error("Error in block receipts conversion", "hash", hash, "err", err)
				continue
			}
		}
		receipts = append(receipts, results)
		bytes += len(results)
	}
	return receipts
}

func handleNewBlockhashes(backend Backend, msg Decoder, peer *Peer) error {
	return errors.New("block announcements disallowed") // We dropped support for non-merge networks
}

func handleNewBlock(backend Backend, msg Decoder, peer *Peer) error {
	return errors.New("block broadcasts disallowed") // We dropped support for non-merge networks
}

// Contextual-difficulty verdict counters. These are enforced: a reject drops the gossiped header (see
// evaluateBTCDiff / handleBTCBlocks). The metric path retains the historical ".../shadow/..." segment on
// purpose — operators watch the same reject series across the shadow (log-only) -> enforce cutover, so a
// continuous near-zero reject rate is legible on one graph rather than resetting at the flip.
//
// Scope (shared by the PoW and merkle gates below): these cover the eth-gossip ingestion path
// (handleBTCBlocks) as a cheaper early filter. The authoritative, consensus-binding enforcement is on the
// apply path into the lightweight header node (AddExternalHeaders); these gossip-side checks are
// defense-in-depth and are not the gate consensus depends on. The reject counter is the metrics signal and
// the throttled reject log.Warn below is the human-readable detail (it is suppressed only for a block whose
// full BODY is already in the store, via the FullBlockAvailable short-circuit at the top of the loop, so
// header-only entries still log).
// Note: accept/skip/reject count validator verdicts, not confirmed store writes — a later
// header/body insert failure on an accept/skip verdict is logged but does not adjust these
// counters. Do not read accept+skip as "admitted to store".
var (
	hvmBTCDiffShadowAccept = metrics.NewRegisteredCounter("eth/hvm/btcdiff/shadow/accept", nil)
	hvmBTCDiffShadowSkip   = metrics.NewRegisteredCounter("eth/hvm/btcdiff/shadow/skip", nil)
	hvmBTCDiffShadowReject = metrics.NewRegisteredCounter("eth/hvm/btcdiff/shadow/reject", nil)

	// btcDiffRejectLogLimiter throttles the per-reject log.Warn so repeated rejects cannot flood the log.
	// The hvmBTCDiffShadowReject counter is the unthrottled signal; this Warn is only the human-readable
	// detail. ~1 line every 5s with a burst.
	btcDiffRejectLogLimiter = rate.NewLimiter(rate.Every(5*time.Second), 4)

	// hvmBTCGossipPoWReject counts gossiped BTC headers dropped by the context-free proof-of-work gate
	// (hash > target, or an out-of-range target). Distinct from the contextual-difficulty reject counter
	// above: a header can pass contextual difficulty (correct Bits) yet fail PoW (no real work). A sustained
	// non-zero rate means a peer is feeding unmined headers over gossip; alert on it.
	hvmBTCGossipPoWReject = metrics.NewRegisteredCounter("eth/hvm/btcdiff/gossip/pow_reject", nil)

	// btcPoWRejectLogLimiter throttles the per-PoW-reject Warn (same rationale as btcDiffRejectLogLimiter;
	// the counter is the unthrottled alert).
	btcPoWRejectLogLimiter = rate.NewLimiter(rate.Every(5*time.Second), 4)

	// hvmBTCGossipMerkleReject counts gossiped BTC block bodies dropped because their transactions do not
	// hash to the header's committed merkle root. The gate below binds a gossiped body to its header's
	// merkle root before storage, so a body of substituted transactions cannot be admitted under a real
	// consensus-chain header hash (see vm.CheckBTCBlockMerkleRoot). A sustained non-zero rate means a peer
	// is feeding bodies that do not match their headers.
	hvmBTCGossipMerkleReject = metrics.NewRegisteredCounter("eth/hvm/btcdiff/gossip/merkle_reject", nil)

	// btcMerkleRejectLogLimiter throttles the per-merkle-reject Warn (same rationale as btcPoWRejectLogLimiter;
	// the counter is the unthrottled alert).
	btcMerkleRejectLogLimiter = rate.NewLimiter(rate.Every(5*time.Second), 4)
)

type btcDiffShadowVerdict int

const (
	btcDiffShadowAccept btcDiffShadowVerdict = iota // header difficulty is contextually valid
	btcDiffShadowSkip                               // parent/anchor unavailable (normal during IBD); NOT a rejection
	btcDiffShadowReject                             // genuine contextual-difficulty violation
)

// classifyBTCDiffShadow maps a vm.ValidateBTCHeaderContext result to a shadow verdict. The skip sentinel
// must stay distinct from a rejection (a real RuleError), mirroring the vm-side requireSkip/requireReject
// contract — collapsing them would flip an IBD skip into a false reject (and, when enforcing, drop a valid
// header).
func classifyBTCDiffShadow(err error) btcDiffShadowVerdict {
	switch {
	case err == nil:
		return btcDiffShadowAccept
	case errors.Is(err, vm.ErrBTCHeaderContextUnavailable):
		return btcDiffShadowSkip
	default:
		return btcDiffShadowReject
	}
}

// evaluateBTCDiff runs the contextual-difficulty validator on a gossiped BTC header, records the verdict
// to the per-outcome counters, logs (throttled) a rejection, and returns the verdict so the caller can
// enforce it via shouldDropBTCHeader.
func evaluateBTCDiff(blockHash chainhash.Hash, hdr *wire.BlockHeader) btcDiffShadowVerdict {
	err := vm.ValidateBTCHeaderContext(hdr)
	verdict := classifyBTCDiffShadow(err)
	switch verdict {
	case btcDiffShadowAccept:
		hvmBTCDiffShadowAccept.Inc(1)
	case btcDiffShadowSkip:
		hvmBTCDiffShadowSkip.Inc(1)
	default:
		hvmBTCDiffShadowReject.Inc(1)
		if btcDiffRejectLogLimiter.Allow() {
			log.Warn("hVM BTC contextual-difficulty REJECT — dropping header (enforce mode); "+
				"a real testnet3/mainnet header here indicates a validator false positive",
				"block", blockHash.String(), "prev", hdr.PrevBlock.String(),
				"bits", fmt.Sprintf("%08x", hdr.Bits), "err", err)
		}
	}
	return verdict
}

// shouldDropBTCHeader reports whether an enforce-mode verdict means the header must not be inserted. Only
// a genuine contextual-difficulty rejection drops. A skip (parent/anchor not yet available — normal during
// IBD) and an accept both proceed to insertion: dropping on skip would stall sync by discarding headers
// whose ancestry simply has not arrived. Isolating this one-line policy makes the "never drop on skip"
// invariant unit-testable without a live TBC node.
func shouldDropBTCHeader(v btcDiffShadowVerdict) bool {
	return v == btcDiffShadowReject
}

// shouldDropBTCHeaderPoW reports whether a vm.CheckBTCHeaderPoW result means the gossiped header must not
// be inserted: drop only on a genuine PoW failure (a btcd RuleError — hash>target / out-of-range target).
// A nil result (valid PoW) and the ErrBTCHeaderContextUnavailable skip sentinel (params not configured)
// both proceed — dropping on the skip would discard honest headers on a transient config gap, and real
// enforcement is the consensus apply path; this gossip gate is defense-in-depth.
func shouldDropBTCHeaderPoW(err error) bool {
	return err != nil && !errors.Is(err, vm.ErrBTCHeaderContextUnavailable)
}

func handleBTCBlocks(backend Backend, msg Decoder, peer *Peer) error {
	log.Debug("Peer sent BTC blocks")

	// Ignore BTC-block gossip when this node has no full TBC node (HvmEnabled=false), rather than
	// nil-deref vm.TBCFullNode (the store calls) below and crash the
	// process. Mirrors the nil-guard every hVM precompile has.
	if vm.TBCFullNode == nil {
		log.Debug("ignoring BtcBlocks message: hVM/TBC full node not enabled on this node")
		return nil
	}

	// Retrieve and decode the propagated block
	res := new(BTCBlocksPacket)
	if err := msg.Decode(res); err != nil {
		log.Info("BTC Blocks decode error", "err", err)
		return fmt.Errorf("%w: message %v: %v", errDecode, msg, err)
	}

	log.Debug("Peer BTC Blocks packet info", "len", len(res.BTCBlocksResponse))

	// Hard per-message header cap. The inbound loop is otherwise bounded only by maxMessageSize
	// (10MiB ≈ 126k minimal headers); maxBtcBlocksServe (32) is enforced only on the serve side, never
	// on ingest. Without this cap a single message could pack tens of thousands of headers, each
	// driving a contextual-difficulty walk serially on this one per-peer goroutine, contending the TBC
	// header-cache mutex shared with consensus-path hVM precompiles. An honest peer never serves more
	// than maxBtcBlocksServe blocks in a response, so a larger batch is protocol abuse.
	if len(res.BTCBlocksResponse) > maxBtcBlocksServe {
		log.Warn("ignoring oversized BtcBlocks message", "count", len(res.BTCBlocksResponse), "cap", maxBtcBlocksServe, "peer", peer.ID())
		return fmt.Errorf("%w: BtcBlocks response of %d exceeds cap %d", errMsgTooLarge, len(res.BTCBlocksResponse), maxBtcBlocksServe)
	}

	for i, btcBlock := range res.BTCBlocksResponse {
		var msgBlock wire.MsgBlock
		err := msgBlock.Deserialize(bytes.NewReader(btcBlock.Bytes()))
		if err != nil {
			log.Error("Unable to deserialize BTC block", "badIndex", i, "err", err)
			continue
		}

		hash := msgBlock.BlockHash()

		exists, err := vm.TBCFullNode.FullBlockAvailable(vm.MainCtx, hash)
		if err != nil {
			log.Error("Unable to check whether TBC has BTC block received over P2P", "badIndex", i, "block", hash.String(), "err", err)
			// Still attempt to add block if unable to determine
		} else if exists {
			log.Info("Received BTC block over P2P which TBC already has, ignoring", "block", hash.String())
			continue
		}

		// Context-free proof-of-work gate on the gossip ingest path (defense-in-depth). A header with a
		// correct Bits field but no real work would otherwise pass the contextual check below; require the
		// work to be real here. PoW is context-free and cheaper than the contextual walk, so reject-before-walk
		// is also DoS-better. A skip sentinel (params not configured) is not a PoW failure and must not drop.
		// This is a gossip-side early filter only; the authoritative enforcement is the apply path into the
		// lightweight consensus node, which is what consensus reads.
		if shouldDropBTCHeaderPoW(vm.CheckBTCHeaderPoW(&msgBlock.Header)) {
			hvmBTCGossipPoWReject.Inc(1)
			if btcPoWRejectLogLimiter.Allow() {
				log.Warn("hVM BTC gossip PoW REJECT — dropping header that fails proof-of-work",
					"block", hash.String(), "bits", fmt.Sprintf("%08x", msgBlock.Header.Bits), "peer", peer.ID())
			}
			continue
		}

		headers := make([]*wire.BlockHeader, 1)
		headers[0] = &msgBlock.Header

		msgHeaders := &wire.MsgHeaders{
			Headers: headers,
		}

		// Enforce: validate this gossiped header's contextual Bitcoin difficulty and drop it on a genuine
		// violation, so an easier-than-consensus header is not admitted to the TBC store via this path.
		// A skip verdict (ancestry not yet available — normal during IBD) and an accept both fall through to
		// the inserts below; only a reject is dropped. evaluateBTCDiff records the verdict counter and logs
		// (throttled) rejects. This is gossip-path defense-in-depth; the consensus-binding enforcement is the
		// contextual-difficulty check on the apply path into the lightweight header node (floor-aware). This
		// gossip/full-node path is not consensus-binding.
		if shouldDropBTCHeader(evaluateBTCDiff(hash, &msgBlock.Header)) {
			continue
		}

		_, _, _, _, err = vm.TBCFullNode.BlockHeadersInsert(vm.MainCtx, msgHeaders)
		if err != nil {
			// Do not exit, try to still insert block below regardless but log error
			log.Error("Unable to add BTC header to TBC", "err", err)
		}

		// A 0-tx message is a header-only relay (a peer advertising a bare header as a wire.MsgBlock); a real
		// BTC block always carries at least the coinbase tx. The header was already inserted above and there
		// is no body to verify or store, so fall through to the next entry. This is a normal message shape,
		// not a merkle failure, so it must not run the body check below nor count as a reject.
		if len(msgBlock.Transactions) == 0 {
			continue
		}

		// Verify the body matches the header's committed merkle root before storing it. This binds the body
		// to its header's merkle root, so a body of substituted transactions cannot be admitted under a real
		// consensus-chain header hash (see vm.CheckBTCBlockMerkleRoot). On mismatch, drop
		// only the body: the PoW/diff-valid header was already inserted above, leaving the normal "header
		// known, block not yet downloaded" state, and the genuine body is re-fetched via P2P. The PoW/diff
		// header gates above are header-only and cheaper, so they run first; this hashes the full tx set and
		// is bounded by the 32-block-per-message / max-message-size caps.
		if err := vm.CheckBTCBlockMerkleRoot(&msgBlock); err != nil {
			hvmBTCGossipMerkleReject.Inc(1)
			if btcMerkleRejectLogLimiter.Allow() {
				log.Warn("hVM BTC gossip merkle REJECT — body does not match header merkle root; not storing body",
					"block", hash.String(), "peer", peer.ID(), "err", err)
			}
			continue
		}

		insert, err := vm.TBCFullNode.BlockInsert(vm.MainCtx, &msgBlock)
		if err != nil {
			// Note: if there is a race condition which inserts the block from elsewhere (either TBC peers or other geth peers)
			// between the FullBlockAvailable call and this insert, it will produce an insert error (database.DuplicateError)
			// but that is harmless and will be printed below.
			log.Error("Unable to add BTC block to TBC", "badIndex", i, "block", hash.String(), "err", err)
			continue
		}

		log.Info("Added BTC block from geth P2P to TBC", "block", hash.String(), "height", insert)
	}

	return nil
}

func handleBlockHeaders(backend Backend, msg Decoder, peer *Peer) error {
	// A batch of headers arrived to one of our previous requests
	res := new(BlockHeadersPacket)
	if err := msg.Decode(res); err != nil {
		return err
	}
	metadata := func() interface{} {
		hashes := make([]common.Hash, len(res.BlockHeadersRequest))
		for i, header := range res.BlockHeadersRequest {
			hashes[i] = header.Hash()
		}
		return hashes
	}
	return peer.dispatchResponse(&Response{
		id:   res.RequestId,
		code: BlockHeadersMsg,
		Res:  &res.BlockHeadersRequest,
	}, metadata)
}

func handleBlockBodies(backend Backend, msg Decoder, peer *Peer) error {
	// A batch of block bodies arrived to one of our previous requests
	res := new(BlockBodiesPacket)
	if err := msg.Decode(res); err != nil {
		return err
	}
	metadata := func() interface{} {
		var (
			txsHashes        = make([]common.Hash, len(res.BlockBodiesResponse))
			uncleHashes      = make([]common.Hash, len(res.BlockBodiesResponse))
			withdrawalHashes = make([]common.Hash, len(res.BlockBodiesResponse))
		)
		hasher := trie.NewStackTrie(nil)
		for i, body := range res.BlockBodiesResponse {
			txsHashes[i] = types.DeriveSha(types.Transactions(body.Transactions), hasher)
			uncleHashes[i] = types.CalcUncleHash(body.Uncles)
			if body.Withdrawals != nil {
				withdrawalHashes[i] = types.DeriveSha(types.Withdrawals(body.Withdrawals), hasher)
			}
		}
		return [][]common.Hash{txsHashes, uncleHashes, withdrawalHashes}
	}
	return peer.dispatchResponse(&Response{
		id:   res.RequestId,
		code: BlockBodiesMsg,
		Res:  &res.BlockBodiesResponse,
	}, metadata)
}

func handleReceipts[L ReceiptsList](backend Backend, msg Decoder, peer *Peer) error {
	// A batch of receipts arrived to one of our previous requests
	res := new(ReceiptsPacket[L])
	if err := msg.Decode(res); err != nil {
		return err
	}
	// Assign temporary hashing buffer to each list item, the same buffer is shared
	// between all receipt list instances.
	buffers := new(receiptListBuffers)
	for i := range res.List {
		res.List[i].setBuffers(buffers)
	}

	metadata := func() interface{} {
		hasher := trie.NewStackTrie(nil)
		hashes := make([]common.Hash, len(res.List))
		for i := range res.List {
			hashes[i] = types.DeriveSha(res.List[i], hasher)
		}
		return hashes
	}
	var enc ReceiptsRLPResponse
	for i := range res.List {
		enc = append(enc, res.List[i].EncodeForStorage())
	}
	return peer.dispatchResponse(&Response{
		id:   res.RequestId,
		code: ReceiptsMsg,
		Res:  &enc,
	}, metadata)
}

func handleNewPooledTransactionHashes(backend Backend, msg Decoder, peer *Peer) error {
	// New transaction announcement arrived, make sure we have
	// a valid and fresh chain to handle them
	if !backend.AcceptTxs(peer) {
		return nil
	}
	ann := new(NewPooledTransactionHashesPacket)
	if err := msg.Decode(ann); err != nil {
		return err
	}
	if len(ann.Hashes) != len(ann.Types) || len(ann.Hashes) != len(ann.Sizes) {
		return fmt.Errorf("NewPooledTransactionHashes: invalid len of fields in %v %v %v", len(ann.Hashes), len(ann.Types), len(ann.Sizes))
	}
	// Schedule all the unknown hashes for retrieval
	for _, hash := range ann.Hashes {
		peer.markTransaction(hash)
	}
	return backend.Handle(peer, ann)
}

func handleGetPooledTransactions(backend Backend, msg Decoder, peer *Peer) error {
	// Decode the pooled transactions retrieval message
	var query GetPooledTransactionsPacket
	if err := msg.Decode(&query); err != nil {
		return err
	}
	hashes, txs := answerGetPooledTransactions(backend, query.GetPooledTransactionsRequest, peer)
	return peer.ReplyPooledTransactionsRLP(query.RequestId, hashes, txs)
}

func answerGetPooledTransactions(backend Backend, query GetPooledTransactionsRequest, peer *Peer) ([]common.Hash, []rlp.RawValue) {
	// Gather transactions until the fetch or network limits is reached
	var (
		bytes  int
		hashes []common.Hash
		txs    []rlp.RawValue
	)
	for _, hash := range query {
		if bytes >= softResponseLimit {
			break
		}
		// Retrieve the requested transaction, skipping if unknown to us
		encoded := backend.TxPool(peer.Peer).GetRLP(hash)
		if len(encoded) == 0 {
			continue
		}
		hashes = append(hashes, hash)
		txs = append(txs, encoded)
		bytes += len(encoded)
	}
	return hashes, txs
}

func handleTransactions(backend Backend, msg Decoder, peer *Peer) error {
	// Transactions arrived, make sure we have a valid and fresh chain to handle them
	if !backend.AcceptTxs(peer) {
		return nil
	}
	// Transactions can be processed, parse all of them and deliver to the pool
	var txs TransactionsPacket
	if err := msg.Decode(&txs); err != nil {
		return err
	}
	// Duplicate transactions are not allowed
	seen := make(map[common.Hash]struct{})
	for i, tx := range txs {
		// Validate and mark the remote transaction
		if tx == nil {
			return fmt.Errorf("Transactions: transaction %d is nil", i)
		}
		hash := tx.Hash()
		if _, exists := seen[hash]; exists {
			return fmt.Errorf("Transactions: multiple copies of the same hash %v", hash)
		}
		seen[hash] = struct{}{}
		peer.markTransaction(hash)
	}
	return backend.Handle(peer, &txs)
}

func handlePooledTransactions(backend Backend, msg Decoder, peer *Peer) error {
	// Transactions arrived, make sure we have a valid and fresh chain to handle them
	if !backend.AcceptTxs(peer) {
		return nil
	}
	// Transactions can be processed, parse all of them and deliver to the pool
	var txs PooledTransactionsPacket
	if err := msg.Decode(&txs); err != nil {
		return err
	}
	// Duplicate transactions are not allowed
	seen := make(map[common.Hash]struct{})
	for i, tx := range txs.PooledTransactionsResponse {
		// Validate and mark the remote transaction
		if tx == nil {
			return fmt.Errorf("PooledTransactions: transaction %d is nil", i)
		}
		hash := tx.Hash()
		if _, exists := seen[hash]; exists {
			return fmt.Errorf("PooledTransactions: multiple copies of the same hash %v", hash)
		}
		seen[hash] = struct{}{}
		peer.markTransaction(hash)
	}
	requestTracker.Fulfil(peer.id, peer.version, PooledTransactionsMsg, txs.RequestId)

	return backend.Handle(peer, &txs.PooledTransactionsResponse)
}

func handleBlockRangeUpdate(backend Backend, msg Decoder, peer *Peer) error {
	var update BlockRangeUpdatePacket
	if err := msg.Decode(&update); err != nil {
		return err
	}
	if err := update.Validate(); err != nil {
		return err
	}
	// We don't do anything with these messages for now, just store them on the peer.
	peer.lastRange.Store(&update)
	return nil
}
