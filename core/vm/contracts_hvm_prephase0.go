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
	"reflect"

	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/txscript"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/params"
)

// Pre-phase0 legacy replay for Hemi testnet.
//
// Hemi testnet history before the current Hvm0Time was produced by Hemi op-geth v1.14.2 (heminetwork v0.2.0),
// when hVM Phase 0 was scheduled earlier. In that window only 0x40..0x46 existed. They were pre-warmed and
// charged the same fixed RequiredGas as today. The results below reproduce what v1.14.2's Run returned
// (`git show v1.14.2:core/vm/contracts.go`) without querying TBC, under the assumption that the TBC index held
// no data for the queried items. Input validation and address decoding are deterministic and reproduced exactly:
//
//   - (nil, nil): v1.14.2 returned empty success.
//   - (nil, ErrHVMLegacyPrecompileFailed): v1.14.2 returned an error, so the call burned all forwarded gas.
//     Example: testnet block 1534614, tx 0xd24f54731f299794664459fcb7b19284d3019af434e092f0e8026a0f8ba1daff,
//     where btcBalAddr got an ABI-encoded string. Receipt: status 0, gasUsed 985098.
//
// Results that depended on TBC contents (balances, UTXOs, headers, tx lookups) cannot be recomputed. Where a
// canonical testnet tx made such a result observable (in a log or storage), the exact historical bytes are pinned
// in legacyHvmKnownResults. Otherwise the result is replayed with the v1.14.2 length, using zero bytes, which
// reproduces gas when the content was never observed.
//
// Known pre-phase0 hVM calls on Hemi testnet (from the explorer, blocks 1534614..1540560; nothing calls
// 0x41..0x43, 0x45 or 0x46 before Hvm0Time):
//   - 0x40: 9 txs with ABI-encoded input (all failed; error, all forwarded gas burned) and 2 with a raw
//     address (1540534, whose balance is logged and therefore pinned; 1540560, whose result is never observed).
//   - 0x44: 10 txs whose caller never logs or stores the header (only its 116-byte length affects gas).

// legacyHvmMaxAddress is the highest hVM precompile address that existed in Hemi op-geth v1.14.2.
const legacyHvmMaxAddress = 0x46

// legacyHvmBtcParams are the Bitcoin params Hemi testnet's TBC ran with (testnet3).
var legacyHvmBtcParams = &chaincfg.TestNet3Params

// PrecompiledContractsHvmLegacy is the hVM precompile set exposed on Hemi testnet before hVM Phase 0:
// 0x40..0x46, using the same singleton instances as PrecompiledContractsHvm0 (so isHVMPrecompile holds).
var PrecompiledContractsHvmLegacy = func() map[common.Address]PrecompiledContract {
	m := make(map[common.Address]PrecompiledContract)
	for addr, p := range PrecompiledContractsHvm0 {
		if addr[common.AddressLength-1] <= legacyHvmMaxAddress {
			m[addr] = p
		}
	}
	return m
}()

// PrecompiledAddressesHvmLegacy lists the addresses of PrecompiledContractsHvmLegacy (filled in init).
var PrecompiledAddressesHvmLegacy []common.Address

// hvmPrecompiles returns the hVM precompile set active under rules: the full Phase 0 set once IsHvm0 is
// active, the legacy set inside the Hemi testnet pre-phase0 window, and nil otherwise.
func hvmPrecompiles(rules params.Rules) map[common.Address]PrecompiledContract {
	switch {
	case rules.IsHvm0:
		return PrecompiledContractsHvm0
	case rules.IsHvmPrecompiles:
		return PrecompiledContractsHvmLegacy
	default:
		return nil
	}
}

// legacyHvmLastHeaderLen is the length of v1.14.2's btcLastHeader result: height(4) || hash(32) ||
// version(4) || prevHash(32) || merkleRoot(32) || timestamp(4) || bits(4) || nonce(4).
const legacyHvmLastHeaderLen = 4 + 32 + 4 + 32 + 32 + 4 + 4 + 4

// legacyHvmKey identifies one historical pre-phase0 hVM precompile call on Hemi testnet.
type legacyHvmKey struct {
	block   uint64
	address byte
	input   string
}

// legacyHvmKnownResults pins TBC-dependent results that canonical testnet history made observable.
var legacyHvmKnownResults = map[legacyHvmKey][]byte{
	// Block 1540534, tx 0x0660a8ff63fddba107aec7d1a005590ca23301a7e7bd0be6b88c764c69d5fb75: the caller logs
	// btcBalAddr("mfiYUqdaf7RXVjX64pZR5343DFaYaV4KMK") = 0x000000000b147ca0 (185,890,976 sats).
	{1540534, 0x40, "mfiYUqdaf7RXVjX64pZR5343DFaYaV4KMK"}: common.FromHex("000000000b147ca0"),
}

// legacyHVMPrecompileResult returns what Hemi op-geth v1.14.2's Run returned for p and input at block, using
// legacyHvmKnownResults for pinned TBC-dependent results. It never touches TBC. Gas is charged by the caller.
func legacyHVMPrecompileResult(p PrecompiledContract, input []byte, block uint64) ([]byte, error) {
	if addr, ok := hvmContractsToAddress[reflect.TypeOf(p)]; ok {
		if ret, ok := legacyHvmKnownResults[legacyHvmKey{block, addr[0], string(input)}]; ok {
			return common.CopyBytes(ret), nil
		}
	}
	switch p.(type) {
	case *btcBalAddr:
		// v1.14.2: len < 24 -> (nil, nil). Otherwise BalanceByAddress, which errors when the address does not
		// decode; the error was returned. A decodable address yields an 8-byte big-endian balance (0 here).
		if len(input) < 24 {
			return nil, nil
		}
		if _, err := legacyPayToAddrScript(string(input)); err != nil {
			return nil, ErrHVMLegacyPrecompileFailed
		}
		return make([]byte, 8), nil

	case *btcUtxosAddrList:
		// v1.14.2: len < 28 -> (nil, nil). Any UtxosByAddress error (including an undecodable address) ->
		// (nil, nil). Otherwise a 1-byte UTXO count followed by the UTXOs (0 UTXOs here).
		if len(input) < 28 {
			return nil, nil
		}
		if _, err := legacyPayToAddrScript(string(input[:len(input)-4])); err != nil {
			return nil, nil
		}
		return []byte{0}, nil

	case *btcTxByTxid:
		// v1.14.2: len != 36 -> (nil, nil); a failed tx lookup -> (nil, nil).
		return nil, nil

	case *btcTxConfirmations:
		// v1.14.2 returned the TxByTxId error when the tx was not indexed. Inputs shorter than 32 bytes
		// panicked (input[0:32]), so they cannot appear in canonical history; treat them as a failure too.
		return nil, ErrHVMLegacyPrecompileFailed

	case *btcLastHeader:
		// v1.14.2 returned TBC's best header (no input validation). The content cannot be reconstructed, but
		// no canonical caller ever observed it; returning the same length reproduces gas exactly.
		return make([]byte, legacyHvmLastHeaderLen), nil

	case *btcHeaderN:
		// v1.14.2: len != 4 -> error. Otherwise a failed/empty header lookup -> (nil, nil).
		if len(input) != 4 {
			return nil, ErrHVMLegacyPrecompileFailed
		}
		return nil, nil

	case *btcAddrToScript:
		// v1.14.2: len < 24 -> (nil, nil); decode or script failure -> error; otherwise the pay-to script.
		// Fully deterministic, no TBC involved.
		if len(input) < 24 {
			return nil, nil
		}
		script, err := legacyPayToAddrScript(string(input))
		if err != nil {
			return nil, ErrHVMLegacyPrecompileFailed
		}
		return script, nil

	default:
		// Not part of the v1.14.2 set (unreachable via dispatch, which only exposes 0x40..0x46).
		return nil, nil
	}
}

// legacyPayToAddrScript mirrors heminetwork v0.2.0 TBC's address handling: decode under testnet3 params,
// then build the pay-to-address script.
func legacyPayToAddrScript(encoded string) ([]byte, error) {
	addr, err := btcutil.DecodeAddress(encoded, legacyHvmBtcParams)
	if err != nil {
		return nil, err
	}
	return txscript.PayToAddrScript(addr)
}
