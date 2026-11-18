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
	"math/big"
	"testing"

	"github.com/btcsuite/btcd/btcutil"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"
	"github.com/stretchr/testify/require"
)

// These tests pin the pre-phase0 legacy window on Hemi testnet (params.HemiTestnetChainID): testnet history
// produced while hVM Phase 0 was scheduled earlier called the hVM precompiles before the (current) Hvm0Time.
// Inside the window the v1.14.2 precompiles (0x40..0x46) must exist (warm, RequiredGas charged) and replay
// v1.14.2's result, including errors that burn all forwarded gas, without ever querying TBC, so re-execution
// reproduces the canonical gas, receipts and state root.

const (
	prePhase0BlockTime = uint64(1)
	prePhase0Hvm0Time  = uint64(1_000)
	hemiMainnetChainID = uint64(43111)
)

// newPrePhase0EVM builds an EVM at prePhase0BlockTime (before Hvm0Time) on Hemi testnet (window active) or
// on Hemi mainnet (no window).
func newPrePhase0EVM(t *testing.T, window bool) (*EVM, *state.StateDB) {
	t.Helper()
	cfg := *params.MergedTestChainConfig
	hvm0 := prePhase0Hvm0Time
	cfg.Hvm0Time = &hvm0
	cfg.ChainID = new(big.Int).SetUint64(hemiMainnetChainID)
	if window {
		cfg.ChainID = big.NewInt(params.HemiTestnetChainID)
	}
	statedb, err := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
	require.NoError(t, err)
	evm := NewEVM(BlockContext{
		BlockNumber: big.NewInt(1),
		Time:        prePhase0BlockTime,
		CanTransfer: func(StateDB, common.Address, *uint256.Int) bool { return true },
		Transfer:    func(StateDB, common.Address, common.Address, *uint256.Int) {},
	}, statedb, &cfg, Config{})
	require.False(t, evm.chainRules.IsHvm0, "precondition: hVM Phase 0 must not be active")
	require.Equal(t, window, evm.chainRules.IsHvmPrecompiles, "precondition: legacy window flag")
	return evm, statedb
}

func TestConfigIsHvmPrecompiles(t *testing.T) {
	hvm0 := uint64(100)
	testnet := big.NewInt(params.HemiTestnetChainID)

	c := &params.ChainConfig{ChainID: testnet, Hvm0Time: &hvm0}
	require.True(t, c.IsHemiTestnet())
	require.True(t, c.IsHvmPrecompiles(0), "testnet: window from genesis")
	require.True(t, c.IsHvmPrecompiles(99), "testnet: window up to phase0")
	require.False(t, c.IsHvm0(99), "window is pre-phase0")
	require.True(t, c.IsHvmPrecompiles(100), "phase0 implies precompiles")

	// Testnet without a scheduled phase0: there is no "before phase0", so no window.
	require.False(t, (&params.ChainConfig{ChainID: testnet}).IsHvmPrecompiles(0))

	// Any other chain (mainnet, devnets, no chain ID): precompiles follow Hvm0Time exactly, as before.
	for _, id := range []*big.Int{new(big.Int).SetUint64(hemiMainnetChainID), big.NewInt(1337), nil} {
		m := &params.ChainConfig{ChainID: id, Hvm0Time: &hvm0}
		require.False(t, m.IsHemiTestnet())
		require.Falsef(t, m.IsHvmPrecompiles(99), "chain %v before phase0", id)
		require.Truef(t, m.IsHvmPrecompiles(100), "chain %v at phase0", id)
	}
}

// Without the window, pre-phase0 behavior is unchanged: 0x40 is not a precompile and not pre-warmed.
func TestPrePhase0NoWindowUnchanged(t *testing.T) {
	evm, _ := newPrePhase0EVM(t, false)
	_, ok := evm.precompile(common.BytesToAddress([]byte{0x40}))
	require.False(t, ok)
	for _, a := range PrecompiledAddressesHvm0 {
		require.NotContains(t, ActivePrecompiles(evm.chainRules), a)
	}
}

// Inside the window only the v1.14.2 hVM precompiles (0x40..0x46) dispatch and are in the warm set;
// 0x47..0x49 did not exist yet and must behave like plain empty accounts.
func TestPrePhase0WindowExposesHvmPrecompiles(t *testing.T) {
	evm, _ := newPrePhase0EVM(t, true)
	active := ActivePrecompiles(evm.chainRules)
	contracts := ActivePrecompiledContracts(evm.chainRules)
	for b := byte(0x40); b <= 0x46; b++ {
		a := common.BytesToAddress([]byte{b})
		p, ok := evm.precompile(a)
		require.Truef(t, ok, "%s must dispatch inside the window", a)
		require.True(t, isHVMPrecompile(p))
		require.Contains(t, active, a)
		require.Contains(t, contracts, a)
	}
	for b := byte(0x47); b <= 0x49; b++ {
		a := common.BytesToAddress([]byte{b})
		_, ok := evm.precompile(a)
		require.Falsef(t, ok, "%s did not exist in v1.14.2 and must not dispatch inside the window", a)
		require.NotContains(t, active, a)
		require.NotContains(t, contracts, a)
	}
	require.Len(t, PrecompiledAddressesHvmLegacy, 7)
}

// The input testnet tx 0xd24f5473…daff (block 1534614) passed to 0x40: an ABI-encoded string, not a raw address.
var prePhase0AbiEncodedAddrInput = common.FromHex(
	"0000000000000000000000000000000000000000000000000000000000000020" +
		"0000000000000000000000000000000000000000000000000000000000000022" +
		"6d6669595571646166375258566a583634705a5235333433444661596156344b" +
		"4d4b000000000000000000000000000000000000000000000000000000000000")

// legacyTestnetAddr is a valid Bitcoin testnet3 P2PKH address (all-zero pubkey hash).
func legacyTestnetAddr(t *testing.T) string {
	t.Helper()
	a, err := btcutil.NewAddressPubKeyHash(make([]byte, 20), legacyHvmBtcParams)
	require.NoError(t, err)
	return a.EncodeAddress()
}

// The legacy results mirror Hemi op-geth v1.14.2's Run, including its errors, which are NOT normalized.
func TestPrePhase0LegacyResults(t *testing.T) {
	evm, _ := newPrePhase0EVM(t, true)
	at := func(b byte) PrecompiledContract {
		p, ok := evm.precompile(common.BytesToAddress([]byte{b}))
		require.True(t, ok)
		return p
	}
	valid := []byte(legacyTestnetAddr(t))
	p2pkh := append(append(common.FromHex("76a914"), make([]byte, 20)...), common.FromHex("88ac")...)

	for _, tc := range []struct {
		name    string
		addr    byte
		input   []byte
		ret     []byte
		wantErr bool
	}{
		{"balAddr short input", 0x40, []byte{0x01}, nil, false},
		{"balAddr undecodable (ABI-encoded) address", 0x40, prePhase0AbiEncodedAddrInput, nil, true},
		{"balAddr valid address", 0x40, valid, make([]byte, 8), false},
		{"utxosAddrList short input", 0x41, make([]byte, 27), nil, false},
		{"utxosAddrList undecodable address", 0x41, prePhase0AbiEncodedAddrInput, nil, false},
		{"utxosAddrList valid address", 0x41, append(append([]byte{}, valid...), 0, 0, 0, 0), []byte{0}, false},
		{"txByTxid", 0x42, make([]byte, 36), nil, false},
		{"txConfirmations", 0x43, make([]byte, 32), nil, true},
		{"lastHeader", 0x44, nil, make([]byte, 116), false},
		{"headerN bad length", 0x45, make([]byte, 3), nil, true},
		{"headerN", 0x45, make([]byte, 4), nil, false},
		{"addrToScript short input", 0x46, []byte{0x01}, nil, false},
		{"addrToScript undecodable address", 0x46, prePhase0AbiEncodedAddrInput, nil, true},
		{"addrToScript valid address", 0x46, valid, p2pkh, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			p := at(tc.addr)
			const gas = uint64(1_000_000)
			ret, rem, err := evm.runPrecompile(p, tc.input, gas)
			require.Equal(t, gas-p.RequiredGas(tc.input), rem, "RequiredGas is always charged")
			if tc.wantErr {
				require.ErrorIs(t, err, ErrHVMLegacyPrecompileFailed)
				return
			}
			require.NoError(t, err)
			require.Equal(t, tc.ret, ret)
		})
	}
}

// A legacy failure burns ALL gas forwarded to the precompile, as any precompile error does.
func TestPrePhase0LegacyFailureBurnsForwardedGas(t *testing.T) {
	evm, statedb := newPrePhase0EVM(t, true)
	sender := common.HexToAddress("0x1111111111111111111111111111111111111111")
	bal := common.BytesToAddress([]byte{0x40})
	statedb.Prepare(evm.chainRules, sender, sender, &bal, ActivePrecompiles(evm.chainRules), nil)

	const gas = uint64(958_455) // what the contract forwarded to 0x40 in tx 0xd24f5473…daff
	ret, left, err := evm.Call(sender, bal, prePhase0AbiEncodedAddrInput, gas, new(uint256.Int))
	require.ErrorIs(t, err, ErrHVMLegacyPrecompileFailed)
	require.Nil(t, ret)
	require.Zero(t, left)
}

// Exact replay of Hemi testnet block 1534614, tx 0xd24f54731f299794664459fcb7b19284d3019af434e092f0e8026a0f8ba1daff:
// the deployed contract at 0x39c6a872…2625 calls 0x40 with abi.encode(string) and require()s success. The canonical
// receipt is status 0 with gasUsed 985,098 (gas limit 1,000,000). Intrinsic gas is 21,000 + 92 zero bytes * 4 +
// 40 non-zero bytes * 16 = 22,008, so execution must use exactly 963,090 and revert with "Precompile call failed".
func TestPrePhase0TestnetBlock1534614(t *testing.T) {
	code := common.FromHex("0x608060405234801561000f575f80fd5b5060043610610029575f3560e01c806343e033b61461002d575b5f80fd5b61004760048036038101906100429190610280565b61005d565b6040516100549190610327565b60405180910390f35b60605f80604073ffffffffffffffffffffffffffffffffffffffff168460405160200161008a9190610399565b6040516020818303038152906040526040516100a691906103f3565b5f604051808303815f865af19150503d805f81146100df576040519150601f19603f3d011682016040523d82523d5f602084013e6100e4565b606091505b509150915081610129576040517f08c379a000000000000000000000000000000000000000000000000000000000815260040161012090610453565b60405180910390fd5b8092505050919050565b5f604051905090565b5f80fd5b5f80fd5b5f80fd5b5f80fd5b5f601f19601f8301169050919050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52604160045260245ffd5b6101928261014c565b810181811067ffffffffffffffff821117156101b1576101b061015c565b5b80604052505050565b5f6101c3610133565b90506101cf8282610189565b919050565b5f67ffffffffffffffff8211156101ee576101ed61015c565b5b6101f78261014c565b9050602081019050919050565b828183375f83830152505050565b5f61022461021f846101d4565b6101ba565b9050828152602081018484840111156102405761023f610148565b5b61024b848285610204565b509392505050565b5f82601f83011261026757610266610144565b5b8135610277848260208601610212565b91505092915050565b5f602082840312156102955761029461013c565b5b5f82013567ffffffffffffffff8111156102b2576102b1610140565b5b6102be84828501610253565b91505092915050565b5f81519050919050565b5f82825260208201905092915050565b8281835e5f83830152505050565b5f6102f9826102c7565b61030381856102d1565b93506103138185602086016102e1565b61031c8161014c565b840191505092915050565b5f6020820190508181035f83015261033f81846102ef565b905092915050565b5f81519050919050565b5f82825260208201905092915050565b5f61036b82610347565b6103758185610351565b93506103858185602086016102e1565b61038e8161014c565b840191505092915050565b5f6020820190508181035f8301526103b18184610361565b905092915050565b5f81905092915050565b5f6103cd826102c7565b6103d781856103b9565b93506103e78185602086016102e1565b80840191505092915050565b5f6103fe82846103c3565b915081905092915050565b7f507265636f6d70696c652063616c6c206661696c6564000000000000000000005f82015250565b5f61043d601683610351565b915061044882610409565b602082019050919050565b5f6020820190508181035f83015261046a81610431565b905091905056fea2646970667358221220202e640dadf235b2487533d435661cd7dc030cc23b0640360f6f09ba0976cacb64736f6c634300081a0033")
	input := append(common.FromHex("43e033b6"), prePhase0AbiEncodedAddrInput...)
	ret, _, err := replayTestnetTx(t, 1534614, "0x39c6a872093a43cCA3aDe6040CcC0faF010e2625", code, input,
		1_000_000, 22_008, 985_098)
	require.ErrorIs(t, err, ErrExecutionReverted)
	require.Contains(t, string(ret), "Precompile call failed")
}

// replayTestnetTx executes a historical Hemi testnet tx (sender 0xbb1d…D38F) against contract code inside the
// pre-phase0 window at block, and asserts that intrinsic + execution gas equals the canonical receipt's gasUsed.
func replayTestnetTx(t *testing.T, block uint64, to string, code, input []byte, gasLimit, intrinsic, wantGasUsed uint64) ([]byte, *state.StateDB, error) {
	t.Helper()
	sender := common.HexToAddress("0xbb1de7bB6049a20ec360f26d468337476Ce2D38F")
	coinbase := common.HexToAddress("0x4200000000000000000000000000000000000011")
	contract := common.HexToAddress(to)

	evm, statedb := newPrePhase0EVM(t, true)
	evm.Context.BlockNumber = new(big.Int).SetUint64(block)
	statedb.SetCode(contract, code, 0)
	statedb.Prepare(evm.chainRules, sender, coinbase, &contract, ActivePrecompiles(evm.chainRules), nil)
	ret, left, err := evm.Call(sender, contract, input, gasLimit-intrinsic, new(uint256.Int))
	require.Equal(t, wantGasUsed, intrinsic+(gasLimit-intrinsic-left), "gasUsed must match the canonical receipt")
	return ret, statedb, err
}

// Bytecode of the testnet callers at 0xe610df42…cc12 (block 1534740) and 0x885cd1be…532c (block 1540534). Both
// expose 0x43e033b6 (btcBalAddr wrapper) and 0xdc04b577 (btcLastHeader wrapper); the second also logs the result.
const (
	prePhase0CallerE610 = "0x608060405234801561000f575f80fd5b5060043610610034575f3560e01c806343e033b614610038578063dc04b57714610068575b5f80fd5b610052600480360381019061004d919061035c565b610086565b60405161005f9190610403565b60405180910390f35b61007061015c565b60405161007d9190610403565b60405180910390f35b60605f80604073ffffffffffffffffffffffffffffffffffffffff16846040516020016100b39190610475565b6040516020818303038152906040526040516100cf91906104cf565b5f604051808303815f865af19150503d805f8114610108576040519150601f19603f3d011682016040523d82523d5f602084013e61010d565b606091505b509150915081610152576040517f08c379a00000000000000000000000000000000000000000000000000000000081526004016101499061052f565b60405180910390fd5b8092505050919050565b60605f80604473ffffffffffffffffffffffffffffffffffffffff1660405161018490610570565b5f604051808303815f865af19150503d805f81146101bd576040519150601f19603f3d011682016040523d82523d5f602084013e6101c2565b606091505b509150915081610207576040517f08c379a00000000000000000000000000000000000000000000000000000000081526004016101fe906105f4565b60405180910390fd5b809250505090565b5f604051905090565b5f80fd5b5f80fd5b5f80fd5b5f80fd5b5f601f19601f8301169050919050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52604160045260245ffd5b61026e82610228565b810181811067ffffffffffffffff8211171561028d5761028c610238565b5b80604052505050565b5f61029f61020f565b90506102ab8282610265565b919050565b5f67ffffffffffffffff8211156102ca576102c9610238565b5b6102d382610228565b9050602081019050919050565b828183375f83830152505050565b5f6103006102fb846102b0565b610296565b90508281526020810184848401111561031c5761031b610224565b5b6103278482856102e0565b509392505050565b5f82601f83011261034357610342610220565b5b81356103538482602086016102ee565b91505092915050565b5f6020828403121561037157610370610218565b5b5f82013567ffffffffffffffff81111561038e5761038d61021c565b5b61039a8482850161032f565b91505092915050565b5f81519050919050565b5f82825260208201905092915050565b8281835e5f83830152505050565b5f6103d5826103a3565b6103df81856103ad565b93506103ef8185602086016103bd565b6103f881610228565b840191505092915050565b5f6020820190508181035f83015261041b81846103cb565b905092915050565b5f81519050919050565b5f82825260208201905092915050565b5f61044782610423565b610451818561042d565b93506104618185602086016103bd565b61046a81610228565b840191505092915050565b5f6020820190508181035f83015261048d818461043d565b905092915050565b5f81905092915050565b5f6104a9826103a3565b6104b38185610495565b93506104c38185602086016103bd565b80840191505092915050565b5f6104da828461049f565b915081905092915050565b7f507265636f6d70696c652063616c6c206661696c6564000000000000000000005f82015250565b5f61051960168361042d565b9150610524826104e5565b602082019050919050565b5f6020820190508181035f8301526105468161050d565b9050919050565b50565b5f61055b5f83610495565b91506105668261054d565b5f82019050919050565b5f61057a82610550565b9150819050919050565b7f507265636f6d70696c652063616c6c20746f206274634c6173744865616465725f8201527f206661696c656400000000000000000000000000000000000000000000000000602082015250565b5f6105de60278361042d565b91506105e982610584565b604082019050919050565b5f6020820190508181035f83015261060b816105d2565b905091905056fea2646970667358221220d11c3e433215ae71ec62a8f8bbcc743db933c3046e529950e402ac27afd85fb464736f6c634300081a0033"
	prePhase0Caller885c = "0x608060405234801561000f575f80fd5b5060043610610034575f3560e01c806343e033b614610038578063dc04b57714610068575b5f80fd5b610052600480360381019061004d9190610395565b610086565b60405161005f919061043c565b60405180910390f35b610070610195565b60405161007d919061043c565b60405180910390f35b60605f80604073ffffffffffffffffffffffffffffffffffffffff16846040516020016100b391906104a0565b6040516020818303038152906040526040516100cf91906104f0565b5f604051808303815f865af19150503d805f8114610108576040519150601f19603f3d011682016040523d82523d5f602084013e61010d565b606091505b50915091507f582326e533af48b16567b0565a82550442e225cf8491cb9ae2a29e1f96935e7c8282604051610143929190610520565b60405180910390a18161018b576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401610182906105a8565b60405180910390fd5b8092505050919050565b60605f80604473ffffffffffffffffffffffffffffffffffffffff166040516101bd906105e9565b5f604051808303815f865af19150503d805f81146101f6576040519150601f19603f3d011682016040523d82523d5f602084013e6101fb565b606091505b509150915081610240576040517f08c379a00000000000000000000000000000000000000000000000000000000081526004016102379061066d565b60405180910390fd5b809250505090565b5f604051905090565b5f80fd5b5f80fd5b5f80fd5b5f80fd5b5f601f19601f8301169050919050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52604160045260245ffd5b6102a782610261565b810181811067ffffffffffffffff821117156102c6576102c5610271565b5b80604052505050565b5f6102d8610248565b90506102e4828261029e565b919050565b5f67ffffffffffffffff82111561030357610302610271565b5b61030c82610261565b9050602081019050919050565b828183375f83830152505050565b5f610339610334846102e9565b6102cf565b9050828152602081018484840111156103555761035461025d565b5b610360848285610319565b509392505050565b5f82601f83011261037c5761037b610259565b5b813561038c848260208601610327565b91505092915050565b5f602082840312156103aa576103a9610251565b5b5f82013567ffffffffffffffff8111156103c7576103c6610255565b5b6103d384828501610368565b91505092915050565b5f81519050919050565b5f82825260208201905092915050565b8281835e5f83830152505050565b5f61040e826103dc565b61041881856103e6565b93506104288185602086016103f6565b61043181610261565b840191505092915050565b5f6020820190508181035f8301526104548184610404565b905092915050565b5f81519050919050565b5f81905092915050565b5f61047a8261045c565b6104848185610466565b93506104948185602086016103f6565b80840191505092915050565b5f6104ab8284610470565b915081905092915050565b5f81905092915050565b5f6104ca826103dc565b6104d481856104b6565b93506104e48185602086016103f6565b80840191505092915050565b5f6104fb82846104c0565b915081905092915050565b5f8115159050919050565b61051a81610506565b82525050565b5f6040820190506105335f830185610511565b81810360208301526105458184610404565b90509392505050565b5f82825260208201905092915050565b7f507265636f6d70696c652063616c6c206661696c6564000000000000000000005f82015250565b5f61059260168361054e565b915061059d8261055e565b602082019050919050565b5f6020820190508181035f8301526105bf81610586565b9050919050565b50565b5f6105d45f836104b6565b91506105df826105c6565b5f82019050919050565b5f6105f3826105c9565b9150819050919050565b7f507265636f6d70696c652063616c6c20746f206274634c6173744865616465725f8201527f206661696c656400000000000000000000000000000000000000000000000000602082015250565b5f61065760278361054e565b9150610662826105fd565b604082019050919050565b5f6020820190508181035f8301526106848161064b565b905091905056fea2646970667358221220b7368f63a5d0faa8c927adeffc3735add8c7aa9b1377c52e74bfe7bbf563fad364736f6c634300081a0033"
)

// Block 1534740, tx 0x190fe4d016699b4ba162e722e7f194747a12e84276d5abbb5d85158b19cc2bf4 (and 9 identical txs up
// to block 1539063): dc04b577() calls 0x44 and returns its result. Receipt: status 1, gasUsed 27,165 / 27,510.
// Intrinsic = 21,000 + 4 non-zero bytes * 16 = 21,064. Only the 116-byte result length affects gas.
func TestPrePhase0TestnetBlock1534740(t *testing.T) {
	ret, statedb, err := replayTestnetTx(t, 1534740, "0xe610df420f926d2deb0f11d5e9a7ceaa5af4cc12",
		common.FromHex(prePhase0CallerE610), common.FromHex("dc04b577"), 27_510, 21_064, 27_165)
	require.NoError(t, err)
	require.Len(t, ret, 32+32+128, "abi.encode(bytes) of the 116-byte header")
	require.Empty(t, statedb.Logs())
}

// Block 1540534, tx 0x0660a8ff63fddba107aec7d1a005590ca23301a7e7bd0be6b88c764c69d5fb75: 43e033b6(addr) calls 0x40
// with the raw address and LOGS the result, so the historical balance (pinned in legacyHvmKnownResults) is part
// of the receipt. Receipt: status 1, gasUsed 76,604 / 77,491, one log whose data carries 0x000000000b147ca0.
func TestPrePhase0TestnetBlock1540534(t *testing.T) {
	input := append(common.FromHex("43e033b6"), prePhase0AbiEncodedAddrInput...)
	wantLogData := common.FromHex(
		"0000000000000000000000000000000000000000000000000000000000000001" +
			"0000000000000000000000000000000000000000000000000000000000000040" +
			"0000000000000000000000000000000000000000000000000000000000000008" +
			"000000000b147ca0000000000000000000000000000000000000000000000000")
	_, statedb, err := replayTestnetTx(t, 1540534, "0x885cd1beDC776C156b97643f70adA7293827532c",
		common.FromHex(prePhase0Caller885c), input, 77_491, 22_008, 76_604)
	require.NoError(t, err)
	logs := statedb.Logs()
	require.Len(t, logs, 1)
	require.Equal(t, common.HexToHash("0x582326e533af48b16567b0565a82550442e225cf8491cb9ae2a29e1f96935e7c"), logs[0].Topics[0])
	require.Equal(t, wantLogData, logs[0].Data, "log must carry the historical balance, as in the canonical receipt")
}

// Inside the window runPrecompile must never call Run (no TBC) and must charge exactly RequiredGas. A
// precompile outside the v1.14.2 set falls through to an empty success.
func TestPrePhase0WindowNoopNeverRuns(t *testing.T) {
	p := panickingHVMPrecompile{} // Run panics: proves the no-op path never reaches it
	hvmPrecompileSet[p] = struct{}{}
	defer delete(hvmPrecompileSet, p)

	evm, _ := newPrePhase0EVM(t, true)
	const gas = uint64(100_000)
	beforeNoop := hvmPrecompilePrePhase0Counter.Snapshot().Count()
	beforeInvalid := hvmPrecompileInvalidDataCounter.Snapshot().Count()

	var (
		ret []byte
		rem uint64
		err error
	)
	require.NotPanics(t, func() { ret, rem, err = evm.runPrecompile(p, []byte{0x01}, gas) })
	require.NoError(t, err)
	require.Nil(t, ret)
	require.Equal(t, gas-panickingHVMGas, rem)
	require.Equal(t, beforeNoop+1, hvmPrecompilePrePhase0Counter.Snapshot().Count())
	require.Equal(t, beforeInvalid, hvmPrecompileInvalidDataCounter.Snapshot().Count(),
		"the pre-phase0 no-op is expected history, not an invalid-data alert")

	// Insufficient gas behaves like any precompile: out of gas, everything consumed.
	_, rem, err = evm.runPrecompile(p, nil, panickingHVMGas-1)
	require.ErrorIs(t, err, ErrOutOfGas)
	require.Zero(t, rem)
}

// Regression for the sepolia/testnet3 sync failure shape: a contract STATICCALLs 0x40 before hVM Phase 0.
// Inside the window the call costs a warm access plus btcBalAddr's RequiredGas and returns empty; without it
// the call is a cold access to an empty account. The difference is what split gasUsed/state root.
func TestPrePhase0ContractCallTo0x40(t *testing.T) {
	// PUSH1 0 x4 (ret/args), PUSH1 0x40, GAS, STATICCALL, POP, STOP
	code := common.FromHex("600060006000600060405afa5000")
	sender := common.HexToAddress("0x1111111111111111111111111111111111111111")
	coinbase := common.HexToAddress("0x2222222222222222222222222222222222222222")
	contract := common.HexToAddress("0x3333333333333333333333333333333333333333")
	const gas = uint64(1_000_000)
	const opsGas = 5*3 + 2 + 2 // 5x PUSH1, GAS, POP

	run := func(window bool) uint64 {
		evm, statedb := newPrePhase0EVM(t, window)
		statedb.SetCode(contract, code, 0)
		statedb.Prepare(evm.chainRules, sender, coinbase, &contract, ActivePrecompiles(evm.chainRules), nil)
		ret, left, err := evm.Call(sender, contract, nil, gas, new(uint256.Int))
		require.NoError(t, err)
		require.Empty(t, ret)
		return gas - left
	}

	require.Equal(t, uint64(opsGas+params.ColdAccountAccessCostEIP2929), run(false),
		"no window: cold call to an empty account (behavior unchanged)")
	require.Equal(t, uint64(opsGas+params.WarmStorageReadCostEIP2929+params.BtcAddrBal), run(true),
		"window: warm hVM precompile charging RequiredGas, empty no-op")
}
