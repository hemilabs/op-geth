package vm

import (
	"encoding/hex"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"
)

func TestSetBitcoinStateRoot(t *testing.T) {
	address := common.BytesToAddress([]byte("contract"))
	t.Logf("the address is %s", address)

	statedb, _ := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
	statedb.SetState(address, common.HexToHash("0x123"), common.HexToHash("0x456"))

	t.Setenv("TMP_BITCOIN_CONTRACT_ADDRESS", address.Hex())
	defer t.Setenv("TMP_BITCOIN_CONTRACT_ADDRESS", "")
	t.Setenv("TMP_BITCOIN_CONTRACT_STORAGE_SLOT", "0x123")
	defer t.Setenv("TMP_BITCOIN_CONTRACT_STORAGE_SLOT", "")

	if _, err := statedb.Commit(1, false, false); err != nil {
		t.Fatal(err)
	}

	vmctx := BlockContext{
		CanTransfer: func(StateDB, common.Address, *uint256.Int) bool { return true },
		Transfer:    func(StateDB, common.Address, common.Address, *uint256.Int) {},
	}
	evm := NewEVM(vmctx, statedb, params.AllEthashProtocolChanges, Config{})

	t.Logf("bitcoinStateRoot = %s", hex.EncodeToString(evm.bitcoinStateRoot))

	if hex.EncodeToString(evm.bitcoinStateRoot) != "0000000000000000000000000000000000000000000000000000000000000456" {
		t.Fatalf("unexpected bitcoin state root in evm: %s", hex.EncodeToString(evm.bitcoinStateRoot))
	}
}
