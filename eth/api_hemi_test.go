package eth

import (
	"io/ioutil"
	"os"
	"testing"
	"time"

	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/go-test/deep"
	"github.com/hemilabs/heminetwork/database"
	"github.com/hemilabs/heminetwork/service/tbc"
)

func TestGetBtcBlockByHash(t *testing.T) {
	type testTableItem struct {
		name          string
		hash          chainhash.Hash
		expectedError error
		testNoInit    bool
	}

	fakeBitcoinBlockHash := chainhash.DoubleHashH([]byte("notreal"))
	realBitcoinBlockHash := *chaincfg.RegressionNetParams.GenesisHash
	realBitcoinBlock := chaincfg.RegressionNetParams.GenesisBlock

	testTable := []testTableItem{
		testTableItem{
			name:          "btc block by hash not found",
			hash:          fakeBitcoinBlockHash,
			expectedError: database.BlockNotFoundError{fakeBitcoinBlockHash},
		},
		testTableItem{
			name:          "btc block by hash found (regtest genesis)",
			hash:          realBitcoinBlockHash,
			expectedError: nil,
		},
		testTableItem{
			name:          "tbc not init yet",
			expectedError: ErrTbcFullNodeNotInit,
			testNoInit:    true,
		},
	}

	for _, testCase := range testTable {
		t.Run(testCase.name, func(t *testing.T) {
			vm.TBCFullNode = nil
			if !testCase.testNoInit {
				tbcParentDir := os.TempDir()
				tbcDir, err := ioutil.TempDir(tbcParentDir, testCase.name)
				if err != nil {
					t.Fatal(err)
				}
				defer os.RemoveAll(tbcDir)

				if err := vm.SetupTBCFullNode(t.Context(), &tbc.Config{
					Network:     "localnet",
					LevelDBHome: tbcDir,
					Seeds:       []string{},
				}); err != nil {
					t.Fatalf("could not set up tbc full node: %s", err)
				}

				select {
				case <-time.After(5 * time.Second):
				case <-t.Context().Done():
					t.Fatal(t.Context().Err())
				}
			}

			backend := initBackend(true)

			block, err := backend.GetBtcBlockByHash(t.Context(), testCase.hash)
			if err != nil && testCase.expectedError == nil {
				t.Fatalf("unexpected error: %s", err)
			} else if err != nil && testCase.expectedError != nil {
				if diff := deep.Equal(err, testCase.expectedError); len(diff) > 0 {
					t.Fatalf("unexpected diff: %s", diff)
				}
			} else if testCase.expectedError == nil {
				if diff := deep.Equal(btcutil.NewBlock(realBitcoinBlock), block); len(diff) > 0 {
					t.Fatalf("unexpected diff: %s", diff)
				}
			}
		})
	}
}

func TestGetBtcBlockHeaderByHash(t *testing.T) {
	type testTableItem struct {
		name          string
		hash          chainhash.Hash
		expectedError error
		testNoInit    bool
	}

	fakeBitcoinBlockHash := chainhash.DoubleHashH([]byte("notreal"))
	realBitcoinBlockHash := *chaincfg.RegressionNetParams.GenesisHash
	realBitcoinBlockHeader := chaincfg.RegressionNetParams.GenesisBlock.Header

	testTable := []testTableItem{
		testTableItem{
			name:          "btc block by hash not found",
			hash:          fakeBitcoinBlockHash,
			expectedError: database.ErrNotFound,
		},
		testTableItem{
			name:          "btc block by hash found (regtest genesis)",
			hash:          realBitcoinBlockHash,
			expectedError: nil,
		},
		testTableItem{
			name:          "tbc not init yet",
			expectedError: ErrTbcFullNodeNotInit,
			testNoInit:    true,
		},
	}

	for _, testCase := range testTable {
		t.Run(testCase.name, func(t *testing.T) {
			vm.TBCFullNode = nil
			if !testCase.testNoInit {
				tbcParentDir := os.TempDir()
				tbcDir, err := ioutil.TempDir(tbcParentDir, testCase.name)
				if err != nil {
					t.Fatal(err)
				}
				defer os.RemoveAll(tbcDir)

				if err := vm.SetupTBCFullNode(t.Context(), &tbc.Config{
					Network:     "localnet",
					LevelDBHome: tbcDir,
					Seeds:       []string{},
				}); err != nil {
					t.Fatalf("could not set up tbc full node: %s", err)
				}

				select {
				case <-time.After(5 * time.Second):
				case <-t.Context().Done():
					t.Fatal(t.Context().Err())
				}
			}

			backend := initBackend(true)

			blockHeader, err := backend.GetBtcBlockHeaderByHash(t.Context(), testCase.hash)
			if err != nil && testCase.expectedError == nil {
				t.Fatalf("unexpected error: %s", err)
			} else if err != nil && testCase.expectedError != nil {
				if diff := deep.Equal(err, testCase.expectedError); len(diff) > 0 {
					t.Fatalf("unexpected diff: %s", diff)
				}
			} else if testCase.expectedError == nil {
				if diff := deep.Equal(&realBitcoinBlockHeader, blockHeader); len(diff) > 0 {
					t.Fatalf("unexpected diff: %s", diff)
				}
			}
		})
	}
}
