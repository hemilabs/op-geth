// Copyright 2017 The go-ethereum Authors
// This file is part of go-ethereum.
//
// go-ethereum is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// go-ethereum is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with go-ethereum. If not, see <http://www.gnu.org/licenses/>.

package main

import (
	"bufio"
	"bytes"
	context2 "context"
	"errors"
	"fmt"
	"os"
	"reflect"
	"runtime"
	"strings"
	"time"
	"unicode"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/hemilabs/heminetwork/cmd/btctool/bdf"
	"github.com/hemilabs/heminetwork/service/tbc"

	"github.com/ethereum/go-ethereum/accounts"
	"github.com/ethereum/go-ethereum/accounts/external"
	"github.com/ethereum/go-ethereum/accounts/keystore"
	"github.com/ethereum/go-ethereum/accounts/scwallet"
	"github.com/ethereum/go-ethereum/accounts/usbwallet"
	"github.com/ethereum/go-ethereum/cmd/utils"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/eth/catalyst"
	"github.com/ethereum/go-ethereum/eth/ethconfig"
	"github.com/ethereum/go-ethereum/internal/ethapi"
	"github.com/ethereum/go-ethereum/internal/flags"
	"github.com/ethereum/go-ethereum/internal/version"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/metrics"
	"github.com/ethereum/go-ethereum/node"
	"github.com/ethereum/go-ethereum/params"
	"github.com/naoina/toml"
	"github.com/urfave/cli/v2"
)

var (
	dumpConfigCommand = &cli.Command{
		Action:      dumpConfig,
		Name:        "dumpconfig",
		Usage:       "Export configuration values in a TOML format",
		ArgsUsage:   "<dumpfile (optional)>",
		Flags:       flags.Merge(nodeFlags, rpcFlags),
		Description: `Export configuration values in TOML format (to stdout by default).`,
	}

	configFileFlag = &cli.StringFlag{
		Name:     "config",
		Usage:    "TOML configuration file",
		Category: flags.EthCategory,
	}
)

// These settings ensure that TOML keys use the same names as Go struct fields.
var tomlSettings = toml.Config{
	NormFieldName: func(rt reflect.Type, key string) string {
		return key
	},
	FieldToKey: func(rt reflect.Type, field string) string {
		return field
	},
	MissingField: func(rt reflect.Type, field string) error {
		id := fmt.Sprintf("%s.%s", rt.String(), field)
		if deprecated(id) {
			log.Warn("Config field is deprecated and won't have an effect", "name", id)
			return nil
		}
		var link string
		if unicode.IsUpper(rune(rt.Name()[0])) && rt.PkgPath() != "main" {
			link = fmt.Sprintf(", see https://godoc.org/%s#%s for available fields", rt.PkgPath(), rt.Name())
		}
		return fmt.Errorf("field '%s' is not defined in %s%s", field, rt.String(), link)
	},
}

type ethstatsConfig struct {
	URL string `toml:",omitempty"`
}

type gethConfig struct {
	Eth      ethconfig.Config
	Node     node.Config
	Ethstats ethstatsConfig
	Metrics  metrics.Config
}

func loadConfig(file string, cfg *gethConfig) error {
	f, err := os.Open(file)
	if err != nil {
		return err
	}
	defer f.Close()

	err = tomlSettings.NewDecoder(bufio.NewReader(f)).Decode(cfg)
	// Add file name to errors that have a line number.
	if _, ok := err.(*toml.LineError); ok {
		err = errors.New(file + ", " + err.Error())
	}
	return err
}

func defaultNodeConfig() node.Config {
	git, _ := version.VCS()
	cfg := node.DefaultConfig
	cfg.Name = clientIdentifier
	cfg.Version = params.VersionWithCommit(git.Commit, git.Date)
	cfg.HTTPModules = append(cfg.HTTPModules, "eth")
	cfg.WSModules = append(cfg.WSModules, "eth")
	cfg.IPCPath = "geth.ipc"
	return cfg
}

// loadBaseConfig loads the gethConfig based on the given command line
// parameters and config file.
func loadBaseConfig(ctx *cli.Context) gethConfig {
	// Load defaults.
	cfg := gethConfig{
		Eth:     ethconfig.Defaults,
		Node:    defaultNodeConfig(),
		Metrics: metrics.DefaultConfig,
	}

	// Load config file.
	if file := ctx.String(configFileFlag.Name); file != "" {
		if err := loadConfig(file, &cfg); err != nil {
			utils.Fatalf("%v", err)
		}
	}

	// Apply flags.
	utils.SetNodeConfig(ctx, &cfg.Node)
	return cfg
}

// makeConfigNode loads geth configuration and creates a blank node instance.
func makeConfigNode(ctx *cli.Context) (*node.Node, gethConfig) {
	cfg := loadBaseConfig(ctx)
	stack, err := node.New(&cfg.Node)
	if err != nil {
		utils.Fatalf("Failed to create the protocol stack: %v", err)
	}
	// Node doesn't by default populate account manager backends
	if err := setAccountManagerBackends(stack.Config(), stack.AccountManager(), stack.KeyStoreDir()); err != nil {
		utils.Fatalf("Failed to set account manager backends: %v", err)
	}

	utils.SetEthConfig(ctx, stack, &cfg.Eth)
	if ctx.IsSet(utils.EthStatsURLFlag.Name) {
		cfg.Ethstats.URL = ctx.String(utils.EthStatsURLFlag.Name)
	}
	applyMetricConfig(ctx, &cfg)

	return stack, cfg
}

// makeFullNode loads geth configuration and creates the Ethereum backend.
func makeFullNode(ctx *cli.Context) (*node.Node, ethapi.Backend) {
	stack, cfg := makeConfigNode(ctx)
	if ctx.IsSet(utils.OverrideCancun.Name) {
		v := ctx.Uint64(utils.OverrideCancun.Name)
		cfg.Eth.OverrideCancun = &v
	}

	if ctx.IsSet(utils.OverrideOptimismCanyon.Name) {
		v := ctx.Uint64(utils.OverrideOptimismCanyon.Name)
		cfg.Eth.OverrideOptimismCanyon = &v
	}

	if ctx.IsSet(utils.OverrideOptimismEcotone.Name) {
		v := ctx.Uint64(utils.OverrideOptimismEcotone.Name)
		cfg.Eth.OverrideOptimismEcotone = &v
	}

	if ctx.IsSet(utils.OverrideOptimismInterop.Name) {
		v := ctx.Uint64(utils.OverrideOptimismInterop.Name)
		cfg.Eth.OverrideOptimismInterop = &v
	}

	if ctx.IsSet(utils.OverrideVerkle.Name) {
		v := ctx.Uint64(utils.OverrideVerkle.Name)
		cfg.Eth.OverrideVerkle = &v
	}

	if ctx.IsSet(utils.OverrideHvmEnabled.Name) {
		v := ctx.Bool(utils.OverrideHvmEnabled.Name)
		cfg.Eth.HvmEnabled = v
	}
	if ctx.IsSet(utils.OverrideHvmGenesisHeader.Name) {
		v := ctx.String(utils.OverrideHvmGenesisHeader.Name)
		cfg.Eth.HvmGenesisHeader = v
	}
	if ctx.IsSet(utils.OverrideHvmGenesisHeight.Name) {
		v := ctx.Uint64(utils.OverrideHvmGenesisHeight.Name)
		cfg.Eth.HvmGenesisHeight = v
	}
	if ctx.IsSet(utils.OverrideHvmHeaderDataDir.Name) {
		v := ctx.String(utils.OverrideHvmHeaderDataDir.Name)
		cfg.Eth.HvmHeaderDataDir = v
	}
	if ctx.IsSet(utils.OverrideHvm0.Name) {
		v := ctx.Uint64(utils.OverrideHvm0.Name)
		cfg.Eth.OverrideHemiHvm0 = &v
	}

	// TODO: expose debug.verbosityFlag or pass verbosity setting up the stack
	verbosity := ctx.Int("verbosity")

	backend, eth := utils.RegisterEthService(stack, &cfg.Eth)

	if cfg.Eth.HvmEnabled {
		// Before starting up any other services, make sure TBC is in correct initial state
		fullNodeTbcCfg := tbc.NewDefaultConfig()

		if ctx.IsSet(utils.TBCListenAddress.Name) {
			fullNodeTbcCfg.ListenAddress = ctx.String(utils.TBCListenAddress.Name)
		}
		if ctx.IsSet(utils.TBCMaxCachedTxs.Name) {
			fullNodeTbcCfg.MaxCachedTxs = ctx.Int(utils.TBCMaxCachedTxs.Name)
		}
		if ctx.IsSet(utils.TBCLevelDBHome.Name) {
			fullNodeTbcCfg.LevelDBHome = ctx.String(utils.TBCLevelDBHome.Name)
		}
		if ctx.IsSet(utils.TBCBlockSanity.Name) {
			fullNodeTbcCfg.BlockSanity = ctx.Bool(utils.TBCBlockSanity.Name)
		}
		if ctx.IsSet(utils.TBCNetwork.Name) {
			fullNodeTbcCfg.Network = ctx.String(utils.TBCNetwork.Name)
		}
		if ctx.IsSet(utils.TBCPrometheusAddress.Name) {
			fullNodeTbcCfg.PrometheusListenAddress = ctx.String(utils.TBCPrometheusAddress.Name)
		}
		if ctx.IsSet(utils.TBCSeeds.Name) {
			fullNodeTbcCfg.Seeds = ctx.StringSlice(utils.TBCSeeds.Name)
		}

		logLevel := "INFO"  // Anything 0-3 (silent to info) maps to "INFO" for TBC
		if verbosity == 4 { // Geth debug = TBC TRACE
			logLevel = "DEBUG"
		} else if verbosity == 5 { // Geth detail = TBC TRACE
			logLevel = "TRACE"
		}

		// Set tbc, tbcd, and leveldb log levels to the log level based on op-geth
		fullNodeTbcCfg.LogLevel = "tbcd=" + logLevel + ";tbc=" + logLevel + ";level=" + logLevel

		// Initialize TBC Bitcoin indexer to answer hVM queries
		err := vm.SetupTBCFullNode(ctx.Context, fullNodeTbcCfg)
		if err != nil {
			log.Crit("Unable to setup TBC Full Node", "err", err)
		}

		genesisHeader, err := bdf.Hex2Header(cfg.Eth.HvmGenesisHeader)
		genesisHash := genesisHeader.BlockHash()
		genesisHeight := cfg.Eth.HvmGenesisHeight

		log.Info("Waiting for TBC full node to finish startup")

		for {
			time.Sleep(100 * time.Millisecond)
			if vm.TBCFullNode.Running() {
				break
			}
		}
		log.Info("TBC full node done loading.")

		log.Info(fmt.Sprintf("TBC Full Node started, will sync to Bitcoin block %s configured as the start "+
			"of hVM consensus tracking on this chain.", genesisHash.String()))

		var syncInfo tbc.SyncInfo

		// Require a complete sync of TBC full node up to the hVM genesis height whether or not we have
		// passed the hVM Phase 0 activation height, so that the node will not continue starting up
		// until it will be in the correct initial condition when the hVM Phase 0 activation occurs,
		// rather than working correctly until then and freezing at activation until TBC is caught up.
		// Would rather have node delay full startup to fully sync TBC to required genesis height
		// than startup without full information and later freeze at hVM Phase 0 activation time.
		for {
			bh, bhb, err := vm.TBCFullNode.BlockHeaderBest(ctx.Context)
			if err != nil {
				// Being unable to retrieve the best block header known by the TBC Full Node indiciates
				// either a bug or data corruption, so exit with crit.
				log.Crit("could not get best block header from TBC full node", "err", err)
			}

			log.Info(fmt.Sprintf("got best block header of %s",
				bhb.BlockHash().String()))

			// Get the current indexer information and make sure both indexers are at the same height
			syncInfo = *vm.GetTBCFullNodeSyncStatus()

			utxoHH := syncInfo.Utxo
			txHH := syncInfo.Tx

			if !bytes.Equal(utxoHH.Hash[:], txHH.Hash[:]) {
				// TBC is in an invalid indexing state as its UTXO and Tx indexers are not matched,
				// attempt to automatically recover by unindexing both back to their common shared
				// ancestor.
				err := vm.FixMismatchedIndexesIfRequired()
				if err != nil {
					// If we have mismatched indexes that we aren't able to repair, this is a critical
					// error and likely due to data corruption in TBC needing manual intervention to resolve.
					log.Crit(fmt.Sprintf("On startup, TBC Full Node has mismatched indexers, "+
						"UTXO = %s @ %d, Tx = %s @ %d, and automatic recovery to walk indexers back to a common "+
						"ancestor failed. This is likely due to TBC state corruption. Either restore a "+
						"working older TBC full node data directory to the currently set TBCLevelDB home (%s), or "+
						"delete it and let op-geth resync the TBC full node from scratch.", utxoHH.Hash.String(),
						utxoHH.Height, txHH.Hash.String(), txHH.Height, fullNodeTbcCfg.LevelDBHome), "err", err)
				}
			}

			if bh >= genesisHeight {
				// TBC full node already has awareness of BTC chain at/beyond the genesis height, so make sure
				// that it is also *indexed* to at least the genesis height.

				// At this point UTXO and Tx indexers are at the same height, so we can do everything based
				// off the UTXO one. Check whether the indexers are above the genesis height, and if not index
				// up to that height.

				if utxoHH.Height < genesisHeight {
					// Safe to assume that a higher height means we are indexed past the effective genesis block
					// (rather than indexed on a fork before the genesis) as the hVM protocol makes the assumption
					// that the effective genesis block will never be forked, and should be set far enough in the
					// past that it is deemed safe.

					// First check that all blocks from the current indexed tip to the target hVM Phase 0 activation
					// effective genesis block are available, and if not kick off async requests to download these
					// from peers. Do this by walking back from the effective genesis header, rather than attempting
					// to walk forward from current indexed tip and determine which known headers are on the canonical
					// chain.

					// Even if we are indexed onto a fork, this function will check the full availability of
					// full blocks from the common fork point between the current indexed tip and the target
					// effective genesis header.
					available, missingFullBlockHeaders, missingHeaderHash, err := vm.TBCBlocksAvailableToHeader(ctx.Context, genesisHeader)
					if err != nil {
						// This is a critical error on startup, generally meaning the TBC Full Node has missing
						// header knowledge somewhere. Errors will only be returned if there is an underlying
						// problem finding the header or reading from the database.

						// Check if there were missing full blocks returned in addition to the error and print them
						// out, but do not attempt a refetch as we are going to exit due to the error.
						if missingFullBlockHeaders != nil && len(*missingFullBlockHeaders) > 0 {
							for i := 0; i < len(*missingFullBlockHeaders); i++ {
								log.Warn(fmt.Sprintf("\tTBC missing full block: %s",
									(*missingFullBlockHeaders)[i].BlockHash().String()))
							}
						}

						log.Crit(fmt.Sprintf("On startup, TBC Full Node reports knowledge of hVM effective "+
							"genesis block, but an unexpected error was encountered when attempting to check all "+
							"full BTC blocks are available to that genesis height. Indexer: %s @ %d, genesis: %s @ %d",
							utxoHH.Hash.String(), utxoHH.Height, genesisHeader.BlockHash().String(), genesisHeight),
							"err", err)
					}

					if !available {
						// One or more full blocks or a header are not known below the hVM Phase 0 activation height,
						// even though the block for the activation height itself is known.

						// If there is a header itself unavailable then this is a critical error, as TBC should not
						// be able to return a best block at/after genesis without having headers prior to it.
						if missingHeaderHash != nil {
							log.Crit(fmt.Sprintf("TBC Full Node reports knowledge of hVM effective genesis "+
								"block %s @ %d, but is missing a header %s below that height",
								genesisHeader.BlockHash().String(), genesisHeight, missingHeaderHash.String()))
						}

						// If there are one or more blocks missing, attempt to refetch them
						if missingFullBlockHeaders != nil {
							if missingFullBlockHeaders != nil && len(*missingFullBlockHeaders) > 0 {
								for i := 0; i < len(*missingFullBlockHeaders); i++ {
									log.Warn(fmt.Sprintf("\tTBC missing full block: %s",
										(*missingFullBlockHeaders)[i].BlockHash().String()))
									vm.TBCAttemptBlockRefetch(context2.Background(), &(*missingFullBlockHeaders)[i])
								}
							}
						} else {
							// Should be impossible to have available=false but neither a missing header or block
							// identified without an error returned, so exit with crit for unexpected behavior
							log.Crit("TBC Full Node reports knowledge of hVM effective genesis block %s @ %d," +
								" but claims to be missing block information below that height without indicating " +
								"what information is missing")
						}
						// Now that we have attempted refetches, allow the loop to run again and if the missing
						// blocks have been received then the else condition below will be hit.
						continue
					} else {
						emptyHash := &chainhash.Hash{}

						if emptyHash.IsEqual(&utxoHH.Hash) && emptyHash.IsEqual(&txHH.Hash) {
							log.Info("both utxo and header hash are zeroed, not synced yet, force syncing")
							err := vm.TBCFullNode.SyncIndexersToHash(ctx.Context, &genesisHash)
							if err != nil {
								log.Crit("could not sync indexers to hash", "error", err)
							}
						}

						// All blocks are available to index up to the genesis header, so move the indexer forward
						err := vm.TBCIndexToHeader(genesisHeader)
						if err != nil {
							log.Crit(fmt.Sprintf("On startup, TBC Full Node reports full knowledge of all "+
								"blocks required to index to the hVM effective genesis block %s @ %d but returned "+
								"an unexpected error while attempting move the indexers to the effective genesis block",
								genesisHeader.BlockHash().String(), genesisHeight), "err", err)
						}

						// Ensure that the full TBC node truly has moved both indexers to the effective genesis block,
						// and if not then fail with crit as the above TBCIndexToHeader must have failed to make
						// the appropriate state changes without returning an error.
						syncInfo = *vm.GetTBCFullNodeSyncStatus()

						utxoHH := syncInfo.Utxo
						txHH := syncInfo.Tx

						if !bytes.Equal(utxoHH.Hash[:], genesisHash[:]) {
							log.Crit(fmt.Sprintf("On startup, TBC Full Node was indexed to the hVM "+
								"effective genesis block %s @ %d but afterwards its UTXO indexer reports it is "+
								"indexed to %s @ %d instead", genesisHash.String(), genesisHeight,
								utxoHH.Hash.String(), utxoHH.Height))
						}

						if !bytes.Equal(txHH.Hash[:], genesisHash[:]) {
							log.Crit(fmt.Sprintf("On startup, TBC Full Node was indexed to the hVM "+
								"effective genesis block %s @ %d but afterwards its Tx indexer reports it is "+
								"indexed to %s @ %d instead", genesisHash.String(), genesisHeight,
								txHH.Hash.String(), txHH.Height))
						}
					}
				}

				// If we got here then we are at/above the hVM genesis height and can break out of the startup loop
				log.Info(fmt.Sprintf("TBC full node indexed to block %s @ %d which is at or beyond hVM "+
					"effective genesis block %s @ %d", bhb.BlockHash().String(), bh, genesisHash.String(),
					genesisHeight))
				break
			} else { // The best block known by TBC is still below the genesis height
				// We could index the chain incrementally as we sync, but in the current implementation
				// we wait until the TBC Full Node is fully synced with all data and then do the indexing
				// all at one time, so for now just log the syncing progress.
				log.Info(fmt.Sprintf("TBC Full Node is performing initial sync, current tip: %s @ %d",
					bhb.BlockHash().String(), bh))
			}

			select {
			case <-time.After(500 * time.Millisecond):
			case <-ctx.Context.Done():
				log.Crit("context done")
			}
		}

		log.Info("TBC initial sync completed", "headerHeight", syncInfo.BlockHeader.Height,
			"utxoIndexHeight", syncInfo.Utxo.Height, "txIndexHeight", syncInfo.Tx.Height)
	}

	// Create gauge with geth system and build information
	if eth != nil { // The 'eth' backend may be nil in light mode
		var protos []string
		for _, p := range eth.Protocols() {
			protos = append(protos, fmt.Sprintf("%v/%d", p.Name, p.Version))
		}
		metrics.NewRegisteredGaugeInfo("geth/info", nil).Update(metrics.GaugeInfoValue{
			"arch":      runtime.GOARCH,
			"os":        runtime.GOOS,
			"version":   cfg.Node.Version,
			"protocols": strings.Join(protos, ","),
		})
	}

	// Configure log filter RPC API.
	filterSystem := utils.RegisterFilterAPI(stack, backend, &cfg.Eth)

	// Configure GraphQL if requested.
	if ctx.IsSet(utils.GraphQLEnabledFlag.Name) {
		utils.RegisterGraphQLService(stack, backend, filterSystem, &cfg.Node)
	}
	// Add the Ethereum Stats daemon if requested.
	if cfg.Ethstats.URL != "" {
		utils.RegisterEthStatsService(stack, backend, cfg.Ethstats.URL)
	}
	// Configure full-sync tester service if requested
	if ctx.IsSet(utils.SyncTargetFlag.Name) {
		hex := hexutil.MustDecode(ctx.String(utils.SyncTargetFlag.Name))
		if len(hex) != common.HashLength {
			utils.Fatalf("invalid sync target length: have %d, want %d", len(hex), common.HashLength)
		}
		utils.RegisterFullSyncTester(stack, eth, common.BytesToHash(hex))
	}
	// Start the dev mode if requested, or launch the engine API for
	// interacting with external consensus client.
	if ctx.IsSet(utils.DeveloperFlag.Name) {
		simBeacon, err := catalyst.NewSimulatedBeacon(ctx.Uint64(utils.DeveloperPeriodFlag.Name), eth)
		if err != nil {
			utils.Fatalf("failed to register dev mode catalyst service: %v", err)
		}
		catalyst.RegisterSimulatedBeaconAPIs(stack, simBeacon)
		stack.RegisterLifecycle(simBeacon)
	} else {
		err := catalyst.Register(stack, eth)
		if err != nil {
			utils.Fatalf("failed to register catalyst service: %v", err)
		}
	}
	return stack, backend
}

// dumpConfig is the dumpconfig command.
func dumpConfig(ctx *cli.Context) error {
	_, cfg := makeConfigNode(ctx)
	comment := ""

	if cfg.Eth.Genesis != nil {
		cfg.Eth.Genesis = nil
		comment += "# Note: this config doesn't contain the genesis block.\n\n"
	}

	out, err := tomlSettings.Marshal(&cfg)
	if err != nil {
		return err
	}

	dump := os.Stdout
	if ctx.NArg() > 0 {
		dump, err = os.OpenFile(ctx.Args().Get(0), os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0644)
		if err != nil {
			return err
		}
		defer dump.Close()
	}
	dump.WriteString(comment)
	dump.Write(out)

	return nil
}

func applyMetricConfig(ctx *cli.Context, cfg *gethConfig) {
	if ctx.IsSet(utils.MetricsEnabledFlag.Name) {
		cfg.Metrics.Enabled = ctx.Bool(utils.MetricsEnabledFlag.Name)
	}
	if ctx.IsSet(utils.MetricsEnabledExpensiveFlag.Name) {
		cfg.Metrics.EnabledExpensive = ctx.Bool(utils.MetricsEnabledExpensiveFlag.Name)
	}
	if ctx.IsSet(utils.MetricsHTTPFlag.Name) {
		cfg.Metrics.HTTP = ctx.String(utils.MetricsHTTPFlag.Name)
	}
	if ctx.IsSet(utils.MetricsPortFlag.Name) {
		cfg.Metrics.Port = ctx.Int(utils.MetricsPortFlag.Name)
	}
	if ctx.IsSet(utils.MetricsEnableInfluxDBFlag.Name) {
		cfg.Metrics.EnableInfluxDB = ctx.Bool(utils.MetricsEnableInfluxDBFlag.Name)
	}
	if ctx.IsSet(utils.MetricsInfluxDBEndpointFlag.Name) {
		cfg.Metrics.InfluxDBEndpoint = ctx.String(utils.MetricsInfluxDBEndpointFlag.Name)
	}
	if ctx.IsSet(utils.MetricsInfluxDBDatabaseFlag.Name) {
		cfg.Metrics.InfluxDBDatabase = ctx.String(utils.MetricsInfluxDBDatabaseFlag.Name)
	}
	if ctx.IsSet(utils.MetricsInfluxDBUsernameFlag.Name) {
		cfg.Metrics.InfluxDBUsername = ctx.String(utils.MetricsInfluxDBUsernameFlag.Name)
	}
	if ctx.IsSet(utils.MetricsInfluxDBPasswordFlag.Name) {
		cfg.Metrics.InfluxDBPassword = ctx.String(utils.MetricsInfluxDBPasswordFlag.Name)
	}
	if ctx.IsSet(utils.MetricsInfluxDBTagsFlag.Name) {
		cfg.Metrics.InfluxDBTags = ctx.String(utils.MetricsInfluxDBTagsFlag.Name)
	}
	if ctx.IsSet(utils.MetricsEnableInfluxDBV2Flag.Name) {
		cfg.Metrics.EnableInfluxDBV2 = ctx.Bool(utils.MetricsEnableInfluxDBV2Flag.Name)
	}
	if ctx.IsSet(utils.MetricsInfluxDBTokenFlag.Name) {
		cfg.Metrics.InfluxDBToken = ctx.String(utils.MetricsInfluxDBTokenFlag.Name)
	}
	if ctx.IsSet(utils.MetricsInfluxDBBucketFlag.Name) {
		cfg.Metrics.InfluxDBBucket = ctx.String(utils.MetricsInfluxDBBucketFlag.Name)
	}
	if ctx.IsSet(utils.MetricsInfluxDBOrganizationFlag.Name) {
		cfg.Metrics.InfluxDBOrganization = ctx.String(utils.MetricsInfluxDBOrganizationFlag.Name)
	}
}

func deprecated(field string) bool {
	switch field {
	case "ethconfig.Config.EVMInterpreter":
		return true
	case "ethconfig.Config.EWASMInterpreter":
		return true
	case "ethconfig.Config.TrieCleanCacheJournal":
		return true
	case "ethconfig.Config.TrieCleanCacheRejournal":
		return true
	default:
		return false
	}
}

func setAccountManagerBackends(conf *node.Config, am *accounts.Manager, keydir string) error {
	scryptN := keystore.StandardScryptN
	scryptP := keystore.StandardScryptP
	if conf.UseLightweightKDF {
		scryptN = keystore.LightScryptN
		scryptP = keystore.LightScryptP
	}

	// Assemble the supported backends
	if len(conf.ExternalSigner) > 0 {
		log.Info("Using external signer", "url", conf.ExternalSigner)
		if extBackend, err := external.NewExternalBackend(conf.ExternalSigner); err == nil {
			am.AddBackend(extBackend)
			return nil
		} else {
			return fmt.Errorf("error connecting to external signer: %v", err)
		}
	}

	// For now, we're using EITHER external signer OR local signers.
	// If/when we implement some form of lockfile for USB and keystore wallets,
	// we can have both, but it's very confusing for the user to see the same
	// accounts in both externally and locally, plus very racey.
	am.AddBackend(keystore.NewKeyStore(keydir, scryptN, scryptP))
	if conf.USB {
		// Start a USB hub for Ledger hardware wallets
		if ledgerhub, err := usbwallet.NewLedgerHub(); err != nil {
			log.Warn(fmt.Sprintf("Failed to start Ledger hub, disabling: %v", err))
		} else {
			am.AddBackend(ledgerhub)
		}
		// Start a USB hub for Trezor hardware wallets (HID version)
		if trezorhub, err := usbwallet.NewTrezorHubWithHID(); err != nil {
			log.Warn(fmt.Sprintf("Failed to start HID Trezor hub, disabling: %v", err))
		} else {
			am.AddBackend(trezorhub)
		}
		// Start a USB hub for Trezor hardware wallets (WebUSB version)
		if trezorhub, err := usbwallet.NewTrezorHubWithWebUSB(); err != nil {
			log.Warn(fmt.Sprintf("Failed to start WebUSB Trezor hub, disabling: %v", err))
		} else {
			am.AddBackend(trezorhub)
		}
	}
	if len(conf.SmartCardDaemonPath) > 0 {
		// Start a smart card hub
		if schub, err := scwallet.NewHub(conf.SmartCardDaemonPath, scwallet.Scheme, keydir); err != nil {
			log.Warn(fmt.Sprintf("Failed to start smart card hub, disabling: %v", err))
		} else {
			am.AddBackend(schub)
		}
	}

	return nil
}
