package eth

import (
	"context"
	"encoding/hex"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/rpc"
	"github.com/hemilabs/heminetwork/api/protocol"
	"github.com/hemilabs/heminetwork/hemi"
)

const maxL2KeystoneCount uint = 50

type L2KeystoneValidityRequest struct {
	L2KeystoneHash chainhash.Hash `json:"l2_keystone_hash"`
	KeystoneCount  uint           `json:"keystone_count"`
}

type L2KeystoneValidityResponse struct {
	L2Keystones []hemi.L2Keystone `json:"keystones"`
	Error       *protocol.Error   `json:"error,omitempty"`
}

type L2KeystoneLatestRequest struct {
	KeystoneCount uint `json:"keystone_count"`
}

// Same as ValidityResponse but keep separate in
// case one changes in future api versions.
type L2KeystoneLatestResponse struct {
	L2Keystones []hemi.L2Keystone `json:"keystones"`
	Error       *protocol.Error   `json:"error,omitempty"`
}

// KeystoneAPI offers HEMI keystone related RPC methods
type HemiAPI struct {
	e *Ethereum
}

// NewHemiAPI creates a new net API instance.
func NewHemiAPI(e *Ethereum) *HemiAPI {
	return &HemiAPI{e: e}
}

// GetLatestKeystones returns the N latest keystones,
// ordered by L2 Block Number in descending order.
func (api *HemiAPI) GetLatestKeystones(count uint) L2KeystoneLatestResponse {
	if count > maxL2KeystoneCount {
		resp := L2KeystoneLatestResponse{Error: protocol.Errorf("count too large")}
		return resp
	}

	kss, err := api.e.APIBackend.GetMostRecentKeystones(count)
	if err != nil {
		resp := L2KeystoneLatestResponse{Error: protocol.Errorf("failed to retrieve keystones")}
		return resp
	}

	resp := L2KeystoneLatestResponse{L2Keystones: kss}
	return resp
}

// GetKeystone returns a keystones and N number
// of its descendants.
func (api *HemiAPI) GetKeystone(abrevHash string, count uint) L2KeystoneValidityResponse {
	if count > maxL2KeystoneCount {
		resp := L2KeystoneValidityResponse{Error: protocol.Errorf("count too large")}
		return resp
	}

	_, err := chainhash.NewHashFromStr(abrevHash)
	if err != nil {
		resp := L2KeystoneValidityResponse{Error: protocol.Errorf(err.Error())}
		return resp
	}

	b, err := hex.DecodeString(abrevHash)
	if err != nil {
		resp := L2KeystoneValidityResponse{Error: protocol.Errorf(err.Error())}
		return resp
	}

	kss, err := api.e.APIBackend.GetKeystoneAndDescendants(b, count)
	if err != nil {
		resp := L2KeystoneValidityResponse{Error: protocol.Errorf(err.Error())}
		return resp
	}

	resp := L2KeystoneValidityResponse{L2Keystones: kss}
	return resp
}

// NewKeystones creates a subscription that notifies a pop miner when a new keystone is available.
func (api *HemiAPI) NewKeystones(ctx context.Context) (*rpc.Subscription, error) {
	notifier, supported := rpc.NotifierFromContext(ctx)
	if !supported {
		return &rpc.Subscription{}, rpc.ErrNotificationsUnsupported
	}

	rpcSub := notifier.CreateSubscription()
	subCh := make(chan string, 10)
	kf := api.e.KeystoneFeed()
	if kf == nil {
		log.Info("subscription attempt during opgeth shutdown")
		return nil, nil
	}
	feedSub := kf.Subscribe(subCh)

	go func() {
		defer func() {
			feedSub.Unsubscribe()
		}()
		for {
			select {
			case notif := <-subCh:
				notifier.Notify(rpcSub.ID, notif)
			case <-rpcSub.Err(): // client send an unsubscribe request
				return
			case <-notifier.Closed(): // connection dropped
				return
			}
		}
	}()

	return rpcSub, nil
}
