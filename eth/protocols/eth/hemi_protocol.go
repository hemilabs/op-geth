//go:build !eth_test
package eth

// ProtocolVersions are the supported versions of the `eth` protocol (first
// is primary) for Hemi.  Hemi only supports ETH68 at this time.
var ProtocolVersions = []uint{ETH68}
