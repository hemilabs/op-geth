package eip1559

import (
	"testing"
)

func TestValidateHolocene1559Params(t *testing.T) {
	tests := []struct {
		name     string
		params   []byte
		expected string
	}{
		{
			name:     "Wrong Length",
			params:   []byte{0x00, 0x01},
			expected: "holocene eip-1559 params should be 8 bytes, got 2",
		},
		{
			name:     "Zero denominator, non-zero elasticity",
			params:   []byte{0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01},
			expected: "holocene params cannot have a 0 denominator unless elasticity is also 0",
		},
		{
			name:     "Zero elasticity, non-zero denominator",
			params:   []byte{0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00},
			expected: "holocene params cannot have a 0 elasticity unless denominator is also 0",
		},
		{
			name:   "Both zero (valid)",
			params: []byte{0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00},
		},
		{
			name:   "Both non-zero (valid)",
			params: []byte{0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01},
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			err := ValidateHolocene1559Params(tc.params)
			if tc.expected == "" && err != nil {
				t.Errorf("Expected no error, but got: %v", err)
			}
			if tc.expected != "" && (err == nil || err.Error() != tc.expected) {
				t.Errorf("Expected error: %s, but got: %v", tc.expected, err)
			}
		})
	}
}

func TestValidateHoloceneExtraData(t *testing.T) {
	// largeGasLimit is well above any elasticity in the existing vectors (the only valid one encodes
	// elasticity 1), so those cases behave as before the elasticity<=gasLimit bound.
	const largeGasLimit = uint64(30_000_000)
	tests := []struct {
		name     string
		extra    []byte
		gasLimit uint64
		expected string
	}{
		{
			name:     "Wrong Length",
			extra:    []byte{0x00, 0x01},
			gasLimit: largeGasLimit,
			expected: "holocene extraData should be 9 bytes, got 2",
		},
		{
			name:     "Wrong Version",
			extra:    []byte{0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00},
			gasLimit: largeGasLimit,
			expected: "holocene extraData version byte should be 0, got 1",
		},
		{
			name:     "Zero denominator, non-zero elasticity",
			extra:    []byte{0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01},
			gasLimit: largeGasLimit,
			expected: "holocene extraData must encode a non-zero denominator",
		},
		{
			name:     "Zero elasticity, non-zero denominator",
			extra:    []byte{0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00},
			gasLimit: largeGasLimit,
			expected: "holocene extraData must encode a non-zero elasticity",
		},
		{
			name:     "Both zero (invalid)",
			extra:    []byte{0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00},
			gasLimit: largeGasLimit,
			expected: "holocene extraData must encode a non-zero denominator",
		},
		{
			name:     "Both non-zero (valid)",
			extra:    []byte{0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01},
			gasLimit: largeGasLimit,
		},
		// Elasticity vs gas-limit bound (the divide-by-zero guard).
		{
			name:     "Elasticity equals gas limit (valid, target==1)",
			extra:    []byte{0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x05},
			gasLimit: 5,
		},
		{
			name:     "Elasticity exceeds gas limit by one (invalid)",
			extra:    []byte{0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x06},
			gasLimit: 5,
			expected: "holocene extraData elasticity 6 exceeds gas limit 5",
		},
		{
			name:     "Large elasticity exceeds gas limit (invalid)",
			extra:    []byte{0x00, 0x00, 0x00, 0x00, 0x01, 0x05, 0x06, 0x07, 0x08}, // elasticity 0x05060708 = 84281096
			gasLimit: largeGasLimit,
			expected: "holocene extraData elasticity 84281096 exceeds gas limit 30000000",
		},
		{
			name:     "Non-zero elasticity with zero gas limit (invalid)",
			extra:    []byte{0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01},
			gasLimit: 0,
			expected: "holocene extraData elasticity 1 exceeds gas limit 0",
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			err := ValidateHoloceneExtraData(tc.extra, tc.gasLimit)
			if tc.expected == "" && err != nil {
				t.Errorf("Expected no error, but got: %v", err)
			}
			if tc.expected != "" && (err == nil || err.Error() != tc.expected) {
				t.Errorf("Expected error: %s, but got: %v", tc.expected, err)
			}
		})
	}
}

// TestValidateJovianExtraData covers the elasticity<=gasLimit bound on the Jovian validator, which
// validates the same 8-byte eip-1559 part as Holocene, so the divide-by-zero guard applies there too.
func TestValidateJovianExtraData(t *testing.T) {
	// Jovian extraData is 17 bytes: version(1) | denominator(4) | elasticity(4) | minBaseFee(8).
	jovian := func(denom, elasticity uint32) []byte {
		b := make([]byte, 17)
		b[0] = JovianExtraDataVersionByte
		b[1], b[2], b[3], b[4] = byte(denom>>24), byte(denom>>16), byte(denom>>8), byte(denom)
		b[5], b[6], b[7], b[8] = byte(elasticity>>24), byte(elasticity>>16), byte(elasticity>>8), byte(elasticity)
		return b // minBaseFee bytes left zero (arbitrary, not validated)
	}
	tests := []struct {
		name     string
		extra    []byte
		gasLimit uint64
		expected string
	}{
		{name: "valid (elasticity below gas limit)", extra: jovian(250, 6), gasLimit: 30_000_000},
		{name: "valid (elasticity equals gas limit)", extra: jovian(250, 6), gasLimit: 6},
		{name: "elasticity exceeds gas limit", extra: jovian(250, 7), gasLimit: 6, expected: "holocene extraData elasticity 7 exceeds gas limit 6"},
		{name: "zero elasticity", extra: jovian(250, 0), gasLimit: 30_000_000, expected: "holocene extraData must encode a non-zero elasticity"},
		{name: "wrong length", extra: make([]byte, 9), gasLimit: 30_000_000, expected: "Jovian extraData should be 17 bytes, got 9"},
		{name: "wrong version byte", extra: func() []byte { b := jovian(250, 6); b[0] = HoloceneExtraDataVersionByte; return b }(), gasLimit: 30_000_000, expected: "Jovian extraData version byte should be 1, got 0"},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			err := ValidateJovianExtraData(tc.extra, tc.gasLimit)
			if tc.expected == "" && err != nil {
				t.Errorf("Expected no error, but got: %v", err)
			}
			if tc.expected != "" && (err == nil || err.Error() != tc.expected) {
				t.Errorf("Expected error: %s, but got: %v", tc.expected, err)
			}
		})
	}
}
