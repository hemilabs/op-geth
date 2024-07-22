package types

import (
	"bytes"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"testing"
)

func TestBtcAttributesDepositDataNoHeaders(t *testing.T) {
	hash, _ := hexutil.Decode("0x1122334455667788112233445566778811223344556677881122334455667788")

	headers := make([][80]byte, 0)

	btcDepData := BtcAttributesDepositData{
		CanonicalTip: [32]byte(hash),
		Headers:      headers,
	}

	serialized, err := btcDepData.MarshalBinary()
	if err != nil {
		t.Errorf("Error: unable to marshal binary: %v", err)
	}

	expected, _ := hexutil.Decode("0xc94f1cca112233445566778811223344556677881122334455667788112233445566778800000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000")
	if !bytes.Equal(serialized, expected) {
		t.Errorf("Error: expected serialized %x but got %x instead", expected, serialized)
	}

	var btcDepParsed BtcAttributesDepositData
	err = btcDepParsed.UnmarshalBinary(serialized)
	if err != nil {
		t.Errorf("Error: unable to unmarshal serialized data %x, err: %v", serialized[:], err)
	}

	if !bytes.Equal(hash[:], btcDepParsed.CanonicalTip[:]) {
		t.Errorf("Error: hash was not unserialized correctly, expected %x but got %x instead", hash[:], btcDepParsed.CanonicalTip[:])
	}
}

func TestBtcAttributesDepositDataOneHeader(t *testing.T) {
	hash, _ := hexutil.Decode("0x1122334455667788112233445566778811223344556677881122334455667788")

	headers := make([][80]byte, 1)
	h0, _ := hexutil.Decode("0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	headers[0] = [80]byte(h0)
	btcDepData := BtcAttributesDepositData{
		CanonicalTip: [32]byte(hash),
		Headers:      headers,
	}

	serialized, err := btcDepData.MarshalBinary()
	if err != nil {
		t.Errorf("Error: unable to marshal binary: %v", err)
	}

	expected, _ := hexutil.Decode("0xc94f1cca11223344556677881122334455667788112233445566778811223344556677880000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000050aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000")
	if !bytes.Equal(serialized, expected) {
		t.Errorf("Error: expected serialized %x but got %x instead", expected, serialized)
	}

	var btcDepParsed BtcAttributesDepositData
	err = btcDepParsed.UnmarshalBinary(serialized)
	if err != nil {
		t.Errorf("Error: unable to unmarshal serialized data %x, err: %v", serialized[:], err)
	}

	if !bytes.Equal(hash[:], btcDepParsed.CanonicalTip[:]) {
		t.Errorf("Error: hash was not unserialized correctly, expected %x but got %x instead", hash[:], btcDepParsed.CanonicalTip[:])
	}

	if !bytes.Equal(h0[:], btcDepParsed.Headers[0][:]) {
		t.Errorf("Error: header was not unserialized correctly, expected %x but got %x instead", h0[:], btcDepParsed.Headers[0][:])
	}
}

func TestBtcAttributesDepositDataSixHeaders(t *testing.T) {
	hash, _ := hexutil.Decode("0x1122334455667788112233445566778811223344556677881122334455667788")

	headers := make([][80]byte, 6)
	h0, _ := hexutil.Decode("0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	h1, _ := hexutil.Decode("0xbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	h2, _ := hexutil.Decode("0xcaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	h3, _ := hexutil.Decode("0xdaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	h4, _ := hexutil.Decode("0xeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	h5, _ := hexutil.Decode("0xfaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	headers[0] = [80]byte(h0)
	headers[1] = [80]byte(h1)
	headers[2] = [80]byte(h2)
	headers[3] = [80]byte(h3)
	headers[4] = [80]byte(h4)
	headers[5] = [80]byte(h5)
	btcDepData := BtcAttributesDepositData{
		CanonicalTip: [32]byte(hash),
		Headers:      headers,
	}

	serialized, err := btcDepData.MarshalBinary()
	if err != nil {
		t.Errorf("Error: unable to marshal binary: %v", err)
	}

	expected, _ := hexutil.Decode("0xc94f1cca11223344556677881122334455667788112233445566778811223344556677880000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000014000000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000024000000000000000000000000000000000000000000000000000000000000002c000000000000000000000000000000000000000000000000000000000000003400000000000000000000000000000000000000000000000000000000000000050aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050baaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050caaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050daaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050eaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050faaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000")
	if !bytes.Equal(serialized, expected) {
		t.Errorf("Error: expected serialized %x but got %x instead", expected, serialized)
	}

	var btcDepParsed BtcAttributesDepositData
	err = btcDepParsed.UnmarshalBinary(serialized)
	if err != nil {
		t.Errorf("Error: unable to unmarshal serialized data %x, err: %v", serialized[:], err)
	}

	if !bytes.Equal(hash[:], btcDepParsed.CanonicalTip[:]) {
		t.Errorf("Error: hash was not unserialized correctly, expected %x but got %x instead", hash[:], btcDepParsed.CanonicalTip[:])
	}

	if !bytes.Equal(h0[:], btcDepParsed.Headers[0][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h0[:], btcDepParsed.Headers[0][:])
	}
	if !bytes.Equal(h1[:], btcDepParsed.Headers[1][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h1[:], btcDepParsed.Headers[1][:])
	}
	if !bytes.Equal(h2[:], btcDepParsed.Headers[2][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h2[:], btcDepParsed.Headers[2][:])
	}
	if !bytes.Equal(h3[:], btcDepParsed.Headers[3][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h3[:], btcDepParsed.Headers[3][:])
	}
	if !bytes.Equal(h4[:], btcDepParsed.Headers[4][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h4[:], btcDepParsed.Headers[4][:])
	}
	if !bytes.Equal(h5[:], btcDepParsed.Headers[5][:]) {
		t.Errorf("Error: hgeader was not unserialized correctly, expected %x but got %x instead", h5[:], btcDepParsed.Headers[5][:])
	}
}
