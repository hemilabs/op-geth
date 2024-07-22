package types

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/log"
	"io"
)

const (
	BtcAttributesDepositedFuncSignature = "updateHvmState(bytes32,bytes[])"
	MaximumBtcHeadersInTx               = 6
	SmartContractArgumentByteLen        = 32 // Each argument to smart contract is padded to 32 bytes

	// Based on function sig + canonical tip + empty byte[] (pos + 0 len = 64)
	MinimumSerializedBtcAttributesDepositedLen = 4 + 32 + (2 * 32)

	HeaderArrayOffset        = 0x40 // 2 * 32 bytes
	BitcoinHeaderLengthBytes = 0x50 // 80 bytes
	BitcoinHashLengthBytes   = 0x20 // 32 bytes
)

var (
	UpdateHvmStateFuncBytes4 = crypto.Keccak256([]byte(BtcAttributesDepositedFuncSignature))[:4]
	uint64EmptyPadding       = [SmartContractArgumentByteLen - 8]byte{}
	btcHeaderPadding         = [SmartContractArgumentByteLen*3 - BitcoinHeaderLengthBytes]byte{} // To store 80 bytes we need to pad to closest higher multiple of 32 (which is 96)
	HvmStateAddress          = common.HexToAddress("0x8400000000000000000000000000000000000000") // Must match optimism repo "predeploys.HvmStateAddr"
)

type BtcAttributesDepositData struct {
	CanonicalTip [BitcoinHashLengthBytes]byte
	Headers      [][BitcoinHeaderLengthBytes]byte
}

func calculateLength(numHeaders int) int {
	return 4 +
		SmartContractArgumentByteLen + // canonical tip hash
		SmartContractArgumentByteLen + // offset of byte array
		SmartContractArgumentByteLen + // length of byte array
		(SmartContractArgumentByteLen * numHeaders) + // 1 for each header offset
		(SmartContractArgumentByteLen * numHeaders) + // 1 for each header length
		(SmartContractArgumentByteLen * numHeaders * 3) // 3 for each header's actual data
}

// MarshalBinary Binary Format
// +---------+-------------------------------+
// | Bytes   | Field                         |
// +---------+-------------------------------+
// | 4       | Function Signature            |
// | 32      | Canonical Tip Hash            |
// | 32      | Starting Pos of Header Arr    |
// | 32      | Header Arr Length             |
// | 32      | Starting Pos of 1st Header    |
// |                  ...                    |
// | 32      | Starting Pos of last Header   |
// | 32      | Length of 1st Header (0x50)   |
// | 96      | 1st Header (80 padded to 96)  |
// |                  ...                    |
// | 32      | Length of Last Header (0x50)  |
// | 96      | Last Header (80 padded to 96) |
// +---------+-------------------------------+
//
// Example (where 1122...7788 is a 32-byte hash, and "aaa...aaa", "bbb...bbb", and "ccc...ccc" are 80-byte headers:
// 0xc94f1cca // keccak256("updateHvmState(bytes32,bytes[])")
// 1122334455667788112233445566778811223344556677881122334455667788 // Canonical tip hash
// 0000000000000000000000000000000000000000000000000000000000000040 // Header array always starts 64 bytes in (next line)
// 0000000000000000000000000000000000000000000000000000000000000003 // Number of headers in array (3)
// 0000000000000000000000000000000000000000000000000000000000000060 // 1st header starts 96 bytes from here (in 3 lines)
// 00000000000000000000000000000000000000000000000000000000000000e0 // 2nd header starts 224 bytes from here (in 7 lines)
// 0000000000000000000000000000000000000000000000000000000000000160 // 3rd header starts 352 bytes from here (in 11 lines)
// 0000000000000000000000000000000000000000000000000000000000000050 // 1st header is length 80 bytes
// aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa // first 32 bytes of header
// aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa // second 32 bytes of header
// aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 // final 16 bytes of header + 16 bytes of padding
// 0000000000000000000000000000000000000000000000000000000000000050 // 2nd header is length 80 bytes
// bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb // first 32 bytes of header
// bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb // second 32 bytes of header
// bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb00000000000000000000000000000000 // final 16 bytes of header + 16 bytes of padding
// 0000000000000000000000000000000000000000000000000000000000000050 // 3rd header is length 80 bytes
// cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc // first 32 bytes of header
// cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc // second 32 bytes of header
// cccccccccccccccccccccccccccccccc00000000000000000000000000000000 // final 16 bytes of header + 16 bytes of padding
//
// Example with no headers:
// 0xc94f1cca // keccak256("updateHvmState(bytes32,bytes[])")
// 1122334455667788112233445566778811223344556677881122334455667788 // Canonical tip hash
// 0000000000000000000000000000000000000000000000000000000000000040 // Header array always starts 64 bytes in (even if empty)
// 0000000000000000000000000000000000000000000000000000000000000000 // Header array has 0 elements, done
func (btcdep *BtcAttributesDepositData) MarshalBinary() ([]byte, error) {
	// See above format for calculation, assumes addresses and amounts are always same length
	btcAttrDepLen := calculateLength(len(btcdep.Headers))

	w := bytes.NewBuffer(make([]byte, 0, btcAttrDepLen))
	w.Write(UpdateHvmStateFuncBytes4[:])
	w.Write(btcdep.CanonicalTip[:])

	// Offset of byte array is always 64 bytes in
	w.Write(uint64EmptyPadding[:])
	binary.Write(w, binary.BigEndian, uint64(HeaderArrayOffset))

	// Write number of elements in byte array
	w.Write(uint64EmptyPadding[:])
	binary.Write(w, binary.BigEndian, uint64(len(btcdep.Headers)))

	if len(btcdep.Headers) == 0 {
		// Done
		return w.Bytes(), nil
	}

	// Each header moves the start of the first header by 32 bytes
	offset := SmartContractArgumentByteLen * len(btcdep.Headers)
	for i := 0; i < len(btcdep.Headers); i++ {
		w.Write(uint64EmptyPadding[:])
		binary.Write(w, binary.BigEndian, uint64(offset))
		// Each header takes 128 bytes (80 padded to 96, and another 32 for length)
		offset += SmartContractArgumentByteLen * 4
	}

	for i := 0; i < len(btcdep.Headers); i++ {
		w.Write(uint64EmptyPadding[:])
		binary.Write(w, binary.BigEndian, uint64(BitcoinHeaderLengthBytes)) // Header length is always 80
		w.Write(btcdep.Headers[i][:])
		w.Write(btcHeaderPadding[:])
	}

	return w.Bytes(), nil
}

func (btcdep *BtcAttributesDepositData) UnmarshalBinary(data []byte) error {
	if len(data) < MinimumSerializedBtcAttributesDepositedLen {
		return fmt.Errorf("serialized Bitcoin Attributes Deposited data must be at least %d bytes,"+
			" but only %d bytes provided", MinimumSerializedBtcAttributesDepositedLen, len(data))
	}

	reader := bytes.NewReader(data)
	sig := make([]byte, 4)
	if _, err := io.ReadFull(reader, sig); err != nil {
		return err
	}
	if !bytes.Equal(sig, UpdateHvmStateFuncBytes4[:]) {
		return fmt.Errorf("serialized Bitcoin Attributes Deposited data must have a "+
			"function signature of 0x%x, but got 0x%x instead", UpdateHvmStateFuncBytes4, sig)
	}

	var canonicalTip [BitcoinHashLengthBytes]byte
	if _, err := io.ReadFull(reader, canonicalTip[:]); err != nil {
		return err
	}

	initialOffset, err := ReadUint64(reader)
	if err != nil {
		return err
	}
	if initialOffset != HeaderArrayOffset {
		return fmt.Errorf("serialized Bitcoin Attributes Deposited data must have an "+
			"initial offset for the header array of %d, but got %d instead", HeaderArrayOffset, initialOffset)
	}

	numHeaders, err := ReadUint64(reader)
	if err != nil {
		return err
	}

	if numHeaders > MaximumBtcHeadersInTx {
		return fmt.Errorf("serialized Bitcoin Attributes Deposited data can only have "+
			"a maximum of %d BTC headers, but got %d", MaximumBtcHeadersInTx, numHeaders)
	}

	expectedOffset := SmartContractArgumentByteLen * int(numHeaders)
	for i := 0; i < int(numHeaders); i++ {
		actualOffset, err := ReadUint64(reader)

		if err != nil {
			return err
		}

		if expectedOffset != int(actualOffset) {
			return fmt.Errorf("serialized Bitcoin Attributes Deposited data with %d headers "+
				"should have an offset of %d for the array at index %d, but got %d instead",
				numHeaders, expectedOffset, i, actualOffset)
		}
		expectedOffset += SmartContractArgumentByteLen * 4
	}

	headers := make([][BitcoinHeaderLengthBytes]byte, numHeaders)
	for i := 0; i < int(numHeaders); i++ {
		headerLength, err := ReadUint64(reader)
		if err != nil {
			return err
		}

		if headerLength != BitcoinHeaderLengthBytes {
			return fmt.Errorf("serialized Bitcoin Attributes Deposited data should have "+
				"Bitcoin headers that are exactly %d bytes long, but the Bitcoin header at index %d "+
				"is encoded with a length of %d instead", BitcoinHeaderLengthBytes, i, headerLength)
		}

		header, err := ReadBitcoinHeader(reader)
		if err != nil {
			return err
		}
		headers[i] = *header
	}

	if !EmptyReader(reader) {
		return fmt.Errorf("serialized Bitcoin Attributes Deposited data has more data than "+
			"expected! Expected size %d, but got %d", len(data), calculateLength(int(numHeaders)))
	}

	btcdep.CanonicalTip = canonicalTip
	btcdep.Headers = headers

	return nil
}

func MakeBtcAttributesDepositedTx(canonicalTip *chainhash.Hash, headers []wire.BlockHeader) (*BtcAttributesDepositedTx, error) {
	headersFlat, err := SerializeHeadersToArray(headers)

	btcAttrDepData := BtcAttributesDepositData{
		CanonicalTip: *canonicalTip,
		Headers:      *headersFlat,
	}

	data, err := btcAttrDepData.MarshalBinary()
	if err != nil {
		log.Error("Unable to marshall binary for Bitcoin attributes data")
		return nil, err
	}

	out := &BtcAttributesDepositedTx{
		To:   &BtcAttributesDepositedSenderAddress,
		Gas:  1_000_000, // Regloith System Tx Gas
		Data: data,
	}

	return out, nil
}

func SerializeHeader(header wire.BlockHeader) (*[BitcoinHeaderLengthBytes]byte, error) {
	var headerBuf bytes.Buffer
	err := header.Serialize(&headerBuf)
	if err != nil {
		hash := header.BlockHash()
		log.Error(fmt.Sprintf("Unable to serialize header %x", hash[:]))
		return nil, err
	}
	headerBytes := [BitcoinHeaderLengthBytes]byte(headerBuf.Bytes())
	return &headerBytes, nil
}

func SerializeHeadersToArray(headers []wire.BlockHeader) (*[][BitcoinHeaderLengthBytes]byte, error) {
	headersFlat := make([][BitcoinHeaderLengthBytes]byte, len(headers))
	for i := 0; i < len(headers); i++ {
		header, err := SerializeHeader(headers[i])
		if err != nil {
			hash := headers[i].BlockHash()
			log.Error(fmt.Sprintf("Unable to serialize header %x when creating a Bitcoin Attributes "+
				"Deposited transaction", hash[:]))
		}
		headersFlat[i] = *header
	}

	return &headersFlat, nil
}

// From Solabi
func EmptyReader(r io.Reader) bool {
	var t [1]byte
	n, err := r.Read(t[:])
	return n == 0 && err == io.EOF
}

// From Solabi
func ReadUint64(r io.Reader) (uint64, error) {
	var readPadding [SmartContractArgumentByteLen - 8]byte
	var n uint64
	if _, err := io.ReadFull(r, readPadding[:]); err != nil {
		return n, err
	} else if !bytes.Equal(readPadding[:], uint64EmptyPadding[:]) {
		return n, fmt.Errorf("number padding was not empty: %x", readPadding[:])
	}
	if err := binary.Read(r, binary.BigEndian, &n); err != nil {
		return 0, fmt.Errorf("expected number length to be 8 bytes")
	}
	return n, nil
}

// TODO: Add this new "ReadBitcoinHeader" upstream into solabi in our optimism fork and import here for use
func ReadBitcoinHeader(r io.Reader) (*[BitcoinHeaderLengthBytes]byte, error) {
	var header [BitcoinHeaderLengthBytes]byte
	if _, err := io.ReadFull(r, header[:]); err != nil {
		return nil, err
	}
	var afterPadding [3*SmartContractArgumentByteLen - BitcoinHeaderLengthBytes]byte
	if _, err := io.ReadFull(r, afterPadding[:]); err != nil {
		return nil, err
	}
	if !bytes.Equal(afterPadding[:], btcHeaderPadding[:]) {
		return nil, fmt.Errorf("header padding was not empty: %x", afterPadding[:])
	}
	return &header, nil
}
