// Copyright 2021 The go-ethereum Authors
// Copyright 2023 Bloq, Inc.
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

package types

import (
	"bytes"
	"encoding/hex"
	"reflect"
	"testing"

	"github.com/davecgh/go-spew/spew"
	"github.com/ethereum/go-ethereum/common"
)

func TestPopPayoutTxEncodeDecode(t *testing.T) {
	govPredeployAddr := common.HexToAddress("0x4200000000000000000000000000000000000042")
	tx := PopPayoutTx{
		To:   &govPredeployAddr,
		Gas:  150_000_000,
		Data: []byte{'d', 'a', 't', 'a'},
	}

	b := new(bytes.Buffer)
	err := tx.encode(b)
	if err != nil {
		t.Fatal(err)
	}

	t.Logf("%v", spew.Sdump(b.Bytes()))

	// Golden wire bytes: the symmetric encode->decode->DeepEqual below survives a {To,Gas,Data} field reorder
	// (RLP decodes positionally), silently changing the on-the-wire layout. Pin the exact bytes to catch that.
	const goldenRLP = "df9442000000000000000000000000000000000000428408f0d1808464617461"
	if got := hex.EncodeToString(b.Bytes()); got != goldenRLP {
		t.Fatalf("PopPayoutTx RLP wire layout changed: got %s want %s (a {To,Gas,Data} reorder survives the round-trip below)", got, goldenRLP)
	}

	tx2 := &PopPayoutTx{}
	err = tx2.decode(b.Bytes())
	if err != nil {
		t.Fatal(err)
	}

	t.Logf("%v", spew.Sdump(tx2))
	if !reflect.DeepEqual(*tx2, tx) {
		t.Fatalf("not equal got %v, wanted %v", spew.Sdump(*tx2), spew.Sdump(tx))
	}
}
