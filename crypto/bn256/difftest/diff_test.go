// Copyright 2026 The go-ethereum Authors
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

// Package bn256diff is a differential regression guard for the alt_bn128 (bn256)
// precompiles and the EIP-198 modexp precompile. It drives the exact precompile
// semantics (point decode + operation + marshal for 0x06/0x07/0x08, and the modexp
// Run for 0x05) over every backend compiled into the tree and asserts they agree
// byte-for-byte on identical inputs, so a dependency bump that made any backend
// diverge would fail here rather than silently change consensus output:
//
//   - cloudflare (crypto/bn256/cloudflare) — the bn256 backend selected on amd64/arm64
//     by builds that alias crypto/bn256 to it.
//   - gnark      (crypto/bn256/gnark)      — the bn256 backend selected on amd64/arm64
//     by builds that alias crypto/bn256 to it.
//   - google     (crypto/bn256/google)     — the bn256 backend selected on every other
//     GOARCH by all builds.
//   - modexp: the stdlib math/big exponentiation vs the go-bigmodexpfix drop-in.
//
// Inputs are pseudo-random from a fixed, logged seed, so the default run is
// deterministic and any failure is reproducible; set FUZZ_SEED=<int> to vary it.
// The default run is a fast per-commit smoke; set FUZZ_N=<mult> to scale the
// iteration budget up for a deep (nightly / on-dependency-bump) run.
//
// The cf/gn/gg replicas mirror core/vm/contracts.go (runBn256Add,
// runBn256ScalarMul, runBn256Pairing) and its getData padding; the modexp
// replicas mirror core/vm bigModExp.Run. Keep them in sync with those functions.
package bn256diff

import (
	"bytes"
	"math/big"
	mrand "math/rand"
	"os"
	"strconv"
	"testing"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	patched "github.com/ethereum/go-bigmodexpfix/src/math/big"
	cf "github.com/ethereum/go-ethereum/crypto/bn256/cloudflare"
	gn "github.com/ethereum/go-ethereum/crypto/bn256/gnark"
	gg "github.com/ethereum/go-ethereum/crypto/bn256/google"
)

// ----- scaling & seeding -----

// scale multiplies every loop's iteration budget. It is 1 by default (a fast
// per-commit smoke); FUZZ_N=<n> scales it up for a deep run.
func scale() int {
	if s := os.Getenv("FUZZ_N"); s != "" {
		if n, err := strconv.Atoi(s); err == nil && n > 0 {
			return n
		}
	}
	return 1
}

// rng is the shared source for all pseudo-random inputs. It is seeded per test by
// seedRNG so the run is deterministic and any failure is reproducible from the
// logged seed. The tests are serial by design and must not add t.Parallel, since
// they share this generator.
var rng *mrand.Rand

// seedRNG re-seeds rng with a fixed default seed (deterministic, reproducible CI),
// overridable via FUZZ_SEED, and logs the seed so a failing run can be replayed.
func seedRNG(t *testing.T) {
	t.Helper()
	seed := int64(20260101)
	if s := os.Getenv("FUZZ_SEED"); s != "" {
		if v, err := strconv.ParseInt(s, 10, 64); err == nil {
			seed = v
		}
	}
	t.Logf("bn256diff seed=%d (set FUZZ_SEED to vary)", seed)
	rng = mrand.New(mrand.NewSource(seed))
}

// ----- vm.getData mirror (right zero-padded) -----

func getData(data []byte, start, size uint64) []byte {
	length := uint64(len(data))
	if start > length {
		start = length
	}
	end := start + size
	if end > length {
		end = length
	}
	out := make([]byte, size)
	copy(out, data[start:end])
	return out
}

// ----- precompile replicas: cloudflare (mirrors core/vm/contracts.go runBn256*) -----

func cfAdd(in []byte) ([]byte, error) {
	x := new(cf.G1)
	if _, err := x.Unmarshal(getData(in, 0, 64)); err != nil {
		return nil, err
	}
	y := new(cf.G1)
	if _, err := y.Unmarshal(getData(in, 64, 64)); err != nil {
		return nil, err
	}
	res := new(cf.G1)
	res.Add(x, y)
	return res.Marshal(), nil
}

func cfMul(in []byte) ([]byte, error) {
	p := new(cf.G1)
	if _, err := p.Unmarshal(getData(in, 0, 64)); err != nil {
		return nil, err
	}
	res := new(cf.G1)
	res.ScalarMult(p, new(big.Int).SetBytes(getData(in, 64, 32)))
	return res.Marshal(), nil
}

func cfPairing(in []byte) ([]byte, error) {
	if len(in)%192 > 0 {
		return nil, errSize
	}
	var cs []*cf.G1
	var ts []*cf.G2
	for i := 0; i < len(in); i += 192 {
		c := new(cf.G1)
		if _, err := c.Unmarshal(in[i : i+64]); err != nil {
			return nil, err
		}
		tp := new(cf.G2)
		if _, err := tp.Unmarshal(in[i+64 : i+192]); err != nil {
			return nil, err
		}
		cs = append(cs, c)
		ts = append(ts, tp)
	}
	if cf.PairingCheck(cs, ts) {
		return true32, nil
	}
	return false32, nil
}

// ----- precompile replicas: gnark (same core/vm/contracts.go semantics) -----

func gnAdd(in []byte) ([]byte, error) {
	x := new(gn.G1)
	if _, err := x.Unmarshal(getData(in, 0, 64)); err != nil {
		return nil, err
	}
	y := new(gn.G1)
	if _, err := y.Unmarshal(getData(in, 64, 64)); err != nil {
		return nil, err
	}
	res := new(gn.G1)
	res.Add(x, y)
	return res.Marshal(), nil
}

func gnMul(in []byte) ([]byte, error) {
	p := new(gn.G1)
	if _, err := p.Unmarshal(getData(in, 0, 64)); err != nil {
		return nil, err
	}
	res := new(gn.G1)
	res.ScalarMult(p, new(big.Int).SetBytes(getData(in, 64, 32)))
	return res.Marshal(), nil
}

func gnPairing(in []byte) ([]byte, error) {
	if len(in)%192 > 0 {
		return nil, errSize
	}
	var cs []*gn.G1
	var ts []*gn.G2
	for i := 0; i < len(in); i += 192 {
		c := new(gn.G1)
		if _, err := c.Unmarshal(in[i : i+64]); err != nil {
			return nil, err
		}
		tp := new(gn.G2)
		if _, err := tp.Unmarshal(in[i+64 : i+192]); err != nil {
			return nil, err
		}
		cs = append(cs, c)
		ts = append(ts, tp)
	}
	if gn.PairingCheck(cs, ts) {
		return true32, nil
	}
	return false32, nil
}

var (
	errSize   = bytes.ErrTooLarge // any sentinel; only nil-ness is compared
	true32    = append(make([]byte, 31), 1)
	false32   = make([]byte, 32)
	modulusFp = fp.Modulus()
	orderFr   = fr.Modulus()
)

// ----- safe call + differential compare -----

type outcome struct {
	out      []byte
	err      error
	panicked bool
}

func call(fn func([]byte) ([]byte, error), in []byte) (o outcome) {
	defer func() {
		if r := recover(); r != nil {
			o.panicked = true
		}
	}()
	o.out, o.err = fn(in)
	return
}

// diff runs two backends on the same input and fails on any observable divergence:
// a panic in one but not the other, an error in one but not the other, or different
// output bytes. The input is printed on failure; combined with the logged seed this
// makes any failure reproducible.
func diff(t *testing.T, label string, in []byte, a, b func([]byte) ([]byte, error)) {
	t.Helper()
	oa, ob := call(a, in), call(b, in)
	if oa.panicked != ob.panicked {
		t.Fatalf("%s PANIC mismatch: in=%x a.panic=%v b.panic=%v", label, in, oa.panicked, ob.panicked)
	}
	if oa.panicked {
		return
	}
	if (oa.err == nil) != (ob.err == nil) {
		t.Fatalf("%s ERR mismatch: in=%x\n  a err=%v\n  b err=%v", label, in, oa.err, ob.err)
	}
	if oa.err == nil && !bytes.Equal(oa.out, ob.out) {
		t.Fatalf("%s OUT mismatch: in=%x\n  a=%x\n  b=%x", label, in, oa.out, ob.out)
	}
}

// ----- input generators (all draw from the seeded rng) -----

func randScalar() *big.Int {
	return new(big.Int).Rand(rng, orderFr)
}

func randBytes(n int) []byte {
	b := make([]byte, n)
	rng.Read(b)
	return b
}

func fp32(v *big.Int) []byte {
	b := make([]byte, 32)
	v.FillBytes(b)
	return b
}

func g1ToEVM(p bn254.G1Affine) []byte {
	out := make([]byte, 64)
	x := p.X.Bytes()
	copy(out[0:32], x[:])
	y := p.Y.Bytes()
	copy(out[32:64], y[:])
	return out
}

func g2ToEVM(p bn254.G2Affine) []byte {
	out := make([]byte, 128)
	xa1 := p.X.A1.Bytes()
	copy(out[0:32], xa1[:])
	xa0 := p.X.A0.Bytes()
	copy(out[32:64], xa0[:])
	ya1 := p.Y.A1.Bytes()
	copy(out[64:96], ya1[:])
	ya0 := p.Y.A0.Bytes()
	copy(out[96:128], ya0[:])
	return out
}

// randE2 returns a seeded pseudo-random Fp2 element.
func randE2() bn254.E2 {
	var u bn254.E2
	u.A0.SetBytes(randBytes(48))
	u.A1.SetBytes(randBytes(48))
	return u
}

// validG1 returns the EVM-format bytes of a random in-subgroup G1 point.
func validG1() []byte {
	_, _, g1, _ := bn254.Generators()
	var p bn254.G1Affine
	p.ScalarMultiplication(&g1, randScalar())
	return g1ToEVM(p)
}

// validG2 returns the EVM-format bytes of a random in-subgroup G2 point.
func validG2() []byte {
	_, _, _, g2 := bn254.Generators()
	var p bn254.G2Affine
	p.ScalarMultiplication(&g2, randScalar())
	return g2ToEVM(p)
}

// nonSubgroupG2 returns the EVM-format bytes of an ON-CURVE but NOT-in-subgroup
// G2 point (the discriminator: a backend without the G2 subgroup check would
// accept it). MapToCurve2 maps to the curve without cofactor clearing.
func nonSubgroupG2(t *testing.T) []byte {
	for tries := 0; tries < 64; tries++ {
		u := randE2()
		p := bn254.MapToCurve2(&u)
		if !p.IsOnCurve() {
			continue
		}
		if p.IsInSubGroup() {
			continue // rare; want the non-subgroup case
		}
		return g2ToEVM(p)
	}
	t.Fatal("could not construct a non-subgroup G2 point")
	return nil
}

// edgeCoords are field-element edge values exercising the >=modulus rejection
// and the zero/infinity handling.
func edgeCoords() [][]byte {
	p := new(big.Int).Set(modulusFp)
	pm1 := new(big.Int).Sub(p, big.NewInt(1))
	pp1 := new(big.Int).Add(p, big.NewInt(1))
	max := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 256), big.NewInt(1))
	vals := []*big.Int{
		big.NewInt(0), big.NewInt(1), big.NewInt(2),
		pm1, p, pp1, max,
	}
	out := make([][]byte, 0, len(vals))
	for _, v := range vals {
		out = append(out, fp32(v))
	}
	return out
}

// ----- tests -----

func TestBn256AddDifferential(t *testing.T) {
	seedRNG(t)
	n := 2000 * scale()
	for i := 0; i < n; i++ {
		diff(t, "add/valid", append(validG1(), validG1()...), cfAdd, gnAdd)
	}
	// infinity + valid, valid + infinity, infinity + infinity
	inf := make([]byte, 64)
	diff(t, "add/inf+valid", append(append([]byte{}, inf...), validG1()...), cfAdd, gnAdd)
	diff(t, "add/valid+inf", append(validG1(), inf...), cfAdd, gnAdd)
	diff(t, "add/inf+inf", append(append([]byte{}, inf...), inf...), cfAdd, gnAdd)
	// edge-coordinate blobs (mostly off-curve / >=modulus -> both reject)
	ec := edgeCoords()
	for _, x := range ec {
		for _, y := range ec {
			pt := append(append([]byte{}, x...), y...)
			diff(t, "add/edge", append(pt, validG1()...), cfAdd, gnAdd)
			diff(t, "add/edge2", append(validG1(), pt...), cfAdd, gnAdd)
		}
	}
	// random raw bytes (almost always reject; exercises decode path)
	for i := 0; i < 800*scale(); i++ {
		diff(t, "add/raw", randBytes(128), cfAdd, gnAdd)
		diff(t, "add/short", randBytes(rng.Intn(130)), cfAdd, gnAdd)
	}
}

func TestBn256ScalarMulDifferential(t *testing.T) {
	seedRNG(t)
	n := 2000 * scale()
	for i := 0; i < n; i++ {
		in := append(validG1(), randBytes(32)...) // random scalar incl. >order
		diff(t, "mul/valid", in, cfMul, gnMul)
	}
	// scalar edge values: 0, 1, order, order-1, order+1, 2^256-1
	scalars := [][]byte{
		fp32(big.NewInt(0)), fp32(big.NewInt(1)),
		fp32(orderFr), fp32(new(big.Int).Sub(orderFr, big.NewInt(1))),
		fp32(new(big.Int).Add(orderFr, big.NewInt(1))),
		fp32(new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 256), big.NewInt(1))),
	}
	for i := 0; i < 100*scale(); i++ {
		p := validG1()
		for _, s := range scalars {
			diff(t, "mul/edgeScalar", append(append([]byte{}, p...), s...), cfMul, gnMul)
		}
	}
	// infinity * scalar
	inf := make([]byte, 64)
	diff(t, "mul/inf", append(append([]byte{}, inf...), randBytes(32)...), cfMul, gnMul)
	for i := 0; i < 800*scale(); i++ {
		diff(t, "mul/raw", randBytes(96), cfMul, gnMul)
		diff(t, "mul/short", randBytes(rng.Intn(98)), cfMul, gnMul)
	}
}

func TestBn256PairingDifferential(t *testing.T) {
	seedRNG(t)
	// empty input -> both must return true (32-byte 1)
	diff(t, "pair/empty", []byte{}, cfPairing, gnPairing)

	n := 120 * scale()
	for i := 0; i < n; i++ {
		k := 1 + rng.Intn(4)
		var in []byte
		for j := 0; j < k; j++ {
			in = append(in, validG1()...)
			in = append(in, validG2()...)
		}
		diff(t, "pair/valid", in, cfPairing, gnPairing)
	}
	// a known true relation: e(P,Q) * e(-P,Q) == 1
	for i := 0; i < 40*scale(); i++ {
		_, _, g1, g2 := bn254.Generators()
		a, b := randScalar(), randScalar()
		var P, negP bn254.G1Affine
		P.ScalarMultiplication(&g1, a)
		negP.Neg(&P)
		var Q bn254.G2Affine
		Q.ScalarMultiplication(&g2, b)
		in := append(g1ToEVM(P), g2ToEVM(Q)...)
		in = append(in, g1ToEVM(negP)...)
		in = append(in, g2ToEVM(Q)...)
		diff(t, "pair/true-relation", in, cfPairing, gnPairing)
	}
	// THE DISCRIMINATOR: on-curve non-subgroup G2 in a pair. Both backends must
	// agree (cloudflare's twist IsOnCurve includes a subgroup check; gnark calls
	// IsInSubGroup). Expected: both REJECT.
	for i := 0; i < 60*scale(); i++ {
		in := append(validG1(), nonSubgroupG2(t)...)
		diff(t, "pair/nonsubgroupG2", in, cfPairing, gnPairing)
		// also mixed with a valid pair preceding it
		in2 := append(validG1(), validG2()...)
		in2 = append(in2, validG1()...)
		in2 = append(in2, nonSubgroupG2(t)...)
		diff(t, "pair/valid+nonsub", in2, cfPairing, gnPairing)
	}
	// infinity points in pairs
	for i := 0; i < 120*scale(); i++ {
		infG1 := make([]byte, 64)
		infG2 := make([]byte, 128)
		diff(t, "pair/infG1", append(append([]byte{}, infG1...), validG2()...), cfPairing, gnPairing)
		diff(t, "pair/infG2", append(validG1(), infG2...), cfPairing, gnPairing)
		diff(t, "pair/infBoth", append(append([]byte{}, infG1...), infG2...), cfPairing, gnPairing)
	}
	// random raw multiples of 192 (almost always reject) + non-multiples
	for i := 0; i < 200*scale(); i++ {
		diff(t, "pair/raw192", randBytes(192*(1+rng.Intn(3))), cfPairing, gnPairing)
		diff(t, "pair/rawbad", randBytes(1+rng.Intn(400)), cfPairing, gnPairing)
	}
}

// ----- modexp differential: stdlib math/big vs go-bigmodexpfix (mirrors bigModExp.Run) -----

// modexpRunStd replicates the EIP-198 modexp Run output using stdlib math/big.
func modexpRunStd(baseLen, expLen, modLen uint64, payload []byte) []byte {
	if baseLen == 0 && modLen == 0 {
		return []byte{}
	}
	base := new(big.Int).SetBytes(getData(payload, 0, baseLen))
	exp := new(big.Int).SetBytes(getData(payload, baseLen, expLen))
	mod := new(big.Int).SetBytes(getData(payload, baseLen+expLen, modLen))
	var v []byte
	switch {
	case mod.BitLen() == 0:
		return leftPad([]byte{}, int(modLen))
	case base.BitLen() == 1:
		v = base.Mod(base, mod).Bytes()
	default:
		v = base.Exp(base, exp, mod).Bytes()
	}
	return leftPad(v, int(modLen))
}

// modexpRunPatched is the same, using the patched library production links.
func modexpRunPatched(baseLen, expLen, modLen uint64, payload []byte) []byte {
	if baseLen == 0 && modLen == 0 {
		return []byte{}
	}
	base := new(patched.Int).SetBytes(getData(payload, 0, baseLen))
	exp := new(patched.Int).SetBytes(getData(payload, baseLen, expLen))
	mod := new(patched.Int).SetBytes(getData(payload, baseLen+expLen, modLen))
	var v []byte
	switch {
	case mod.BitLen() == 0:
		return leftPad([]byte{}, int(modLen))
	case base.BitLen() == 1:
		v = base.Mod(base, mod).Bytes()
	default:
		v = base.Exp(base, exp, mod).Bytes()
	}
	return leftPad(v, int(modLen))
}

func leftPad(b []byte, size int) []byte {
	if len(b) >= size {
		return b
	}
	out := make([]byte, size)
	copy(out[size-len(b):], b)
	return out
}

func TestModExpDifferential(t *testing.T) {
	seedRNG(t)
	n := 6000 * scale()
	for i := 0; i < n; i++ {
		// random lengths up to 64 bytes each (drawn from the seeded rng so coverage
		// does not shrink with the iteration count).
		bl := uint64(rng.Intn(65))
		el := uint64(rng.Intn(65))
		ml := uint64(rng.Intn(65))
		payload := randBytes(int(bl + el + ml))
		s := modexpRunStd(bl, el, ml, payload)
		p := modexpRunPatched(bl, el, ml, payload)
		if !bytes.Equal(s, p) {
			t.Fatalf("modexp mismatch: bl=%d el=%d ml=%d payload=%x\n  std    =%x\n  patched=%x", bl, el, ml, payload, s, p)
		}
	}
	// structured edges: mod=0, mod=1, base=0, exp=0, big values, even/odd mod
	type vec struct {
		bl, el, ml uint64
		payload    []byte
	}
	mk := func(b, e, m []byte) vec {
		return vec{uint64(len(b)), uint64(len(e)), uint64(len(m)), append(append(append([]byte{}, b...), e...), m...)}
	}
	big0 := []byte{}
	one := []byte{1}
	bigOdd := fp32(modulusFp) // a large odd modulus
	bigEven := fp32(new(big.Int).Sub(modulusFp, big.NewInt(1)))
	vecs := []vec{
		mk(one, one, big0),                   // mod len 0
		mk(one, one, []byte{0}),              // mod = 0
		mk(one, one, one),                    // mod = 1
		mk([]byte{0}, one, bigOdd),           // base 0
		mk(randBytes(48), big0, bigOdd),      // exp 0 (empty) -> result 1 mod m
		mk(randBytes(48), []byte{0}, bigOdd), // exp 0 (explicit)
		mk(randBytes(64), randBytes(64), bigOdd),
		mk(randBytes(64), randBytes(64), bigEven),
		mk(fp32(new(big.Int).Sub(modulusFp, big.NewInt(1))), fp32(orderFr), bigOdd),
	}
	for _, v := range vecs {
		s := modexpRunStd(v.bl, v.el, v.ml, v.payload)
		p := modexpRunPatched(v.bl, v.el, v.ml, v.payload)
		if !bytes.Equal(s, p) {
			t.Fatalf("modexp edge mismatch: %+v\n  std    =%x\n  patched=%x", v, s, p)
		}
	}
}

// cofactorTorsionG2 returns EVM-format bytes of a G2 point in the cofactor
// torsion: T = [r]*R for a random on-curve R, where r is the prime subgroup
// order. T has order dividing the G2 cofactor h and is therefore NOT in the
// order-r subgroup (unless it lands on O, which we skip). This specifically
// stresses gnark's FAST IsInSubGroup (psi/endomorphism membership test) against
// cloudflare's NAIVE [Order]P==O check — the one class a generic random
// non-subgroup point only approximates.
func cofactorTorsionG2() ([]byte, bool) {
	for tries := 0; tries < 64; tries++ {
		u := randE2()
		R := bn254.MapToCurve2(&u)
		if !R.IsOnCurve() {
			continue
		}
		var T bn254.G2Affine
		T.ScalarMultiplication(&R, orderFr) // [r]R -> cofactor torsion
		if T.IsInfinity() {
			continue
		}
		return g2ToEVM(T), true
	}
	return nil, false
}

func TestBn256SubgroupCheckDiscriminators(t *testing.T) {
	seedRNG(t)
	n := 800 * scale()
	got := 0
	for i := 0; i < n; i++ {
		blob, ok := cofactorTorsionG2()
		if !ok {
			continue
		}
		got++
		// cofactor-torsion G2 as the only pair (both backends must agree: reject)
		diff(t, "subgroup/cofactor-torsion", append(validG1(), blob...), cfPairing, gnPairing)
		// and after a leading valid pair
		in := append(validG1(), validG2()...)
		in = append(in, validG1()...)
		in = append(in, blob...)
		diff(t, "subgroup/valid+cofactor-torsion", in, cfPairing, gnPairing)
		// also assert the two G2 DECODERS agree directly (accept/reject parity),
		// independent of the pairing math
		gd := func(b []byte) ([]byte, error) {
			p := new(gn.G2)
			_, err := p.Unmarshal(b)
			return nil, err
		}
		cd := func(b []byte) ([]byte, error) {
			p := new(cf.G2)
			_, err := p.Unmarshal(b)
			return nil, err
		}
		diff(t, "subgroup/g2decode-parity", blob, cd, gd)
	}
	if got == 0 {
		t.Fatal("generated no cofactor-torsion points")
	}
	t.Logf("tested %d cofactor-torsion G2 discriminators (x3 checks each)", got)
}

// TestBn256PanicProbe guards the property that bn256 precompiles are NOT behind
// the EVM recover() boundary, so a gnark PANIC would HALT a node where cloudflare
// returns an error (CALL-fail). diff()'s call() wrapper converts a panic to a flag
// and fails on any panic-parity mismatch, so any gnark-panics-where-cloudflare-
// errors case is caught here.
func TestBn256PanicProbe(t *testing.T) {
	seedRNG(t)
	r := orderFr
	max256 := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 256), big.NewInt(1))
	// scalars incl. exact multiples of r (s==0 mod r stresses gnark SplitScalar/
	// mulGLV hiWordIndex truncation) — all kept < 2^256 so FillBytes is safe.
	scalars := [][]byte{
		fp32(big.NewInt(0)), fp32(big.NewInt(1)),
		fp32(r),
		fp32(new(big.Int).Mul(r, big.NewInt(2))),
		fp32(new(big.Int).Mul(r, big.NewInt(3))),
		fp32(new(big.Int).Sub(r, big.NewInt(1))),
		fp32(new(big.Int).Add(r, big.NewInt(1))),
		fp32(max256),
	}
	gen := append(fp32(big.NewInt(1)), fp32(big.NewInt(2))...) // (1,2): bn254 G1 generator
	inf := make([]byte, 64)
	n := 120 * scale()
	for i := 0; i < n; i++ {
		bases := [][]byte{gen, inf, validG1(), validG1()}
		for _, b := range bases {
			for _, s := range scalars {
				in := append(append([]byte{}, b...), s...)
				diff(t, "panic/mul", in, cfMul, gnMul)
			}
		}
	}
	// large mixed valid/infinity pairing inputs (up to ~64 pairs)
	for i := 0; i < 20*scale(); i++ {
		pairs := 1 + rng.Intn(64)
		var in []byte
		for j := 0; j < pairs; j++ {
			switch j % 3 {
			case 0:
				in = append(in, validG1()...)
				in = append(in, validG2()...)
			case 1:
				in = append(in, make([]byte, 64)...) // infinity G1
				in = append(in, validG2()...)
			case 2:
				in = append(in, validG1()...)
				in = append(in, make([]byte, 128)...) // infinity G2
			}
		}
		diff(t, "panic/pairing-mixed", in, cfPairing, gnPairing)
	}
	// near-modulus coordinates fed to ecAdd (decode boundary then add arithmetic)
	pm1 := fp32(new(big.Int).Sub(modulusFp, big.NewInt(1)))
	pm2 := fp32(new(big.Int).Sub(modulusFp, big.NewInt(2)))
	for i := 0; i < 60*scale(); i++ {
		for _, c := range [][]byte{pm1, pm2} {
			in := append(append(append([]byte{}, c...), c...), validG1()...)
			diff(t, "panic/add-nearmod", in, cfAdd, gnAdd)
			in2 := append(append([]byte{}, validG1()...), c...)
			in2 = append(in2, c...)
			diff(t, "panic/add-nearmod2", in2, cfAdd, gnAdd)
		}
	}
}

// ----- google (bn256_slow) precompile replicas: the THIRD backend used by all
// builds on every non-amd64/arm64 GOARCH. If google disagrees with cloudflare or
// gnark on any input, an exotic-arch node would fork from the amd64/arm64 fleet. -----

func ggAdd(in []byte) ([]byte, error) {
	x := new(gg.G1)
	if _, err := x.Unmarshal(getData(in, 0, 64)); err != nil {
		return nil, err
	}
	y := new(gg.G1)
	if _, err := y.Unmarshal(getData(in, 64, 64)); err != nil {
		return nil, err
	}
	res := new(gg.G1)
	res.Add(x, y)
	return res.Marshal(), nil
}

func ggMul(in []byte) ([]byte, error) {
	p := new(gg.G1)
	if _, err := p.Unmarshal(getData(in, 0, 64)); err != nil {
		return nil, err
	}
	res := new(gg.G1)
	res.ScalarMult(p, new(big.Int).SetBytes(getData(in, 64, 32)))
	return res.Marshal(), nil
}

func ggPairing(in []byte) ([]byte, error) {
	if len(in)%192 > 0 {
		return nil, errSize
	}
	var cs []*gg.G1
	var ts []*gg.G2
	for i := 0; i < len(in); i += 192 {
		c := new(gg.G1)
		if _, err := c.Unmarshal(in[i : i+64]); err != nil {
			return nil, err
		}
		tp := new(gg.G2)
		if _, err := tp.Unmarshal(in[i+64 : i+192]); err != nil {
			return nil, err
		}
		cs = append(cs, c)
		ts = append(ts, tp)
	}
	if gg.PairingCheck(cs, ts) {
		return true32, nil
	}
	return false32, nil
}

// TestBn256ThreeBackendParity checks that cloudflare, gnark, and google agree on
// every class, so no node forks by architecture. It critically includes the
// non-subgroup and cofactor-torsion G2 classes (google's twist IsOnCurve also
// subgroup-checks). The google backend is pure-Go and comparatively slow, so this
// test is skipped under -short (the exotic-arch equivalence it guards is not the
// amd64/arm64 consensus path); the cloudflare/gnark comparison is fully covered by
// the other tests.
func TestBn256ThreeBackendParity(t *testing.T) {
	if testing.Short() {
		t.Skip("skipping slow pure-Go google three-backend parity under -short")
	}
	seedRNG(t)
	n := 120 * scale()
	for i := 0; i < n; i++ {
		a := append(validG1(), validG1()...)
		diff(t, "3way/add cf-gg", a, cfAdd, ggAdd)
		diff(t, "3way/add gn-gg", a, gnAdd, ggAdd)

		m := append(validG1(), randBytes(32)...)
		diff(t, "3way/mul cf-gg", m, cfMul, ggMul)
		diff(t, "3way/mul gn-gg", m, gnMul, ggMul)

		p := append(validG1(), validG2()...)
		p = append(p, validG1()...)
		p = append(p, validG2()...)
		diff(t, "3way/pair cf-gg", p, cfPairing, ggPairing)
		diff(t, "3way/pair gn-gg", p, gnPairing, ggPairing)
	}
	// the cross-arch subgroup question: non-subgroup + cofactor-torsion G2 must be
	// rejected identically by all three backends.
	for i := 0; i < 60*scale(); i++ {
		ns := append(validG1(), nonSubgroupG2(t)...)
		diff(t, "3way/nonsub cf-gg", ns, cfPairing, ggPairing)
		diff(t, "3way/nonsub gn-gg", ns, gnPairing, ggPairing)
		if ct, ok := cofactorTorsionG2(); ok {
			c := append(validG1(), ct...)
			diff(t, "3way/cofactor cf-gg", c, cfPairing, ggPairing)
			diff(t, "3way/cofactor gn-gg", c, gnPairing, ggPairing)
			diff(t, "3way/cofactor-decode gn-gg", ct, func(b []byte) ([]byte, error) {
				p := new(gn.G2)
				_, err := p.Unmarshal(b)
				return nil, err
			}, func(b []byte) ([]byte, error) {
				p := new(gg.G2)
				_, err := p.Unmarshal(b)
				return nil, err
			})
		}
	}
	// edge coords, infinity, true-relation
	ec := edgeCoords()
	for _, x := range ec {
		for _, y := range ec {
			pt := append(append([]byte{}, x...), y...)
			diff(t, "3way/edge cf-gg", append(pt, validG1()...), cfAdd, ggAdd)
		}
	}
	inf := make([]byte, 64)
	diff(t, "3way/inf cf-gg", append(append([]byte{}, inf...), validG1()...), cfAdd, ggAdd)
	for i := 0; i < 15*scale(); i++ {
		_, _, g1, g2 := bn254.Generators()
		a, b := randScalar(), randScalar()
		var P, negP bn254.G1Affine
		P.ScalarMultiplication(&g1, a)
		negP.Neg(&P)
		var Q bn254.G2Affine
		Q.ScalarMultiplication(&g2, b)
		in := append(g1ToEVM(P), g2ToEVM(Q)...)
		in = append(in, g1ToEVM(negP)...)
		in = append(in, g2ToEVM(Q)...)
		diff(t, "3way/true-relation cf-gg", in, cfPairing, ggPairing)
		diff(t, "3way/true-relation gn-gg", in, gnPairing, ggPairing)
	}
}
