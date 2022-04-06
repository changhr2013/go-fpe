package fpe

import (
	"crypto/cipher"
	"errors"
	"fmt"
	"math"
	"math/big"
)

const _BlockSize int = 16
const _LOG2 float64 = math.Ln2

// EncryptFF1 FPE-FF1 加密
func EncryptFF1(cipher cipher.Block, radix int, tweak []byte, buf []byte, off int, length int) ([]byte, error) {

	err := checkByteArgs(cipher, true, radix, buf, off, length)
	if err != nil {
		return nil, err
	}

	// Algorithm 7
	n := length
	u := n / 2
	v := n - u

	A := toShort(buf, off, u)
	B := toShort(buf, off+u, v)

	encryptShortArr, err := encFF1(cipher, radix, tweak, n, u, v, A, B)
	if err != nil {
		return nil, err
	}
	return toByte(encryptShortArr), nil
}

// DecryptFF1 FPE-FF1 解密
func DecryptFF1(cipher cipher.Block, radix int, tweak []byte, buf []byte, off int, length int) ([]byte, error) {

	err := checkByteArgs(cipher, true, radix, buf, off, length)
	if err != nil {
		return nil, err
	}

	// Algorithm 8
	n := length
	u := n / 2
	v := n - u

	A := toShort(buf, off, u)
	B := toShort(buf, off+u, v)

	rvArr, err := decFF1(cipher, radix, tweak, n, u, v, A, B)
	if err != nil {
		return nil, err
	}
	return toByte(rvArr), nil
}

// compute function
func encFF1(cipher cipher.Block, radix int, T []byte, n int, u int, v int, A []int16, B []int16) ([]int16, error) {

	t := len(T)
	b := (int(math.Ceil(math.Log(float64(radix))*float64(v)/_LOG2)) + 7) / 8
	d := (((b + 3) / 4) * 4) + 4

	P := calculateP_FF1(radix, byte(u), n, t)

	bigRadix := big.NewInt(int64(radix))
	modUV := calculateModUV(bigRadix, u, v)

	m := v

	for i := 0; i < 10; i++ {

		// i. - iv.
		y, err := calculateY_FF1(cipher, bigRadix, T, b, d, i, P, B)
		if err != nil {
			return nil, err
		}

		// v
		m = n - m
		modulus := modUV[i&1]

		// vi.
		numBigInt := num(bigRadix, A)
		modBigInt := numBigInt.Add(numBigInt, y)
		c := modBigInt.Mod(modBigInt, modulus)

		// vii. - ix.
		C := A
		A = B
		B = C
		err = str(bigRadix, c, m, C, 0)
		if err != nil {
			return nil, err
		}
	}

	return concatenateShort(A, B), nil
}

func decFF1(cipher cipher.Block, radix int, T []byte, n int, u int, v int, A []int16, B []int16) ([]int16, error) {

	t := len(T)
	b := (int(math.Ceil(math.Log(float64(radix))*float64(v)/_LOG2)) + 7) / 8
	d := (((b + 3) / 4) * 4) + 4

	P := calculateP_FF1(radix, byte(u), n, t)

	bigRadix := big.NewInt(int64(radix))
	modUV := calculateModUV(bigRadix, u, v)

	m := u

	for i := 9; i >= 0; i-- {

		// i. - iv.
		y, err := calculateY_FF1(cipher, bigRadix, T, b, d, i, P, A)
		if err != nil {
			return nil, err
		}

		// v
		m = n - m
		modulus := modUV[i&1]

		// vi.
		numBigInt := num(bigRadix, B)
		modBigInt := numBigInt.Sub(numBigInt, y)
		c := modBigInt.Mod(modBigInt, modulus)

		// vii. - ix.
		C := B
		B = A
		A = C
		err = str(bigRadix, c, m, C, 0)
		if err != nil {
			return nil, err
		}

	}

	return concatenateShort(A, B), nil
}

func calculateY_FF1(cipher cipher.Block, bigRadix *big.Int, T []byte, b int, d int, round int, P []byte, AB []int16) (*big.Int, error) {

	t := len(T)

	// i.
	numAB := num(bigRadix, AB)
	bytesAB := numAB.Bytes()

	zeroes := -(t + b + 1) & 15

	Q := make([]byte, t+zeroes+1+b)

	copy(Q[0:t], T)

	Q[t+zeroes] = byte(round)

	copy(Q[len(Q)-len(bytesAB):], bytesAB)

	// ii.
	R, err := prf(cipher, concatenate(P, Q))
	if err != nil {
		return nil, err
	}

	// iii.
	sBlocks := R
	if d > _BlockSize {

		sBlocksLen := (d + _BlockSize - 1) / _BlockSize
		sBlocks = make([]byte, sBlocksLen*_BlockSize)
		copy(sBlocks[0:_BlockSize], R[0:_BlockSize])

		uint32Bytes := make([]byte, 4)
		for j := 0; j < sBlocksLen; j++ {
			sOff := j * _BlockSize
			copy(sBlocks[sOff:sOff+_BlockSize], R[0:_BlockSize])
			intToBigEndian(j, uint32Bytes, 0)

			xor(uint32Bytes, 0, sBlocks, sOff+_BlockSize-4, 4)
			cipher.Encrypt(sBlocks[sOff:], sBlocks[sOff:])
		}

	}

	// iv.
	numBigInt := big.NewInt(0).SetBytes(sBlocks[0:d])
	return numBigInt, nil

}

func num(R *big.Int, x []int16) *big.Int {
	result := big.NewInt(0)

	for i := 0; i < len(x); i++ {

		result = result.Mul(result, R)

		result = result.Add(result, big.NewInt(int64(uint16(x[i])&(0xFFFF))))
	}
	return result
}

func calculateP_FF1(radix int, uLow byte, n int, t int) []byte {
	P := make([]byte, _BlockSize)
	P[0] = 1
	P[1] = 2
	P[2] = 1

	// Radix
	P[3] = 0
	P[4] = byte(radix >> 8)
	P[5] = byte(radix)

	P[6] = 10
	P[7] = uLow
	intToBigEndian(n, P, 8)
	intToBigEndian(t, P, 12)
	return P
}

func calculateModUV(bigRadix *big.Int, u int, v int) []*big.Int {
	modUV := make([]*big.Int, 2)
	modUV0 := big.NewInt(0).SetBytes(bigRadix.Bytes())
	modUV0.Exp(modUV0, big.NewInt(int64(u)), nil)
	modUV[0] = modUV0
	modUV[1] = modUV0
	if v != u {
		modUV[1] = modUV[1].Mul(modUV[1], bigRadix)
	}
	return modUV
}

func intToBigEndian(n int, bs []byte, off int) {
	bs[off] = byte(uint(n) >> 24)
	off++
	bs[off] = byte(uint(n) >> 16)
	off++
	bs[off] = byte(uint(n) >> 24)
	off++
	bs[off] = byte(n)
}

func prf(c cipher.Block, x []byte) ([]byte, error) {

	if (len(x) & _BlockSize) != 0 {
		return nil, errors.New("illegal argument exception")
	}

	m := len(x) / _BlockSize
	y := make([]byte, _BlockSize)

	for i := 0; i < m; i++ {
		xor(x, i*_BlockSize, y, 0, _BlockSize)
		c.Encrypt(y, y)
	}

	return y, nil
}

func xor(x []byte, xOff int, y []byte, yOff int, length int) {
	for i := 0; i < length; i++ {
		y[yOff+i] ^= x[xOff+i]
	}
}

func concatenate(a []byte, b []byte) []byte {
	if nil == a {
		// b might also be nil
		result := make([]byte, len(b))
		copy(result, b)
		return result
	}
	if nil == b {
		// a might also be nil
		result := make([]byte, len(a))
		copy(result, a)
		return result
	}

	r := make([]byte, len(a)+len(b))
	copy(r[0:len(a)], a)
	copy(r[len(a):], b)
	return r
}

func concatenateShort(a []int16, b []int16) []int16 {
	if nil == a {
		// b might also be nil
		result := make([]int16, len(b))
		copy(result, b)
		return result
	}
	if nil == b {
		// a might also be nil
		result := make([]int16, len(a))
		copy(result, a)
		return result
	}

	r := make([]int16, len(a)+len(b))
	copy(r[0:len(a)], a)
	copy(r[len(a):], b)
	return r
}

func str(R *big.Int, x *big.Int, m int, output []int16, off int) error {

	if x.Sign() < 0 {
		return errors.New("illegal argument exception")
	}

	for i := 1; i <= m; i++ {

		q, r := x.DivMod(x, R, new(big.Int))

		output[off+m-i] = int16(r.Int64())
		x = q
	}
	if x.Sign() != 0 {
		return errors.New("illegal argument exception")
	}
	return nil
}

func toShort(buf []byte, off int, length int) []int16 {

	s := make([]int16, length)

	for i := 0; i != len(s); i++ {
		s[i] = int16(buf[off+i] & 0xFF)
	}
	return s
}

func toByte(buf []int16) []byte {
	s := make([]byte, len(buf))
	for i := 0; i != len(s); i++ {
		s[i] = byte(buf[i])
	}
	return s
}

// argument check
func checkCipher(cipher cipher.Block) error {
	if _BlockSize != cipher.BlockSize() {
		return errors.New("illegal block size")
	}
	return nil
}

func checkLength(isFF1 bool, radix int, length int) error {

	if length < 2 || math.Pow(float64(radix), float64(length)) < 1000000 {
		return errors.New("input too short")
	}

	if !isFF1 {
		maxLen := 2 * (int)(math.Floor(math.Log(math.Pow(2, 96))/math.Log(float64(radix))))
		if length > maxLen {
			return errors.New(fmt.Sprintf("maximum input length is %d", maxLen))
		}
	}
	return nil
}

func checkByteData(isFF1 bool, radix int, buf []byte, off int, length int) error {

	err := checkLength(isFF1, radix, length)
	if err != nil {
		return err
	}

	for i := 0; i < length; i++ {
		b := int(buf[off+i] & 0xFF)
		if b >= radix {
			return errors.New("input data outside of radix")
		}
	}
	return nil
}

func checkShortData(isFF1 bool, radix int, buf []int16, off int, length int) error {

	err := checkLength(isFF1, radix, length)
	if err != nil {
		return err
	}

	for i := 0; i < length; i++ {
		b := int(uint16(buf[off+i]) & 0xFFFF)
		if b >= radix {
			return errors.New("input data outside of radix")
		}
	}
	return nil
}

func checkByteArgs(cipher cipher.Block, isFF1 bool, radix int, buf []byte, off int, length int) error {
	err := checkCipher(cipher)
	if err != nil {
		return err
	}

	if radix < 2 || radix > (1<<16) {
		return errors.New("illegal radix")
	}

	err = checkByteData(isFF1, radix, buf, off, length)
	if err != nil {
		return err
	}

	return nil
}

func checkShortArgs(cipher cipher.Block, isFF1 bool, radix int, buf []int16, off int, length int) error {
	err := checkCipher(cipher)
	if err != nil {
		return err
	}

	if radix < 2 || radix > (1<<16) {
		return errors.New("illegal radix")
	}

	err = checkShortData(isFF1, radix, buf, off, length)
	if err != nil {
		return err
	}

	return nil
}
