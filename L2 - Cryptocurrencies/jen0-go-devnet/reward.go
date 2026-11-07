package main

// Mining reward, integer-only (SPEC 5.4).
//
//	Reward(N) = 2520 × N^(−a) × V,   V = r^Z,   Z = Φ⁻¹(u),
//	u = top 12 bits of SHA256(seal of block N+1 ‖ "reward").
//
// Rewritten in base 2 so that only one exponential is needed:
//
//	Reward(N) = 2520 × 2^( Z·log2(r) − a·log2(N) )
//
// Every step below uses integers (Q32.32 and Q2.62 fixed point, math/big for
// products), so every node computes the identical picogram amount on every
// CPU. No floating point is used in consensus.

import (
	"crypto/sha256"
	"math/big"
	"math/bits"
)

// log2Q32 returns log2(n) in Q32.32 for n >= 1, computed bit by bit by
// repeated squaring of the mantissa (exact up to the last fractional bit).
func log2Q32(n uint64) int64 {
	if n == 0 {
		panic("log2 of zero")
	}
	k := bits.Len64(n) - 1 // integer part
	// mantissa m = n / 2^k in [1, 2), as Q2.62
	var m uint64
	if k <= 62 {
		m = n << (62 - k)
	} else {
		m = n >> (k - 62)
	}
	frac := int64(0)
	for i := 1; i <= 32; i++ {
		hi, lo := bits.Mul64(m, m) // m^2 in Q4.124
		m = hi<<2 | lo>>62         // back to Q2.62 (m^2 < 4 fits)
		if m >= 1<<63 {            // m >= 2.0
			frac |= 1 << (32 - i)
			m >>= 1
		}
	}
	return int64(k)<<32 | frac
}

// exp2FracQ62 returns 2^f in Q2.62 for f in [0, 2^32) (a Q0.32 fraction),
// as the product of the precomputed 2^(2^-i) for each set bit of f.
func exp2FracQ62(f uint64) uint64 {
	acc := uint64(1) << 62
	for i := 1; i <= 32; i++ {
		if f&(1<<(32-i)) != 0 {
			hi, lo := bits.Mul64(acc, Exp2FracQ62[i-1])
			acc = hi<<2 | lo>>62
		}
	}
	return acc
}

// RewardZIndex derives the table index from the next block's seal hash.
// Using the NEXT block means no miner can see or steer its own draw (SPEC 5.4).
func RewardZIndex(nextSeal [32]byte) int {
	h := sha256.Sum256(append(nextSeal[:], []byte("reward")...))
	return int(h[0])<<4 | int(h[1])>>4 // top 12 bits
}

// RawRewardPico returns 2520 × N^(−a) in picograms (V = 1). Used for display.
func RawRewardPico(height uint64) uint64 {
	return rewardPico(height, 0)
}

// RewardPico returns the full reward of block `height`, given the table index
// drawn from the seal of block height+1.
func RewardPico(height uint64, zIndex int) uint64 {
	return rewardPico(height, PhiInvQ32[zIndex])
}

func rewardPico(height uint64, zQ32 int64) uint64 {
	if height == 0 {
		return 0
	}
	// exponent E = Z·log2(r) − a·log2(N), in Q32.32 (products done in big ints)
	z := new(big.Int).Mul(big.NewInt(zQ32), big.NewInt(Log2RQ32))
	n := new(big.Int).Mul(big.NewInt(AQ32), big.NewInt(log2Q32(height)))
	e := new(big.Int).Sub(z, n)
	e.Rsh(e, 32) // floor division by 2^32 (Rsh on negative big.Int floors)
	E := e.Int64()

	intPart := E >> 32                // floor(E), arithmetic shift
	frac := uint64(E) & (1<<32 - 1)    // E − floor(E), in Q0.32
	mant := exp2FracQ62(frac)          // 2^frac in Q2.62

	// result = 2520 × 10^12 × mant × 2^intPart / 2^62, floored
	res := new(big.Int).SetUint64(InitialReward)
	res.Mul(res, new(big.Int).SetUint64(Pico))
	res.Mul(res, new(big.Int).SetUint64(mant))
	shift := intPart - 62
	if shift >= 0 {
		res.Lsh(res, uint(shift))
	} else {
		res.Rsh(res, uint(-shift))
	}
	if !res.IsUint64() {
		panic("reward overflow")
	}
	return res.Uint64()
}
