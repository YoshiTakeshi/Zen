package main

// Coin weight (SPEC 6.4, from the original Zen page, "Coin's weight").
//
// Balances, fees and rewards are counted in fixed pico-units. "1 JEN" is a
// floating unit on top of them: W pico-units, the coin weight, measured from
// the chain's own payments so that a coin always has its standard fineness:
//
//	W = metallic average of fees  ÷  geometric average of fee rates
//
//   - Each block with payments records its mean fee, the standard deviation of
//     its fees, and the mean log2 of its fee rates.
//   - Previous blocks are averaged with weights halving over Fibonacci-sized
//     groups: the last block weight 1, the 2 before it 1/2, the 3 before 1/4,
//     then 5 at 1/8, 8 at 1/16 ... (10 groups, 231 blocks, in this devnet).
//   - Metallic average (Bronze) = average − 0.5164 × standard deviation: the
//     point below which 1/r = 30.3% of a normal distribution lies (Golden would
//     use +0.3003, Silver −0.2167).
//   - W moves at most 1% per block toward that target (smooth resizing).
//
// The smallest payment is W × lowest fee ÷ highest fee = W × 0.01% ÷ 6%, so
// even the smallest payment pays at least 0.01% of a coin in fee.

import (
	"math/big"
)

const (
	MetallicZ1e4      = -5164   // Φ⁻¹(1/r) for Bronze, ×10^4
	FeeWindowGroups   = 10      // Fibonacci groups 1,2,3,5,...,89 = 231 blocks
	CoinWeightStepPct = 1       // largest change of W per block, percent
	GenesisCoinWeight = Pico    // starting coin weight (1 JEN = 10^12 pico at genesis)
)

// FeeStat summarises one block's payments.
type FeeStat struct {
	N           uint32 `json:"n"`
	MeanFee     uint64 `json:"mean_fee"`      // pico-units
	SDFee       uint64 `json:"sd_fee"`        // pico-units
	MeanLog2Q32 int64  `json:"mean_log2_q32"` // mean log2(fee rate), Q32.32 (negative)
}

func blockFeeStat(txs []CTx) (FeeStat, bool) {
	if len(txs) == 0 {
		return FeeStat{}, false
	}
	sum, sumSq := new(big.Int), new(big.Int)
	var lg int64
	for _, t := range txs {
		f := new(big.Int).SetUint64(t.Fee)
		sum.Add(sum, f)
		sumSq.Add(sumSq, new(big.Int).Mul(f, f))
		lg += log2Q32(t.Fee) - log2Q32(t.Amount+t.Fee)
	}
	n := big.NewInt(int64(len(txs)))
	mean := new(big.Int).Div(sum, n)
	// variance = E[f²] − E[f]²
	v := new(big.Int).Div(sumSq, n)
	v.Sub(v, new(big.Int).Mul(mean, mean))
	if v.Sign() < 0 {
		v.SetInt64(0)
	}
	return FeeStat{N: uint32(len(txs)), MeanFee: mean.Uint64(), SDFee: new(big.Int).Sqrt(v).Uint64(), MeanLog2Q32: lg / int64(len(txs))}, true
}

// fibWeights gives the weight of each past block (most recent first): 2^9 for
// the last block, 2^8 for the 2 before, 2^7 for the 3 before, ...
func fibWeights() []int64 {
	var w []int64
	a, b := 1, 2
	for g := 0; g < FeeWindowGroups; g++ {
		for i := 0; i < a; i++ {
			w = append(w, 1<<(FeeWindowGroups-1-g))
		}
		a, b = b, a+b
	}
	return w
}

var feeWeights = fibWeights()

// mulPow2 returns v × 2^(e), e in Q32.32, floored (integer-only, like the reward).
func mulPow2(v uint64, eQ32 int64) uint64 {
	intPart := eQ32 >> 32
	mant := exp2FracQ62(uint64(eQ32) & (1<<32 - 1))
	res := new(big.Int).SetUint64(v)
	res.Mul(res, new(big.Int).SetUint64(mant))
	if s := intPart - 62; s >= 0 {
		res.Lsh(res, uint(s))
	} else {
		res.Rsh(res, uint(-s))
	}
	if !res.IsUint64() {
		return ^uint64(0)
	}
	return res.Uint64()
}

// CoinWeightTarget computes the metallic average fee, the geometric fee rate
// (as mean log2) and the target W from a fee history (most recent first).
func CoinWeightTarget(hist []FeeStat) (metAvg uint64, log2Rate int64, target uint64, ok bool) {
	if len(hist) == 0 {
		return 0, 0, 0, false
	}
	sw, sMean, sSD, sLog := new(big.Int), new(big.Int), new(big.Int), new(big.Int)
	for i, h := range hist {
		if i >= len(feeWeights) {
			break
		}
		w := big.NewInt(feeWeights[i])
		sw.Add(sw, w)
		sMean.Add(sMean, new(big.Int).Mul(w, new(big.Int).SetUint64(h.MeanFee)))
		sSD.Add(sSD, new(big.Int).Mul(w, new(big.Int).SetUint64(h.SDFee)))
		sLog.Add(sLog, new(big.Int).Mul(w, big.NewInt(h.MeanLog2Q32)))
	}
	avg := new(big.Int).Div(sMean, sw)
	sd := new(big.Int).Div(sSD, sw)
	met := new(big.Int).Mul(sd, big.NewInt(MetallicZ1e4))
	met.Quo(met, big.NewInt(10000))
	met.Add(met, avg)
	// a heavy-tailed fee spread could push the metallic average below zero:
	// floor it at a tenth of the plain average
	if floor := new(big.Int).Div(avg, big.NewInt(10)); met.Cmp(floor) < 0 {
		met = floor
	}
	log2Rate = new(big.Int).Quo(sLog, sw).Int64()
	metAvg = met.Uint64()
	return metAvg, log2Rate, mulPow2(metAvg, -log2Rate), true
}

// stepCoinWeight moves W toward the target by at most CoinWeightStepPct.
func stepCoinWeight(w, target uint64) uint64 {
	lo, hi := w-w*CoinWeightStepPct/100, w+w*CoinWeightStepPct/100
	switch {
	case target < lo:
		return lo
	case target > hi:
		return hi
	}
	return target
}

// MinPayment is the smallest amount a payment may move: W × lowest fee ÷ highest fee.
func MinPayment(w uint64) uint64 {
	m := new(big.Int).SetUint64(w)
	m.Mul(m, big.NewInt(FeeMaxDen))
	m.Div(m, big.NewInt(FeeMinDen*FeeMaxNum))
	return m.Uint64()
}
