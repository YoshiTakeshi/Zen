package main

// The Sen peg (Jen-0.9, SPEC 6.5): W follows "base units per Sen", read from
// the chain's own payments, with no oracle and no extra field.
//
// Two kinds of payment, told apart by their amount alone:
//   - JEN-mode: the amount is an exact whole number of sixths of a recent W
//     (wallets price in Sen and pay k JEN = k x W; the smallest denomination
//     is 1/6). Amounts are in picograms, so a converted amount essentially
//     never lands on such a value by chance. The network reads the PRICE IN
//     SEN: count = amount / W.
//   - gram-mode: any other amount (converted from dirhams, dollars, ...). The
//     network reads the VALUE IN BASE UNITS.
//
// Target:  W = typical gram-mode amount / typical JEN-mode count
// where "typical" is a value-weighted geometric average over the Fibonacci
// window (231 blocks), each payment's log clipped to +-1.5 (natural log) around
// the previous window's value, so fake extreme payments pull little.
// Only payments paying at least the standard 1% fee count (faking costs fees).
// If JEN-mode payments are under PegMinShare of the window's payments (or
// gram-mode ones under PegMinGram), W falls back to the typical transfer of
// gram-mode payments (the size rule of Jen-0.7.1, exact-JEN payments ignored).
// W moves at most CoinWeightStepPct per block either way.
//
// All consensus arithmetic is integer: log2 in Q32.32 (reward.go), sums in big.Int.

import (
	"math/big"
	"math/bits"
)

const (
	PegMinSharePermille = 20 // JEN-mode payments must be >= 2% of the window's payments
	PegMinGram          = 20 // and at least this many gram-mode payments in the window
	RecentWs            = 8  // a JEN-mode amount may use the W of the last 8 blocks
)

// clip band: ln(1.5)... no: +-1.5 in natural log = +-2.1640 in log2, Q32.32
var pegClipQ32 = int64(9294388452) // round(1.5 / ln 2 * 2^32)

// RatioStat is one block's contribution: value-weighted sums of clipped log2
// for gram-mode amounts (G) and JEN-mode counts (D), and the counts of each.
type RatioStat struct {
	GW, GL, DW, DL *big.Int
	NG, ND         uint64
}

// jenCount reports whether amount is a JEN-mode payment: an exact whole
// number of sixths of one of the recent W values. Returns the count in sixths.
func jenCount(amount uint64, ws []uint64) (uint64, bool) {
	for _, w := range ws {
		if w == 0 {
			continue
		}
		hi, lo := bits.Mul64(amount, 6)
		if hi >= w {
			continue
		}
		q, r := bits.Div64(hi, lo, w)
		if r == 0 && q >= 1 {
			return q, true
		}
	}
	return 0, false
}

// countsForPeg: only payments at or above the standard 1% fee rate count.
func countsForPeg(t CTx) bool {
	return new(big.Int).Mul(new(big.Int).SetUint64(t.Fee), big.NewInt(101)).Cmp(new(big.Int).SetUint64(t.Amount+t.Fee)) >= 0
}

func clipQ32(x, c int64, have bool) int64 {
	if !have {
		return x
	}
	if x < c-pegClipQ32 {
		return c - pegClipQ32
	}
	if x > c+pegClipQ32 {
		return c + pegClipQ32
	}
	return x
}

var log2Six = log2Q32(6)

// blockRatioStat splits a block's payments by mode and returns the peg sums and
// the gram-mode payments (for the fallback size rule).
func blockRatioStat(txs []CTx, ws []uint64, cG, cD int64, have bool) (RatioStat, []CTx) {
	rs := RatioStat{GW: new(big.Int), GL: new(big.Int), DW: new(big.Int), DL: new(big.Int)}
	var gram []CTx
	for _, t := range txs {
		k6, jen := jenCount(t.Amount, ws)
		if !jen {
			gram = append(gram, t)
		}
		if !countsForPeg(t) || t.Amount == 0 {
			continue
		}
		if jen {
			l := clipQ32(log2Q32(k6)-log2Six, cD, have) // log2 of the count in JEN
			w := new(big.Int).SetUint64(k6)
			rs.DW.Add(rs.DW, w)
			rs.DL.Add(rs.DL, new(big.Int).Mul(w, big.NewInt(l)))
			rs.ND++
		} else {
			l := clipQ32(log2Q32(t.Amount), cG, have)
			w := new(big.Int).SetUint64(t.Amount)
			rs.GW.Add(rs.GW, w)
			rs.GL.Add(rs.GL, new(big.Int).Mul(w, big.NewInt(l)))
			rs.NG++
		}
	}
	return rs, gram
}

// PegTarget computes the window's typical log2 values and the target W.
// ok is false when there are too few payments of either kind (use the fallback).
func PegTarget(hist []RatioStat) (target uint64, meanG, meanD int64, ok bool) {
	gw, gl, dw, dl := new(big.Int), new(big.Int), new(big.Int), new(big.Int)
	var ng, nd uint64
	for i, h := range hist {
		if i >= len(feeWeights) {
			break
		}
		f := big.NewInt(feeWeights[i])
		gw.Add(gw, new(big.Int).Mul(f, h.GW))
		gl.Add(gl, new(big.Int).Mul(f, h.GL))
		dw.Add(dw, new(big.Int).Mul(f, h.DW))
		dl.Add(dl, new(big.Int).Mul(f, h.DL))
		ng += h.NG
		nd += h.ND
	}
	if gw.Sign() == 0 || dw.Sign() == 0 {
		return 0, 0, 0, false
	}
	meanG = new(big.Int).Quo(gl, gw).Int64()
	meanD = new(big.Int).Quo(dl, dw).Int64()
	if ng < PegMinGram || nd*1000 < PegMinSharePermille*(nd+ng) {
		return 0, meanG, meanD, false
	}
	// W = 2^(meanG - meanD): computed as 2^20 x 2^(e - 20) for precision
	return mulPow2(1<<20, meanG-meanD-(20<<32)), meanG, meanD, true
}
