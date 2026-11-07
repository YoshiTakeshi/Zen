package main

// The balanced resize rule (Jen-0.10, SPEC 6.3 and 4.10). Capacity, minting
// entry and each minter's share of a block are tied together:
//
//   - The cap grows only when fees run above standard AND blocks are nearly
//     full; it holds when fees are high but blocks are not full (too few
//     provers, not too little demand); it shrinks only when fees are at or
//     under standard and blocks are under three-quarters full.
//   - A minter may fill at most 5/4 x cap x its share of recent tickets, so
//     one big prover (or a miner preferring its own leaves) cannot fill a
//     block alone, and a full block means many minters took part.
//   - Half of every fee goes into a pool paid out 1/32 per block, so fees a
//     miner-minter pays to itself to fake congestion are partly lost.
//   - The credential window widens with the cap (up to 4x), so more minters
//     can hold a credential when the network needs more provers.
//
// All arithmetic is integer; the cap is kept in thousandths of a leaf so
// small steps accumulate.

// CredWindow is how many blocks a ticket keeps its minter credentialed at
// leaf cap c.
func CredWindow(c uint64) uint64 {
	if !Balanced {
		return CredBlocks
	}
	f := c / CredWidenAt
	if f < 1 {
		f = 1
	}
	if f > CredWidenMax {
		f = CredWidenMax
	}
	return CredBlocks * f
}

// ticketCounts counts each minter's tickets in the credential window before
// this block, plus the block's own tickets.
func (s *State) ticketCounts(own []Ticket) (map[uint32]uint64, uint64) {
	cnt := map[uint32]uint64{}
	total := uint64(0)
	w := CredWindow(s.Capacity)
	for i, blk := range s.TicketLog {
		if uint64(i) >= w {
			break
		}
		for _, m := range blk {
			cnt[m]++
			total++
		}
	}
	for _, t := range own {
		cnt[t.Minter]++
		total++
	}
	return cnt, total
}

// LeafQuota is the most leaves minter m may put in the block after this
// state, given the block's own tickets.
func (s *State) LeafQuota(m uint32, own []Ticket) int {
	cnt, total := s.ticketCounts(own)
	return quotaFor(cnt[m], total, s.LeafCap())
}

func quotaFor(t, total uint64, capLeaves int) int {
	if !Balanced || total == 0 {
		return capLeaves
	}
	num := QuotaNum * uint64(capLeaves) * t
	den := QuotaDen * total
	q := (num + den - 1) / den // round up
	if q < 1 {
		q = 1
	}
	if q > uint64(capLeaves) {
		q = uint64(capLeaves)
	}
	return int(q)
}

// stepBalanced moves the cap (thousandths of a leaf) one block.
// log2Rate is the recent fee rate (Fibonacci-weighted geometric mean, Q32.32
// log2); fullEMA the recent fullness in permille.
func stepBalanced(capMilli, fullEMA uint64, log2Rate int64, haveRate bool) (uint64, string) {
	std := -log2Q32(10000 / StandardFeeBps) // log2(1%)
	band := log2Q32(102) - log2Q32(100)     // log2(1.02)
	feeHigh := haveRate && log2Rate > std+band
	lo, hi := CapacityMin*1000, CapacityMax*1000
	switch {
	case feeHigh && fullEMA > FullGrowPermille:
		step := capMilli * CapGrowPer10k / 10000
		if step < 1 {
			step = 1
		}
		capMilli += step
		if capMilli > hi {
			capMilli = hi
		}
		return capMilli, "grow"
	case feeHigh:
		return capMilli, "hold" // fees high but blocks not full: too few provers
	case fullEMA < FullShrinkPermille:
		step := capMilli * CapShrinkPer10k / 10000
		if step < 1 {
			step = 1
		}
		if capMilli > lo+step {
			capMilli -= step
		} else {
			capMilli = lo
		}
		return capMilli, "shrink"
	}
	return capMilli, "hold"
}

// stepFullEMA moves the fullness average toward this block's fullness.
func stepFullEMA(ema uint64, leaves, capLeaves int) uint64 {
	full := uint64(0)
	if capLeaves > 0 {
		full = uint64(leaves) * 1000 / uint64(capLeaves)
	}
	if full > 1000 {
		full = 1000
	}
	return uint64(int64(ema) + (int64(full)-int64(ema))/FullEMADiv)
}
