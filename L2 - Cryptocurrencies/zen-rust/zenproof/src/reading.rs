// The reading of S (SPEC 6.6): how the network learns how many base units one coin weighs, from its own payments.
//
//   S  =  typical ordinary value (base units)  /  typical Sen price (Sen)
//
// Everything is integer arithmetic, so every node reads the same S.
//  - A counted payment (the peg of blockdata.rs: each gram counts once) adds its coin-days weight to one of two
//    histograms of about 1,000 log-spaced bins: Sen-priced payments (amount = a whole number of sixths of the S of
//    one of the last 8 blocks) by price in sixths, all others by value in base units.
//  - At the end of each day the reading takes the middle 20% of counted weight on each side (by log value),
//    and S_day = 6 * ordinary / sixths.
//  - Day window: Fibonacci groups of days (1, 2, 3, 5, 8, 13) weighted 32, 16, 8, 4, 2, 1; a day's reading is first
//    clipped to +-10% of the window before it.
//  - Anchor and band: the anchor follows the window by at most 0.75% a day; S stays within +-10% of it.
//  - Only payments paying at least the standard fee count. Receiver cap: one account may bring at most `cap_bp`
//    ten-thousandths of the previous day's counted Sen-priced weight into the reading (0 = off).
// Not here yet: bonds on disagreement and their penalty (SPEC 6.6).
use crate::blockdata::{weight, Counted, BPD};
use std::collections::HashMap;
use std::sync::OnceLock;

pub const BINS: usize = 1024;
const FRAC: u128 = 1 << 32;
const GROUPS: [usize; 6] = [1, 2, 3, 5, 8, 13];
const WINDOW_DAYS: usize = 32;
pub const RECENT_S: usize = 8;
/// anchor speed per day, in ten-thousandths: 0.75% up, 0.74% down (0.0013% a block). Chosen from the simulation of README round 17:
/// a maximal push reaches +16% in 7 days and +38% in 30, an honest +50% change is followed to within 5% in 35 days.
pub const ANCHOR_UP: u64 = 75;
pub const ANCHOR_DOWN: u64 = 74;

fn isqrt(n: u128) -> u128 {
    if n < 2 { return n; }
    let mut x = 1u128 << ((128 - n.leading_zeros() + 1) / 2);
    loop { let y = (x + n / x) / 2; if y >= x { return x; } x = y; }
}
/// thresholds, fixed point 2^-32: t[i] = 2^(i/64) ... bins are 1/16 octave (4.4%) wide; shared table, integer only
fn table() -> &'static Vec<u128> {
    static T: OnceLock<Vec<u128>> = OnceLock::new();
    T.get_or_init(|| {
        let mut r = 2 * FRAC;                       // 2^(1/16) = four square roots of 2
        for _ in 0..4 { r = isqrt(r * FRAC); }
        let mut t = vec![FRAC];
        for i in 0..BINS { let n = t[i] * r / FRAC; t.push(n); }
        t
    })
}
pub fn bin_of(v: u64) -> usize {
    let t = table();
    let vq = (v.max(1) as u128) * FRAC;
    (t.partition_point(|x| *x <= vq) - 1).min(BINS - 1)
}
/// value (fixed point 2^-32) at a bin position in 1/1024 bins
fn value_at(q: u128) -> u128 {
    let t = table();
    let i = ((q / 1024) as usize).min(BINS - 1);
    let f = q % 1024;
    t[i] + (t[i + 1] - t[i]) * f / 1024
}
/// the weighted mean position (1/1024 bin) of the middle 20% of the histogram; None when it is empty
fn middle(hist: &[u128]) -> Option<u128> {
    let total: u128 = hist.iter().sum();
    if total == 0 { return None; }
    let (lo, hi) = (total * 40 / 100, total * 60 / 100);
    let (mut cum, mut num, mut den) = (0u128, 0u128, 0u128);
    for (i, w) in hist.iter().enumerate() {
        let (a, b) = (cum.max(lo), (cum + w).min(hi));
        if b > a { num += (b - a) * (i as u128 * 1024 + 512); den += b - a; }
        cum += w;
    }
    if den == 0 { return None; }
    Some(num / den)
}

#[derive(Clone, Debug)]
pub struct ReadParams {
    /// standard fee in thousandths of the amount (Jen 10 = 1%, Ken 4, Yen 1)
    pub std_fee_pm: u64,
    /// receiver cap, ten-thousandths of the previous day's counted Sen-priced weight (3 = 0.03%); 0 = off
    pub cap_bp: u64,
    /// a day needs at least this many counted payments on each side to give a reading
    pub min_obs: u64,
}
impl ReadParams { pub fn jen() -> Self { ReadParams { std_fee_pm: 10, cap_bp: 3, min_obs: 100 } } }

/// one counted payment as the reading sees it
#[derive(Clone, Copy, Debug)]
pub struct Observed { pub c: Counted, pub pay: u64, pub fee: u64, pub to: u64 }

#[derive(Clone, Debug)]
pub struct Reading {
    pub rp: ReadParams,
    pub s: u64,
    pub anchor: u64,
    hist_sen: Vec<u128>, hist_ord: Vec<u128>,
    n_sen: u64, n_ord: u64,
    today_by_recv: HashMap<u64, u128>,
    cap: Option<u128>,
    /// S used by the last RECENT_S blocks, newest last
    recent: Vec<u64>,
    /// day readings, newest last (after the clip)
    pub days: Vec<u64>,
    pub days_read: u64, pub days_skipped: u64,
}

impl Reading {
    pub fn new(rp: ReadParams, s0: u64) -> Reading {
        let s0 = (s0 - s0 % 6).max(6);   // S is a multiple of 6 so that a sixth of a Sen is a whole number of base units
        Reading { rp, s: s0, anchor: s0, hist_sen: vec![0; BINS], hist_ord: vec![0; BINS], n_sen: 0, n_ord: 0,
                  today_by_recv: HashMap::new(), cap: None, recent: vec![s0], days: vec![], days_read: 0, days_skipped: 0 }
    }

    /// everything the reading remembers, for a snapshot (maps in key order, so the bytes are the same for the same state)
    pub fn encode(&self, w: &mut crate::store::Wr) {
        w.u64(self.rp.std_fee_pm); w.u64(self.rp.cap_bp); w.u64(self.rp.min_obs);
        w.u64(self.s); w.u64(self.anchor);
        for h in [&self.hist_sen, &self.hist_ord] { w.u64(h.len() as u64); for x in h.iter() { w.u128(*x); } }
        w.u64(self.n_sen); w.u64(self.n_ord);
        let mut t: Vec<_> = self.today_by_recv.iter().collect(); t.sort();
        w.u64(t.len() as u64); for (k, v) in t { w.u64(*k); w.u128(*v); }
        match self.cap { Some(c) => { w.u8(1); w.u128(c); } None => w.u8(0) }
        w.u64(self.recent.len() as u64); for x in &self.recent { w.u64(*x); }
        w.u64(self.days.len() as u64); for x in &self.days { w.u64(*x); }
        w.u64(self.days_read); w.u64(self.days_skipped);
    }
    pub fn decode(r: &mut crate::store::Rd, rp: &ReadParams) -> anyhow::Result<Reading> {
        if (r.u64()?, r.u64()?, r.u64()?) != (rp.std_fee_pm, rp.cap_bp, rp.min_obs) { anyhow::bail!("the snapshot was made with other reading parameters"); }
        let (s, anchor) = (r.u64()?, r.u64()?);
        let mut hists = vec![];
        for _ in 0..2 {
            let n = r.count(16)?;
            if n != BINS { anyhow::bail!("wrong number of histogram bins"); }
            hists.push((0..n).map(|_| r.u128()).collect::<anyhow::Result<Vec<_>>>()?);
        }
        let hist_ord = hists.pop().unwrap(); let hist_sen = hists.pop().unwrap();
        let (n_sen, n_ord) = (r.u64()?, r.u64()?);
        let n = r.count(24)?;
        let mut today_by_recv = HashMap::new();
        for _ in 0..n { let k = r.u64()?; today_by_recv.insert(k, r.u128()?); }
        let cap = match r.u8()? { 0 => None, 1 => Some(r.u128()?), _ => anyhow::bail!("bad cap flag") };
        let n = r.count(8)?; let recent = (0..n).map(|_| r.u64()).collect::<anyhow::Result<Vec<_>>>()?;
        let n = r.count(8)?; let days = (0..n).map(|_| r.u64()).collect::<anyhow::Result<Vec<_>>>()?;
        let (days_read, days_skipped) = (r.u64()?, r.u64()?);
        Ok(Reading { rp: rp.clone(), s, anchor, hist_sen, hist_ord, n_sen, n_ord, today_by_recv, cap, recent, days, days_read, days_skipped })
    }
    /// n if `pay` is exactly n sixths of the S of one of the last blocks
    fn sixths(&self, pay: u64) -> Option<u64> {
        for s in self.recent.iter().rev() {
            if *s > 0 && (pay as u128 * 6) % *s as u128 == 0 { let n = (pay as u128 * 6 / *s as u128) as u64; if n >= 1 { return Some(n); } }
        }
        None
    }
    pub fn observe(&mut self, o: &Observed) {
        if o.c.amt == 0 || o.fee as u128 * 1000 < o.pay as u128 * self.rp.std_fee_pm as u128 { return; }
        let mut w = weight(&o.c) as u128;
        if w == 0 { return; }
        match self.sixths(o.pay) {
            Some(n) => {
                if let Some(cap) = self.cap {
                    let used = self.today_by_recv.entry(o.to).or_insert(0);
                    w = w.min(cap.saturating_sub(*used));
                    *used += w;
                    if w == 0 { return; }
                }
                self.hist_sen[bin_of(n)] += w; self.n_sen += 1;
            }
            None => { self.hist_ord[bin_of(o.pay)] += w; self.n_ord += 1; }
        }
    }
    /// called after every block with the S that block used
    pub fn block_done(&mut self, s_used: u64) {
        self.recent.push(s_used);
        if self.recent.len() > RECENT_S { self.recent.remove(0); }
    }
    /// today's reading (S from the middle 20% on each side), if both sides have enough payments
    pub fn day_reading(&self) -> Option<u64> {
        if self.n_sen < self.rp.min_obs || self.n_ord < self.rp.min_obs { return None; }
        let (qs, qo) = (middle(&self.hist_sen)?, middle(&self.hist_ord)?);
        let (vs, vo) = (value_at(qs), value_at(qo));
        if vs == 0 { return None; }
        Some((6 * vo / vs).min(u64::MAX as u128) as u64)
    }
    /// the Fibonacci-weighted mean of the day readings
    pub fn window(&self) -> Option<u64> {
        if self.days.is_empty() { return None; }
        let (mut num, mut den, mut k) = (0u128, 0u128, 0usize);
        'o: for (g, n) in GROUPS.iter().enumerate() {
            for _ in 0..*n {
                if k >= self.days.len() { break 'o; }
                let r = self.days[self.days.len() - 1 - k] as u128;
                let w = 32u128 >> g;
                num += r * w; den += w; k += 1;
            }
        }
        Some((num / den) as u64)
    }
    /// close the day: take today's reading, move the window, the anchor and S; start the next day
    pub fn end_day(&mut self) {
        let sen_total: u128 = self.hist_sen.iter().sum();
        if let Some(d) = self.day_reading() {
            let p = self.window().unwrap_or(self.s);   // before any reading, the genesis S
            let r = d.clamp(p - p / 10, p + p / 10);
            self.days.push(r);
            if self.days.len() > WINDOW_DAYS { self.days.remove(0); }
            let cand = self.window().unwrap();
            self.anchor = cand.clamp(self.anchor - self.anchor * ANCHOR_DOWN / 10_000, self.anchor + self.anchor * ANCHOR_UP / 10_000).max(1);
            let s = cand.clamp(self.anchor - self.anchor / 10, self.anchor + self.anchor / 10);
            self.s = (s - s % 6).max(6);
            self.days_read += 1;
        } else { self.days_skipped += 1; }
        self.hist_sen.iter_mut().for_each(|x| *x = 0); self.hist_ord.iter_mut().for_each(|x| *x = 0);
        self.n_sen = 0; self.n_ord = 0; self.today_by_recv.clear();
        self.cap = if self.rp.cap_bp > 0 && sen_total > 0 { Some(sen_total * self.rp.cap_bp as u128 / 10_000) } else { None };
    }
    pub fn is_day_end(height: u64) -> bool { (height + 1) % BPD == 0 }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn pay(pay: u64, fee_pm: u64, to: u64) -> Observed {
        Observed { c: Counted { amt: pay, age: 30 }, pay, fee: (pay * fee_pm + 999) / 1000, to }
    }
    fn rp() -> ReadParams { ReadParams { std_fee_pm: 10, cap_bp: 0, min_obs: 5 } }
    /// feed one day of honest payments: shops price goods at `price_sixths` sixths of a Sen (ordinary payments are the
    /// same goods valued in base units at `true_s` per Sen)
    fn feed_day(r: &mut Reading, true_s: u64, goods_sen6: &[u64], n: usize) {
        for k in 0..n {
            let g = goods_sen6[k % goods_sen6.len()];
            let s_now = r.s;
            // Sen-priced: g sixths of the Sen now in force
            r.observe(&pay(g * (s_now / 6), 10, k as u64));
            // ordinary: the same goods in base units at the true Sen value (not a multiple of any recent S/6)
            r.observe(&pay(g * true_s / 6 + 1 + (k as u64 % 7), 10, 1000 + k as u64));
        }
    }
    #[test]
    fn table_is_log_spaced() {
        let t = table();
        assert_eq!(t[0], FRAC);
        let octave = t[16] as f64 / FRAC as f64; assert!((octave - 2.0).abs() < 1e-6, "{octave}");
        let top = t[1024] as f64 / FRAC as f64; assert!((top / 2f64.powi(64) - 1.0).abs() < 1e-5);
        assert_eq!(bin_of(1), 0); assert_eq!(bin_of(2), 16); assert_eq!(bin_of(1 << 20), 320);
    }
    #[test]
    fn reads_the_ratio() {
        let mut r = Reading::new(rp(), 10_000);
        r.recent = vec![r.s];
        feed_day(&mut r, 20_000, &[12, 6, 18, 12, 9, 15], 60);
        let d = r.day_reading().unwrap() as f64;
        assert!((d / 20_000.0 - 1.0).abs() < 0.06, "reading {d}");
    }
    #[test]
    fn follows_slowly_within_the_band() {
        let mut r = Reading::new(rp(), 10_000);
        let mut last = r.anchor;
        for day in 0..90 {
            r.recent = vec![r.s];
            feed_day(&mut r, 20_000, &[12, 6, 18, 12, 9, 15], 60);
            r.end_day();
            assert!(r.anchor as f64 <= last as f64 * 1.0076, "day {day}: anchor {} -> {}", last, r.anchor);
            assert!((r.s as f64) <= r.anchor as f64 * 1.1 + 6.0 && (r.s as f64) >= r.anchor as f64 * 0.9 - 6.0, "band");
            last = r.anchor;
        }
        assert!((r.s as f64 / 20_000.0 - 1.0).abs() < 0.06, "S {}", r.s);
    }
    #[test]
    fn standard_fee_and_cap() {
        let mut r = Reading::new(ReadParams { std_fee_pm: 10, cap_bp: 100, min_obs: 1 }, 600);
        r.recent = vec![600];
        // a payment under the standard fee does not count
        r.observe(&pay(6000, 5, 1));
        assert_eq!(r.n_sen + r.n_ord, 0);
        r.observe(&pay(6000, 10, 1)); r.observe(&pay(7001, 10, 2));
        assert_eq!((r.n_sen, r.n_ord), (1, 1));
        r.end_day();
        // next day: one receiver may bring at most 1% of the day's Sen-priced weight
        let cap = r.cap.unwrap();
        for _ in 0..50 { r.observe(&pay(6000, 10, 1)); }
        assert!(r.today_by_recv[&1] <= cap, "{} > {}", r.today_by_recv[&1], cap);
    }
    /// the strongest possible pusher (all weight, always the same direction): how far S can go in 7 and 30 days
    #[test]
    fn hard_bound_of_a_maximal_push() {
        let mut r = Reading::new(rp(), 10_002);
        let s0 = r.s as f64;
        let (mut w7, mut w30) = (0.0, 0.0);
        for day in 1..=30 {
            r.recent = vec![r.s];
            let u = r.s / 6;
            for k in 0..50 { r.observe(&pay(u, 10, 5000 + k)); r.observe(&pay(40_000 + k, 10, 9000 + k)); }
            r.end_day();
            if day == 7 { w7 = r.s as f64 / s0 - 1.0; }
            if day == 30 { w30 = r.s as f64 / s0 - 1.0; }
        }
        println!("maximal push: S moved +{:.1}% in 7 days, +{:.1}% in 30 days", w7 * 100.0, w30 * 100.0);
        assert!(w7 <= 1.1 * 1.0075f64.powi(7) - 1.0 + 0.01, "{w7}");
    }
    /// a pusher with more weight than all honest payments moves S only within the band
    #[test]
    fn push_is_bounded() {
        let mut r = Reading::new(rp(), 10_002);
        for _ in 0..7 {
            r.recent = vec![r.s];
            let u = r.s / 6;
            for k in 0..400 { r.observe(&pay(u, 10, 5000 + k)); }                 // attacker: price of 1/6 Sen, ~62% of the weight
            for k in 0..20 { r.observe(&pay(12 * u, 10, k)); r.observe(&pay(20_000 + k, 10, 9000 + k)); }   // honest
            r.end_day();
        }
        println!("pushed S {} from 10002 in 7 days", r.s);
        assert!(r.s as f64 <= 10_002.0 * 1.1 * 1.0075f64.powi(7) + 6.0, "S {}", r.s);
        assert!(r.s > 10_002, "the attacker did move S: {}", r.s);
    }
}
