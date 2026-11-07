//! Official exchange rates (stage 6). A rate is not announced by anyone: it is worked out from the trades that really finished.
//! Each chain keeps a tape of its filled orders (an order spent by its claim); the rate for selling this chain's metal for another's is the
//! volume-weighted median price of the newest fills, and it exists only when enough different people traded (so one account cannot make it).
//! The tape is a view over the blocks (not part of the consensus state); every node that replays the blocks gets the same one.
use crate::F;
use plonky2::field::types::{Field, PrimeField64};
use anyhow::{anyhow, Result};
use serde_json::{json, Value};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fill { pub height: u64, pub sell: u64, pub want_chain: u8, pub want_amt: u64, pub maker: [F; 4], pub taker: [F; 4] }
/// how many fills a tape keeps, how many the rate looks at, and how old (in blocks) a fill may be
pub const TAPE: usize = 256;
pub const LOOK: usize = 32;
pub const MAX_AGE: u64 = 20_000;
/// fewest fills, makers and takers (distinct) for a rate to exist
pub const MIN_FILLS: usize = 3;
pub const MIN_PARTIES: usize = 2;
/// prices are `asked units per 1e9 sold units`
pub const SCALE: u128 = 1_000_000_000;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rate { pub price: u128, pub fills: usize, pub volume: u128, pub last: u64 }

pub fn price_of(f: &Fill) -> u128 { f.want_amt as u128 * SCALE / f.sell.max(1) as u128 }

/// the official rate for selling this chain's metal for `want_chain`'s at height `now`, if there is one
pub fn official(tape: &[Fill], want_chain: u8, now: u64) -> Option<Rate> {
    let mut v: Vec<&Fill> = tape.iter().filter(|f| f.want_chain == want_chain && now.saturating_sub(f.height) <= MAX_AGE).collect();
    if v.len() > LOOK { v = v.split_off(v.len() - LOOK); }
    let distinct = |g: &dyn Fn(&Fill) -> [F; 4]| { let mut a: Vec<[u64; 4]> = v.iter().map(|f| g(f).map(|x| x.to_canonical_u64())).collect(); a.sort(); a.dedup(); a.len() };
    if v.len() < MIN_FILLS || distinct(&|f| f.maker) < MIN_PARTIES || distinct(&|f| f.taker) < MIN_PARTIES { return None; }
    // the median by volume: sort by price, walk until half of the sold volume is passed
    let mut by: Vec<(u128, u128)> = v.iter().map(|f| (price_of(f), f.sell as u128)).collect();
    by.sort();
    let total: u128 = by.iter().map(|x| x.1).sum();
    let (mut acc, mut price) = (0u128, by[0].0);
    for (p, w) in &by { acc += w; price = *p; if acc * 2 >= total { break; } }
    Some(Rate { price, fills: v.len(), volume: total, last: v.iter().map(|f| f.height).max().unwrap_or(0) })
}

/// two chains' rates for one pair into one: X->Y sells quote Y per X; Y->X sells quote X per Y, which is 1/that in Y per X.
/// Both sides give their geometric mean (they should agree: a gap is an arbitrage someone will close).
pub fn pair(xy: Option<u128>, yx: Option<u128>) -> Option<(f64, f64)> {
    let a = xy.map(|p| p as f64 / SCALE as f64);
    let b = yx.filter(|p| *p > 0).map(|p| SCALE as f64 / p as f64);
    match (a, b) {
        (Some(a), Some(b)) => Some(((a * b).sqrt(), (a - b).abs() / ((a + b) / 2.0))),
        (Some(a), None) | (None, Some(a)) => Some((a, 0.0)),
        _ => None,
    }
}

/// `market rates <api of Yen> <api of Ken> <api of Jen>`: the official rates, from the three chains' tapes
pub fn market_main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    match a.get(2).map(String::as_str) {
        Some("rates") => {
            let apis: Vec<String> = a[3..].to_vec();
            if apis.len() != 3 { return Err(anyhow!("usage: market rates <api of chain 1> <api of chain 2> <api of chain 3>")); }
            let names = ["Yen", "Ken", "Jen"];
            let rates: Vec<Value> = apis.iter().map(|x| crate::tx::http_get(x, "/api/rate")).collect::<Result<_>>()?;
            let get = |from: usize, to: usize| rates[from]["rates"].as_array().into_iter().flatten().find(|r| r["want_chain"].as_u64() == Some(to as u64 + 1)).and_then(|r| r["price"].as_str()?.parse::<u128>().ok());
            for (x, y) in [(0, 1), (0, 2), (1, 2)] {
                match pair(get(x, y), get(y, x)) {
                    Some((r, gap)) => println!("1 {} = {:.6} {}   (gap between the two directions {:.2}%)", names[x], r, names[y], gap * 100.0),
                    None => println!("{} / {}: no official rate yet (too few different traders)", names[x], names[y]),
                }
            }
            Ok(())
        }
        _ => { println!("market rates <api1> <api2> <api3>"); Ok(()) }
    }
}
pub fn fills_json(tape: &[Fill], now: u64) -> Value {
    let rates: Vec<Value> = (1..=3u8).filter_map(|w| official(tape, w, now).map(|r| json!({"want_chain": w, "price": r.price.to_string(), "fills": r.fills, "volume": r.volume.to_string(), "last_height": r.last}))).collect();
    json!({"rates": rates, "scale": SCALE.to_string(), "tape_len": tape.len()})
}

#[cfg(test)]
mod tests {
    use super::*;
    fn f(h: u64, sell: u64, want: u64, m: u64, t: u64) -> Fill { Fill { height: h, sell, want_chain: 2, want_amt: want, maker: [F::from_canonical_u64(m); 4], taker: [F::from_canonical_u64(t); 4] } }
    #[test]
    fn a_rate_needs_enough_different_traders_and_follows_the_volume_median() {
        // one maker and one taker trading with themselves, however often, make no rate
        let wash: Vec<Fill> = (0..10).map(|i| f(i, 100, 50, 1, 2)).collect();
        assert!(official(&wash, 2, 20).is_none());
        // three fills from two makers and two takers do
        let mut t = vec![f(1, 100, 50, 1, 5), f(2, 100, 52, 2, 5), f(3, 100, 54, 2, 6)];
        let r = official(&t, 2, 10).unwrap();
        assert_eq!(r.price, 520_000_000, "the middle price");
        // a big fill moves the volume median, a tiny one at a crazy price does not
        t.push(f(4, 1, 100, 3, 7));
        assert_eq!(official(&t, 2, 10).unwrap().price, 520_000_000);
        t.push(f(5, 1000, 600, 3, 7));
        assert_eq!(official(&t, 2, 10).unwrap().price, 600_000_000);
        // another chain's fills and old fills do not count
        assert!(official(&t, 3, 10).is_none());
        assert!(official(&t, 2, 10 + MAX_AGE + 10).is_none());
        // the two directions of a pair agree up to a gap
        let (r, gap) = pair(Some(520_000_000), Some(1_900_000_000)).unwrap();
        assert!(r > 0.5 && r < 0.53, "{r}");
        assert!(gap > 0.0 && gap < 0.1);
    }
}
