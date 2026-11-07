// Schnorr signatures over the curve y^2 = x^3 + 2x^2 + 263z*x defined over GF(p^5), p = Goldilocks,
// GF(p^5) = GF(p)[z]/(z^5 - 3) (the EcGFp5 curve equation of T. Pornin).
//
// OPTIMISED VERSION. Same scheme as p2sig (e = 128 bits of Poseidon(R, A, msg), s = r + e*k as a
// plain 385-bit integer, check s*G == R + e*A), but the circuit is built differently:
//
//  * In the circuit, points use short Weierstrass coordinates X = x + 2/3 (y^2 = X^3 + aX + b).
//    The addition formulas then have no constant term, so an all-zero row satisfies them and
//    unused gate slots need no special handling.
//  * A custom gate, DblAddGate, computes acc' = 2*acc + Q in ONE operation ((acc+Q)+acc, two
//    slopes, no explicit doubling). Two operations fit in one Plonky2 row (60 routed wires +
//    30 advice wires).
//  * One loop over the 385 bits does s*G and e*A together (Shamir's trick): each bit adds one of
//    four points {H, H+G, H-A, H+G-A}, picked with 1-3 arithmetic ops per coordinate. H is an
//    offset point so the accumulator never meets the identity; the offsets are known constants
//    and are removed at the end with a single extra DblAdd.
//  * No table of 385 constant points (constants cost Plonky2 rows).
//
// Native signing code keeps plain long-Weierstrass coordinates and converts when hashing.
use anyhow::Result;
use num_bigint::BigUint;
use plonky2::field::extension::quintic::QuinticExtension;
use plonky2::field::extension::Extendable;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::gates::gate::Gate;
use plonky2::gates::util::StridedConstraintConsumer;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator, WitnessGeneratorRef};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::plonk::config::Hasher;
use plonky2::plonk::vars::{EvaluationTargets, EvaluationVars, EvaluationVarsBase};
use plonky2::util::serialization::{Buffer, IoResult};

pub type F = GoldilocksField;
pub type E = QuinticExtension<F>;
pub const D: usize = 2;
/// EcGFp5 prime group order n (T. Pornin, ecgfp5 README): the curve has 2n points
pub const N_ORDER: &str = "1067993516717146951041484916571792702745057740581727230159139685185762082554198619328292418486241";
pub fn n_order() -> BigUint { BigUint::parse_bytes(N_ORDER.as_bytes(), 10).unwrap() }
/// s is reduced mod n, so it has at most 319 bits
pub const S_BITS: usize = 319;
pub const E_BITS: usize = 128;

pub fn e(c: [u64; 5]) -> E { QuinticExtension(c.map(F::from_canonical_u64)) }
pub fn a2() -> E { e([2, 0, 0, 0, 0]) }
pub fn a4() -> E { e([0, 263, 0, 0, 0]) }
fn third() -> E { e([3, 0, 0, 0, 0]).inverse() }
/// shift between long (x) and short (X) Weierstrass coordinates: X = x + a2/3
pub fn shift() -> E { a2() * third() }
/// short Weierstrass a, b
pub fn sw_a() -> E { a4() - a2() * a2() * third() }
pub fn sw_b() -> E { e([2, 0, 0, 0, 0]) * a2() * a2() * a2() * third() * third() * third() - a2() * a4() * third() }

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct P { pub x: E, pub y: E }
pub fn add(p: P, q: P) -> P {
    let l = (q.y - p.y) * (q.x - p.x).inverse();
    let x = l * l - a2() - p.x - q.x;
    P { x, y: l * (p.x - x) - p.y }
}
pub fn dbl(p: P) -> P {
    let three = e([3, 0, 0, 0, 0]);
    let two = e([2, 0, 0, 0, 0]);
    let l = (three * p.x * p.x + two * a2() * p.x + a4()) * (two * p.y).inverse();
    let x = l * l - a2() - p.x - p.x;
    P { x, y: l * (p.x - x) - p.y }
}
pub fn neg(p: P) -> P { P { x: p.x, y: -p.y } }
pub fn on_curve(p: P) -> bool { p.y * p.y == p.x * p.x * p.x + a2() * p.x * p.x + a4() * p.x }
/// short Weierstrass coordinates (X, y) used inside the circuit and in all hashes
pub fn sw(p: P) -> (E, E) { (p.x + shift(), p.y) }
pub fn lift(x: E) -> Option<P> {
    let rhs = x * x * x + a2() * x * x + a4() * x;
    sqrt(rhs).map(|y| P { x, y })
}
/// Tonelli-Shanks in GF(p^5): q - 1 = 2^32 * t with t odd
pub fn sqrt(a: E) -> Option<E> {
    if a == E::ZERO { return Some(a); }
    let q = E::order();
    let one = BigUint::from(1u32);
    let qm1 = &q - &one;
    if a.exp_biguint(&(&qm1 >> 1)) != E::ONE { return None; }
    let s = 32u32;
    let t = &qm1 >> s;
    let mut zc = 2u64;
    let z = loop { let c = e([zc, 1, 0, 0, 0]); if c.exp_biguint(&(&qm1 >> 1)) != E::ONE { break c; } zc += 1; };
    let mut m = s;
    let mut c = z.exp_biguint(&t);
    let mut tt = a.exp_biguint(&t);
    let mut r = a.exp_biguint(&((&t + &one) >> 1));
    while tt != E::ONE {
        let mut i = 0; let mut t2 = tt;
        while t2 != E::ONE { t2 = t2 * t2; i += 1; }
        let mut b = c; for _ in 0..(m - i - 1) { b = b * b; }
        m = i; c = b * b; tt = tt * c; r = r * b;
    }
    Some(r)
}
/// k*P, k > 0 (MSB-first double-and-add)
pub fn mul(p: P, k: &BigUint) -> P {
    let n = k.bits();
    assert!(n > 0);
    let mut acc = p;
    for i in (0..n - 1).rev() { acc = dbl(acc); if k.bit(i) { acc = add(acc, p); } }
    acc
}
pub fn pow2(mut p: P, n: usize) -> P { for _ in 0..n { p = dbl(p); } p }

pub struct Params {
    pub g: P, pub g1: P,      // G = 2*G1 (generator), G1 its "half"
    pub h0: P,                // accumulator start
    pub h: P, pub h1: P,      // offset H = 2*H1 added every bit
    pub hg: P,                // H + G
    pub cp: P,                // C' = 2^(n-1) H0 + (2^n - 1) H1, so that the loop ends at 2C' + sG - eA
}
pub fn params() -> Params {
    let g1 = lift(e([12883135586176881569, 4356519642755055268, 5248930565894896907, 2165973894480315022, 2448410071095648785])).expect("G");
    let g = dbl(g1);
    let mut hs = vec![];
    let mut t = 5u64;
    while hs.len() < 2 { if let Some(p) = lift(e([t, 1, 7, 0, t * 3])) { hs.push(p); } t += 1; }
    let (h1, h0) = (hs[0], hs[1]);
    let h = dbl(h1);
    let hg = add(h, g);
    let ones = (BigUint::from(1u32) << S_BITS) - BigUint::from(1u32);
    let cp = add(pow2(h0, S_BITS - 1), mul(h1, &ones));
    Params { g, g1, h0, h, h1, hg, cp }
}
/// k*G
pub fn mul_g(prm: &Params, k: &BigUint) -> P { mul(prm.g, k) }

/// native model of the circuit's loop (used as a self-check before proving)
pub fn native_check(prm: &Params, a: P, r: P, s: &BigUint, e: &BigUint) -> bool {
    let t2 = add(dbl(prm.h1), neg(a));
    let t3 = add(dbl(prm.g1), t2);
    let mut acc = prm.h0;
    for i in (0..S_BITS).rev() {
        let q = match (s.bit(i as u64), e.bit(i as u64)) { (false, false) => prm.h, (true, false) => prm.hg, (false, true) => t2, (true, true) => t3 };
        acc = add(add(acc, q), acc);
    }
    acc == add(add(prm.cp, r), prm.cp)
}

fn swf(p: P) -> Vec<F> { let (x, y) = sw(p); let mut v = x.0.to_vec(); v.extend(y.0); v }
pub fn challenge(r: P, a: P, msg: [F; 4]) -> BigUint {
    let mut v = swf(r); v.extend(swf(a)); v.extend(msg);
    let hsh = PoseidonHash::hash_no_pad(&v);
    BigUint::from(hsh.elements[0].to_canonical_u64()) + (BigUint::from(hsh.elements[1].to_canonical_u64()) << 64)
}
pub fn pk_hash(a: P) -> [F; 4] { PoseidonHash::hash_no_pad(&swf(a)).elements }

// ---------------------------------------------------------------- the DblAdd gate
// One op: inputs P = (x, y), Q = (xq, yq) (short Weierstrass), output 2P + Q = (x4, y4).
//   l1 (xq - x) = yq - y                 slope P -> Q
//   xr = l1^2 - x - xq                   R = P + Q (x only)
//   (l1 + l2)(x - xr) = 2y               l2 = slope R -> P, without materialising yR
//   x4 = l2^2 - xr - x
//   y4 = l2 (x - x4) - y
// 25 constraints of degree 2 per op. An all-zero op satisfies them.
pub const OPS: usize = 2;
const ROUTED: usize = 30;        // x, y, xq, yq, x4, y4 per op
const ADV: usize = OPS * ROUTED; // advice wires l1, l2, xr, w1, w2 per op start here
const ADV_PER_OP: usize = 25;
fn w_x(i: usize) -> usize { ROUTED * i }
fn w_y(i: usize) -> usize { ROUTED * i + 5 }
fn w_xq(i: usize) -> usize { ROUTED * i + 10 }
fn w_yq(i: usize) -> usize { ROUTED * i + 15 }
fn w_x4(i: usize) -> usize { ROUTED * i + 20 }
fn w_y4(i: usize) -> usize { ROUTED * i + 25 }
fn w_l1(i: usize) -> usize { ADV + ADV_PER_OP * i }
fn w_l2(i: usize) -> usize { ADV + ADV_PER_OP * i + 5 }
fn w_xr(i: usize) -> usize { ADV + ADV_PER_OP * i + 10 }
fn w_w1(i: usize) -> usize { ADV + ADV_PER_OP * i + 15 } // 1 / (xq - x)
fn w_w2(i: usize) -> usize { ADV + ADV_PER_OP * i + 20 } // 1 / (x - xr)

fn m5<T: Field>(a: [T; 5], b: [T; 5]) -> [T; 5] {
    let w = T::from_canonical_u64(3);
    core::array::from_fn(|k| {
        let mut acc = T::ZERO;
        for i in 0..5 { let j = (k + 5 - i) % 5; let t = a[i] * b[j]; acc += if i + j == k { t } else { w * t }; }
        acc
    })
}
fn s5<T: Field>(a: [T; 5], b: [T; 5]) -> [T; 5] { core::array::from_fn(|i| a[i] - b[i]) }
fn a5<T: Field>(a: [T; 5], b: [T; 5]) -> [T; 5] { core::array::from_fn(|i| a[i] + b[i]) }
fn constraints<T: Field>(get: impl Fn(usize) -> T, i: usize, out: &mut Vec<T>) {
    let g5 = |s: usize| -> [T; 5] { core::array::from_fn(|k| get(s + k)) };
    let (x, y, xq, yq, x4, y4) = (g5(w_x(i)), g5(w_y(i)), g5(w_xq(i)), g5(w_yq(i)), g5(w_x4(i)), g5(w_y4(i)));
    let (l1, l2, xr) = (g5(w_l1(i)), g5(w_l2(i)), g5(w_xr(i)));
    let (w1, w2) = (g5(w_w1(i)), g5(w_w2(i)));
    let one: [T; 5] = core::array::from_fn(|k| if k == 0 { T::ONE } else { T::ZERO });
    out.extend(s5(m5(l1, s5(xq, x)), s5(yq, y)));
    out.extend(s5(xr, s5(s5(m5(l1, l1), x), xq)));
    out.extend(s5(m5(a5(l1, l2), s5(x, xr)), a5(y, y)));
    out.extend(s5(x4, s5(s5(m5(l2, l2), xr), x)));
    out.extend(s5(y4, s5(m5(l2, s5(x, x4)), y)));
    // no exceptional case: xq != x (P != +-Q) and x != xr (P+Q != +-P)
    out.extend(s5(m5(w1, s5(xq, x)), one));
    out.extend(s5(m5(w2, s5(x, xr)), one));
}

type ETg = [ExtensionTarget<D>; 5];
fn m5c(b: &mut CircuitBuilder<F, D>, a: ETg, c: ETg) -> ETg {
    let w = F::from_canonical_u64(3);
    core::array::from_fn(|k| {
        let mut acc = b.zero_extension();
        for i in 0..5 {
            let j = (k + 5 - i) % 5;
            acc = if i + j == k { b.mul_add_extension(a[i], c[j], acc) } else { b.arithmetic_extension(w, F::ONE, a[i], c[j], acc) };
        }
        acc
    })
}
fn s5c(b: &mut CircuitBuilder<F, D>, a: ETg, c: ETg) -> ETg { core::array::from_fn(|i| b.sub_extension(a[i], c[i])) }
fn a5c(b: &mut CircuitBuilder<F, D>, a: ETg, c: ETg) -> ETg { core::array::from_fn(|i| b.add_extension(a[i], c[i])) }

#[derive(Debug, Clone)]
pub struct DblAddGate;
impl Gate<F, D> for DblAddGate {
    fn id(&self) -> String { "EcGFp5DblAddGate".into() }
    fn serialize(&self, _dst: &mut Vec<u8>, _c: &CommonCircuitData<F, D>) -> IoResult<()> { Ok(()) }
    fn deserialize(_src: &mut Buffer, _c: &CommonCircuitData<F, D>) -> IoResult<Self> { Ok(DblAddGate) }
    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<<F as Extendable<D>>::Extension> {
        let mut out = Vec::with_capacity(35 * OPS);
        for i in 0..OPS { constraints(|k| vars.local_wires[k], i, &mut out); }
        out
    }
    fn eval_unfiltered_base_one(&self, vars: EvaluationVarsBase<F>, mut yc: StridedConstraintConsumer<F>) {
        let mut out = Vec::with_capacity(35 * OPS);
        for i in 0..OPS { constraints(|k| vars.local_wires[k], i, &mut out); }
        yc.many(out);
    }
    fn eval_unfiltered_circuit(&self, b: &mut CircuitBuilder<F, D>, vars: EvaluationTargets<D>) -> Vec<ExtensionTarget<D>> {
        let mut out = Vec::with_capacity(35 * OPS);
        for i in 0..OPS {
            let g5 = |s: usize| -> ETg { core::array::from_fn(|k| vars.local_wires[s + k]) };
            let (x, y, xq, yq, x4, y4) = (g5(w_x(i)), g5(w_y(i)), g5(w_xq(i)), g5(w_yq(i)), g5(w_x4(i)), g5(w_y4(i)));
            let (l1, l2, xr) = (g5(w_l1(i)), g5(w_l2(i)), g5(w_xr(i)));
            let (w1, w2) = (g5(w_w1(i)), g5(w_w2(i)));
            // C1
            let d = s5c(b, xq, x); let m = m5c(b, l1, d); let r = s5c(b, yq, y); out.extend(s5c(b, m, r));
            // C2
            let m = m5c(b, l1, l1); let t = s5c(b, m, x); let t = s5c(b, t, xq); out.extend(s5c(b, xr, t));
            // C3
            let s = a5c(b, l1, l2); let d = s5c(b, x, xr); let m = m5c(b, s, d); let yy = a5c(b, y, y); out.extend(s5c(b, m, yy));
            // C4
            let m = m5c(b, l2, l2); let t = s5c(b, m, xr); let t = s5c(b, t, x); out.extend(s5c(b, x4, t));
            // C5
            let d = s5c(b, x, x4); let m = m5c(b, l2, d); let t = s5c(b, m, y); out.extend(s5c(b, y4, t));
            // C6, C7
            let one = b.one_extension(); let zero = b.zero_extension();
            let one5: ETg = core::array::from_fn(|k| if k == 0 { one } else { zero });
            let d = s5c(b, xq, x); let m = m5c(b, w1, d); out.extend(s5c(b, m, one5));
            let d = s5c(b, x, xr); let m = m5c(b, w2, d); out.extend(s5c(b, m, one5));
        }
        out
    }
    fn generators(&self, row: usize, _c: &[F]) -> Vec<WitnessGeneratorRef<F, D>> {
        (0..OPS).map(|i| WitnessGeneratorRef::new(DblAddGen { row, i }.adapter())).collect()
    }
    fn num_wires(&self) -> usize { ADV + ADV_PER_OP * OPS }
    fn num_constants(&self) -> usize { 0 }
    fn degree(&self) -> usize { 2 }
    fn num_constraints(&self) -> usize { 35 * OPS }
}

#[derive(Debug, Clone, Default)]
struct DblAddGen { row: usize, i: usize }
impl SimpleGenerator<F, D> for DblAddGen {
    fn id(&self) -> String { "EcGFp5DblAddGen".into() }
    fn dependencies(&self) -> Vec<Target> {
        let i = self.i;
        [w_x(i), w_y(i), w_xq(i), w_yq(i)].iter().flat_map(|&s| (0..5).map(move |k| s + k)).map(|c| Target::wire(self.row, c)).collect()
    }
    fn run_once(&self, w: &PartitionWitness<F>, out: &mut GeneratedValues<F>) -> Result<()> {
        let g = |s: usize| -> E { QuinticExtension(core::array::from_fn(|k| w.get_target(Target::wire(self.row, s + k)))) };
        let i = self.i;
        let (x, y, xq, yq) = (g(w_x(i)), g(w_y(i)), g(w_xq(i)), g(w_yq(i)));
        let inv = |v: E| v.try_inverse().ok_or_else(|| anyhow::anyhow!("DblAdd exceptional case (point equality)"));
        let w1 = inv(xq - x)?;
        let l1 = (yq - y) * w1;
        let xr = l1 * l1 - x - xq;
        let w2 = inv(x - xr)?;
        let l2 = (y + y) * w2 - l1;
        let x4 = l2 * l2 - xr - x;
        let y4 = l2 * (x - x4) - y;
        for (s, v) in [(w_l1(i), l1), (w_l2(i), l2), (w_xr(i), xr), (w_w1(i), w1), (w_w2(i), w2), (w_x4(i), x4), (w_y4(i), y4)] {
            for k in 0..5 { out.set_target(Target::wire(self.row, s + k), v.0[k])?; }
        }
        Ok(())
    }
    fn serialize(&self, _dst: &mut Vec<u8>, _c: &CommonCircuitData<F, D>) -> IoResult<()> { Ok(()) }
    fn deserialize(_src: &mut Buffer, _c: &CommonCircuitData<F, D>) -> IoResult<Self> { unimplemented!() }
}

// ---------------------------------------------------------------- circuit helpers
pub type ET = [Target; 5];
#[derive(Clone, Copy, Debug)]
pub struct PT { pub x: ET, pub y: ET }

thread_local! { static DBLADD_OPS: core::cell::Cell<usize> = const { core::cell::Cell::new(0) }; }
/// call before building a circuit that uses DblAdd
pub fn dbladd_reset() { DBLADD_OPS.with(|c| c.set(0)); }
/// an all-zero gate op does not satisfy the non-exceptional checks, so fill a half-used last row
/// with a real (dummy) operation
pub fn dbladd_pad(b: &mut CircuitBuilder<F, D>, prm: &Params) {
    if DBLADD_OPS.with(|c| c.get()) % OPS != 0 { let g = pt_const(b, prm.g1); let h = pt_const(b, prm.h1); dbl_add(b, g, h); }
}
/// 2P + Q in one gate op
pub fn dbl_add(b: &mut CircuitBuilder<F, D>, p: PT, q: PT) -> PT {
    DBLADD_OPS.with(|c| c.set(c.get() + 1));
    let (row, i) = b.find_slot(DblAddGate, &[], &[]);
    for k in 0..5 {
        b.connect(p.x[k], Target::wire(row, w_x(i) + k));
        b.connect(p.y[k], Target::wire(row, w_y(i) + k));
        b.connect(q.x[k], Target::wire(row, w_xq(i) + k));
        b.connect(q.y[k], Target::wire(row, w_yq(i) + k));
    }
    PT { x: core::array::from_fn(|k| Target::wire(row, w_x4(i) + k)), y: core::array::from_fn(|k| Target::wire(row, w_y4(i) + k)) }
}
pub fn ec_const(b: &mut CircuitBuilder<F, D>, c: E) -> ET { c.0.map(|v| b.constant(v)) }
/// constant point, in short Weierstrass coordinates
pub fn pt_const(b: &mut CircuitBuilder<F, D>, p: P) -> PT { let (x, y) = sw(p); PT { x: ec_const(b, x), y: ec_const(b, y) } }
pub fn ec_mul(b: &mut CircuitBuilder<F, D>, x: ET, y: ET) -> ET {
    let w = F::from_canonical_u64(3);
    core::array::from_fn(|k| {
        let mut acc = b.zero();
        for i in 0..5 {
            let j = (k + 5 - i) % 5;
            acc = if i + j == k { b.mul_add(x[i], y[j], acc) } else { b.arithmetic(w, F::ONE, x[i], y[j], acc) };
        }
        acc
    })
}
/// y^2 == X^3 + aX + b
pub fn assert_on_curve(b: &mut CircuitBuilder<F, D>, p: PT) {
    let y2 = ec_mul(b, p.y, p.y);
    let x2 = ec_mul(b, p.x, p.x);
    let x3 = ec_mul(b, x2, p.x);
    let ca = ec_const(b, sw_a());
    let ax = ec_mul(b, ca, p.x);
    let bb = sw_b();
    for k in 0..5 {
        let t = b.add(x3[k], ax[k]);
        let t = b.add_const(t, bb.0[k]);
        b.connect(t, y2[k]);
    }
}
/// 64-bit decomposition that must be the canonical one (value < p = 2^64 - 2^32 + 1):
/// not (high 32 bits all ones and low 32 bits non-zero)
pub fn split64_canonical(b: &mut CircuitBuilder<F, D>, x: Target) -> Vec<BoolTarget> {
    let bits = b.split_le(x, 64);
    let lo = b.le_sum(bits[..32].iter());
    let hi = b.le_sum(bits[32..].iter());
    let all_ones = b.constant(F::from_canonical_u64((1u64 << 32) - 1));
    let eq = b.is_equal(hi, all_ones);
    let m = b.mul(eq.target, lo);
    b.assert_zero(m);
    bits
}
/// s (little-endian bits) < n, scanning from the most significant bit
pub fn assert_less_than_n(b: &mut CircuitBuilder<F, D>, s: &[BoolTarget]) {
    let n = n_order();
    assert_eq!(n.bits() as usize, s.len());
    let mut lt = b.zero();
    let mut eq = b.one();
    for i in (0..s.len()).rev() {
        if n.bit(i as u64) {
            let not_s = b.not(s[i]);
            lt = b.mul_add(eq, not_s.target, lt); // n_i = 1, s_i = 0 while equal so far: s < n
            eq = b.mul(eq, s[i].target);
        } else {
            let not_s = b.not(s[i]);
            eq = b.mul(eq, not_s.target);           // n_i = 0, s_i = 1 while equal: s > n (eq drops, lt stays 0)
        }
    }
    let one = b.one();
    b.connect(lt, one);
}
pub struct SigT { pub a: PT, pub r: PT, pub s_bits: Vec<BoolTarget> }
pub fn add_virtual_pt(b: &mut CircuitBuilder<F, D>) -> PT { PT { x: core::array::from_fn(|_| b.add_virtual_target()), y: core::array::from_fn(|_| b.add_virtual_target()) } }
fn coords(p: &PT) -> [Target; 10] { core::array::from_fn(|c| if c < 5 { p.x[c] } else { p.y[c - 5] }) }
fn from_coords(c: [Target; 10]) -> PT { PT { x: core::array::from_fn(|k| c[k]), y: core::array::from_fn(|k| c[5 + k]) } }
fn pcoords(p: P) -> [F; 10] { let (x, y) = sw(p); core::array::from_fn(|c| if c < 5 { x.0[c] } else { y.0[c - 5] }) }

/// pk hash of A (binds the account leaf) and the signature check on msg (4 targets)
pub fn verify_sig(b: &mut CircuitBuilder<F, D>, prm: &Params, msg: [Target; 4]) -> (SigT, [Target; 4]) {
    let a = add_virtual_pt(b);
    let r = add_virtual_pt(b);
    let s_bits: Vec<BoolTarget> = (0..S_BITS).map(|_| b.add_virtual_bool_target_safe()).collect();
    assert_on_curve(b, a);
    assert_on_curve(b, r);
    let mut v = a.x.to_vec(); v.extend(a.y);
    let pk = b.hash_n_to_hash_no_pad::<PoseidonHash>(v).elements;
    let mut v = r.x.to_vec(); v.extend(r.y); v.extend(a.x); v.extend(a.y); v.extend(msg);
    let hsh = b.hash_n_to_hash_no_pad::<PoseidonHash>(v);
    let mut e_bits = split64_canonical(b, hsh.elements[0]);
    e_bits.extend(split64_canonical(b, hsh.elements[1]));
    assert_less_than_n(b, &s_bits);

    // the four points to pick from: T0 = H, T1 = H+G (constants), T2 = H-A, T3 = H+G-A
    let neg_a = PT { x: a.x, y: core::array::from_fn(|k| b.neg(a.y[k])) };
    let h1 = pt_const(b, prm.h1);
    let t2 = dbl_add(b, h1, neg_a);
    let g1 = pt_const(b, prm.g1);
    let t3 = dbl_add(b, g1, t2);
    let t0c = pcoords(prm.h);
    let t1c = pcoords(prm.hg);
    let dc1: [F; 10] = core::array::from_fn(|c| t1c[c] - t0c[c]);
    let (t2c, t3c) = (coords(&t2), coords(&t3));
    let d2: [Target; 10] = core::array::from_fn(|c| b.add_const(t2c[c], -t0c[c]));
    let d3: [Target; 10] = core::array::from_fn(|c| { let t = b.sub(t3c[c], t2c[c]); b.add_const(t, -dc1[c]) });
    let one = b.one();
    let t0t: [Target; 10] = core::array::from_fn(|c| b.constant(t0c[c]));

    let mut acc = pt_const(b, prm.h0);
    for i in (0..S_BITS).rev() {
        let b1 = s_bits[i].target;
        let q: [Target; 10] = core::array::from_fn(|c| {
            let base = b.arithmetic(dc1[c], F::ONE, b1, one, t0t[c]); // T0 + b1 (T1 - T0)
            if i < E_BITS {
                let v = b.mul_add(b1, d3[c], d2[c]);                 // (T2 - T0) + b1 (T3 - T2 - T1 + T0)
                b.mul_add(e_bits[i].target, v, base)
            } else { base }
        });
        acc = dbl_add(b, acc, from_coords(q));
    }
    // acc = 2C' + sG - eA; must equal 2C' + R
    let cp = pt_const(b, prm.cp);
    let right = dbl_add(b, cp, r);
    for k in 0..5 { b.connect(acc.x[k], right.x[k]); b.connect(acc.y[k], right.y[k]); }
    (SigT { a, r, s_bits }, pk)
}
pub fn set_pt(pw: &mut plonky2::iop::witness::PartialWitness<F>, t: PT, p: P) -> Result<()> {
    let (x, y) = sw(p);
    for i in 0..5 { pw.set_target(t.x[i], x.0[i])?; pw.set_target(t.y[i], y.0[i])?; }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::PoseidonGoldilocksConfig;
    fn lt_ok(v: &BigUint) -> bool {
        let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let bits: Vec<BoolTarget> = (0..S_BITS).map(|_| b.add_virtual_bool_target_safe()).collect();
        assert_less_than_n(&mut b, &bits);
        let data = b.build::<PoseidonGoldilocksConfig>();
        let mut pw = PartialWitness::new();
        for i in 0..S_BITS { pw.set_bool_target(bits[i], v.bit(i as u64)).unwrap(); }
        data.prove(pw).is_ok()
    }
    #[test]
    fn s_less_than_n() {
        let n = n_order();
        let one = BigUint::from(1u32);
        for v in [BigUint::from(0u32), BigUint::from(12345u32), &n - &one, &n >> 1] { assert!(lt_ok(&v), "should accept"); }
        for v in [n.clone(), &n + &one, (BigUint::from(1u32) << S_BITS) - &one] { assert!(!lt_ok(&v), "should reject"); }
    }
    #[test]
    fn dbladd_rejects_equal_points() {
        // P == Q is an exceptional case: the generator refuses, so no proof
        let prm = params();
        let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        dbladd_reset();
        let g = pt_const(&mut b, prm.g); let g2 = pt_const(&mut b, prm.g);
        dbl_add(&mut b, g, g2);
        dbladd_pad(&mut b, &prm);
        let data = b.build::<PoseidonGoldilocksConfig>();
        assert!(data.prove(PartialWitness::new()).is_err());
    }
}
