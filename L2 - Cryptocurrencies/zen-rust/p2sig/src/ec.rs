// Schnorr signatures over the curve y^2 = x^3 + 2x^2 + 263z*x defined over GF(p^5), p = Goldilocks,
// GF(p^5) = GF(p)[z]/(z^5 - 3) (the EcGFp5 curve equation of T. Pornin), in plain affine
// Weierstrass coordinates. Native code (signing) and Plonky2 gadgets (verification).
//
// Scheme (same in the Groth16 benchmark): secret k, public A = k*G; nonce r, R = r*G;
// e = first 128 bits of Poseidon(R, A, message); s = r + e*k as a plain integer (385 bits).
// Verify: s*G == R + e*A. The circuit does s*G with a fixed-base table (385 point additions)
// and e*A with double-and-add (128 doublings and additions).
use anyhow::Result;
use num_bigint::BigUint;
use plonky2::field::extension::quintic::QuinticExtension;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::plonk::config::Hasher;
use plonky2::util::serialization::{Buffer, IoResult};

pub type F = GoldilocksField;
pub type E = QuinticExtension<F>;
pub const D: usize = 2;
pub const S_BITS: usize = 385;
pub const E_BITS: usize = 128;

pub fn e(c: [u64; 5]) -> E { QuinticExtension(c.map(F::from_canonical_u64)) }
pub fn a2() -> E { e([2, 0, 0, 0, 0]) }
pub fn a4() -> E { e([0, 263, 0, 0, 0]) }

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
/// a point with the given x (if any)
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
    // non-residue
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
/// scalar multiplication with an offset point H (never hits the identity in practice):
/// returns k*P + 2^bits * H  (MSB-first double-and-add starting from H)
pub fn mul_off(p: P, k: &BigUint, bits: usize, h: P) -> P {
    let mut acc = h;
    for i in (0..bits).rev() {
        acc = dbl(acc);
        if k.bit(i as u64) { acc = add(acc, p); }
    }
    acc
}
/// fixed-base: H + k*G using the table G_i = 2^i G
pub fn mul_fixed(table: &[P], k: &BigUint, h: P) -> P {
    let mut acc = h;
    for (i, g) in table.iter().enumerate() { if k.bit(i as u64) { acc = add(acc, *g); } }
    acc
}
pub fn pow2(mut p: P, n: usize) -> P { for _ in 0..n { p = dbl(p); } p }

pub struct Params { pub g: P, pub h1: P, pub h2: P, pub table: Vec<P>, pub c2: P }
pub fn params() -> Params {
    // G: from the EcGFp5 generator's x coordinate; H1, H2: independent offset points
    let g = lift(e([12883135586176881569, 4356519642755055268, 5248930565894896907, 2165973894480315022, 2448410071095648785])).expect("G");
    let mut h = vec![];
    let mut t = 5u64;
    while h.len() < 2 { if let Some(p) = lift(e([t, 1, 7, 0, t * 3])) { h.push(p); } t += 1; }
    let mut table = vec![g];
    for i in 1..S_BITS { let p = dbl(table[i - 1]); table.push(p); }
    let c2 = pow2(h[1], E_BITS);
    Params { g, h1: h[0], h2: h[1], table, c2 }
}

pub fn challenge(r: P, a: P, msg: [F; 4]) -> BigUint {
    let mut v = r.x.0.to_vec(); v.extend(r.y.0); v.extend(a.x.0); v.extend(a.y.0); v.extend(msg);
    let hsh = PoseidonHash::hash_no_pad(&v);
    BigUint::from(hsh.elements[0].to_canonical_u64()) + (BigUint::from(hsh.elements[1].to_canonical_u64()) << 64)
}
pub fn pk_hash(a: P) -> [F; 4] {
    let mut v = a.x.0.to_vec(); v.extend(a.y.0);
    PoseidonHash::hash_no_pad(&v).elements
}

// ---------------------------------------------------------------- circuit
pub type ET = [Target; 5];
#[derive(Clone, Copy, Debug)]
pub struct PT { pub x: ET, pub y: ET }

pub fn ec_const(b: &mut CircuitBuilder<F, D>, c: E) -> ET { c.0.map(|v| b.constant(v)) }
pub fn ec_add(b: &mut CircuitBuilder<F, D>, x: ET, y: ET) -> ET { core::array::from_fn(|i| b.add(x[i], y[i])) }
pub fn ec_sub(b: &mut CircuitBuilder<F, D>, x: ET, y: ET) -> ET { core::array::from_fn(|i| b.sub(x[i], y[i])) }
pub fn ec_mul(b: &mut CircuitBuilder<F, D>, x: ET, y: ET) -> ET {
    let w = F::from_canonical_u64(3);
    let mut out = [b.zero(); 5];
    for k in 0..5 {
        let mut acc = b.zero();
        for i in 0..5 {
            let j = (k + 5 - i) % 5;
            if i + j == k { acc = b.mul_add(x[i], y[j], acc); }
            else { acc = b.arithmetic(w, F::ONE, x[i], y[j], acc); }
        }
        out[k] = acc;
    }
    out
}
#[derive(Debug, Clone)]
struct DivGen { num: ET, den: ET, out: ET }
impl SimpleGenerator<F, D> for DivGen {
    fn id(&self) -> String { "Fp5DivGen".into() }
    fn dependencies(&self) -> Vec<Target> { let mut v = self.num.to_vec(); v.extend(self.den); v }
    fn run_once(&self, w: &PartitionWitness<F>, out: &mut GeneratedValues<F>) -> Result<()> {
        let n = QuinticExtension(self.num.map(|t| w.get_target(t)));
        let d = QuinticExtension(self.den.map(|t| w.get_target(t)));
        let q = n * d.inverse();
        for i in 0..5 { out.set_target(self.out[i], q.0[i])?; }
        Ok(())
    }
    fn serialize(&self, _dst: &mut Vec<u8>, _c: &CommonCircuitData<F, D>) -> IoResult<()> { Ok(()) }
    fn deserialize(_src: &mut Buffer, _c: &CommonCircuitData<F, D>) -> IoResult<Self> { unimplemented!() }
}
pub fn ec_div(b: &mut CircuitBuilder<F, D>, num: ET, den: ET) -> ET {
    let out: ET = core::array::from_fn(|_| b.add_virtual_target());
    b.add_simple_generator(DivGen { num, den, out });
    let chk = ec_mul(b, out, den);
    for i in 0..5 { b.connect(chk[i], num[i]); }
    out
}
pub fn pt_add(b: &mut CircuitBuilder<F, D>, p: PT, q: PT) -> PT {
    let dy = ec_sub(b, q.y, p.y); let dx = ec_sub(b, q.x, p.x);
    let l = ec_div(b, dy, dx);
    let l2 = ec_mul(b, l, l);
    let s = ec_add(b, p.x, q.x);
    let mut x = ec_sub(b, l2, s);
    let two = b.constant(F::from_canonical_u64(2));
    x[0] = b.sub(x[0], two); // - a2
    let t = ec_sub(b, p.x, x);
    let ly = ec_mul(b, l, t);
    PT { x, y: ec_sub(b, ly, p.y) }
}
pub fn pt_dbl(b: &mut CircuitBuilder<F, D>, p: PT) -> PT {
    let x2 = ec_mul(b, p.x, p.x);
    // num = 3x^2 + 4x + 263z
    let three = F::from_canonical_u64(3); let four = F::from_canonical_u64(4);
    let mut num: ET = core::array::from_fn(|i| { let t = b.mul_const(four, p.x[i]); b.mul_const_add(three, x2[i], t) });
    let c = b.constant(F::from_canonical_u64(263)); num[1] = b.add(num[1], c);
    let den: ET = core::array::from_fn(|i| b.add(p.y[i], p.y[i]));
    let l = ec_div(b, num, den);
    let l2 = ec_mul(b, l, l);
    let s = ec_add(b, p.x, p.x);
    let mut x = ec_sub(b, l2, s);
    let two = b.constant(F::from_canonical_u64(2));
    x[0] = b.sub(x[0], two);
    let t = ec_sub(b, p.x, x);
    let ly = ec_mul(b, l, t);
    PT { x, y: ec_sub(b, ly, p.y) }
}
pub fn pt_const(b: &mut CircuitBuilder<F, D>, p: P) -> PT { PT { x: ec_const(b, p.x), y: ec_const(b, p.y) } }
pub fn pt_select(b: &mut CircuitBuilder<F, D>, c: BoolTarget, p: PT, q: PT) -> PT {
    PT { x: core::array::from_fn(|i| b.select(c, p.x[i], q.x[i])), y: core::array::from_fn(|i| b.select(c, p.y[i], q.y[i])) }
}
pub struct SigT { pub a: PT, pub r: PT, pub s_bits: Vec<BoolTarget> }
pub fn add_virtual_pt(b: &mut CircuitBuilder<F, D>) -> PT { PT { x: core::array::from_fn(|_| b.add_virtual_target()), y: core::array::from_fn(|_| b.add_virtual_target()) } }
/// pk hash of A (to bind the account leaf) and the signature check on msg (4 targets)
pub fn verify_sig(b: &mut CircuitBuilder<F, D>, prm: &Params, msg: [Target; 4]) -> (SigT, [Target; 4]) {
    let a = add_virtual_pt(b);
    let r = add_virtual_pt(b);
    let s_bits: Vec<BoolTarget> = (0..S_BITS).map(|_| b.add_virtual_bool_target_safe()).collect();
    let mut v = a.x.to_vec(); v.extend(a.y);
    let pk = b.hash_n_to_hash_no_pad::<PoseidonHash>(v).elements;
    // challenge e (128 bits)
    let mut v = r.x.to_vec(); v.extend(r.y); v.extend(a.x); v.extend(a.y); v.extend(msg);
    let hsh = b.hash_n_to_hash_no_pad::<PoseidonHash>(v);
    let mut e_bits = b.split_le(hsh.elements[0], 64);
    e_bits.extend(b.split_le(hsh.elements[1], 64));
    // left: H1 + s*G (fixed base)
    let mut acc = pt_const(b, prm.h1);
    for i in 0..S_BITS {
        let g = pt_const(b, prm.table[i]);
        let t = pt_add(b, acc, g);
        acc = pt_select(b, s_bits[i], t, acc);
    }
    let c2 = pt_const(b, prm.c2);
    let left = pt_add(b, acc, c2);            // H1 + sG + 2^128 H2
    // right: 2^128 H2 + e*A (double-and-add), + R, + H1
    let mut acc = pt_const(b, prm.h2);
    for i in (0..E_BITS).rev() {
        acc = pt_dbl(b, acc);
        let t = pt_add(b, acc, a);
        acc = pt_select(b, e_bits[i], t, acc);
    }
    let acc = pt_add(b, acc, r);
    let h1 = pt_const(b, prm.h1);
    let right = pt_add(b, acc, h1);
    for i in 0..5 { b.connect(left.x[i], right.x[i]); b.connect(left.y[i], right.y[i]); }
    (SigT { a, r, s_bits }, pk)
}
pub fn set_pt(pw: &mut plonky2::iop::witness::PartialWitness<F>, t: PT, p: P) -> Result<()> {
    for i in 0..5 { pw.set_target(t.x[i], p.x.0[i])?; pw.set_target(t.y[i], p.y.0[i])?; }
    Ok(())
}
