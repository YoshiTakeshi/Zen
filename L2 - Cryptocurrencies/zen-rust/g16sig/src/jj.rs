// Schnorr/EdDSA-style signatures on Jubjub (twisted Edwards, a = -1, d = -10240/10241 over the
// BLS12-381 scalar field), native code and bellpepper gadgets. Same scheme as the Plonky2 benchmark:
// e = low 128 bits of Poseidon(R, A, message), s = r + e*k as a plain integer (385 bits),
// check s*G == R + e*A. Complete Edwards formulas: 7 constraints per addition.
use bellpepper_core::{boolean::{AllocatedBit, Boolean}, num::AllocatedNum, ConstraintSystem, SynthesisError};
use blstrs::Scalar as F;
use ff::Field;
use num_bigint::BigUint;

pub const S_BITS: usize = 385;
pub const E_BITS: usize = 128;
pub fn d() -> F { -(F::from(10240u64) * F::from(10241u64).invert().unwrap()) }

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct P { pub x: F, pub y: F }
pub fn id() -> P { P { x: F::ZERO, y: F::ONE } }
pub fn add(p: P, q: P) -> P {
    let c = d() * p.x * q.x * p.y * q.y;
    P { x: (p.x * q.y + p.y * q.x) * (F::ONE + c).invert().unwrap(), y: (p.y * q.y + p.x * q.x) * (F::ONE - c).invert().unwrap() }
}
pub fn on_curve(p: P) -> bool { -(p.x * p.x) + p.y * p.y == F::ONE + d() * p.x * p.x * p.y * p.y }
pub fn generator() -> P {
    let mut t = 2u64;
    loop {
        let y = F::from(t);
        let num = y * y - F::ONE; let den = d() * y * y + F::ONE;
        let x2 = num * den.invert().unwrap();
        let s = x2.sqrt();
        if bool::from(s.is_some()) {
            let mut p = P { x: s.unwrap(), y };
            for _ in 0..3 { p = add(p, p); } // clear the cofactor 8
            if p != id() { return p; }
        }
        t += 1;
    }
}
pub fn mul(p: P, k: &BigUint) -> P {
    let mut acc = id();
    for i in (0..k.bits()).rev() { acc = add(acc, acc); if k.bit(i) { acc = add(acc, p); } }
    acc
}
pub fn table(g: P) -> Vec<P> { let mut t = vec![g]; for i in 1..S_BITS { let x = t[i - 1]; t.push(add(x, x)); } t }
pub fn to_big(x: &F) -> BigUint { BigUint::from_bytes_le(&x.to_bytes_le()) }

// ---------------------------------------------------------------- gadgets
pub struct PT { pub x: AllocatedNum<F>, pub y: AllocatedNum<F> }
fn val(a: &AllocatedNum<F>) -> F { a.get_value().unwrap_or(F::ZERO) }
pub fn add_c<CS: ConstraintSystem<F>>(mut cs: CS, p: &PT, q: &PT) -> Result<PT, SynthesisError> {
    let t1 = p.x.mul(cs.namespace(|| "t1"), &q.y)?;
    let t2 = p.y.mul(cs.namespace(|| "t2"), &q.x)?;
    let t3 = p.x.mul(cs.namespace(|| "t3"), &q.x)?;
    let t4 = p.y.mul(cs.namespace(|| "t4"), &q.y)?;
    let c = t3.mul(cs.namespace(|| "c"), &t4)?;
    let dd = d();
    let (cv, x3v, y3v) = { let cv = val(&c); (cv, (val(&t1) + val(&t2)) * (F::ONE + dd * cv).invert().unwrap_or(F::ZERO), (val(&t3) + val(&t4)) * (F::ONE - dd * cv).invert().unwrap_or(F::ZERO)) };
    let _ = cv;
    let x3 = AllocatedNum::alloc(cs.namespace(|| "x3"), || Ok(x3v))?;
    let y3 = AllocatedNum::alloc(cs.namespace(|| "y3"), || Ok(y3v))?;
    cs.enforce(|| "x3c", |lc| lc + x3.get_variable(), |lc| lc + CS::one() + (dd, c.get_variable()), |lc| lc + t1.get_variable() + t2.get_variable());
    cs.enforce(|| "y3c", |lc| lc + y3.get_variable(), |lc| lc + CS::one() - (dd, c.get_variable()), |lc| lc + t3.get_variable() + t4.get_variable());
    Ok(PT { x: x3, y: y3 })
}
/// point = bit ? (px, py) : identity, where (px, py) is a constant
pub fn sel_const<CS: ConstraintSystem<F>>(mut cs: CS, bit: &AllocatedBit, p: P) -> Result<PT, SynthesisError> {
    let b = bit.get_value().unwrap_or(false);
    let x = AllocatedNum::alloc(cs.namespace(|| "sx"), || Ok(if b { p.x } else { F::ZERO }))?;
    let y = AllocatedNum::alloc(cs.namespace(|| "sy"), || Ok(if b { p.y } else { F::ONE }))?;
    cs.enforce(|| "sxc", |lc| lc + bit.get_variable(), |lc| lc + (p.x, CS::one()), |lc| lc + x.get_variable());
    cs.enforce(|| "syc", |lc| lc + bit.get_variable(), |lc| lc + (p.y - F::ONE, CS::one()), |lc| lc + y.get_variable() - CS::one());
    Ok(PT { x, y })
}
/// point = bit ? q : identity, q variable
pub fn sel_var<CS: ConstraintSystem<F>>(mut cs: CS, bit: &Boolean, q: &PT) -> Result<PT, SynthesisError> {
    let b = bit.get_value().unwrap_or(false);
    let x = AllocatedNum::alloc(cs.namespace(|| "vx"), || Ok(if b { val(&q.x) } else { F::ZERO }))?;
    let y = AllocatedNum::alloc(cs.namespace(|| "vy"), || Ok(if b { val(&q.y) } else { F::ONE }))?;
    cs.enforce(|| "vxc", |_| bit.lc(CS::one(), F::ONE), |lc| lc + q.x.get_variable(), |lc| lc + x.get_variable());
    cs.enforce(|| "vyc", |_| bit.lc(CS::one(), F::ONE), |lc| lc + q.y.get_variable() - CS::one(), |lc| lc + y.get_variable() - CS::one());
    Ok(PT { x, y })
}
pub fn identity<CS: ConstraintSystem<F>>(mut cs: CS) -> Result<PT, SynthesisError> {
    let x = AllocatedNum::alloc(cs.namespace(|| "ix"), || Ok(F::ZERO))?;
    let y = AllocatedNum::alloc(cs.namespace(|| "iy"), || Ok(F::ONE))?;
    cs.enforce(|| "ixc", |lc| lc + x.get_variable(), |lc| lc + CS::one(), |lc| lc);
    cs.enforce(|| "iyc", |lc| lc + y.get_variable(), |lc| lc + CS::one(), |lc| lc + CS::one());
    Ok(PT { x, y })
}
/// check s*G == R + e*A, with e = low E_BITS bits of `e_full`
pub fn verify<CS: ConstraintSystem<F>>(mut cs: CS, table: &[P], a: &PT, r: &PT, s: &BigUint, e_full: &AllocatedNum<F>) -> Result<(), SynthesisError> {
    let ebits = e_full.to_bits_le_strict(cs.namespace(|| "ebits"))?;
    // s*G, fixed base
    let mut acc = identity(cs.namespace(|| "id0"))?;
    for i in 0..S_BITS {
        let bit = AllocatedBit::alloc(cs.namespace(|| format!("s{i}")), Some(s.bit(i as u64)))?;
        let g = sel_const(cs.namespace(|| format!("g{i}")), &bit, table[i])?;
        acc = add_c(cs.namespace(|| format!("fa{i}")), &acc, &g)?;
    }
    let left = acc;
    // e*A, double-and-add
    let mut acc = identity(cs.namespace(|| "id1"))?;
    for i in (0..E_BITS).rev() {
        acc = add_c(cs.namespace(|| format!("dbl{i}")), &acc, &acc)?;
        let q = sel_var(cs.namespace(|| format!("sa{i}")), &ebits[i], a)?;
        acc = add_c(cs.namespace(|| format!("va{i}")), &acc, &q)?;
    }
    let right = add_c(cs.namespace(|| "plusR"), &acc, r)?;
    cs.enforce(|| "eqx", |lc| lc + left.x.get_variable(), |lc| lc + CS::one(), |lc| lc + right.x.get_variable());
    cs.enforce(|| "eqy", |lc| lc + left.y.get_variable(), |lc| lc + CS::one(), |lc| lc + right.y.get_variable());
    Ok(())
}
