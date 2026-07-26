//! Shallue-van de Woestijne map

use std::fmt::Debug;

use crate::CurveMap;
use ark_ec::{
    short_weierstrass::{self, Affine, SWCurveConfig},
    CurveConfig,
};
use ark_ff::{BigInteger, Field, PrimeField, Zero};

#[cfg(test)]
mod tests;

type F<C> = <C as CurveConfig>::BaseField;

fn curve_equation_rhs<C: SWCurveConfig>(x: F<C>) -> F<C> {
    C::add_b(x.square() * x + C::mul_by_a(x))
}

fn is_square<F: Field>(x: F) -> bool {
    matches!(x.legendre(), ark_ff::LegendreSymbol::QuadraticResidue)
}

fn check_z<C: SWCurveConfig>(z_candidate: F<C>) -> bool {
    let z = z_candidate;
    let gz: F<C> = curve_equation_rhs::<C>(z);
    if gz.is_zero() {
        return false;
    }
    let num = F::<C>::from(3_u8) * z.square();
    let num = num + C::mul_by_a(F::<C>::from(4_u8));
    let num = -num;
    let denom = gz * F::<C>::from(4_u8);
    let div = num / denom;
    if div.is_zero() {
        return false;
    }

    if !is_square(div) {
        return false;
    }
    if is_square(gz) {
        true
    } else {
        let z_half = (-z) / F::<C>::from(2_u8);
        let gz_half = curve_equation_rhs::<C>(z_half);
        is_square(gz_half)
    }
}
fn find_z<C: SWCurveConfig>() -> Option<F<C>> {
    let mut z = F::<C>::ONE;
    for _ in 0..1000 {
        if check_z::<C>(z) {
            return Some(z);
        } else {
            z += F::<C>::ONE;
        }
    }
    None
}

#[derive(Copy, PartialEq, Eq)]
pub struct SvdwMap<C: SWCurveConfig> {
    z: C::BaseField,
}

impl<C: SWCurveConfig> Debug for SvdwMap<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SvdwMap").field("z", &self.z).finish()
    }
}

impl<C: SWCurveConfig> Clone for SvdwMap<C>
where
    C::BaseField: Debug,
{
    fn clone(&self) -> Self {
        Self { z: self.z }
    }
}

fn sgn0_is_even<F: PrimeField>(x: F) -> bool {
    x.into_bigint().is_even()
}

impl<C: SWCurveConfig> Default for SvdwMap<C> {
    fn default() -> Self {
        let z = find_z::<C>().unwrap();
        Self { z }
    }
}

impl<C: SWCurveConfig> SvdwMap<C>
where
    C::BaseField: PrimeField,
{
    pub fn new() -> Self {
        let z = find_z::<C>().unwrap();
        Self { z }
    }

    pub fn map(&self, u: F<C>) -> Affine<C> {
        let [one, two, three, four] = [1_u8, 2, 3, 4].map(F::<C>::from);
        let z = self.z;
        let g = |x| curve_equation_rhs::<C>(x);
        let gz = g(z);
        let tv1 = u.square() * gz;
        let tv2 = one + tv1;
        let tv1 = one - tv1;
        let tv3 = (tv1 * tv2).inverse().unwrap();
        //TODO: precompute
        let tv4 = (-gz * (three * z.square() + C::mul_by_a(four)))
            .sqrt()
            .unwrap();
        let tv4: F<C> = if sgn0_is_even(tv4) { tv4 } else { -tv4 };
        let tv5 = u * tv1 * tv3 * tv4;
        //TODO: precompute
        let tv6 = (-four * gz) / (three * z.square() + C::mul_by_a(four));

        //TODO: precompute div
        let x1 = -z / two - tv5;
        //TODO: precompute div
        let x2 = -z / two + tv5;
        let x3 = z + tv6 * (tv2.square() * tv3).square();
        let x = match [x1, x2].map(curve_equation_rhs::<C>).map(is_square::<F<C>>) {
            [true, _] => x1,
            [false, true] => x2,
            _ => x3,
        };
        let y = curve_equation_rhs::<C>(x).sqrt().unwrap();
        let (x, y) = match [u, y].map(sgn0_is_even::<F<C>>) {
            [true, true] | [false, false] => (x, y),
            _ => (x, -y),
        };
        Affine {
            x,
            y,
            infinity: false,
        }
    }
}

impl<C: SWCurveConfig> CurveMap<short_weierstrass::Projective<C>> for SvdwMap<C>
where
    C::BaseField: PrimeField,
{
    fn map_to_curve(&self, u: C::BaseField) -> short_weierstrass::Projective<C> {
        self.map(u).into()
    }

    fn new() -> Self {
        let z = find_z::<C>().unwrap();
        Self { z }
    }
}
