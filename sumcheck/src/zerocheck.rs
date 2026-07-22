//! Utilities for zerocheck.

use crate::{
    polynomials::{Evals, MultiPoint},
    sumcheck::{Proof, ProverOutput, SumcheckFunction, SumcheckProver},
    SumcheckError,
};
use ark_ff::Field;
use sponge::sponge::Duplex;
use std::{
    iter::successors,
    ops::{Add, Mul},
    vec::IntoIter,
};
use transcript::{params::ParamResolver, Transcript};

/// Multilinear polynomial of form:
/// p(x_0) = x_0 * ß + (1 - x_0) * c
/// p(x_{i+1}) = (x_{i+1} * ß^{2^i} + (1 - x_{i+1}) * c_i) * p(x_i)
/// For some challenge ß and c = 1.
/// Making the MLE essentially a vector
/// 1, ß, ß^2, .. , ß^{2^k}
/// Represented as a product of degree 1 univariate polynomials.
/// For v varibles, point evaluation if O(v) and MLE computation is
/// O(2^v).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompactPowers<F: Field> {
    coefficients: Vec<(F, F)>,
}

impl<F: Field> CompactPowers<F> {
    pub fn new(chall: F, vars: usize) -> Self {
        let coefficients = successors(Some(chall), |last| Some(last.square()))
            .map(|c| (c, F::one()))
            .take(vars)
            .collect();
        Self { coefficients }
    }

    pub fn point_eval(&self, point: &MultiPoint<F>) -> F {
        assert_eq!(self.coefficients.len(), point.vars());

        self.coefficients
            .iter()
            .zip(point.inner_ref())
            .fold(F::one(), |acc, ((b, c), x)| {
                acc * (*x * b + (F::one() - x) * c)
            })
    }

    /// Returns evaluations over the hypercube.
    pub fn eval_over_domain(&self) -> Vec<F> {
        self.eval_over_domain_scaled(F::one())
    }

    /// Returns evaluations over the hypercube, scaling
    /// each of them by the provided scalar.
    pub fn eval_over_domain_scaled(&self, scalar: F) -> Vec<F> {
        let vars = self.coefficients.len();

        // p(x) = 0 * ß + (1 - 0) * c = c
        let eval_at_zero = self
            .coefficients
            .iter()
            .fold(F::one(), |acc, (_, c)| acc * c);
        let eval_at_zero = eval_at_zero * scalar;

        // Multiplying each of these has the effect of swaping the corresponding
        // from 0 to 1.
        // For example: e(0,0,0,0) * f0 * f2 = e(1,0,1,0).
        let mut flips: Vec<F> = self
            .coefficients
            .iter()
            .map(|(b, c)| c.inverse().unwrap() * b)
            .collect();
        // as write_evals() recurses in the reverse order.
        flips.reverse();

        let mut mle = vec![F::zero(); 1 << vars];
        mle[0] = eval_at_zero;
        mle[1] = eval_at_zero;

        write_evals(&mut mle, &flips);
        mle
    }

    /// Pops upper factor and returns its evaluation in the point.
    fn fix_upper_var(&mut self, point: F) -> F {
        let upper_factor = self.coefficients.pop();
        let (b, c) = upper_factor.unwrap();
        point * b + (F::one() - point) * c
    }

    pub(crate) fn factors(&self) -> &[(F, F)] {
        &self.coefficients
    }
}

impl<F: Field> transcript::Message<F> for CompactPowers<F> {
    fn len(vars: usize, _param_resolver: &ParamResolver) -> usize {
        vars * 2
    }

    fn to_field_elements(&self) -> Vec<F> {
        self.coefficients
            .iter()
            .flat_map(|(a, b)| [*a, *b])
            .collect()
    }
}

/// Unlike `crate::eq`, the base case expects dest to contain the
/// evaluation at 0 already.
fn write_evals<F: Field>(dest: &mut [F], flips: &[F]) {
    assert!(dest.len().is_power_of_two());
    if flips.len() == 1 {
        assert_eq!(dest.len(), 2);
        dest[1] *= flips[0];
    } else {
        let var = flips[0];
        let (left, right) = dest.split_at_mut(dest.len() / 2);
        assert_eq!(left.len(), right.len());
        write_evals(left, &flips[1..]);
        for (l, r) in left.iter().zip(right.iter_mut()) {
            *r = *l * var;
        }
    }
}

#[cfg(test)]
fn test<F: Field>(chall: F) {
    let vars = 5;
    let powers = CompactPowers::new(chall, vars);
    assert_eq!(
        powers.point_eval(&MultiPoint::new(vec![F::zero(); vars])),
        F::one()
    );
    let powers = powers.eval_over_domain();
    assert_eq!(powers.len(), 1 << vars);
    let mut expected = F::one();
    for eval in powers {
        assert_eq!(eval, expected);
        expected *= chall;
    }
}

#[test]
fn compact_powers() {
    use ark_ff::UniformRand;
    use ark_vesta::Fr;
    use rand::{rngs::StdRng, SeedableRng};

    let mut rng = StdRng::seed_from_u64(0);
    let chall = Fr::rand(&mut rng);
    test(chall);
}

impl<F: Field> Mul<F> for CompactPowers<F> {
    type Output = Self;

    fn mul(mut self, rhs: F) -> Self::Output {
        for (b, c) in self.coefficients.iter_mut() {
            *b *= rhs;
            *c *= rhs;
        }
        self
    }
}

impl<F: Field> Add<Self> for CompactPowers<F> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        for (l, r) in self.coefficients.iter_mut().zip(rhs.coefficients) {
            l.0 += r.0;
            l.1 += r.1;
        }
        self
    }
}

#[cfg(test)]
fn bits(x: usize, left: usize) -> Vec<u8> {
    match left {
        0 => {
            vec![]
        }
        left => {
            let bit = x & 0b1;
            let mut tail = bits(x >> 1, left - 1);
            tail.push(bit as u8);
            tail
        }
    }
}

#[cfg(test)]
fn compact_powers_over_domain<F: Field>(challs: [F; 3]) {
    let vars = 5;
    let [c1, c2, c3] = challs;
    let powers1 = CompactPowers::new(c1, vars);
    let powers2 = CompactPowers::new(c2, vars);
    let powers3 = powers1.clone() * c3 + powers2.clone();

    let mut evals3 = powers3.eval_over_domain().into_iter();
    for i in 0..(1 << vars) {
        let point = bits(i, vars).into_iter().map(F::from);
        let point = MultiPoint::new(point.rev().collect());
        let e3 = evals3.next().unwrap();
        assert_eq!(e3, powers3.point_eval(&point));
    }
}

#[test]
fn powers_over_domain() {
    use ark_ff::UniformRand;
    use ark_vesta::Fr;
    use rand::{rngs::StdRng, SeedableRng};

    let mut rng = StdRng::seed_from_u64(0);
    let mut chall = || Fr::rand(&mut rng);

    let challs = [(); 3].map(|_| chall());
    compact_powers_over_domain(challs);
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum ZeroCheckIdx<I> {
    ZeroCheckChallenge,
    Inner(I),
}

#[derive(Clone, Debug)]
pub struct ZeroCheckMles<V, I> {
    zerocheck: V,
    inner: I,
}

impl<V, I> ZeroCheckMles<V, I> {
    pub const fn new(zerocheck: V, inner: I) -> Self {
        Self { zerocheck, inner }
    }

    pub fn map<V2, I2, M1, M2>(self, f: M1, inner_f: M2) -> ZeroCheckMles<V2, I2>
    where
        M1: Fn(V) -> V2,
        M2: Fn(I) -> I2,
    {
        let Self { zerocheck, inner } = self;
        let zerocheck = f(zerocheck);
        let inner = inner_f(inner);
        ZeroCheckMles { zerocheck, inner }
    }

    pub const fn inner(&self) -> &I {
        &self.inner
    }
}

impl<V: Copy, I: Evals<V>> Evals<V> for ZeroCheckMles<V, I> {
    type Idx = ZeroCheckIdx<I::Idx>;

    fn index(&self, index: Self::Idx) -> &V {
        match index {
            ZeroCheckIdx::ZeroCheckChallenge => &self.zerocheck,
            ZeroCheckIdx::Inner(idx) => self.inner.index(idx),
        }
    }

    fn combine<C: Fn(V, V) -> V>(&self, other: &Self, f: C) -> Self {
        let zerocheck = f(self.zerocheck, other.zerocheck);
        let inner = self.inner.combine(&other.inner, f);
        ZeroCheckMles { zerocheck, inner }
    }

    fn flatten(self, vec: &mut Vec<V>) {
        let Self { zerocheck, inner } = self;
        vec.push(zerocheck);
        inner.flatten(vec);
    }

    fn unflatten(elems: &mut IntoIter<V>) -> Self {
        let zerocheck = elems.next().unwrap();
        let inner = I::unflatten(elems);
        Self { zerocheck, inner }
    }
}

impl<F: Field, SF, I> SumcheckProver<F, SF>
where
    I: Evals<F>,
    SF: SumcheckFunction<F, Mles<F> = ZeroCheckMles<F, I>>,
{
    pub fn prove_zerocheck<S: Duplex<F>>(
        &self,
        powers: CompactPowers<F>,
        transcript: &mut Transcript<F, S>,
        mle: Vec<SF::Mles<F>>,
        challs: &SF::Challs,
    ) -> Result<ProverOutput<F, SF>, SumcheckError> {
        let nvars = powers.coefficients.len();
        let mut messages = Vec::with_capacity(nvars);

        let mut vars = vec![];
        let mut shrinking_powers = ShrinkingPowers::new(powers);
        let mles = (0..nvars).try_fold(mle, |mle, _| {
            let mle: Vec<SF::Mles<F>> = mle;
            let m = self.message_symbolic(&mle, challs);
            let [var] = transcript
                .send_message(&m)
                .map_err(SumcheckError::TranscriptError)?;
            messages.push(m);
            vars.push(var);
            Ok(Self::fix_vars_custom(mle, &mut shrinking_powers, var))
        })?;

        vars.reverse();
        let point = MultiPoint::new(vars);
        debug_assert_eq!(mles.len(), 1);
        let evals = mles[0].clone();

        let proof = Proof::from_messages(messages);

        Ok(ProverOutput {
            point,
            proof,
            evals,
        })
    }

    /// Fixes variables like `EvalsExt::fix_var` for the inner MLEs,
    /// But handles the zerocheck MLE differently, as it is the product of univariate
    /// polynomials and just treated as a single MLE for convenience.
    fn fix_vars_custom(
        mut mle: Vec<ZeroCheckMles<F, I>>,
        shrinking_powers: &mut ShrinkingPowers<F>,
        var: F,
    ) -> Vec<ZeroCheckMles<F, I>> {
        let half_len = mle.len() / 2;
        let one_minus_var = F::one() - var;
        let (left, right) = mle.split_at_mut(half_len);

        let mut powers = shrinking_powers.fix(var).into_iter();

        let f = |a, b| one_minus_var * a + var * b;
        for (left, right) in left.iter_mut().zip(right) {
            let left_inner: &mut I = &mut left.inner;
            let inner = left_inner.combine(&right.inner, f);

            let zerocheck = powers.next().unwrap();
            *left = ZeroCheckMles { zerocheck, inner };
        }
        mle.truncate(half_len);
        mle
    }
}

/// Structure holding a partially fixed `CompactPowers`.
/// Allow to fix variables 1 at a time and compute the corresponding MLE.
pub(crate) struct ShrinkingPowers<F: Field> {
    powers: CompactPowers<F>,
    constants: Vec<F>,
}

impl<F: Field> ShrinkingPowers<F> {
    pub(crate) fn new(powers: CompactPowers<F>) -> Self {
        Self {
            powers,
            constants: vec![],
        }
    }

    /// Fixes upper variables and computes MLE.
    pub(crate) fn fix(&mut self, point: F) -> Vec<F> {
        assert_ne!(self.powers.coefficients.len(), 0, "no variable left to fix");

        let constant = self.powers.fix_upper_var(point);
        self.constants.push(constant);

        let scale = self
            .constants
            .iter()
            .cloned()
            .fold(F::one(), |acc, c| acc * c);
        if self.powers.coefficients.is_empty() {
            vec![scale]
        } else {
            self.powers.eval_over_domain_scaled(scale)
        }
    }
}

#[cfg(test)]
fn mle_equivalence_test<F: Field>(elems: Vec<F>) {
    let mut elems = elems.into_iter();
    const VARS: usize = 3;

    let fixes = [(); VARS].map(|_| elems.next().unwrap());
    let p1 = CompactPowers::new(elems.next().unwrap(), VARS);
    let p2 = CompactPowers::new(elems.next().unwrap(), VARS);
    let fold = elems.next().unwrap();
    let mut powers = p1 * fold + p2;
    powers.coefficients[2].0 = F::one();
    powers.coefficients[2].1 = F::one();
    let mut full_eval = F::one();
    for (fix, (b, c)) in fixes.iter().zip(powers.coefficients.clone()) {
        let eval = b * fix + c * (F::one() - fix);
        full_eval *= eval;
        println!("factor_eval: {}", eval)
    }
    let check_point = MultiPoint::new(fixes.to_vec());
    assert_eq!(full_eval, powers.point_eval(&check_point));

    // let c1 = powers.fix_upper_var(fixes[0]);
    // println!("c = {}", c1);
    // let c2 = powers.fix_upper_var(fixes[1]);
    // println!("c = {}", c2);
    // let c3 = powers.fix_upper_var(fixes[2]);
    // println!("c = {}", c3);
}

#[test]
fn mle_equivalence() {
    use crate::utils::Fm;
    use ark_ff::UniformRand;
    use rand::{rngs::StdRng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(0);
    let elems = [(); 10].map(|_| Fm::rand(&mut rng));
    mle_equivalence_test::<Fm>(elems.to_vec());
}

#[test]
fn factor_folding() {
    use crate::utils::Fm;
    use ark_ff::{One, UniformRand};
    use rand::{rngs::StdRng, SeedableRng};

    let vars = 5;
    let mut rng = StdRng::seed_from_u64(0);
    let mut elem = || Fm::rand(&mut rng);
    let chall: Fm = elem();

    let p1 = CompactPowers::new(elem(), vars);
    let p2 = CompactPowers::new(elem(), vars);
    let p3: CompactPowers<Fm> = p1.clone() * chall + p2.clone();

    let check_point = [(); 5].map(|_| elem());

    let eval = |(a, b), x| a * x + b * (Fm::one() - x);
    let mut res = Fm::one();

    #[allow(clippy::needless_range_loop)]
    for i in 0..vars {
        let p1 = eval(p1.coefficients[i], check_point[i]);
        let p2 = eval(p2.coefficients[i], check_point[i]);
        let p3 = eval(p3.coefficients[i], check_point[i]);
        assert_eq!(p1 * chall + p2, p3);
        res *= p1 * chall + p2;
    }
    let check_point = MultiPoint::new(check_point.to_vec());

    let p1ev = p1.point_eval(&check_point);
    let p2ev = p2.point_eval(&check_point);
    let p3ev = p3.point_eval(&check_point);
    assert_ne!(p1ev * chall + p2ev, p3ev);
}

// Test the CompactPowers representation (core of zerocheck used
// in the folding/zero-knowledge reductions) sums to a known value
// over the boolean hypercube.  This test helps catch regressions,
// such as exponential ordering mistakes, missing powers, broken
// eval_over_domain and incorrect tensor-product factorization.
#[test]
fn compact_powers_hypercube_sum() {
    use ark_ff::{One, UniformRand};
    use ark_vesta::Fr;
    use rand::{rngs::StdRng, SeedableRng};

    let mut rng = StdRng::seed_from_u64(0);
    let chall = Fr::rand(&mut rng);
    let vars = 5;

    // Compute the vars length factorized coefficient pairs
    let powers = CompactPowers::new(chall, vars);
    // Compute the 2^vars length full evaluation vector
    let evals = powers.eval_over_domain();
    // Sum over full vector
    let sum: Fr = evals.iter().cloned().sum();

    // Sum over the hypercube = prod_j (chall^(2^j) + 1) closed form with
    // vars terms in factorized form
    let expected: Fr = (0..vars)
        .map(|j| Fr::one() + chall.pow([1 << j, 0, 0, 0]))
        .product();

    assert_eq!(sum, expected, "Hypercube sum mismatch");
}
