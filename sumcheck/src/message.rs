use crate::{barycentric_eval::BarycentricWeights, sumcheck::Var};
use ark_ff::Field;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Message<F: Field>(Vec<F>);

impl<F: Field> Message<F> {
    pub(crate) fn new(evals: Vec<F>) -> Self {
        Self(evals)
    }
}

impl<F: Field> Message<F> {
    fn bin_op<B: Fn(F, F) -> F>(mut self, rhs: &Self, f: B) -> Self {
        for ab in self.0.iter_mut().zip(rhs.0.iter()) {
            let (a, b): (&mut F, &F) = ab;
            *a = f(*a, *b);
        }
        self
    }
    pub fn eval_at_0(&self) -> F {
        self.0[0]
    }
    pub fn eval_at_1(&self) -> F {
        self.0[1]
    }
    pub(crate) fn eval_at_x(&self, x: F, weights: &BarycentricWeights<F>) -> F {
        weights.evaluate(&self.0, x)
    }
}

impl<F: Field> Add<Self> for Message<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.bin_op(&rhs, |a: F, b: F| a + b)
    }
}
impl<F: Field> Sub<Self> for Message<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.bin_op(&rhs, |a: F, b: F| a - b)
    }
}
impl<F: Field> Mul<Self> for Message<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.bin_op(&rhs, |a: F, b: F| a * b)
    }
}
impl<F: Field> Add<&Self> for Message<F> {
    type Output = Self;

    fn add(self, rhs: &Self) -> Self::Output {
        self.bin_op(rhs, |a: F, b: F| a + b)
    }
}
impl<F: Field> Sub<&Self> for Message<F> {
    type Output = Self;

    fn sub(self, rhs: &Self) -> Self::Output {
        self.bin_op(rhs, |a: F, b: F| a - b)
    }
}
impl<F: Field> Mul<&Self> for Message<F> {
    type Output = Self;

    fn mul(self, rhs: &Self) -> Self::Output {
        self.bin_op(rhs, |a: F, b: F| a * b)
    }
}
impl<F: Field> Add<F> for Message<F> {
    type Output = Self;

    fn add(mut self, rhs: F) -> Self::Output {
        for e in self.0.iter_mut() {
            *e += rhs
        }
        self
    }
}
impl<F: Field> Sub<F> for Message<F> {
    type Output = Self;

    fn sub(mut self, rhs: F) -> Self::Output {
        for e in self.0.iter_mut() {
            *e -= rhs
        }
        self
    }
}
impl<F: Field> Mul<F> for Message<F> {
    type Output = Self;

    fn mul(mut self, rhs: F) -> Self::Output {
        for e in self.0.iter_mut() {
            *e *= rhs
        }
        self
    }
}
impl<F: Field> MulAssign<F> for Message<F> {
    fn mul_assign(&mut self, rhs: F) {
        for e in self.0.iter_mut() {
            *e *= rhs
        }
    }
}
impl<F: Field> AddAssign<&Self> for Message<F> {
    fn add_assign(&mut self, rhs: &Self) {
        for (l, r) in self.0.iter_mut().zip(rhs.0.iter()) {
            *l += r;
        }
    }
}

impl<F: Field> Var<F> for Message<F> {}
impl<F: Field> AddAssign for Message<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = rhs + &*self;
    }
}
