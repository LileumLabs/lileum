//! New sumcheck implementation based on the new Reduction.

pub mod evals;
pub mod folding;
mod message;
pub mod oracles;
mod point;
mod prove;
mod reduction;
mod relation;
#[cfg(test)]
mod tests;
pub mod zerocheck;

pub use oracles::OracleQueryInstance;
pub use point::MultiPoint;
pub use prove::ProverKey;
pub use reduction::{SumcheckError, SumcheckReduction, SumcheckVerifierKey};
pub use relation::{SumcheckInstance, SumcheckRelation};

#[derive(Clone, Debug)]
/// A message of the sumcheck protocol, represented as
/// the evaluations of polynomial over the domain 0..d.
pub struct SumcheckMessage<F>(Vec<F>);

use ark_ff::Field;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub};

pub trait Var<F: Field>:
    Sized
    + Add<Self, Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + Sub<Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + Mul<Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + Add<F, Output = Self>
    + Sub<F, Output = Self>
    + Mul<F, Output = Self>
    + for<'a> AddAssign<&'a Self>
    + MulAssign<F>
    + Clone
{
}

pub(crate) mod degree {
    use crate::sumcheck2::{
        evals::{Evals, Mles},
        oracles::{EvalLocation, Oracle},
        Var,
    };
    use ark_ff::Field;
    use std::ops::{Add, AddAssign, Mul, MulAssign, Sub};

    #[derive(Clone, Copy, Debug)]
    pub struct Degree(pub usize);

    impl Add for Degree {
        type Output = Self;

        fn add(self, rhs: Self) -> Self::Output {
            Degree(self.0.max(rhs.0))
        }
    }

    impl Add<&Self> for Degree {
        type Output = Self;

        fn add(self, rhs: &Self) -> Self::Output {
            Degree(self.0.max(rhs.0))
        }
    }

    impl Sub<Self> for Degree {
        type Output = Self;

        fn sub(self, rhs: Self) -> Self::Output {
            Degree(self.0.max(rhs.0))
        }
    }

    impl Sub<&Self> for Degree {
        type Output = Self;

        fn sub(self, rhs: &Self) -> Self::Output {
            Degree(self.0.max(rhs.0))
        }
    }

    impl Mul for Degree {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            Degree(self.0 + rhs.0)
        }
    }

    impl Mul<&Self> for Degree {
        type Output = Self;

        fn mul(self, rhs: &Self) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            Degree(self.0 + rhs.0)
        }
    }

    impl<F: Field> Add<F> for Degree {
        type Output = Self;

        fn add(self, _rhs: F) -> Self::Output {
            self
        }
    }

    impl<F: Field> Sub<F> for Degree {
        type Output = Self;

        fn sub(self, _rhs: F) -> Self::Output {
            self
        }
    }

    impl<F: Field> Mul<F> for Degree {
        type Output = Self;

        fn mul(self, _rhs: F) -> Self::Output {
            self
        }
    }

    impl AddAssign<&Self> for Degree {
        fn add_assign(&mut self, rhs: &Self) {
            *self = *self + rhs;
        }
    }

    impl<F: Field> MulAssign<F> for Degree {
        fn mul_assign(&mut self, _rhs: F) {}
    }

    impl<F: Field> Var<F> for Degree {}

    pub fn sumcheck_degree<F: Field, O: Oracle<F>>(oracle: &O) -> usize {
        let natures: Mles<O::Function, O::Nature> = oracle.natures();

        let intitial_degrees = <O::Function as Evals>::map_evals(&natures, |nature: &O::Nature| {
            let location: EvalLocation = (*nature).into();
            //NOTE: This may not always be true in sumcheck, and it ceirtainly is not
            // in sumfold.
            // This function is only to be used by sumcheck, for now it will be assumed
            // that instance evals are always 0, and the rest always 1. But at some
            // point it may be better to use some trait for the natures instead of just
            // Into<EvalLocation>.
            match location {
                EvalLocation::Structure => Degree(1),
                EvalLocation::Instance => Degree(0),
                EvalLocation::Witness => Degree(1),
            }
        });

        let degree: Degree = oracle.call_function(&intitial_degrees);
        degree.0
    }
}
