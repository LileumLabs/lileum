//! New sumcheck implementation based on the new Reduction.

mod barycentric_eval;
pub(crate) mod degree;
pub mod eq;
pub mod evals;
pub mod folding;
mod message;
pub mod oracles;
mod point;
mod powers;
mod prove;
mod reduction;
mod relation;
#[cfg(test)]
mod tests;
pub mod zerocheck;
// Currently unused but may be used again in the future.
// mod symbolic;
pub mod utils;

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

impl<F: Field> Var<F> for F {}
