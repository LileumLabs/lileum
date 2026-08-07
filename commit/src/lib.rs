use ark_ff::Field;
use reduction::{Argument, Message, NoError};
use std::{
    fmt::Debug,
    ops::{Add, Mul},
};

pub mod multipoint;
pub mod oracle;
mod relation;

#[cfg(feature = "ipa")]
pub mod ipa;

pub use relation::{OpenInstance, OpeningRelation};

pub trait CommitmentSchemeCore<F: Field>: Clone + Debug + Eq + 'static {
    type Commitment: for<'a> Add<&'a Self::Commitment, Output = Self::Commitment>
        + Add<Output = Self::Commitment>
        + Mul<F, Output = Self::Commitment>
        + Eq
        + Clone
        + Debug
        + Message<F, Params = (), Error = NoError>;

    fn new(vars: usize) -> Self;

    fn commit_mle(&self, evals: &[F]) -> Self::Commitment;

    fn commit_small_set(&self, evals: &[u8], set: [F; 256]) -> Self::Commitment {
        let evals: Vec<F> = evals.iter().map(|i| set[*i as usize]).collect();
        self.commit_mle(evals.as_slice())
    }
    /// Further specialized version of [Self::commit_small_set], where the set is
    /// [0..256].
    fn commit_bytes(&self, evals: &[u8]) -> Self::Commitment {
        let set: Vec<F> = (0..256).map(|i| F::from(i as u8)).collect();
        let set: [F; 256] = set.try_into().unwrap();
        self.commit_small_set(evals, set)
    }
}

pub trait CommitmentScheme<F: Field>:
    CommitmentSchemeCore<F> + Argument<F, OpeningRelation<F, Self>>
{
}
