use crate::lilium2::reductions::matrix_product::matrix_sum::MatrixSumNature;
use ark_ff::Field;
use commit::commit2::oracle::CommittedNature;
use std::fmt::Debug;
use std::vec::IntoIter;
use sumcheck::{
    sumcheck::Var,
    sumcheck2::{
        evals::{Evals, EvalsCore},
        oracles::{composite::Either, core::CoreNature, partial::OracleEval, SumcheckFunction},
    },
};
use sumcheck_derive::EvalsCore;

#[derive(Clone, Copy, Debug, PartialEq, Eq, EvalsCore)]
pub struct MatrixSumEvals<V: Clone + Debug, const N: usize> {
    matrices: [V; N],
    z: V,
    challenge: V,
}

impl<F: Field, const N: usize> MatrixSumEvals<F, N> {
    pub(crate) fn zero() -> Self {
        Self {
            matrices: [F::ZERO; N],
            z: F::ZERO,
            challenge: F::ZERO,
        }
    }
}

impl<F: Field, const N: usize> MatrixSumEvals<OracleEval<F>, N> {
    pub(crate) fn evals() -> Self {
        MatrixSumEvals {
            matrices: [OracleEval::ProverProvided; N],
            z: OracleEval::None,
            challenge: OracleEval::None,
        }
    }
}

impl<F: Field, const N: usize> SumcheckFunction<F> for MatrixSumEvals<(), N> {
    type Natures = Either<MatrixSumNature, Either<CoreNature, CommittedNature>>;

    type Data = ();

    fn natures() -> Self::Mles<Self::Natures> {
        use Either::*;
        MatrixSumEvals {
            matrices: [Left(MatrixSumNature); N],
            z: Right(Right(CommittedNature::Witness)),
            challenge: Right(Left(CoreNature::Challenge)),
        }
    }

    fn function<V: Var<F> + Debug>(_: &(), evals: &Self::Mles<V>) -> V {
        let MatrixSumEvals {
            matrices,
            z,
            challenge,
        } = evals;

        let mut acc = matrices[0].clone() * z;
        for matrix in &matrices[1..] {
            acc = acc * challenge;
            let m_eq = matrix.clone() * z;
            acc += &m_eq;
        }
        acc
    }
}
