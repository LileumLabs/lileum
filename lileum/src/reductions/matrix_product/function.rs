use crate::reductions::matrix_product::matrix_sum::{MatrixSumNature, MatrixSumOracle};
use ark_ff::Field;
use commit::oracle::{CommittedNature, CommittedOracle};
use lcs::matrix::Matrix;
use std::{fmt::Debug, vec::IntoIter};
use sumcheck::{
    MultiPoint, Var,
    eq::eq,
    evals::{Evals, EvalsCore},
    oracles::{
        SumcheckFunction,
        composite::{CompositeOracle, Either},
        core::{CoreNature, CoreOracle},
        partial::OracleEval,
    },
};
use sumcheck_derive::EvalsCore;

#[derive(Clone, Copy, Debug, PartialEq, Eq, EvalsCore)]
pub struct MatrixSumEvals<V: Clone + Debug, const N: usize> {
    pub matrices: [V; N],
    pub z: V,
    pub challenge: V,
}

impl<V: Clone + Debug + Default, const N: usize> Default for MatrixSumEvals<V, N> {
    fn default() -> Self {
        Self {
            matrices: [(); N].map(|_| Default::default()),
            z: Default::default(),
            challenge: Default::default(),
        }
    }
}

impl<F: Field, const N: usize> MatrixSumEvals<F, N> {
    pub(crate) fn zero() -> Self {
        Self {
            matrices: [F::ZERO; N],
            z: F::ZERO,
            challenge: F::ZERO,
        }
    }

    pub fn matrix_partial_eval(matrix: &Matrix, rx: &[F]) -> Vec<F> {
        let mut res = vec![F::zero(); rx.len()];
        for (j, i) in matrix.iter() {
            res[i] += rx[j];
        }
        res
    }

    pub fn witness(
        structure: &[Self],
        matrices: [&Matrix; N],
        z: &[F],
        rx: &MultiPoint<F>,
    ) -> Vec<Self> {
        let mut witness = structure.to_vec();
        let rx = eq(rx);
        for (i, matrix) in matrices.iter().enumerate() {
            let colum_evals = Self::matrix_partial_eval(matrix, &rx);
            for (col, eval) in witness.iter_mut().zip(colum_evals) {
                col.matrices[i] = eval;
            }
        }
        for (col, eval) in witness.iter_mut().zip(z) {
            col.z = *eval;
        }
        witness
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

impl<F: Field, const N: usize> MatrixSumEvals<Vec<F>, N> {
    pub fn coefficients(challenge: F) -> Self {
        Self {
            challenge: vec![challenge],
            ..Default::default()
        }
    }
}

impl<T: Clone + Debug, const N: usize> MatrixSumEvals<Option<T>, N> {
    pub fn core_oracle_functions() -> Self {
        Self {
            matrices: [(); N].map(|_| None),
            z: None,
            challenge: None,
        }
    }
}

pub type Oracle<F, SF, C, const N: usize> = CompositeOracle<
    F,
    SF,
    MatrixSumOracle<F, C, N>,
    CompositeOracle<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>,
>;

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
