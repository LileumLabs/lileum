use crate::lilium2::reductions::matrix_product::function::MatrixSumEvals;
use ark_ff::Field;
use ccs::matrix::Matrix;
use commit::commit2::CommitmentScheme;
use std::{marker::PhantomData, rc::Rc};
use sumcheck::{
    polynomials::MultiPoint,
    sumcheck2::oracles::{
        partial::{Nature, OracleEval, OracleParams, PartialOracle, PartialQueryInstance},
        EvalLocation, UnexpectedVars,
    },
};
use transcript::reduction2::{Message, Relation};

/// An oracle to partially evaluated matrices.
/// For matrix M(X,Y) and point r, it can be used to to run
/// sumcheck over M(r,Y).
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct MatrixSumOracle<F, C, const N: usize> {
    matrices: [Rc<Matrix>; N],
    _phantom: PhantomData<(F, C)>,
}

impl<F, C, const N: usize> MatrixSumOracle<F, C, N> {
    #[allow(dead_code)]
    pub fn new(matrices: [Rc<Matrix>; N]) -> Self {
        Self {
            matrices,
            _phantom: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MatrixSumInstance<F: Field, C: CommitmentScheme<F>> {
    point: MultiPoint<F>,
    z: C::Commitment,
}

impl<F: Field, C: CommitmentScheme<F>> Message<F> for MatrixSumInstance<F, C> {
    type Params = OracleParams;

    type Error = UnexpectedVars;

    fn len(params: &Self::Params) -> usize {
        params.vars + C::Commitment::len(&())
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        let MatrixSumInstance { point, z } = self;
        let Ok(mut elems) = z.to_field_elements(&());
        elems.extend(point.to_field_elements(&params.vars)?);
        Ok(elems)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct MatrixSumNature;

impl From<MatrixSumNature> for EvalLocation {
    fn from(_: MatrixSumNature) -> Self {
        EvalLocation::Witness
    }
}

impl Nature for MatrixSumNature {
    fn prover_provided(self) -> bool {
        true
    }
}

impl<F, C, const N: usize> PartialOracle<F, MatrixSumEvals<(), N>> for MatrixSumOracle<F, C, N>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Instance = MatrixSumInstance<F, C>;

    type VerifierKey = Self;

    type Builder = Self;

    type Nature = MatrixSumNature;

    type QueryRelation = MatrixSumQuery<F, C, N>;

    fn build(builder: Self::Builder, _: &(), _: Rc<Vec<MatrixSumEvals<F, N>>>) -> Self {
        builder
    }

    fn instance_evals(_: &Self::Instance) -> MatrixSumEvals<F, N> {
        MatrixSumEvals::zero()
    }

    fn evals(
        _key: &Self::VerifierKey,
        _instance: &Self::Instance,
        _point: &MultiPoint<F>,
    ) -> MatrixSumEvals<OracleEval<F>, N> {
        MatrixSumEvals::evals()
    }
}

pub struct MatrixSumQuery<F, C, const N: usize>(PhantomData<(F, C)>);

impl<F: Field, C: CommitmentScheme<F>, const N: usize> Relation for MatrixSumQuery<F, C, N> {
    type Structure = MatrixSumOracle<F, C, N>;

    type Instance = PartialQueryInstance<F, MatrixSumEvals<(), N>, MatrixSumInstance<F, C>>;

    type Witness = Vec<MatrixSumEvals<F, N>>;

    fn check(
        _structure: &Self::Structure,
        _instance: &Self::Instance,
        _witness: &Self::Witness,
    ) -> bool {
        todo!()
    }
}
