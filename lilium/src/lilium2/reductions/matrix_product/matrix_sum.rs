use crate::lilium2::reductions::matrix_product::function::MatrixSumEvals;
use ark_ff::Field;
use ccs::matrix::Matrix;
use commit::commit2::CommitmentScheme;
use spark::spark3::{FlexibleSparkRelation, FlexibleSparkStructure, SparkInstance};
use sponge::sponge::Duplex;
use std::{marker::PhantomData, rc::Rc};
use sumcheck::{
    eq::eq,
    polynomials::MultiPoint,
    sumcheck2::oracles::{
        partial::{Nature, OracleEval, OracleParams, PartialOracle, PartialQueryInstance},
        EvalLocation, UnexpectedVars,
    },
};
use transcript::reduction2::{
    GuardedProof, Message, ProverOutput, Reduction, Relation, Transcript, TranscriptBuilder,
    VerifierTranscript,
};

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
pub struct MatrixSumInstance<F: Field> {
    point: MultiPoint<F>,
}

impl<F: Field> MatrixSumInstance<F> {
    pub fn new(point: MultiPoint<F>) -> Self {
        Self { point }
    }
}

impl<F: Field> Message<F> for MatrixSumInstance<F> {
    type Params = OracleParams;

    type Error = UnexpectedVars;

    fn len(params: &Self::Params) -> usize {
        params.vars
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        let MatrixSumInstance { point } = self;
        point.to_field_elements(&params.vars)
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
    type Instance = MatrixSumInstance<F>;

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

    type Instance = PartialQueryInstance<F, MatrixSumEvals<(), N>, MatrixSumInstance<F>>;

    type Witness = Vec<MatrixSumEvals<F, N>>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let MatrixSumEvals {
            matrices,
            z,
            challenge,
        } = instance.evals();
        assert!(z.is_none());
        assert!(challenge.is_none());

        let matrix_evals: Option<[F; N]> = matrices
            .iter()
            .cloned()
            .collect::<Option<Vec<F>>>()
            .map(TryInto::try_into)
            .and_then(Result::ok);

        let matrix_evals: [F; N] = if let Some(e) = matrix_evals {
            e
        } else {
            return false;
        };

        let rx = &instance.oracle_instance().point;
        let ry = instance.point();

        let rx = eq(rx);
        let ry = eq(ry);
        for (matrix, expected_eval) in structure.matrices.iter().zip(matrix_evals) {
            //TODO: maybe compare with witness.
            let _ = witness;
            let partially_evaluated_matrix =
                MatrixSumEvals::<F, N>::matrix_partial_eval(matrix, &rx);
            let eval = ry
                .iter()
                .zip(partially_evaluated_matrix)
                .fold(F::ZERO, |acc, (ry, eval)| acc + eval * ry);
            if eval != expected_eval {
                return false;
            }
        }

        true
    }
}

impl<F, C, const N: usize> Reduction<F, MatrixSumQuery<F, C, N>, [FlexibleSparkRelation<F>; N]>
    for MatrixSumOracle<F, C, N>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = ();

    type Proof = ();

    type Error = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        _builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        todo!()
    }

    fn verifier_key(
        _structure_1: &Self,
        _structure_2: &[FlexibleSparkStructure<F>; N],
    ) -> Self::VerifierKey {
        todo!()
    }

    fn key_pair(
        _structure_1: &Self,
        _structure_2: &[FlexibleSparkStructure<F>; N],
    ) -> (Self::VerifierKey, Self::ProverKey) {
        todo!()
    }

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: <MatrixSumQuery<F, C, N> as Relation>::Instance,
        _witness: <MatrixSumQuery<F, C, N> as Relation>::Witness,
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<[FlexibleSparkRelation<F>; N], Self::Proof> {
        todo!()
    }

    fn verify<S: Duplex<F>>(
        _key: &Self::VerifierKey,
        _instance: <MatrixSumQuery<F, C, N> as Relation>::Instance,
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<[SparkInstance<F>; N], Self::Error> {
        todo!()
    }
}
