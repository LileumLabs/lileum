use ark_ff::Field;
use ccs::matrix::Matrix;
use commit::commit2::{
    oracle::{
        CommittedNature, CommittedOracle, CommittedOracleInstance, CommittedQueryRelation,
        VerifierKey as CommittedVerifierKey,
    },
    CommitmentScheme,
};
use std::{marker::PhantomData, ops::Add, rc::Rc};
use sumcheck::{
    evals::EvalsCore,
    folding::{FieldFolder, Foldable},
    oracles::{
        composite::{CompositeOracle, Either},
        core::CoreOracle,
        partial::{Nature, OracleEval, OracleParams, PartialOracle, PartialQueryInstance},
        EvalLocation, Oracle, SumcheckFunction,
    },
    MultiPoint,
};
use transcript::{Message, NoError, Relation};

#[derive(Clone, Debug)]
pub struct MatrixProductOracle<F, C, SF, const N: usize>
where
    F: Field,
    SF: SumcheckFunction<F>,
    C: CommitmentScheme<F>,
{
    matrices: [Rc<Matrix>; N],
    vector: SF::Mles<bool>,
    committed_oracle: CommittedOracle<F, C, SF>,
    pcs: C,
    vars: usize,
}

impl<F, SF, C, const N: usize> MatrixProductOracle<F, C, SF, N>
where
    F: Field,
    SF: SumcheckFunction<F>,
    C: CommitmentScheme<F>,
{
    pub fn new(
        matrices: [Rc<Matrix>; N],
        vector: SF::Mles<bool>,
        committed_oracle: CommittedOracle<F, C, SF>,
        pcs: C,
        vars: usize,
    ) -> Self {
        Self {
            matrices,
            vector,
            committed_oracle,
            pcs,
            vars,
        }
    }

    pub fn matrices(&self) -> &[Rc<Matrix>; N] {
        &self.matrices
    }

    pub fn committed_oracle(&self) -> &CommittedOracle<F, C, SF> {
        &self.committed_oracle
    }

    /// A filter to select the vector MLE.
    pub fn vector(&self) -> &SF::Mles<bool> {
        &self.vector
    }

    pub fn pcs(&self) -> &C {
        &self.pcs
    }

    pub fn vars(&self) -> usize {
        self.vars
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MatrixProductInstance<F: Field, C: CommitmentScheme<F>>(pub(crate) C::Commitment);

impl<F: Field, C: CommitmentScheme<F>> Message<F> for MatrixProductInstance<F, C> {
    type Params = OracleParams;

    type Error = NoError;

    fn len(_: &Self::Params) -> usize {
        C::Commitment::len(&())
    }

    fn to_field_elements(&self, _: &Self::Params) -> Result<Vec<F>, Self::Error> {
        self.0.to_field_elements(&())
    }
}

impl<F: Field, C: CommitmentScheme<F>> Foldable<F> for MatrixProductInstance<F, C> {
    fn fold(folder: &FieldFolder<F>, a: Self, b: Self) -> Self {
        Self(folder.fold_abstract(a.0, b.0))
    }
}

#[derive(Clone, Copy, Debug)]
// pub struct MatrixNature;
pub struct MatrixNature;

impl Nature for MatrixNature {
    fn prover_provided(self) -> bool {
        true
    }
}

impl From<MatrixNature> for EvalLocation {
    fn from(_: MatrixNature) -> Self {
        EvalLocation::Witness
    }
}

#[derive(Clone, Debug)]
pub struct Key<F: Field, C: CommitmentScheme<F>, SF: SumcheckFunction<F>> {
    vector: SF::Mles<bool>,
    committed_key: CommittedVerifierKey<F, C>,
}

impl<F, C, SF> Key<F, C, SF>
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
{
    pub fn convert_instance(
        &self,
        instance: &MatrixProductInstance<F, C>,
    ) -> CommittedOracleInstance<F, C, SF> {
        let commit = &instance.0;
        let commits = SF::map_evals(&self.vector, |is_vector| {
            is_vector.then_some(commit.clone())
        });
        CommittedOracleInstance::new(commits)
    }
}

impl<F, SF, C, const N: usize> From<MatrixProductOracle<F, C, SF, N>> for Key<F, C, SF>
where
    F: Field,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
    C: CommitmentScheme<F>,
{
    fn from(oracle: MatrixProductOracle<F, C, SF, N>) -> Self {
        let committed_key = CommittedVerifierKey::from(oracle.committed_oracle);
        let vector = oracle.vector;
        Self {
            committed_key,
            vector,
        }
    }
}

impl<F, C, SF, const N: usize> PartialOracle<F, SF> for MatrixProductOracle<F, C, SF, N>
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F>,
    SF::Natures: Into<EvalLocation> + Nature,
{
    type Instance = MatrixProductInstance<F, C>;

    type VerifierKey = Key<F, C, SF>;

    type Builder = Self;

    type Nature = Either<CommittedNature, MatrixNature>;

    type QueryRelation = MatrixOracleQuery<F, C, SF, N>;

    fn build(builder: Self, _: &SF::Data, _: Rc<Vec<<SF>::Mles<F>>>) -> Self {
        builder
    }

    fn instance_evals(instance: &Self::Instance) -> <SF>::Mles<F> {
        let MatrixProductInstance(commit) = instance;
        let instance = CommittedOracleInstance::new_single_commit(commit.clone());
        CommittedOracle::<F, C, SF>::instance_evals(&instance)
    }

    fn evals(
        key: &Key<F, C, SF>,
        instance: &Self::Instance,
        point: &MultiPoint<F>,
    ) -> <SF>::Mles<OracleEval<F>> {
        let natures = SF::natures();
        let committed_instance = &key.convert_instance(instance);

        let committed_evals = CommittedOracle::evals(&key.committed_key, committed_instance, point);

        SF::combine(&committed_evals, &natures, |eval, nature| {
            let nature: Option<MatrixNature> = nature.into_dynamic().into();
            match nature {
                Some(MatrixNature) => OracleEval::ProverProvided,
                None => *eval,
            }
        })
    }
}

pub struct MatrixOracleQuery<F, C, SF, const N: usize>(PhantomData<(F, C, SF)>);

impl<F, C, SF, const N: usize> Relation for MatrixOracleQuery<F, C, SF, N>
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature + Into<EvalLocation>,
{
    type Structure = MatrixProductOracle<F, C, SF, N>;

    type Instance = PartialQueryInstance<F, SF, MatrixProductInstance<F, C>>;

    type Witness = Vec<SF::Mles<F>>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let vector_count = structure
            .vector
            .clone()
            .flatten_vec()
            .into_iter()
            .fold(0, |acc, x| if x { acc + 1 } else { acc });

        if vector_count != 1 {
            return false;
        }

        let vector = {
            let mut vector = vec![];
            let vector_filter = &structure.vector;
            //TODO: check the nature is CommittedNature::Witness
            for witness in witness {
                let filtered =
                    SF::combine(witness, vector_filter, |w, f| if *f { *w } else { F::ZERO });
                vector.push(filtered.flatten_vec().into_iter().fold(F::ZERO, Add::add));
            }
            vector
        };

        let matrix_indices: SF::Mles<Option<usize>> = {
            let mut next = 0;
            let indices = SF::natures()
                .flatten_vec()
                .into_iter()
                .map(|nature| {
                    let nature = nature.into_dynamic().into();
                    nature.map(|_: MatrixNature| {
                        next += 1;
                        next - 1
                    })
                })
                .collect();
            if next != N {
                return false;
            }
            SF::Mles::unflatten_vec(indices)
        };

        for (i, matrix) in structure.matrices.iter().enumerate() {
            let product = matrix.as_ref() * vector.as_slice();
            assert_eq!(product.len(), witness.len());

            for (product, witness) in product.into_iter().zip(witness) {
                let expected = SF::combine(&matrix_indices, witness, |index, witness| {
                    index
                        .map(|index| if index == i { Some(*witness) } else { None })
                        .flatten()
                });
                let expected = expected
                    .flatten_vec()
                    .into_iter()
                    .fold(None, |acc, e| acc.xor(e));

                if product != expected.unwrap() {
                    return false;
                }
            }
        }

        // Check inner oracle
        let commit = instance.oracle_instance().0.clone();
        let evals = SF::combine(&SF::natures(), instance.evals(), |nature, eval| {
            let nature: Option<MatrixNature> = nature.into_dynamic().into();
            match nature {
                Some(MatrixNature) => None,
                None => *eval,
            }
        });
        let oracle_instance = CommittedOracleInstance::new_single_commit(commit);
        let point = instance.point();
        let instance = PartialQueryInstance::new(evals, oracle_instance, point);
        CommittedQueryRelation::check(&structure.committed_oracle, &instance, witness);

        true
    }
}

pub type FlcsOracle<F, C, SF, const IO: usize> =
    CompositeOracle<F, SF, CoreOracle<F, SF>, MatrixProductOracle<F, C, SF, IO>>;

pub type FlcsOracleInstance<F, C, SF, const IO: usize> =
    <FlcsOracle<F, C, SF, IO> as Oracle<F>>::Instance;

pub type FlcsOracleParams<F, C, SF, const IO: usize> =
    <FlcsOracleInstance<F, C, SF, IO> as Message<F>>::Params;
