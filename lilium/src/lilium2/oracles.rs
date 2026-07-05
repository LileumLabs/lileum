use ark_ff::Field;
use ccs::matrix::Matrix;
use commit::commit2::oracle::CommittedOracle;
use std::{marker::PhantomData, ops::Add, rc::Rc};
use sumcheck::{
    polynomials::MultiPoint,
    sumcheck2::{
        evals::EvalsCore,
        oracles::{
            composite::CompositeOracle,
            core::CoreOracle,
            partial::{Nature, OracleEval, OracleParams, PartialOracle, PartialQueryInstance},
            EvalLocation, SumcheckFunction,
        },
    },
};
use transcript::reduction2::{Message, NoError, Relation};

#[derive(Clone, Debug)]
pub struct MatrixProductOracle<F, SF, const N: usize>
where
    F: Field,
    SF: SumcheckFunction<F>,
{
    matrices: [Rc<Matrix>; N],
    vector: SF::Mles<bool>,

    _f: PhantomData<F>,
}

impl<F, SF, const N: usize> MatrixProductOracle<F, SF, N>
where
    F: Field,
    SF: SumcheckFunction<F>,
{
    pub fn matrices(&self) -> &[Rc<Matrix>; N] {
        &self.matrices
    }
}

#[derive(Clone, Copy, Debug)]
pub struct MatrixProductInstance;

impl<F: Field> Message<F> for MatrixProductInstance {
    type Params = OracleParams;

    type Error = NoError;

    fn len(_: &Self::Params) -> usize {
        0
    }

    fn to_field_elements(&self, _: &Self::Params) -> Result<Vec<F>, Self::Error> {
        Ok(vec![])
    }
}

#[derive(Clone, Copy, Debug)]
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

#[derive(Clone, Copy, Debug)]
pub struct Key;

impl<F, SF, const N: usize> From<MatrixProductOracle<F, SF, N>> for Key
where
    F: Field,
    SF: SumcheckFunction<F>,
{
    fn from(_: MatrixProductOracle<F, SF, N>) -> Self {
        Key
    }
}

impl<F, SF, const N: usize> PartialOracle<F, SF> for MatrixProductOracle<F, SF, N>
where
    F: Field,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
{
    type Instance = MatrixProductInstance;

    type VerifierKey = Key;

    type Builder = Self;

    type Nature = MatrixNature;

    type QueryRelation = MatrixOracleQuery<F, SF, N>;

    fn build(builder: Self, _: &SF::Data, _: Rc<Vec<<SF>::Mles<F>>>) -> Self {
        builder
    }

    fn instance_evals(_: &Self::Instance) -> <SF>::Mles<F> {
        SF::map_evals(&SF::natures(), |_| F::ZERO)
    }

    fn evals(
        _key: &Key,
        _instance: &Self::Instance,
        _point: &MultiPoint<F>,
    ) -> <SF>::Mles<OracleEval<F>> {
        let natures = SF::natures();

        SF::map_evals(&natures, |nature| {
            let nature: Option<MatrixNature> = nature.into_dynamic().into();
            match nature {
                Some(MatrixNature) => OracleEval::ProverProvided,
                None => OracleEval::None,
            }
        })
    }
}

pub struct MatrixOracleQuery<F, SF, const N: usize>(PhantomData<(F, SF)>);

impl<F, SF, const N: usize> Relation for MatrixOracleQuery<F, SF, N>
where
    F: Field,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
{
    type Structure = MatrixProductOracle<F, SF, N>;

    type Instance = PartialQueryInstance<F, SF, MatrixProductInstance>;

    type Witness = Vec<SF::Mles<F>>;

    fn check(structure: &Self::Structure, _: &Self::Instance, witness: &Self::Witness) -> bool {
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

        true
    }
}

pub type FlcsOracle<F, C, SF, const IO: usize> = CompositeOracle<
    F,
    SF,
    CommittedOracle<F, C, SF>,
    CompositeOracle<F, SF, CoreOracle<F, SF>, MatrixProductOracle<F, SF, IO>>,
>;
