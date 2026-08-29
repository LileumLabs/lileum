use crate::{
    evals::{Evals, Mles},
    oracles::{EvalLocation, Oracle},
};
use alloc::vec::Vec;
use ark_ff::Field;
use core::{marker::PhantomData, ops::Add};
use reduction::{Message, Relation};

fn merge<F: Field, O: Oracle<F>>(
    structure: &Mles<O::Function, F>,
    instance: &Mles<O::Function, F>,
    witness: &Mles<O::Function, F>,
    locations: &Mles<O::Function, EvalLocation>,
) -> Mles<O::Function, F> {
    use EvalLocation::*;

    let evals: Mles<O::Function, F> = <O::Function as Evals>::combine3(
        [structure, instance],
        locations,
        |s: &F, i, l: &EvalLocation| match l {
            Structure => *s,
            Instance => *i,
            Witness => F::ZERO,
        },
    );

    <O::Function as Evals>::combine3(
        [&evals, witness],
        locations,
        |e: &F, w, l: &EvalLocation| match l {
            Structure | Instance => *e,
            Witness => *w,
        },
    )
}

pub(crate) fn oracle_evals<F: Field, O: Oracle<F>>(
    oracle: &O,
    instance: &O::Instance,
    witness: &[Mles<O::Function, F>],
) -> Vec<F> {
    let locations: Mles<O::Function, O::Nature> = oracle.natures();
    let locations: Mles<O::Function, EvalLocation> =
        <O::Function as Evals>::map_evals(&locations, |n: &O::Nature| (*n).into());

    let mle = oracle.structure();
    assert_eq!(mle.len(), witness.len());

    let instance_evals = O::instance_evals(instance);

    mle.iter()
        .zip(witness)
        .map(|(structure, witness)| {
            let evals = merge::<F, O>(structure, &instance_evals, witness, &locations);
            oracle.call_function(&evals)
        })
        .collect()
}

#[derive(Clone, Copy, Debug)]
/// An instance in the sumcheck relation, consting of the
/// claimed sum of the evaluations of the oracle over the
/// domain. And the instance of the oracle.
pub struct SumcheckInstance<F: Field, O: Oracle<F>> {
    /// The claimed sum.
    pub(crate) sum: F,
    pub(crate) oracle_instance: O::Instance,
}

impl<F: Field, O: Oracle<F>> SumcheckInstance<F, O> {
    pub fn new(sum: F, oracle_instance: O::Instance) -> Self {
        Self {
            sum,
            oracle_instance,
        }
    }
}

impl<F: Field, O: Oracle<F>> Message<F> for SumcheckInstance<F, O> {
    type Params = <O::Instance as Message<F>>::Params;

    type Error = <O::Instance as Message<F>>::Error;

    fn len(params: &Self::Params) -> usize {
        1 + O::Instance::len(params)
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        let mut elems = self.oracle_instance.to_field_elements(params)?;
        elems.insert(0, self.sum);
        Ok(elems)
    }
}

/// The sumcheck relation over a given oracle.
#[derive(Clone, Copy, Debug)]
pub struct SumcheckRelation<F, O>(PhantomData<(F, O)>);

impl<F: Field, O: Oracle<F>> Relation for SumcheckRelation<F, O> {
    type Structure = O;

    type Instance = SumcheckInstance<F, O>;

    type Witness = Vec<Mles<O::Function, F>>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let sum = oracle_evals(structure, &instance.oracle_instance, witness)
            .into_iter()
            .fold(F::ZERO, Add::add);

        sum == instance.sum
    }
}
