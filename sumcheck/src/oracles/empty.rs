use crate::{
    MultiPoint,
    oracles::{
        EvalLocation, SumcheckFunction,
        partial::{Nature, OracleEval, OracleParams, PartialOracle, PartialQueryInstance},
    },
};
use alloc::{rc::Rc, vec::Vec};
use ark_ff::Field;
use core::marker::PhantomData;
use reduction::{Message, NoError, Relation};

// #[derive(Clone, Copy, Debug)]
// pub struct EmptyOracle<F, SF>(PhantomData<(F, SF)>);

#[derive(Clone, Copy, Debug)]
pub enum NoNature {}

impl Nature for NoNature {}

impl From<NoNature> for EvalLocation {
    fn from(val: NoNature) -> Self {
        match val {}
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EmptyInstance;

impl<F: Field> Message<F> for EmptyInstance {
    type Params = OracleParams;

    type Error = NoError;

    fn len(_params: &Self::Params) -> usize {
        0
    }

    fn to_field_elements(&self, _params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        Ok(Vec::new())
    }
}

pub struct EmptyRelation<F, SF>(PhantomData<(F, SF)>);

impl<F: Field, SF: SumcheckFunction<F>> Relation for EmptyRelation<F, SF> {
    type Structure = ();

    type Instance = PartialQueryInstance<F, SF, EmptyInstance>;

    type Witness = Vec<SF::Mles<F>>;

    fn check(
        _structure: &Self::Structure,
        _instance: &Self::Instance,
        _witness: &Self::Witness,
    ) -> bool {
        true
    }
}

impl<F: Field, SF: SumcheckFunction<F>> PartialOracle<F, SF> for () {
    type Instance = EmptyInstance;

    type VerifierKey = ();

    type Nature = NoNature;

    type QueryRelation = EmptyRelation<F, SF>;

    type Builder = ();

    fn build(_: (), _: &SF::Data, _: Rc<Vec<SF::Mles<F>>>) -> Self {}

    fn instance_evals(_instance: &EmptyInstance) -> SF::Mles<F> {
        SF::map_evals(&SF::natures(), |_| F::ZERO)
    }

    fn evals(
        _key: &Self::VerifierKey,
        _instance: &Self::Instance,
        _point: &MultiPoint<F>,
    ) -> SF::Mles<OracleEval<F>> {
        SF::map_evals(&SF::natures(), |_| OracleEval::None)
    }
}
