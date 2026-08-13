use crate::{
    MultiPoint,
    evals::{EvalsExt, Mles},
    oracles::{EvalLocation, Oracle, SumcheckFunction, partial::Nature},
};
use ark_ff::Field;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct TestingOracle<F: Field, SF: SumcheckFunction<F>> {
    vars: usize,
    evals: Rc<Vec<SF::Mles<F>>>,
    data: SF::Data,
}

#[derive(Clone, Copy, Debug)]
pub struct TestingNature;

impl Nature for TestingNature {}

impl From<TestingNature> for EvalLocation {
    fn from(_: TestingNature) -> Self {
        EvalLocation::Witness
    }
}

impl<F, SF> Oracle<F> for TestingOracle<F, SF>
where
    F: Field,
    SF: SumcheckFunction<F, Natures = TestingNature>,
{
    type Function = SF;

    type Instance = ();

    type Witness = Vec<SF::Mles<F>>;

    type Nature = TestingNature;

    fn instance_evals(_: &()) -> Mles<Self::Function, F> {
        SF::map_evals(&SF::natures(), |_| F::ZERO)
    }

    fn structure(&self) -> Rc<Vec<Mles<Self::Function, F>>> {
        Rc::clone(&self.evals)
    }

    fn data(&self) -> &SF::Data {
        &self.data
    }

    fn vars(&self) -> usize {
        self.vars
    }

    fn oracle_params(&self) {}

    fn eval(
        &self,
        point: &MultiPoint<F>,
        _: &(),
        witness: &Self::Witness,
    ) -> Mles<Self::Function, F> {
        EvalsExt::eval(witness, point)
    }

    fn witness_from_evals(evals: Vec<Mles<Self::Function, F>>) -> Self::Witness {
        evals
    }

    fn natures(&self) -> Mles<Self::Function, Self::Nature> {
        SF::natures()
    }
}

impl<F: Field, SF: SumcheckFunction<F>> TestingOracle<F, SF> {
    pub fn new(vars: usize, data: SF::Data) -> Self {
        let zero = SF::map_evals(&SF::natures(), |_| F::ZERO);
        let evals = vec![zero; 1 << vars];
        let evals = Rc::new(evals);
        Self { vars, evals, data }
    }
}
