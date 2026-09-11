use crate::gates::{self, BinaryGate};
use alloc::vec::{IntoIter, Vec};
use ark_ff::Field;
use commit::oracle::CommittedNature;
use core::fmt::Debug;
use sumcheck::{
    Var,
    evals::{Evals, EvalsCore},
    oracles::{SumcheckFunction, composite::Either, core::CoreNature},
};
use sumcheck_derive::EvalsCore;

#[derive(Clone, Debug, EvalsCore)]
struct Mles<V: Clone + Debug> {
    table: V,
    trace: V,
    selectors: [V; 2],
    //TODO:enforce
    lookups: [V; 3],
}

impl<F: Field> SumcheckFunction<F> for Mles<()> {
    type Natures = Either<CoreNature, CommittedNature>;

    type Data = ();

    fn natures() -> Self::Mles<Self::Natures> {
        use Either::*;

        Mles {
            table: Right(CommittedNature::Witness),
            trace: Right(CommittedNature::Witness),
            selectors: [Right(CommittedNature::Structure); 2],
            lookups: [Right(CommittedNature::Witness); 3],
        }
    }

    fn function<V: Var<F> + Debug>(_: &(), evals: &Self::Mles<V>) -> V {
        let Mles {
            table: _,
            trace: _,
            selectors,
            lookups,
        } = evals;
        let [a, b, c] = lookups;
        let constraints = gates::Add::check(a, b, c) * &selectors[0];
        constraints + gates::Eq::check(a, b, c) * &selectors[1]
    }
}
