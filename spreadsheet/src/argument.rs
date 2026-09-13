use crate::{
    circuit_builder::WiredGate,
    gates::{self, BinaryGate},
};
use alloc::vec::{IntoIter, Vec};
use ark_ff::Field;
use commit::{CommitmentScheme, oracle::CommittedNature};
use core::{fmt::Debug, marker::PhantomData};
use reduction::Relation;
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

pub struct SpreadsheetRelation<F, C>(PhantomData<(F, C)>);

pub struct SpreadsheetStructure<F: Field, C: CommitmentScheme<F>> {
    data_table_size: usize,
    gates: Vec<WiredGate>,
    pcs: C,
    _f: PhantomData<F>,
}

impl<F: Field, C: CommitmentScheme<F>> Relation for SpreadsheetRelation<F, C> {
    type Structure = SpreadsheetStructure<F, C>;

    type Instance = C::Commitment;

    type Witness = Vec<F>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        assert!(witness.len().is_power_of_two());
        if structure.data_table_size != witness.len() {
            return false;
        }

        let expected_commit = structure.pcs.commit_mle(witness);
        if &expected_commit != instance {
            return false;
        }

        WiredGate::check(&structure.gates, witness)
    }
}
