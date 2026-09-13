use crate::{
    circuit_builder::WiredGate,
    gates::{self, BinaryGate},
};
use alloc::vec::{IntoIter, Vec};
use ark_ff::Field;
use commit::{CommitmentScheme, oracle::CommittedNature};
use core::{fmt::Debug, marker::PhantomData};
use reduction::{
    Argument, GuardedProof, ProverOutput, Reduction, Relation, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;
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

impl<F: Field, C: CommitmentScheme<F>> Reduction<F, Self, ()> for SpreadsheetRelation<F, C> {
    type ProverKey = ();

    type VerifierKey = ();

    type Proof = ();

    type Error = ();

    type Params = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        _builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        todo!()
    }

    fn verifier_key(_structure: &SpreadsheetStructure<F, C>) -> Self::VerifierKey {
        todo!()
    }

    fn key_pair(_structure: &SpreadsheetStructure<F, C>) -> (Self::VerifierKey, Self::ProverKey) {
        todo!()
    }

    fn params(_key: &Self::VerifierKey) -> Self::Params {
        todo!()
    }

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: C::Commitment,
        _witness: Vec<F>,
        _transcript: &mut reduction::Transcript<F, S>,
    ) -> ProverOutput<(), Self::Proof> {
        todo!()
    }

    fn verify<S: Duplex<F>>(
        _key: &Self::VerifierKey,
        _instance: C::Commitment,
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<(), Self::Error> {
        todo!()
    }
}

impl<F: Field, C: CommitmentScheme<F>> Argument<F, Self> for SpreadsheetRelation<F, C> {}
