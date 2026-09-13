use crate::{
    circuit_builder::WiredGate,
    gates::{self, BinaryGate},
};
use alloc::vec::{IntoIter, Vec};
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use commit::{
    CommitmentScheme,
    oracle::{CommittedNature, CommittedOracle, CommittedOracleInstance},
};
use core::{fmt::Debug, marker::PhantomData};
use reduction::{
    Argument, GuardedProof, ProverOutput, Reduction, Relation, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;
use sumcheck::{
    OracleQueryInstance, SumcheckMessage, SumcheckVerifierKey, Var,
    evals::{Evals, EvalsCore},
    oracles::{
        SumcheckFunction,
        composite::{
            CompositeOracle, CompositeOracleInstance, CompositeReductionKey, Either, ProverEvals,
        },
        core::{CoreNature, CoreOracle, CoreOracleInstance, SmallFunctions},
    },
    zerocheck::{ZerocheckReduction, ZerocheckSumcheckReduction},
};
use sumcheck_derive::EvalsCore;

#[derive(Clone, Debug, Default, EvalsCore)]
pub struct Mles<V: Clone + Debug> {
    table: V,
    trace: V,
    selectors: [V; 2],
    //TODO:enforce
    lookups: [V; 3],
}

impl<V: Clone + Debug + CanonicalSerialize> CanonicalSerialize for Mles<V> {
    fn serialize_with_mode<W: ark_serialize::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        let Self {
            table,
            trace,
            selectors,
            lookups,
        } = self;
        table.serialize_with_mode(&mut writer, compress)?;
        trace.serialize_with_mode(&mut writer, compress)?;
        selectors.serialize_with_mode(&mut writer, compress)?;
        lookups.serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        let Self {
            table,
            trace,
            selectors,
            lookups,
        } = self;
        table.serialized_size(compress)
            + trace.serialized_size(compress)
            + selectors.serialized_size(compress)
            + lookups.serialized_size(compress)
    }
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

impl<F: Field> SmallFunctions<F> for Mles<()> {
    fn small_functions() -> Self::Mles<Option<sumcheck::oracles::core::Func<F>>> {
        todo!()
    }
}

pub struct SpreadsheetRelation<F, C>(PhantomData<(F, C)>);

impl<F, C> SpreadsheetRelation<F, C>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    pub fn core_oracle_instance(vars: usize) -> CoreOracleInstance<F, Mles<()>> {
        let coefficients = Mles::map_evals(&Mles::<()>::default(), |_| Vec::new());
        CoreOracleInstance::new(&coefficients, vars)
    }

    pub fn committed_oracle_instance(
        data_commit: C::Commitment,
        trace_commit: C::Commitment,
    ) -> CommittedOracleInstance<F, C, Mles<()>> {
        let commits = Mles {
            table: Some(data_commit),
            trace: Some(trace_commit),
            selectors: [(); 2].map(|_| None),
            lookups: [(); 3].map(|_| None),
        };
        CommittedOracleInstance::new(commits)
    }
}

pub struct SpreadsheetStructure<C> {
    data_table_size: usize,
    gates: Vec<WiredGate>,
    pcs: C,
}

impl<F: Field, C: CommitmentScheme<F>> Relation for SpreadsheetRelation<F, C> {
    type Structure = SpreadsheetStructure<C>;

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

type Oracle<F, C, SF = Mles<()>> =
    CompositeOracle<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;
type CompositeKey<F, C, SF = Mles<()>> =
    CompositeReductionKey<F, Mles<()>, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

#[derive(Clone, Debug)]
pub struct Proof<F: Field, C: CommitmentScheme<F>> {
    trace_committment: C::Commitment,
    sumcheck: Vec<SumcheckMessage<F>>,
    composite: ProverEvals<F>,
    open_proof: C::Proof,
}

#[derive(CanonicalSerialize)]
pub struct VerifierKey<F: Field, C: CommitmentScheme<F>> {
    zerocheck_key: usize,
    sumcheck: SumcheckVerifierKey<F, Oracle<F, C>>,
    composite: CompositeKey<F, C>,
    pcs: C::VerifierKey,
}

impl<F: Field, C: CommitmentScheme<F>> Reduction<F, Self, ()> for SpreadsheetRelation<F, C> {
    type ProverKey = ();

    type VerifierKey = VerifierKey<F, C>;

    type Proof = Proof<F, C>;

    type Error = ();

    type Params = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        _builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        todo!()
    }

    fn verifier_key(_structure: &SpreadsheetStructure<C>) -> Self::VerifierKey {
        todo!()
    }

    fn key_pair(_structure: &SpreadsheetStructure<C>) -> (Self::VerifierKey, Self::ProverKey) {
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
        key: &Self::VerifierKey,
        instance: C::Commitment,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<(), Self::Error> {
        let (trace_commit, []) = transcript
            .receive_message(|proof| proof.trace_committment.clone(), &proof, &())
            .unwrap();

        let oracle_instance = CompositeOracleInstance {
            oracle1_instance: Self::core_oracle_instance(key.sumcheck.vars()),
            oracle2_instance: Self::committed_oracle_instance(instance, trace_commit),
        };
        let instance = oracle_instance;
        let instance = ZerocheckReduction::verify(
            &key.zerocheck_key,
            instance,
            GuardedProof::empty(),
            transcript,
        )
        .unwrap();

        let instance: OracleQueryInstance<F, _> = ZerocheckSumcheckReduction::verify(
            &key.sumcheck,
            instance,
            proof.clone().map(|proof| proof.sumcheck),
            transcript,
        )
        .unwrap();

        let (core_instance, committed_instance) = CompositeOracle::verify(
            &key.composite,
            instance,
            proof.clone().map(|proof| proof.composite),
            transcript,
        )
        .unwrap();

        let () = CoreOracle::verify(
            key.composite.p1_key(),
            core_instance,
            GuardedProof::empty(),
            transcript,
        )
        .unwrap();

        let open_instance = CommittedOracle::verify(
            key.composite.p2_key(),
            committed_instance,
            GuardedProof::empty(),
            transcript,
        )
        .unwrap();

        let () = C::verify(
            &key.pcs,
            open_instance,
            proof.map(|proof| proof.open_proof),
            transcript,
        )
        .unwrap();
        Ok(())
    }
}

impl<F: Field, C: CommitmentScheme<F>> Argument<F, Self> for SpreadsheetRelation<F, C> {}
