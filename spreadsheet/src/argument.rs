use crate::{
    circuit_builder::{DataOrTrace, WiredGate},
    gates::{self, BinaryGate},
};
use alloc::{
    rc::Rc,
    vec::{IntoIter, Vec},
};
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};
use commit::{
    CommitmentScheme,
    oracle::{CommittedNature, CommittedOracle, CommittedOracleInstance},
};
use common::power_of_two_vec::Pow2Vec;
use core::{fmt::Debug, marker::PhantomData};
use reduction::{
    Argument, GuardedProof, ProverOutput, Reduction, Relation, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;
use sumcheck::{
    MultiPoint, OracleQueryInstance, SumcheckError, SumcheckMessage, SumcheckVerifierKey, Var,
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
    fn small_functions() -> Mles<Option<fn(&[F], &MultiPoint<F>) -> F>> {
        Mles {
            table: None,
            trace: None,
            selectors: [(); 2].map(|_| None),
            lookups: [(); 3].map(|_| None),
        }
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
        lookup_commits: [C::Commitment; 3],
    ) -> CommittedOracleInstance<F, C, Mles<()>> {
        let commits = Mles {
            table: Some(data_commit),
            trace: Some(trace_commit),
            selectors: [(); 2].map(|_| None),
            lookups: lookup_commits.map(Some),
        };
        CommittedOracleInstance::new(commits)
    }
}

#[derive(Clone, Debug)]
pub struct SpreadsheetStructure<C> {
    gates: Pow2Vec<WiredGate>,
    pcs: C,
}

impl<F: Field, C: CommitmentScheme<F>> Relation for SpreadsheetRelation<F, C> {
    type Structure = SpreadsheetStructure<C>;

    type Instance = C::Commitment;

    type Witness = Pow2Vec<F>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        if witness.inner().len() != structure.gates.inner().len() {
            return false;
        }

        let expected_commit = structure.pcs.commit_mle(witness.inner());
        if &expected_commit != instance {
            return false;
        }

        WiredGate::check(structure.gates.inner(), witness.inner())
    }
}

type Oracle<F, C, SF = Mles<()>> =
    CompositeOracle<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;
type CompositeKey<F, C, SF = Mles<()>> =
    CompositeReductionKey<F, Mles<()>, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

#[derive(Clone, Debug)]
pub struct Proof<F: Field, C: CommitmentScheme<F>> {
    trace_committment: C::Commitment,
    lookup_commitments: [C::Commitment; 3],
    sumcheck: Vec<SumcheckMessage<F>>,
    composite: ProverEvals<F>,
    open_proof: C::Proof,
}

impl<F: Field, C: CommitmentScheme<F>> Valid for Proof<F, C>
where
    C::Commitment: CanonicalDeserialize,
    C::Proof: CanonicalDeserialize,
{
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        let Self {
            trace_committment,
            lookup_commitments,
            sumcheck,
            composite,
            open_proof,
        } = self;
        trace_committment.check()?;
        lookup_commitments.check()?;
        sumcheck.check()?;
        composite.check()?;
        open_proof.check()
    }
}

impl<F: Field, C: CommitmentScheme<F>> CanonicalDeserialize for Proof<F, C>
where
    C::Commitment: CanonicalDeserialize,
    C::Proof: CanonicalDeserialize,
{
    fn deserialize_with_mode<R: ark_serialize::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let trace_committment =
            CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        let lookup_commitments =
            CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        let sumcheck =
            CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        let composite =
            CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        let open_proof = CanonicalDeserialize::deserialize_with_mode(reader, compress, validate)?;

        Ok(Proof {
            trace_committment,
            lookup_commitments,
            sumcheck,
            composite,
            open_proof,
        })
    }
}

impl<F: Field, C: CommitmentScheme<F>> CanonicalSerialize for Proof<F, C>
where
    C::Commitment: CanonicalSerialize,
    C::Proof: CanonicalSerialize,
{
    fn serialize_with_mode<W: ark_serialize::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        let Self {
            trace_committment,
            lookup_commitments,
            sumcheck,
            composite,
            open_proof,
        } = self;
        trace_committment.serialize_with_mode(&mut writer, compress)?;
        lookup_commitments.serialize_with_mode(&mut writer, compress)?;
        sumcheck.serialize_with_mode(&mut writer, compress)?;
        composite.serialize_with_mode(&mut writer, compress)?;
        open_proof.serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        let Self {
            trace_committment,
            lookup_commitments,
            sumcheck,
            composite,
            open_proof,
        } = self;
        trace_committment.serialized_size(compress)
            + lookup_commitments.serialized_size(compress)
            + sumcheck.serialized_size(compress)
            + composite.serialized_size(compress)
            + open_proof.serialized_size(compress)
    }
}

#[derive(CanonicalSerialize)]
pub struct VerifierKey<F: Field, C: CommitmentScheme<F>> {
    zerocheck_key: usize,
    sumcheck: SumcheckVerifierKey<F, Oracle<F, C>>,
    composite: CompositeKey<F, C>,
    pcs: C::VerifierKey,
}

pub struct ProverKey<F: Field, C: CommitmentScheme<F>> {
    strucuture: SpreadsheetStructure<C>,
    sumcheck: sumcheck::ProverKey<F, Oracle<F, C>>,
    composite: CompositeKey<F, C>,
    committed: commit::oracle::ProverKey<F, Mles<()>, C>,
    pcs: C::ProverKey,
}

#[derive(Clone, Debug)]
pub enum SpreadsheetError<F: Field, C: CommitmentScheme<F>> {
    Sumcheck(SumcheckError),
    CompositeOracle,
    CoreOracle,
    Pcs(C::Error),
}

impl<F: Field, C: CommitmentScheme<F>> Reduction<F, Self, ()> for SpreadsheetRelation<F, C> {
    type ProverKey = ProverKey<F, C>;

    type VerifierKey = VerifierKey<F, C>;

    type Proof = Proof<F, C>;

    type Error = SpreadsheetError<F, C>;

    type Params = ();

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        builder
            .round::<F, C::Commitment, 0>(&())
            .round::<F, [C::Commitment; 3], 0>(&())
            .subprotocol::<ZerocheckReduction<F, Oracle<F, C>>, _, _, _>(&key.zerocheck_key)
            .subprotocol::<ZerocheckSumcheckReduction<F, _>, _, _, _>(&key.sumcheck)
            .subprotocol::<CompositeOracle<F, _, _, _>, _, _, _>(&key.composite)
            .subprotocol::<CoreOracle<F, Mles<()>>, _, _, _>(&())
            .subprotocol::<CommittedOracle<F, C, Mles<()>>, _, _, _>(key.composite.p2_key())
            .subprotocol::<C, _, _, _>(&key.pcs)
    }

    fn verifier_key(structure: &SpreadsheetStructure<C>) -> Self::VerifierKey {
        let mles = Rc::new(structure.sumcheck_structure());
        let builder1 = ();
        let builder2 = structure.pcs.clone();
        let oracle = Oracle::<F, C>::new((), mles, builder1, builder2);

        let sumcheck = ZerocheckSumcheckReduction::verifier_key(&oracle);

        let zerocheck_key = sumcheck.vars();

        let composite = CompositeOracle::verifier_key(&oracle);

        let pcs = C::verifier_key(&structure.pcs);

        VerifierKey {
            zerocheck_key,
            sumcheck,
            composite,
            pcs,
        }
    }

    fn key_pair(structure: &SpreadsheetStructure<C>) -> (Self::VerifierKey, Self::ProverKey) {
        let mles = Rc::new(structure.sumcheck_structure());
        let builder1 = ();
        let builder2 = structure.pcs.clone();
        let oracle = Oracle::<F, C>::new((), mles, builder1, builder2);

        let (sumcheck_verifier, sumcheck_prover) = ZerocheckSumcheckReduction::key_pair(&oracle);

        let zerocheck_key = sumcheck_verifier.vars();

        let composite = CompositeOracle::verifier_key(&oracle);

        let (pcs_verifier, pcs_prover) = C::key_pair(&structure.pcs);

        let verifier_key = VerifierKey {
            zerocheck_key,
            sumcheck: sumcheck_verifier,
            composite: composite.clone(),
            pcs: pcs_verifier,
        };

        let (_, committed) = CommittedOracle::key_pair(&oracle.inner_oracles().1);

        let prover_key = ProverKey {
            strucuture: structure.clone(),
            sumcheck: sumcheck_prover,
            composite,
            committed,
            pcs: pcs_prover,
        };

        (verifier_key, prover_key)
    }

    fn params(_: &Self::VerifierKey) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: C::Commitment,
        witness: Pow2Vec<F>,
        transcript: &mut reduction::Transcript<F, S>,
    ) -> ProverOutput<(), Self::Proof> {
        //TODO: check len
        let trace = WiredGate::compute_trace(key.strucuture.gates.inner(), witness.inner());
        let trace_commit = key.strucuture.pcs.commit_mle(&trace);

        let [] = transcript.send_message(&trace_commit, &());

        let witness: Vec<Mles<F>> = key.witness(witness.inner(), &trace);
        let lookup_commits = key.commit_lookups(&witness);

        let [] = transcript.send_message(&lookup_commits, &());

        let oracle_instance = CompositeOracleInstance {
            oracle1_instance: Self::core_oracle_instance(key.sumcheck.vars()),
            oracle2_instance: Self::committed_oracle_instance(
                instance,
                trace_commit.clone(),
                lookup_commits.clone(),
            ),
        };

        let ProverOutput {
            instance,
            witness,
            proof: (),
        } = ZerocheckReduction::<F, Oracle<F, C>>::prove(
            &key.strucuture.vars(),
            oracle_instance,
            witness,
            transcript,
        );

        let ProverOutput {
            instance,
            witness,
            proof: sumcheck_proof,
        } = ZerocheckSumcheckReduction::prove(&key.sumcheck, instance, witness, transcript);

        let ProverOutput {
            instance: (core_instance, committed_instance),
            witness,
            proof: composite_proof,
        } = CompositeOracle::prove(&key.composite, instance, witness, transcript);

        let ProverOutput {
            instance: (),
            witness: (),
            proof: (),
        } = CoreOracle::prove(
            key.composite.p1_key(),
            core_instance,
            witness.clone(),
            transcript,
        );

        let ProverOutput {
            instance,
            witness,
            proof: (),
        } = CommittedOracle::prove(&key.committed, committed_instance, witness, transcript);

        let ProverOutput {
            instance: (),
            witness: (),
            proof: open_proof,
        } = C::prove(&key.pcs, instance, witness, transcript);

        let proof = Proof {
            trace_committment: trace_commit,
            lookup_commitments: lookup_commits,
            sumcheck: sumcheck_proof,
            composite: composite_proof,
            open_proof,
        };

        ProverOutput {
            instance: (),
            witness: (),
            proof,
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: C::Commitment,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<(), Self::Error> {
        let Ok((trace_commit, [])) =
            transcript.receive_message(|proof| proof.trace_committment.clone(), &proof, &());
        let Ok((lookup_commits, [])) =
            transcript.receive_message(|proof| proof.lookup_commitments.clone(), &proof, &());

        let oracle_instance = CompositeOracleInstance {
            oracle1_instance: Self::core_oracle_instance(key.sumcheck.vars()),
            oracle2_instance: Self::committed_oracle_instance(
                instance,
                trace_commit,
                lookup_commits,
            ),
        };
        let instance = oracle_instance;
        let Ok(instance) = ZerocheckReduction::verify(
            &key.zerocheck_key,
            instance,
            GuardedProof::empty(),
            transcript,
        );

        let instance: OracleQueryInstance<F, _> = ZerocheckSumcheckReduction::verify(
            &key.sumcheck,
            instance,
            proof.clone().map(|proof| proof.sumcheck),
            transcript,
        )
        .map_err(SpreadsheetError::Sumcheck)?;

        let (core_instance, committed_instance) = CompositeOracle::verify(
            &key.composite,
            instance,
            proof.clone().map(|proof| proof.composite),
            transcript,
        )
        .map_err(|_| SpreadsheetError::CompositeOracle)?;

        let () = CoreOracle::verify(
            key.composite.p1_key(),
            core_instance,
            GuardedProof::empty(),
            transcript,
        )
        .map_err(|_| SpreadsheetError::CoreOracle)?;

        let Ok(open_instance) = CommittedOracle::verify(
            key.composite.p2_key(),
            committed_instance,
            GuardedProof::empty(),
            transcript,
        );

        let () = C::verify(
            &key.pcs,
            open_instance,
            proof.map(|proof| proof.open_proof),
            transcript,
        )
        .map_err(SpreadsheetError::Pcs)?;
        Ok(())
    }
}

impl<F: Field, C: CommitmentScheme<F>> Argument<F, Self> for SpreadsheetRelation<F, C> {}

impl<F: Field, C: CommitmentScheme<F>> ProverKey<F, C> {
    pub fn witness(&self, data: &[F], trace: &[F]) -> Vec<Mles<F>> {
        let _ = (data, trace);
        let mut witness = self.sumcheck.structure().to_vec();

        for (evals, data) in witness.iter_mut().zip(data) {
            evals.table = *data;
        }

        for (evals, trace) in witness.iter_mut().zip(trace) {
            evals.trace = *trace;
        }

        for (evals, gate) in witness.iter_mut().zip(&self.strucuture.gates) {
            for (lookup, var) in evals.lookups.iter_mut().zip(gate.io()) {
                let val = match var.1 {
                    DataOrTrace::Data => data[var.0],
                    DataOrTrace::Trace => trace[var.0],
                };
                *lookup = val;
            }
        }

        witness
    }

    fn commit_lookups(&self, mles: &[Mles<F>]) -> [C::Commitment; 3] {
        let pcs = &self.strucuture.pcs;
        let lookups1: Vec<F> = mles.iter().map(|mles| mles.lookups[0]).collect();
        let commit1 = pcs.commit_mle(&lookups1);
        let lookups2: Vec<F> = mles.iter().map(|mles| mles.lookups[0]).collect();
        let commit2 = pcs.commit_mle(&lookups2);
        let lookups3: Vec<F> = mles.iter().map(|mles| mles.lookups[0]).collect();
        let commit3 = pcs.commit_mle(&lookups3);
        [commit1, commit2, commit3]
    }
}

impl<C> SpreadsheetStructure<C> {
    pub fn new(data_table_size: usize, mut gates: Vec<WiredGate>, pcs: C) -> Self {
        let len = data_table_size.max(gates.len()).next_power_of_two();
        gates.resize(len, WiredGate::padding());
        let gates = Pow2Vec::new(gates);

        Self { gates, pcs }
    }

    pub fn vars(&self) -> usize {
        self.gates.inner().len().ilog2() as usize
    }

    fn sumcheck_structure<F: Field>(&self) -> Vec<Mles<F>> {
        let Self { gates, .. } = self;
        let zero: Mles<F> = Mles::default();
        gates
            .inner()
            .iter()
            .map(|gate| {
                let selectors = match gate.gate() {
                    gates::GateType::Add => [F::ONE, F::ZERO],
                    gates::GateType::Eq => [F::ZERO, F::ONE],
                    gates::GateType::Nop => [F::ZERO, F::ZERO],
                };
                Mles { selectors, ..zero }
            })
            .collect()
    }
}
