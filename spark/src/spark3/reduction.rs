use crate::spark3::{
    committed::{MinorStructure, SparkOracle},
    prove::ProverKey,
    sumcheck_argument::{SparkChallenges, SparkEvals},
    SparkInstance, StaticSparkRelation, StaticSparkStructure,
};
use ark_ff::Field;
use commit::commit2::{
    oracle::{CommittedOracle, CommittedOracleInstance},
    CommitmentScheme, OpenInstance, OpeningRelation,
};
use sponge::sponge::Duplex;
use std::marker::PhantomData;
use sumcheck::sumcheck2::{
    oracles::{
        composite::{CompositeOracle, CompositeOracleInstance, CompositeReductionKey, ProverEvals},
        core::{CoreOracle, CoreOracleInstance},
        partial::{Nature, PartialOracle, PartialQueryInstance},
        SumcheckFunction,
    },
    MultiPoint, SumcheckError, SumcheckInstance, SumcheckMessage, SumcheckReduction,
    SumcheckVerifierKey,
};
use transcript::reduction2::{
    GuardedProof, ProverOutput, Reduction, Transcript, TranscriptBuilder, VerifierTranscript,
};

#[derive(Clone, Copy, Debug)]
pub struct SparkReduction<F: Field, C: CommitmentScheme<F>, const N: usize>(PhantomData<(F, C)>);

type Rel1<F, C, const N: usize> = StaticSparkRelation<F, C, N>;
type Rel2<F, C> = OpeningRelation<F, C>;

#[derive(Clone, Debug)]
pub struct Proof<F: Field, C: CommitmentScheme<F>, const N: usize> {
    pub lookup_commitments: [C::Commitment; N],
    pub inverse_commitments: [C::Commitment; N],
    pub sumcheck_proof: Vec<SumcheckMessage<F>>,
    pub oracle_query_proof: ProverEvals<F>,
}

fn split_point<F: Field, const N: usize>(point: &MultiPoint<F>) -> [MultiPoint<F>; N] {
    point
        .inner_ref()
        .chunks(8)
        .map(|segment| {
            assert_eq!(segment.len(), 8);
            MultiPoint::new(segment.to_vec())
        })
        .collect::<Vec<MultiPoint<F>>>()
        .try_into()
        .unwrap()
}

pub struct Key<F, C, SF, const N: usize>
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
    CommittedOracle<F, C, SF>: PartialOracle<F, SF>,
{
    minor_structure: MinorStructure<N>,
    sumcheck_key: SumcheckVerifierKey<F, SparkOracle<F, C, N>>,
    oracle_key: CompositeReductionKey<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>,
    vars: usize,
}

impl<F, C, SF, const N: usize> Key<F, C, SF, N>
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
    CommittedOracle<F, C, SF>: PartialOracle<F, SF>,
{
    pub(crate) fn new(
        minor_structure: MinorStructure<N>,
        sumcheck_key: SumcheckVerifierKey<F, SparkOracle<F, C, N>>,
        oracle_key: CompositeReductionKey<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>,
        vars: usize,
    ) -> Self {
        Self {
            minor_structure,
            sumcheck_key,
            oracle_key,
            vars,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum SparkError {
    Sumcheck(SumcheckError),
    CompositeOracle,
    CoreOracle,
}

impl<F, C, const N: usize> Reduction<F, Rel1<F, C, N>, Rel2<F, C>> for SparkReduction<F, C, N>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ProverKey<F, C, N>;

    type VerifierKey = Key<F, C, SparkEvals<(), N>, N>;

    type Proof = Proof<F, C, N>;

    type Error = SparkError;

    type Params = usize;

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        let vars = key.sumcheck_key.vars();
        builder
            .round::<F, [C::Commitment; N], 2>(&())
            .round::<F, [C::Commitment; N], 0>(&())
            .point::<F>(vars)
            .round::<F, (), 1>(&())
            .subprotocol::<SumcheckReduction<F, SparkOracle<F, C, N>>, _, _, _>(&key.sumcheck_key)
            .subprotocol::<CompositeOracle<F, SparkEvals<(), N>, _, _>, _, _, _>(&key.oracle_key)
            .subprotocol::<CoreOracle<F, SparkEvals<(), N>>, _, _, _>(key.oracle_key.p1_key())
            .subprotocol::<CommittedOracle<F, C, SparkEvals<(), N>>, F, _, _>(
                key.oracle_key.p2_key(),
            )
    }

    fn verifier_key(structure: &StaticSparkStructure<F, C, N>) -> Self::VerifierKey {
        // TODO: specialize instead of creating both keys.
        let (verifier_key, _) = Self::key_pair(structure);
        verifier_key
    }

    fn key_pair(structure: &StaticSparkStructure<F, C, N>) -> (Self::VerifierKey, Self::ProverKey) {
        ProverKey::new(&structure.mle, structure.pcs.clone())
    }

    fn params(key: &Self::VerifierKey) -> Self::Params {
        key.vars
    }

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: SparkInstance<F>,
        _witness: (),
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        //TODO: allow more flexibility
        assert!(instance.point.vars() >= N * 8);
        let points = instance
            .point
            .inner()
            .chunks(8)
            .map(|chunk| {
                assert_eq!(chunk.len(), 8);
                MultiPoint::new(chunk.to_vec())
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        key.prove(points, transcript)
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: SparkInstance<F>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        // FIRST ROUND: Sending commitments to lookups, getting challenges
        // for lookup argument.
        let Ok((lookup_commitments, [c1, c2])) =
            transcript.receive_message(|proof| proof.lookup_commitments.clone(), &proof, &());

        let lookup_chall = c1;
        let compression_chall = c2;

        // SECOND ROUND: Sending commitments to the inverses of the indexed lookups.
        // Another challenge is received to combine the multiple sumchecks into 1.
        let Ok((inverse_commitments, [])) =
            transcript.receive_message(|proof| proof.inverse_commitments.clone(), &proof, &());

        let zerocheck_point = MultiPoint::new(transcript.point());

        let Ok(((), [c3])) = transcript.receive_message(|_| (), &proof, &());

        let combination_chall = c3;

        let SparkInstance { point, eval } = instance;

        let points = split_point(&point);
        // Expected sums from computing the left side directly.
        let expected_sums =
            key.minor_structure
                .expected_sums(&points, lookup_chall, compression_chall);

        let sum = expected_sums
            .into_iter()
            .fold(F::zero(), |acc, s| acc * combination_chall + s);
        let sum = sum * combination_chall + eval;

        let challenges = SparkChallenges::new(combination_chall, compression_chall, lookup_chall);

        let sumcheck_instance = sumcheck_instance::<F, C, N>(
            sum,
            lookup_commitments,
            inverse_commitments,
            zerocheck_point,
            &challenges,
        );

        let sumcheck_proof = proof.clone().map(|proof| proof.sumcheck_proof);
        let query_instance = SumcheckReduction::verify(
            &key.sumcheck_key,
            sumcheck_instance,
            sumcheck_proof,
            transcript,
        )
        .map_err(SparkError::Sumcheck)?;

        let oracle_proof = proof.map(|proof| proof.oracle_query_proof);
        let red =
            CompositeOracle::verify(&key.oracle_key, query_instance, oracle_proof, transcript)
                .map_err(|_| SparkError::CompositeOracle)?;

        let (core_query, committed_query) = red;
        let core_query: PartialQueryInstance<F, _, CoreOracleInstance<F, _>> = core_query;

        let core_proof = GuardedProof::empty();
        CoreOracle::verify(key.oracle_key.p1_key(), core_query, core_proof, transcript)
            .map_err(|_| SparkError::CoreOracle)?;

        let committed_query: PartialQueryInstance<F, _, CommittedOracleInstance<F, C, _>> =
            committed_query;

        let proof = GuardedProof::empty();
        let Ok(open_instance) =
            CommittedOracle::verify(key.oracle_key.p2_key(), committed_query, proof, transcript);

        Ok(open_instance)
    }
}

//TODO: maybe move to mod.rs
pub(crate) fn sumcheck_instance<F, C, const N: usize>(
    sum: F,
    lookup_commitments: [C::Commitment; N],
    inverse_commitments: [C::Commitment; N],
    zerocheck_point: MultiPoint<F>,
    challenges: &SparkChallenges<F>,
) -> SumcheckInstance<F, SparkOracle<F, C, N>>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    let vars = zerocheck_point.vars();
    let coefficients: SparkEvals<Vec<F>, N> =
        SparkEvals::oracle_instance(challenges, zerocheck_point);
    let core_oracle_instance = CoreOracleInstance::new(&coefficients, vars);

    let commits = SparkEvals::arrange_commitments(lookup_commitments, inverse_commitments);
    let committed_oracle_instance = CommittedOracleInstance::new(commits);

    let oracle_instance = CompositeOracleInstance {
        oracle1_instance: core_oracle_instance,
        oracle2_instance: committed_oracle_instance,
    };

    SumcheckInstance::new(sum, oracle_instance)
}
