use crate::lilium2::{
    oracles::{MatrixNature, MatrixOracleQuery, MatrixProductInstance, MatrixProductOracle},
    reductions::matrix_product::{
        function::{MatrixSumEvals, Oracle},
        matrix_sum::{MatrixSumInstance, MatrixSumOracle},
    },
};
use ark_ff::Field;
use commit::commit2::{
    oracle::{
        CommittedNature, CommittedOracle, CommittedOracleInstance,
        VerifierKey as CommittedVerifierKey,
    },
    CommitmentScheme, OpenInstance, OpeningRelation,
};
use spark::spark3::{FlexibleSparkRelation, FlexibleSparkStructure, SparkInstance};
use sponge::sponge::Duplex;
use std::marker::PhantomData;
use sumcheck::sumcheck2::{
    evals::EvalsCore,
    oracles::{
        composite::{CompositeOracle, CompositeOracleInstance, CompositeReductionKey, ProverEvals},
        core::{CoreOracle, CoreOracleInstance},
        partial::{Nature, PartialQueryInstance},
        SumcheckFunction,
    },
    SumcheckInstance, SumcheckMessage, SumcheckReduction, SumcheckVerifierKey,
};
use transcript::reduction2::{
    GuardedProof, ProverOutput, Reduction, Transcript, TranscriptBuilder, VerifierTranscript,
};

mod function;
mod matrix_sum;

#[allow(dead_code)]
pub struct MatrixProductReduction;

type CompositeKey<F, C, const N: usize, SF> = CompositeReductionKey<
    F,
    SF,
    MatrixSumOracle<F, C, N>,
    CompositeOracle<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>,
>;

type Func<const N: usize> = MatrixSumEvals<(), N>;

pub struct VerifierKey<F: Field, C: CommitmentScheme<F>, SF, const N: usize> {
    sumcheck_key: SumcheckVerifierKey<F>,
    committed_oracle1: CommittedVerifierKey<F, C>,
    committed_oracle2: CommittedVerifierKey<F, C>,
    composite_key: CompositeKey<F, C, N, Func<N>>,
    _phatom: PhantomData<SF>,
}

#[derive(Clone, Debug)]
pub struct Proof<F: Field> {
    sumcheck: Vec<SumcheckMessage<F>>,
    prover_evals: ProverEvals<F>,
}

type Rel1<F, C, SF, const N: usize> = MatrixOracleQuery<F, C, SF, N>;
type Rel2<F, C, const N: usize> = ([OpeningRelation<F, C>; 2], [FlexibleSparkRelation<F>; N]);

impl<F, C, SF, const N: usize> Reduction<F, Rel1<F, C, SF, N>, Rel2<F, C, N>>
    for MatrixProductReduction
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F>,
{
    type ProverKey = ();

    type VerifierKey = VerifierKey<F, C, SF, N>;

    type Proof = Proof<F>;

    type Error = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        _builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        todo!()
    }

    fn verifier_key(
        _structure_1: &MatrixProductOracle<F, C, SF, N>,
        _structure_2: &([C; 2], [FlexibleSparkStructure<F>; N]),
    ) -> Self::VerifierKey {
        todo!()
    }

    fn key_pair(
        _structure_1: &MatrixProductOracle<F, C, SF, N>,
        _structure_2: &([C; 2], [FlexibleSparkStructure<F>; N]),
    ) -> (Self::VerifierKey, Self::ProverKey) {
        todo!()
    }

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: PartialQueryInstance<F, SF, MatrixProductInstance<F, C>>,
        _witness: Vec<SF::Mles<F>>,
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<Rel2<F, C, N>, Self::Proof> {
        todo!()
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: PartialQueryInstance<F, SF, MatrixProductInstance<F, C>>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<([OpenInstance<F, C>; 2], [SparkInstance<F>; N]), Self::Error> {
        let oracle_instance = instance.oracle_instance();
        let MatrixProductInstance(z) = oracle_instance.clone();

        // Run the inner CommittedOracle reduction.
        let Ok(open_instance1) = {
            let oracle_instance = CommittedOracleInstance::<F, C, SF>::new_single_commit(z.clone());
            let evals = SF::combine(&SF::natures(), instance.evals(), |nature, eval| {
                let nature: Option<CommittedNature> = nature.into_dynamic().into();
                nature.and(*eval)
            });
            let point = instance.point();
            let instance = PartialQueryInstance::new(evals, oracle_instance, point);
            let proof = GuardedProof::empty();
            CommittedOracle::verify(&key.committed_oracle1, instance, proof, transcript)
        };

        let query = {
            let Ok(((), [chall])) = transcript.receive_message(|_| {}, &GuardedProof::empty(), &());

            let sum = sumcheck_sum::<F, SF, N>(instance.evals(), chall);

            let point = instance.point();
            let matrix_sum_instance = MatrixSumInstance::<F>::new(point.clone());

            let committed_instance = CommittedOracleInstance::<F, C, Func<N>>::new_single_commit(z);

            let core_instance = {
                //TODO:
                let vars = 3;
                let coefficients = MatrixSumEvals::coefficients(chall);
                CoreOracleInstance::<F, Func<N>>::new(&coefficients, vars)
            };

            let oracle_instance = CompositeOracleInstance {
                oracle1_instance: matrix_sum_instance,
                oracle2_instance: CompositeOracleInstance {
                    oracle1_instance: core_instance,
                    oracle2_instance: committed_instance,
                },
            };

            let sumcheck_instance: SumcheckInstance<F, Oracle<F, Func<N>, C, N>> =
                SumcheckInstance::new(sum, oracle_instance);

            let sumcheck_proof = proof.clone().map(|proof| proof.sumcheck);
            SumcheckReduction::<F, Oracle<F, MatrixSumEvals<(), N>, C, N>>::verify(
                &key.sumcheck_key,
                sumcheck_instance,
                sumcheck_proof,
                transcript,
            )
            //TODO:handle
            .unwrap()
        };

        let (matrix, composite) = CompositeOracle::verify(
            &key.composite_key,
            query,
            proof.map(|proof| proof.prover_evals),
            transcript,
        )
        //TODO:handle
        .unwrap();

        let (core, committed) = key.composite_key.p2_key().split(composite);

        let _ = CoreOracle::verify(
            key.composite_key.p2_key().p1_key(),
            core,
            GuardedProof::empty(),
            transcript,
        );

        let Ok(open_instance2) = {
            let proof = GuardedProof::empty();
            CommittedOracle::verify(&key.committed_oracle2, committed, proof, transcript)
        };

        let spark_instances = {
            let proof = GuardedProof::empty();
            MatrixSumOracle::<F, C, N>::verify(&(), matrix, proof, transcript).unwrap()
        };

        Ok(([open_instance1, open_instance2], spark_instances))
    }
}

fn sumcheck_sum<F, SF, const N: usize>(evals: &SF::Mles<Option<F>>, challenge: F) -> F
where
    F: Field,
    SF: SumcheckFunction<F>,
{
    SF::combine(&SF::natures(), evals, |nature, eval| {
        let nature: Option<MatrixNature> = nature.into_dynamic().into();
        nature.and(*eval)
    })
    .flatten_vec()
    .into_iter()
    .flatten()
    .fold(F::ZERO, |acc, val| acc * challenge + val)
}
