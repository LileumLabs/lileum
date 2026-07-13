use crate::lilium2::{
    oracles::{MatrixNature, MatrixOracleQuery, MatrixProductInstance, MatrixProductOracle},
    reductions::matrix_product::{
        function::{MatrixSumEvals, Oracle},
        matrix_sum::{MatrixSumInstance, MatrixSumOracle},
    },
};
use ark_ff::Field;
use ccs::matrix::Matrix;
use commit::commit2::{
    self,
    oracle::{
        CommittedNature, CommittedOracle, CommittedOracleInstance,
        VerifierKey as CommittedVerifierKey,
    },
    CommitmentScheme, OpenInstance, OpeningRelation,
};
use spark::spark3::{FlexibleSparkRelation, FlexibleSparkStructure, SparkInstance};
use sponge::sponge::Duplex;
use std::{marker::PhantomData, rc::Rc};
use sumcheck::sumcheck2::{
    evals::EvalsCore,
    oracles::{
        composite::{CompositeOracle, CompositeOracleInstance, CompositeReductionKey, ProverEvals},
        core::{CoreOracle, CoreOracleInstance},
        partial::{Nature, PartialQueryInstance},
        SumcheckFunction,
    },
    ProverKey as SumcheckProver, SumcheckInstance, SumcheckMessage, SumcheckReduction,
    SumcheckVerifierKey,
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

pub struct ProverKey<F, C, SF, const N: usize>
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F>,
{
    committed_oracle1: commit2::oracle::ProverKey<F, SF, C>,
    sumcheck_key: SumcheckProver<F, Oracle<F, Func<N>, C, N>>,
    matrices: [Rc<Matrix>; N],
    // Filter to select the vector MLE.
    vector: SF::Mles<bool>,
    composite_key: CompositeKey<F, C, N, Func<N>>,
    committed_oracle2: commit2::oracle::ProverKey<F, MatrixSumEvals<(), N>, C>,
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
    type ProverKey = ProverKey<F, C, SF, N>;

    type VerifierKey = VerifierKey<F, C, SF, N>;

    type Proof = Proof<F>;

    type Error = ();

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        let VerifierKey {
            sumcheck_key,
            committed_oracle1,
            committed_oracle2,
            composite_key,
            ..
        } = key;
        builder
            .subprotocol::<CommittedOracle<F, C, SF>, _, _, _>(committed_oracle1)
            .round::<F, (), 1>(&())
            .subprotocol::<SumcheckReduction<F, Oracle<F, Func<N>, C, N>>, F, _, _>(sumcheck_key)
            .subprotocol::<Oracle<F, Func<N>, C, N>, _, _, _>(composite_key)
            .subprotocol::<CoreOracle<F, Func<N>>, _, _, _>(composite_key.p2_key().p1_key())
            .subprotocol::<CommittedOracle<F, C, SF>, _, _, _>(committed_oracle2)
            .subprotocol::<MatrixSumOracle<F, C, N>, _, _, _>(&())
    }

    fn verifier_key(
        structure_1: &MatrixProductOracle<F, C, SF, N>,
        structure_2: &([C; 2], [FlexibleSparkStructure<F>; N]),
    ) -> Self::VerifierKey {
        let vars = {
            let rows = structure_1
                .matrices()
                .iter()
                .map(|matrix| matrix.len())
                .max()
                .unwrap();
            let vars = rows.next_power_of_two().ilog2();
            vars as usize
        };
        let mles = vec![MatrixSumEvals::zero(); 1 << vars];
        let mles = Rc::new(mles);

        let builder1 = MatrixSumOracle::new(structure_1.matrices().clone());

        let core_oracle = CoreOracle::new(MatrixSumEvals::core_oracle_functions());
        let [pcs, _] = &structure_2.0;
        let builder2 = (core_oracle, pcs.clone());

        let oracle = Oracle::new((), mles, builder1, builder2);

        let sumcheck_key = SumcheckReduction::verifier_key(&oracle, &oracle);

        let committed_oracle1 = CommittedOracle::verifier_key(structure_1.committed_oracle(), pcs);

        let committed_oracle2 =
            CommittedOracle::verifier_key(&oracle.inner_oracles().1.inner_oracles().1, pcs);

        let composite_key = Oracle::verifier_key(&oracle, oracle.inner_oracles());

        VerifierKey {
            sumcheck_key,
            committed_oracle1,
            committed_oracle2,
            composite_key,
            _phatom: PhantomData,
        }
    }

    fn key_pair(
        _structure_1: &MatrixProductOracle<F, C, SF, N>,
        _structure_2: &([C; 2], [FlexibleSparkStructure<F>; N]),
    ) -> (Self::VerifierKey, Self::ProverKey) {
        todo!()
    }

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: PartialQueryInstance<F, SF, MatrixProductInstance<F, C>>,
        witness: Vec<SF::Mles<F>>,
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<Rel2<F, C, N>, Self::Proof> {
        let oracle_instance = instance.oracle_instance();
        let MatrixProductInstance(z) = oracle_instance.clone();

        //TODO: Optimize.
        let z_witness: Vec<F> = witness
            .iter()
            .map(|evals| {
                SF::combine(&key.vector, evals, |filter, eval| filter.then_some(*eval))
                    .flatten_vec()
                    .into_iter()
                    .flatten()
                    .next()
                    .unwrap()
            })
            .collect();

        // Run the inner CommittedOracle reduction.
        let open_out1 = {
            let oracle_instance = CommittedOracleInstance::<F, C, SF>::new_single_commit(z.clone());
            let evals = SF::combine(&SF::natures(), instance.evals(), |nature, eval| {
                let nature: Option<CommittedNature> = nature.into_dynamic().into();
                nature.and(*eval)
            });
            let point = instance.point();
            let instance = PartialQueryInstance::new(evals, oracle_instance, point);
            CommittedOracle::prove(&key.committed_oracle1, instance, witness, transcript)
        };

        let query = {
            let [chall] = transcript.send_message(&(), &());

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

            let structure = key.sumcheck_key.structure();
            let matrices: [&Matrix; N] = key.matrices.each_ref().map(AsRef::as_ref);
            let witness = MatrixSumEvals::witness(structure, matrices, &z_witness, point);

            SumcheckReduction::<F, Oracle<F, MatrixSumEvals<(), N>, C, N>>::prove(
                &key.sumcheck_key,
                sumcheck_instance,
                witness,
                transcript,
            )
        };

        let ProverOutput {
            instance,
            witness,
            proof: sumcheck,
        } = query;

        let ProverOutput {
            instance: (matrix, composite),
            witness,
            proof: prover_evals,
        } = CompositeOracle::prove(&key.composite_key, instance, witness, transcript);

        let proof = Proof {
            sumcheck,
            prover_evals,
        };

        let (core, committed) = key.composite_key.p2_key().split(composite);

        let _ = CoreOracle::prove(
            key.composite_key.p2_key().p1_key(),
            core,
            witness.clone(),
            transcript,
        );

        let open_out2 = {
            CommittedOracle::prove(
                &key.committed_oracle2,
                committed,
                witness.clone(),
                transcript,
            )
        };

        let open_out = ProverOutput::combine_tuple(open_out1, open_out2)
            .map_proof(|_| ())
            .map_rel(|(a, b)| [a, b], |(a, b)| [a, b]);

        let spark_out = { MatrixSumOracle::<F, C, N>::prove(&(), matrix, witness, transcript) };

        ProverOutput::combine_tuple(open_out, spark_out).map_proof(|_| proof)
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
