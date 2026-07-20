use crate::lilium2::{
    oracles::{FlcsOracle, MatrixProductOracle},
    reductions::{
        flcs::{compute_sumcheck_witness, FlcsEvals},
        matrix_product::{self, MatrixProductReduction},
    },
    relations::{FlcsInstance, FlcsRelation, FlcsStructure},
};
use ark_ff::Field;
use ccs::matrix::Matrix;
use commit::commit2::{
    multipoint::{self, MultipointBatching},
    CommitmentScheme, OpenInstance, OpeningRelation,
};
use spark::spark3::{
    flexible::{self, FlexibleSparkError},
    FlexibleSpark, FlexibleSparkStructure,
};
use sponge::sponge::Duplex;
use std::rc::Rc;
use sumcheck::sumcheck2::{
    oracles::{
        self,
        composite::{CompositeOracle, CompositeReductionKey, ProverEvals},
        core::{CoreOracle, CoreOracleInstance},
    },
    zerocheck::ZerocheckSumcheckReduction,
    ProverKey as SumcheckProverKey, SumcheckError, SumcheckMessage, SumcheckVerifierKey,
};
use transcript::reduction2::{
    GuardedProof, ProverOutput, Reduction, Transcript, TranscriptBuilder, VerifierTranscript,
};

/// FLCS -> CommitOpening
pub struct FlcsReduction;

type CompositeKey<F, C, const IO: usize, SF> =
    CompositeReductionKey<F, SF, CoreOracle<F, SF>, MatrixProductOracle<F, C, SF, IO>>;

pub struct VerifierKey<F, C, const IO: usize, const S: usize, const I: usize>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    sumcheck_key: SumcheckVerifierKey<F>,
    composite_key: CompositeKey<F, C, IO, FlcsEvals<(), IO, S, I>>,
    matrix_oracle_key: matrix_product::VerifierKey<F, C, FlcsEvals<(), IO, S, I>, IO>,
    spark_keys: [flexible::VerifierKey<F, C>; IO],
    batching1: multipoint::VerifierKey<F, C, IO>,
    batching2: multipoint::VerifierKey<F, C, 3>,
}

pub struct ProverKey<F, C, const IO: usize, const S: usize, const I: usize>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    sumcheck: SumcheckProverKey<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>,
    composite_key: CompositeKey<F, C, IO, FlcsEvals<(), IO, S, I>>,
    matrices: [Rc<Matrix>; IO],
    matrix_oracle_key: matrix_product::ProverKey<F, C, FlcsEvals<(), IO, S, I>, IO>,
    spark_keys: [flexible::ProverKey<F, C>; IO],
    batching1: multipoint::ProverKey<F, C, IO>,
    batching2: multipoint::ProverKey<F, C, 3>,
}

#[derive(Clone, Debug)]
pub struct Proof<F: Field, C: CommitmentScheme<F>, const IO: usize> {
    sumcheck_proof: Vec<SumcheckMessage<F>>,
    oracle_evals1: ProverEvals<F>,
    matrix_product: matrix_product::Proof<F>,
    spark_proofs: [flexible::Proof<F, C>; IO],
    batching1: multipoint::Proof<F>,
    batching2: multipoint::Proof<F>,
}

#[derive(Clone, Debug)]
pub enum FlcsError {
    Sumcheck(SumcheckError),
    Composite,
    Core,
    MatrixProduct(matrix_product::Error),
    Spark(FlexibleSparkError),
    Batching1(multipoint::Error),
    Batching2(multipoint::Error),
}

impl<F, C, const I: usize, const IO: usize, const S: usize>
    Reduction<F, FlcsRelation<F, C, I, IO, S>, OpeningRelation<F, C>> for FlcsReduction
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ProverKey<F, C, IO, S, I>;

    type VerifierKey = VerifierKey<F, C, IO, S, I>;

    type Proof = Proof<F, C, IO>;

    type Error = FlcsError;

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        let builder = builder
            .subprotocol::<ZerocheckSumcheckReduction<F, FlcsOracle<F, C, FlcsEvals<(), IO, S,I>, IO>>, F, _, _>(&key.sumcheck_key)
            .subprotocol::<CompositeOracle<F,FlcsEvals<(),IO,S,I>,_,_>,_,_,_>(&key.composite_key)
            .subprotocol::<CoreOracle<F,FlcsEvals<(),IO,S,I>>,_,_,_>(key.composite_key.p1_key())
            .subprotocol::<MatrixProductReduction,_,_,_>(&key.matrix_oracle_key);
        let builder = key.spark_keys.iter().fold(builder, |builder, key| {
            builder.subprotocol::<FlexibleSpark<F, C>, _, _, _>(key)
        });
        builder
            .subprotocol::<MultipointBatching<F, C, IO>, _, _, _>(&key.batching1)
            .subprotocol::<MultipointBatching<F, C, 3>, _, _, _>(&key.batching2)
    }

    fn verifier_key(structure_1: &FlcsStructure<F, C, IO, S, I>, _: &C) -> Self::VerifierKey {
        let FlcsStructure {
            ccs_structure,
            pcs,
            oracle,
        } = structure_1;

        let sumcheck_key = ZerocheckSumcheckReduction::<
            F,
            FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>,
        >::verifier_key(oracle, oracle);

        let vars = sumcheck_key.vars();

        let composite_key = CompositeOracle::verifier_key(oracle, oracle.inner_oracles());

        let spark_structure = spark_structure(&ccs_structure.io_matrices);
        let matrix_structure = ([pcs.clone(), pcs.clone()], spark_structure);
        let matrix_oracle_key =
            MatrixProductReduction::verifier_key(&oracle.inner_oracles().1, &matrix_structure);
        let (_, spark_structure) = matrix_structure;

        let spark_keys =
            spark_structure.map(|structure| FlexibleSpark::verifier_key(&structure, pcs));

        let batching_structure = (pcs.clone(), vars);
        let batching1 = MultipointBatching::verifier_key(&batching_structure, pcs);
        let batching2 = MultipointBatching::verifier_key(&batching_structure, pcs);

        VerifierKey {
            sumcheck_key,
            composite_key,
            matrix_oracle_key,
            spark_keys,
            batching1,
            batching2,
        }
    }

    fn key_pair(
        structure_1: &FlcsStructure<F, C, IO, S, I>,
        structure_2: &C,
    ) -> (Self::VerifierKey, Self::ProverKey) {
        let verifier_key = <Self as Reduction<
            F,
            FlcsRelation<F, C, I, IO, S>,
            OpeningRelation<F, C>,
        >>::verifier_key(structure_1, structure_2);

        let FlcsStructure {
            ccs_structure,
            pcs,
            oracle,
        } = structure_1;

        let (_, sumcheck) = ZerocheckSumcheckReduction::<
            F,
            FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>,
        >::key_pair(oracle, oracle);

        let vars = {
            use oracles::Oracle;
            oracle.vars()
        };

        let composite_key = CompositeOracle::verifier_key(oracle, oracle.inner_oracles());

        let matrices = structure_1
            .ccs_structure
            .io_matrices
            .each_ref()
            .map(|matrix| Rc::new(matrix.clone()));

        let spark_structure = spark_structure(&ccs_structure.io_matrices);
        let matrix_structure = ([pcs.clone(), pcs.clone()], spark_structure);
        let (_, matrix_oracle_key) =
            MatrixProductReduction::key_pair(&oracle.inner_oracles().1, &matrix_structure);
        let (_, spark_structure) = matrix_structure;

        let spark_keys =
            spark_structure.map(|structure| FlexibleSpark::key_pair(&structure, pcs).1);

        let batching_structure = (pcs.clone(), vars);
        let (_, batching1) = MultipointBatching::key_pair(&batching_structure, pcs);
        let (_, batching2) = MultipointBatching::key_pair(&batching_structure, pcs);

        let prover_key = ProverKey {
            sumcheck,
            composite_key,
            matrices,
            matrix_oracle_key,
            spark_keys,
            batching1,
            batching2,
        };
        (verifier_key, prover_key)
    }

    fn prove<D: Duplex<F>>(
        key: &Self::ProverKey,
        instance: FlcsInstance<F, C, IO, S, I>,
        witness: Vec<F>,
        transcript: &mut Transcript<F, D>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        let instance = instance.0;

        let witness = key.witness(&witness, &instance.oracle_instance().oracle1_instance);
        let ProverOutput {
            instance,
            witness,
            proof: sumcheck_proof,
        } = ZerocheckSumcheckReduction::<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>::prove(
            &key.sumcheck,
            instance,
            witness,
            transcript,
        );

        let ProverOutput {
            instance: (core, matrix),
            witness,
            proof: oracle_evals1,
        } = CompositeOracle::prove(&key.composite_key, instance, witness, transcript);

        CoreOracle::prove(
            key.composite_key.p1_key(),
            core,
            witness.clone(),
            transcript,
        );

        let ProverOutput {
            instance,
            witness,
            proof: matrix_product,
        } = MatrixProductReduction::prove(&key.matrix_oracle_key, matrix, witness, transcript);

        let ([open_instance1, open_instance2], spark_instances) = instance;
        let ([open_witness1, open_witness2], _) = witness;

        let (out, spark_proofs) = {
            let mut instances = [(); IO].map(|_| None);
            let mut witnesses = [(); IO].map(|_| None);
            let mut proofs = [(); IO].map(|_| None);

            for (i, (key, instance)) in key.spark_keys.iter().zip(spark_instances).enumerate() {
                let ProverOutput {
                    instance,
                    witness,
                    proof,
                } = FlexibleSpark::prove(key, instance, (), transcript);
                instances[i] = Some(instance);
                witnesses[i] = Some(witness);
                proofs[i] = Some(proof);
            }

            let instances: [OpenInstance<F, C>; IO] = instances.map(Option::unwrap);
            let witnesses: [Vec<F>; IO] = witnesses.map(Option::unwrap);

            let out = MultipointBatching::prove(&key.batching1, instances, witnesses, transcript);
            (out, proofs.map(Option::unwrap))
        };

        let ProverOutput {
            instance: open_instance3,
            witness: open_witness3,
            proof: batching1,
        } = out;

        let instance = [open_instance1, open_instance2, open_instance3];
        let witness = [open_witness1, open_witness2, open_witness3];

        let ProverOutput {
            instance,
            witness,
            proof: batching2,
        } = MultipointBatching::prove(&key.batching2, instance, witness, transcript);

        let proof = Proof {
            sumcheck_proof,
            oracle_evals1,
            matrix_product,
            spark_proofs,
            batching1,
            batching2,
        };

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    fn verify<D: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: FlcsInstance<F, C, IO, S, I>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, D>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        let instance = instance.0;

        let instance =
            ZerocheckSumcheckReduction::<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>::verify(
                &key.sumcheck_key,
                instance,
                proof.clone().map(|proof| proof.sumcheck_proof),
                transcript,
            )
            .map_err(FlcsError::Sumcheck)?;

        let (core_instance, matrix_instance) = CompositeOracle::verify(
            &key.composite_key,
            instance,
            proof.clone().map(|proof| proof.oracle_evals1),
            transcript,
        )
        .map_err(|()| FlcsError::Composite)?;

        CoreOracle::verify(
            key.composite_key.p1_key(),
            core_instance,
            GuardedProof::empty(),
            transcript,
        )
        .map_err(|()| FlcsError::Core)?;

        let (open_instances, spark_instances) = MatrixProductReduction::verify(
            &key.matrix_oracle_key,
            matrix_instance,
            proof.clone().map(|proof| proof.matrix_product),
            transcript,
        )
        .map_err(FlcsError::MatrixProduct)?;

        let [open_instance1, open_instance2] = open_instances;

        let open_instance3 = {
            let mut instances = [(); IO].map(|_| None);

            for (i, (key, instance)) in key.spark_keys.iter().zip(spark_instances).enumerate() {
                let proof = proof.clone().map(|proof| proof.spark_proofs[i].clone());
                let open_instance = FlexibleSpark::verify(key, instance, proof, transcript)
                    .map_err(FlcsError::Spark)?;
                instances[i] = Some(open_instance);
            }

            let instances: [OpenInstance<F, C>; IO] = instances.map(Option::unwrap);

            MultipointBatching::verify(
                &key.batching1,
                instances,
                proof.clone().map(|proof| proof.batching1),
                transcript,
            )
            .map_err(FlcsError::Batching1)?
        };

        let instance = [open_instance1, open_instance2, open_instance3];

        let instance = MultipointBatching::verify(
            &key.batching2,
            instance,
            proof.map(|proof| proof.batching2),
            transcript,
        )
        .map_err(FlcsError::Batching2)?;

        Ok(instance)
    }
}

impl<F, C, const IO: usize, const S: usize, const I: usize> ProverKey<F, C, IO, S, I>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    fn witness(
        &self,
        witness: &[F],
        instance: &CoreOracleInstance<F, FlcsEvals<(), IO, S, I>>,
    ) -> Vec<FlcsEvals<F, IO, S, I>> {
        let structure = self.sumcheck.structure();
        let matrices = &self.matrices;
        compute_sumcheck_witness(structure, matrices, witness, instance)
    }
}

fn spark_structure<F: Field, const N: usize>(
    matrices: &[Matrix; N],
) -> [FlexibleSparkStructure<F>; N] {
    matrices.each_ref().map(|matrix| {
        let evals = matrix.to_evals();
        let (x_max, y_max) = evals
            .iter()
            .fold((0, 0), |acc, (x, y)| (acc.0.max(*x), acc.1.max(*y)));
        assert!(x_max.highest_one().unwrap_or(0) + y_max.highest_one().unwrap_or(0) < 64);
        let evals = evals
            .into_iter()
            .map(|(x, y)| {
                let addr = x + (y << (x_max.highest_one().unwrap_or(0) + 1));
                (addr as u64, F::ONE)
            })
            .collect();
        FlexibleSparkStructure::new(Rc::new(evals))
    })
}
