use crate::lilium2::{
    oracles::{FlcsOracle, MatrixProductOracle},
    reductions::{
        flcs::FlcsEvals,
        matrix_product::{self, MatrixProductReduction},
    },
    relations::{FlcsInstance, FlcsRelation, FlcsStructure},
};
use ark_ff::Field;
use commit::commit2::{CommitmentScheme, OpenInstance, OpeningRelation};
use spark::spark3::{flexible, FlexibleSpark};
use sponge::sponge::Duplex;
use sumcheck::sumcheck2::{
    oracles::{
        composite::{CompositeOracle, CompositeReductionKey, ProverEvals},
        core::CoreOracle,
    },
    zerocheck::ZerocheckSumcheckReduction,
    SumcheckMessage, SumcheckVerifierKey,
};
use transcript::reduction2::{
    GuardedProof, ProverOutput, Reduction, Transcript, TranscriptBuilder, VerifierTranscript,
};

pub struct FlcsReduction;

type CompositeKey<F, C, const IO: usize, SF> =
    CompositeReductionKey<F, SF, CoreOracle<F, SF>, MatrixProductOracle<F, C, SF, IO>>;

pub struct VerifierKey<F, C, const IO: usize, const S: usize>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    sumcheck_key: SumcheckVerifierKey<F>,
    composite_key: CompositeKey<F, C, IO, FlcsEvals<(), IO, S>>,
    matrix_oracle_key: matrix_product::VerifierKey<F, C, FlcsEvals<(), IO, S>, IO>,
    spark_keys: [flexible::VerifierKey<F, C>; IO],
}

#[derive(Clone, Debug)]
pub struct Proof<F: Field, C: CommitmentScheme<F>, const IO: usize> {
    sumcheck_proof: Vec<SumcheckMessage<F>>,
    oracle_evals1: ProverEvals<F>,
    matrix_product: matrix_product::Proof<F>,
    spark_proofs: [flexible::Proof<F, C>; IO],
}

impl<F, C, const I: usize, const IO: usize, const S: usize>
    Reduction<F, FlcsRelation<F, C, I, IO, S>, OpeningRelation<F, C>> for FlcsReduction
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = VerifierKey<F, C, IO, S>;

    type Proof = Proof<F, C, IO>;

    type Error = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        _builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        todo!()
    }

    fn verifier_key(
        _structure_1: &FlcsStructure<F, C, IO, S>,
        _structure_2: &C,
    ) -> Self::VerifierKey {
        todo!()
    }

    fn key_pair(
        _structure_1: &FlcsStructure<F, C, IO, S>,
        _structure_2: &C,
    ) -> (Self::VerifierKey, Self::ProverKey) {
        todo!()
    }

    fn prove<D: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: FlcsInstance<F, C, IO, S>,
        _witness: Vec<F>,
        _transcript: &mut Transcript<F, D>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        todo!()
    }

    fn verify<D: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: FlcsInstance<F, C, IO, S>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, D>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        let instance = instance.0;

        let instance =
            ZerocheckSumcheckReduction::<F, FlcsOracle<F, C, FlcsEvals<(), IO, S>, IO>>::verify(
                &key.sumcheck_key,
                instance,
                proof.clone().map(|proof| proof.sumcheck_proof),
                transcript,
            )
            //TODO: handle
            .unwrap();

        let (core_instance, matrix_instance) = CompositeOracle::verify(
            &key.composite_key,
            instance,
            proof.clone().map(|proof| proof.oracle_evals1),
            transcript,
        )
        //TODO: handle
        .unwrap();

        CoreOracle::verify(
            key.composite_key.p1_key(),
            core_instance,
            GuardedProof::empty(),
            transcript,
        )
        //TODO:handle
        .unwrap();

        let (open_instances, spark_instances) = MatrixProductReduction::verify(
            &key.matrix_oracle_key,
            matrix_instance,
            proof.clone().map(|proof| proof.matrix_product),
            transcript,
        )
        //TODO:handle
        .unwrap();

        let [open_instance1, open_instance2] = open_instances;

        let open_instance3 = {
            let mut instances = [(); IO].map(|_| None);

            for (i, (key, instance)) in key.spark_keys.iter().zip(spark_instances).enumerate() {
                let proof = proof.clone().map(|proof| proof.spark_proofs[i].clone());
                //TODO:handle
                let open_instance =
                    FlexibleSpark::verify(key, instance, proof, transcript).unwrap();
                instances[i] = Some(open_instance);
            }

            let instances: [OpenInstance<F, C>; IO] = instances.map(Option::unwrap);
            instances
        };

        let _ = ([open_instance1, open_instance2], open_instance3);

        todo!()
    }
}
