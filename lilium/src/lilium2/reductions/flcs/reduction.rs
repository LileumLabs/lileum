use crate::lilium2::{
    oracles2::{FlcsOracle, MatrixProductOracle},
    reductions::flcs::FlcsEvals,
    relations::{FlcsInstance, FlcsRelation, FlcsStructure},
};
use ark_ff::Field;
use commit::commit2::{CommitmentScheme, OpenInstance, OpeningRelation};
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

#[allow(dead_code)]
struct FlcsReduction;

type CompositeKey<F, C, const IO: usize, SF> =
    CompositeReductionKey<F, SF, CoreOracle<F, SF>, MatrixProductOracle<F, C, SF, IO>>;

#[allow(dead_code)]
struct VerifierKey<F, C, const IO: usize, const S: usize>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    sumcheck_key: SumcheckVerifierKey<F>,
    composite_key: CompositeKey<F, C, IO, FlcsEvals<(), IO, S>>,
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
struct Proof<F> {
    sumcheck_proof: Vec<SumcheckMessage<F>>,
    oracle_evals1: ProverEvals<F>,
}

impl<F, C, const I: usize, const IO: usize, const S: usize>
    Reduction<F, FlcsRelation<F, C, I, IO, S>, OpeningRelation<F, C>> for FlcsReduction
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = VerifierKey<F, C, IO, S>;

    type Proof = Proof<F>;

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

        let (core, committed) = CompositeOracle::verify(
            &key.composite_key,
            instance,
            proof.map(|proof| proof.oracle_evals1),
            transcript,
        )
        //TODO: handle
        .unwrap();

        let _ = (core, committed);
        // let (core, matrix) = key.composite_key.p2_key().split(composite);

        todo!()
    }
}
