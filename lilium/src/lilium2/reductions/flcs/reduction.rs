use crate::lilium2::relations::{FlcsInstance, FlcsRelation, FlcsStructure};
use ark_ff::Field;
use commit::commit2::{CommitmentScheme, OpenInstance, OpeningRelation};
use sponge::sponge::Duplex;
use transcript::reduction2::{
    GuardedProof, ProverOutput, Reduction, Transcript, TranscriptBuilder, VerifierTranscript,
};

#[allow(dead_code)]
struct FlcsReduction;

impl<F, C, const I: usize, const IO: usize, const S: usize>
    Reduction<F, FlcsRelation<F, C, I, IO, S>, OpeningRelation<F, C>> for FlcsReduction
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = ();

    type Proof = ();

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
        _key: &Self::VerifierKey,
        _instance: FlcsInstance<F, C, IO, S>,
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, D>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        todo!()
    }
}
