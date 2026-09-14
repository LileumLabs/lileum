use crate::{
    reductions::{FlcsReduction, flcs::reduction},
    relations::{FlcsInstance, FlcsRelation, FlcsStructure},
};
use ::reduction::{
    Argument, GuardedProof, ProverOutput, Reduction, Transcript, TranscriptBuilder,
    VerifierTranscript,
};
use alloc::vec::Vec;
use ark_ff::Field;
use commit::CommitmentScheme;
use sponge::sponge::Duplex;
use sumcheck::oracles::partial::OracleParams;

#[derive(Clone, Copy, Debug)]
/// FLCS -> ()
pub struct FlcsArgument;

#[derive(Clone, Debug)]
pub struct Proof<F, C, const IO: usize>(reduction::Proof<F, C, IO>, C::Proof)
where
    F: Field,
    C: CommitmentScheme<F>;

#[derive(Clone, Debug)]
pub enum Error<F: Field, C: CommitmentScheme<F>> {
    Reduction(reduction::FlcsError),
    Pcs(C::Error),
}

impl<F, C, const I: usize, const IO: usize, const S: usize>
    Reduction<F, FlcsRelation<F, C, I, IO, S>, ()> for FlcsArgument
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = (reduction::ProverKey<F, C, IO, S, I>, C::ProverKey);

    type VerifierKey = (reduction::VerifierKey<F, C, IO, S, I>, C::VerifierKey);

    type Proof = Proof<F, C, IO>;

    type Error = Error<F, C>;

    type Params = (OracleParams, OracleParams);

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        builder
            .subprotocol::<FlcsReduction, _, _, _>(&key.0)
            .subprotocol::<C, _, _, _>(&key.1)
    }

    fn verifier_key(structure: &FlcsStructure<F, C, IO, S, I>) -> Self::VerifierKey {
        let pcs = &structure.pcs;
        let reduction_key = FlcsReduction::verifier_key(structure);
        let opening_key = C::verifier_key(pcs);

        (reduction_key, opening_key)
    }

    fn key_pair(structure: &FlcsStructure<F, C, IO, S, I>) -> (Self::VerifierKey, Self::ProverKey) {
        let pcs = &structure.pcs;
        let reduction_keys = FlcsReduction::key_pair(structure);
        let opening_keys = C::key_pair(pcs);

        let verifier_key = (reduction_keys.0, opening_keys.0);
        let prover_key = (reduction_keys.1, opening_keys.1);
        (verifier_key, prover_key)
    }

    fn params(key: &Self::VerifierKey) -> Self::Params {
        FlcsReduction::params(&key.0)
    }

    fn prove<D: Duplex<F>>(
        key: &Self::ProverKey,
        instance: FlcsInstance<F, C, IO, S, I>,
        witness: Vec<F>,
        transcript: &mut Transcript<F, D>,
    ) -> ProverOutput<(), Self::Proof> {
        let ProverOutput {
            instance,
            witness,
            proof: reduction_proof,
        } = FlcsReduction::prove(&key.0, instance, witness, transcript);

        let ProverOutput {
            instance,
            witness,
            proof: open_proof,
        } = C::prove(&key.1, instance, witness, transcript);

        let proof = Proof(reduction_proof, open_proof);

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
    ) -> Result<(), Self::Error> {
        let opening_instance = FlcsReduction::verify(
            &key.0,
            instance,
            proof.clone().map(|proof| proof.0),
            transcript,
        )
        .map_err(Error::Reduction)?;

        C::verify(
            &key.1,
            opening_instance,
            proof.map(|proof| proof.1),
            transcript,
        )
        .map_err(Error::Pcs)
    }
}

impl<F, C, const I: usize, const IO: usize, const S: usize>
    Argument<F, FlcsRelation<F, C, I, IO, S>> for FlcsArgument
where
    F: Field,
    C: CommitmentScheme<F>,
{
}
