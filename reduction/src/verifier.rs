use crate::{
    GuardedProof, Message, Reduction, Relation, TranscriptBuilder, transcript::VerifierTranscript,
    transcript_builder::TranscriptDescriptor,
};

use ark_ff::Field;
use sponge::sponge::Duplex;

/// A verifier for relation R.
pub struct Verifier<F, S, R1, R2, R>
where
    F: Field,
    R1: Relation,
    R1::Instance: Message<F>,
    R2: Relation,
    S: Duplex<F>,
    R: Reduction<F, R1, R2>,
{
    key: R::VerifierKey,
    params: <R1::Instance as Message<F>>::Params,
    transcript_descriptor: TranscriptDescriptor<F, S>,
}

#[derive(Debug)]
pub enum VerificationError<F, R1, R2, R>
where
    F: Field,
    R1: Relation,
    R1::Instance: Message<F>,
    R2: Relation,
    R: Reduction<F, R1, R2>,
{
    InvalidInstance(<R1::Instance as Message<F>>::Error),
    ReductionError(R::Error),
}

impl<F, S, R1, R2, R> Verifier<F, S, R1, R2, R>
where
    F: Field,
    R1: Relation,
    R1::Instance: Message<F>,
    R2: Relation,
    S: Duplex<F>,
    R: Reduction<F, R1, R2, Params = <R1::Instance as Message<F>>::Params>,
{
    /// Creates verifier from the structures of both relations.
    pub fn new(structure: &R1::Structure) -> Self {
        let key = R::verifier_key(structure);

        let params = R::params(&key);

        let transcript_descriptor = TranscriptDescriptor::for_reduction::<R1, R2, R>(&key, &params);

        Verifier {
            key,
            params,
            transcript_descriptor,
        }
    }

    /// Verify that the instance is in R1 by the provided proof.
    pub fn verify(
        &self,
        instance: R1::Instance,
        proof: R::Proof,
    ) -> Result<R2::Instance, VerificationError<F, R1, R2, R>> {
        let transcript = self.transcript_descriptor.instantiate();
        let mut transcript = VerifierTranscript::<F, S>::new(transcript);

        let instance = transcript.wrap(instance);
        let (instance, []) = transcript
            .unwrap_guard(instance, &self.params)
            .map_err(VerificationError::InvalidInstance)?;
        let proof = GuardedProof::new(proof);

        let reduced = R::verify(&self.key, instance, proof, &mut transcript)
            .map_err(VerificationError::ReductionError);

        // This shouldn't be possible through the public API.
        if let Err(err) = transcript.finish() {
            // TODO: use let chain
            if reduced.is_ok() {
                panic!("Transcript error: {:?}", err);
            }
        }

        reduced
    }
}

/// There are reductions which are not intended to be used alone, from
/// relations whose instance is only supposed to exist transitively
/// during the protocol, and thus don't implement [`Message<F>`].
/// But it may still be desired to test them in isolation. For that
/// purpose, this verifier works similarly to [Verifier], but `R1::Instance`
/// doesn't need to implement [`Message<F>`].
pub struct UnsafeVerifier<F, S, R1, R2, R>
where
    F: Field,
    R1: Relation,
    R2: Relation,
    S: Duplex<F>,
    R: Reduction<F, R1, R2>,
{
    key: R::VerifierKey,
    transcript_descriptor: TranscriptDescriptor<F, S>,
}

impl<F, S, R1, R2, R> UnsafeVerifier<F, S, R1, R2, R>
where
    F: Field,
    R1: Relation,
    R2: Relation,
    S: Duplex<F>,
    R: Reduction<F, R1, R2>,
{
    /// Creates verifier from the structures of both relations.
    pub fn new(structure: &R1::Structure) -> Self {
        let key = R::verifier_key(structure);

        let transcript_descriptor = TranscriptBuilder::new()
            .subprotocol::<R, F, R1, R2>(&key)
            .finish();

        UnsafeVerifier {
            key,
            transcript_descriptor,
        }
    }

    /// Verify that the instance is in R1 by the provided proof. Panics
    /// if the reduction returns an error.
    pub fn verify(&self, instance: R1::Instance, proof: R::Proof) -> R2::Instance {
        let transcript = self.transcript_descriptor.instantiate();
        let mut transcript = VerifierTranscript::<F, S>::new(transcript);

        let proof = GuardedProof::new(proof);

        let reduced = R::verify(&self.key, instance, proof, &mut transcript);

        // This shouldn't be possible through the public API.
        if let Err(err) = transcript.finish() {
            // TODO: use let chain
            if reduced.is_ok() {
                panic!("Transcript error: {:?}", err);
            }
        }

        reduced.unwrap()
    }
}
