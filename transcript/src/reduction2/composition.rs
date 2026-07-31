use super::{
    transcript::VerifierTranscript, GuardedProof, ProverOutput, Reduction, Relation, Transcript,
};
use crate::reduction2::{Message, TranscriptBuilder};
use ark_ff::Field;
use sponge::sponge::Duplex;

pub use crate::reduction2::relations::CompoundRelation;

/// Sequential composition of reductions A and B, to and
/// from R respectively.
pub struct SeqComposition<A, B, R>(A, B, R);

#[derive(Clone, Debug)]
pub struct CompoundKey<A, B> {
    a_key: A,
    b_key: B,
}

#[derive(Clone, Copy, Debug)]
pub enum CompoundError<A, B> {
    ErrorInA(A),
    ErrorInB(B),
}

impl<F, R1, R2, R3, A, B> Reduction<F, CompoundRelation<R1, R2>, R3> for SeqComposition<A, B, R2>
where
    F: Field,
    R1: Relation,
    R2: Relation,
    R3: Relation,
    R1::Instance: Message<F>,
    R2::Instance: Message<F>,
    A: Reduction<F, R1, R2>,
    B: Reduction<F, R2, R3>,
{
    type ProverKey = CompoundKey<A::ProverKey, B::ProverKey>;

    type VerifierKey = CompoundKey<A::VerifierKey, B::VerifierKey>;

    type Proof = (A::Proof, B::Proof);

    type Error = CompoundError<A::Error, B::Error>;

    type Params = A::Params;

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        let builder = A::transcript_pattern(&key.a_key, builder);
        B::transcript_pattern(&key.b_key, builder)
    }

    fn verifier_key(structure: &(R1::Structure, R2::Structure)) -> Self::VerifierKey {
        let a_key = A::verifier_key(&structure.0);
        let b_key = B::verifier_key(&structure.1);
        CompoundKey { a_key, b_key }
    }

    fn key_pair(
        structure: &(R1::Structure, R2::Structure),
    ) -> (Self::VerifierKey, Self::ProverKey) {
        let (a_key_v, a_key_p) = A::key_pair(&structure.0);
        let (b_key_v, b_key_p) = B::key_pair(&structure.1);
        let verifier_key = CompoundKey {
            a_key: a_key_v,
            b_key: b_key_v,
        };
        let prover_key = CompoundKey {
            a_key: a_key_p,
            b_key: b_key_p,
        };
        (verifier_key, prover_key)
    }

    fn params(key: &Self::VerifierKey) -> Self::Params {
        A::params(&key.a_key)
    }

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: R1::Instance,
        witness: R1::Witness,
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<R3, Self::Proof> {
        let ProverOutput {
            instance,
            witness,
            proof: proof_a,
        } = A::prove(&key.a_key, instance, witness, transcript);
        let ProverOutput {
            instance,
            witness,
            proof: proof_b,
        } = B::prove(&key.b_key, instance, witness, transcript);
        let proof = (proof_a, proof_b);
        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: R1::Instance,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<R3::Instance, Self::Error> {
        let (proof_a, proof_b) = proof.split();

        let instance = A::verify(&key.a_key, instance, proof_a, transcript)
            .map_err(CompoundError::ErrorInA)?;

        let instance = B::verify(&key.b_key, instance, proof_b, transcript)
            .map_err(CompoundError::ErrorInB)?;

        Ok(instance)
    }
}
