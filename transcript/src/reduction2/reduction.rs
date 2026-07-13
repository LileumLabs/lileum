use super::Relation;
use crate::reduction2::{
    FoldingRelation, GuardedProof, Transcript, TranscriptBuilder, VerifierTranscript,
};
use ark_ff::Field;
use sponge::sponge::Duplex;
use std::fmt::Debug;

pub struct ProverOutput<R: Relation, P> {
    pub instance: R::Instance,
    pub witness: R::Witness,
    pub proof: P,
}

impl<R1: Relation, R2: Relation, P> ProverOutput<(R1, R2), (P, P)> {
    pub fn combine_tuple(a: ProverOutput<R1, P>, b: ProverOutput<R2, P>) -> Self {
        Self {
            instance: (a.instance, b.instance),
            witness: (a.witness, b.witness),
            proof: (a.proof, b.proof),
        }
    }
}

impl<R: Relation, P> ProverOutput<R, P> {
    pub fn map_rel<R2: Relation, F1, F2>(self, f1: F1, f2: F2) -> ProverOutput<R2, P>
    where
        F1: FnOnce(R::Instance) -> R2::Instance,
        F2: FnOnce(R::Witness) -> R2::Witness,
    {
        let Self {
            instance,
            witness,
            proof,
        } = self;
        let instance = f1(instance);
        let witness = f2(witness);
        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    pub fn map_proof<P2, F: FnOnce(P) -> P2>(self, f: F) -> ProverOutput<R, P2> {
        let Self {
            instance,
            witness,
            proof,
        } = self;
        let proof = f(proof);
        ProverOutput {
            instance,
            witness,
            proof,
        }
    }
}

/// A reduction from relation R1 to R2.
pub trait Reduction<F: Field, R1: Relation, R2: Relation> {
    type ProverKey;
    type VerifierKey;
    type Proof: Clone;
    type Error: Clone + Debug;

    /// Defines the shape of the interactive protocol, any interactions which
    /// deviate from it will result in panics in the prover and errors in the
    /// verifier.
    fn transcript_pattern(key: &Self::VerifierKey, builder: TranscriptBuilder)
        -> TranscriptBuilder;

    fn verifier_key(structure_1: &R1::Structure, structure_2: &R2::Structure) -> Self::VerifierKey;

    fn key_pair(
        structure_1: &R1::Structure,
        structure_2: &R2::Structure,
    ) -> (Self::VerifierKey, Self::ProverKey);

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: R1::Instance,
        witness: R1::Witness,
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<R2, Self::Proof>;

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: R1::Instance,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<R2::Instance, Self::Error>;
}

/// An argument is just a reduction where the target relation is unit.
pub trait Argument<F: Field, R: Relation>: Reduction<F, R, ()> {}

/// A reduction from R x R -> R.
pub trait FoldingScheme<F: Field, R: Relation>: Reduction<F, FoldingRelation<R>, R> {}
