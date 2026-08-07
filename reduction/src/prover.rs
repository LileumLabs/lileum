use crate::{transcript_builder::TranscriptDescriptor, Message, ProverOutput, Reduction, Relation};
use ark_ff::Field;
use sponge::sponge::Duplex;

/// A prover for relation R.
pub struct Prover<F, S, R1, R2, R>
where
    F: Field,
    R1: Relation,
    R1::Instance: Message<F>,
    R2: Relation,
    S: Duplex<F>,
    R: Reduction<F, R1, R2>,
{
    key: R::ProverKey,
    params: <R1::Instance as Message<F>>::Params,
    transcript_descriptor: TranscriptDescriptor<F, S>,
}

impl<F, S, R1, R2, R> Prover<F, S, R1, R2, R>
where
    F: Field,
    R1: Relation,
    R1::Instance: Message<F>,
    R2: Relation,
    S: Duplex<F>,
    R: Reduction<F, R1, R2, Params = <R1::Instance as Message<F>>::Params>,
{
    /// Creates prover from the structures of both relations.
    pub fn new(structure: &R1::Structure) -> Self {
        let (verifier_key, key) = R::key_pair(structure);

        let params = R::params(&verifier_key);

        let transcript_descriptor =
            TranscriptDescriptor::for_reduction::<R1, R2, R>(&verifier_key, &params);

        Self {
            key,
            params,
            transcript_descriptor,
        }
    }

    /// Prove an instance-witness pair.
    pub fn prove(
        &self,
        instance: R1::Instance,
        witness: R1::Witness,
    ) -> ProverOutput<R2, R::Proof> {
        let mut transcript = self.transcript_descriptor.instantiate();
        let [] = transcript.send_message(&instance, &self.params);
        let out = R::prove(&self.key, instance, witness, &mut transcript);
        transcript.finish();
        out
    }
}
