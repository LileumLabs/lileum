use crate::{Message, Reduction, Relation, Transcript, message::PointRound};
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use sponge::sponge::{Duplex, SpongeBuilder};
use std::any::{TypeId, type_name};

#[derive(Clone, Copy, Debug)]
pub(crate) struct Round {
    pub name: &'static str,
    pub id: TypeId,
    pub message_len: usize,
    pub challenges: usize,
}

impl Round {
    fn new<F, M: Message<F>>(params: &M::Params, challenges: usize) -> Self {
        let name = type_name::<M>();
        let id = TypeId::of::<M>();
        let message_len = M::len(params);

        Self {
            name,
            id,
            message_len,
            challenges,
        }
    }
}

/// Builder to define the shape all interactions in some
/// reduction should follow.
pub struct TranscriptBuilder {
    rounds: Vec<Round>,
    sponge: SpongeBuilder,
}

impl TranscriptBuilder {
    pub(crate) fn new(domain_separation: [u8; 32]) -> Self {
        let sponge = SpongeBuilder::new(domain_separation);
        let rounds = vec![];
        Self { rounds, sponge }
    }

    /// Add a round where the prover sends message M to the verifier, and the verifier
    /// responds with N challenges.
    pub fn round<F: Field, M: Message<F>, const N: usize>(self, params: &M::Params) -> Self {
        let Self { mut rounds, sponge } = self;

        let round = Round::new::<F, M>(params, N);

        let sponge = sponge
            .absorb(round.message_len as u32)
            .squeeze(round.challenges as u32);

        rounds.push(round);

        Self { rounds, sponge }
    }

    /// Add a round where the verifier send a challenge point of given number of variables.
    pub fn point<F: Field>(self, vars: usize) -> Self {
        let Self { mut rounds, sponge } = self;
        let round = Round::new::<F, PointRound>(&(), vars);

        let sponge = sponge.squeeze(round.challenges as u32);
        rounds.push(round);

        Self { rounds, sponge }
    }

    pub(crate) fn finish<F: Field, S: Duplex<F>>(self) -> TranscriptDescriptor<F, S> {
        let Self { rounds, sponge } = self;
        let sponge = S::from_builder(sponge);
        TranscriptDescriptor { sponge, rounds }
    }

    /// Run some other reduction, same as `R::transcript_pattern(key, builder)`.
    pub fn subprotocol<R, F, R1, R2>(self, key: &R::VerifierKey) -> Self
    where
        F: Field,
        R1: Relation,
        R2: Relation,
        R: Reduction<F, R1, R2>,
    {
        R::transcript_pattern(key, self)
    }
}

/// A finished and immutable transcript. It can no longer be changed,
/// but it can be instantiated into a transcript to run the corresponding
/// interaction.
pub(crate) struct TranscriptDescriptor<F: Field, S: Duplex<F>> {
    sponge: S::Initializer,
    rounds: Vec<Round>,
}

impl<F: Field, S: Duplex<F>> TranscriptDescriptor<F, S> {
    pub(crate) fn instantiate(&self) -> Transcript<F, S> {
        let sponge = S::instantiate(&self.sponge);
        let rounds = self.rounds.clone().into_iter();
        Transcript::new(sponge, rounds)
    }

    /// Creates a descriptor for the given reduction.
    pub(crate) fn for_reduction<R1, R2, R>(
        key: &R::VerifierKey,
        instance_params: &<R1::Instance as Message<F>>::Params,
    ) -> Self
    where
        R1: Relation,
        R1::Instance: Message<F>,
        R2: Relation,
        R: Reduction<F, R1, R2>,
    {
        let mut key_bytes: Vec<u8> = vec![];
        key.serialize_uncompressed(&mut key_bytes).unwrap();
        let domain_separation: [u8; 32] = blake3::hash(&key_bytes).into();

        TranscriptBuilder::new(domain_separation)
            .round::<F, R1::Instance, 0>(instance_params)
            .subprotocol::<R, F, R1, R2>(key)
            .finish()
    }
}
