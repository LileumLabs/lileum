use crate::reduction2::{
    message::PointRound, transcript_builder::Round, Error, GuardedProof, Message,
};
use ark_ff::Field;
use sponge::sponge::Duplex;
use std::{
    any::{type_name, Any, TypeId},
    marker::PhantomData,
    vec::IntoIter,
};

/// Protects a potential protocol message, preventing any access
/// which could bypass the transcript.
pub struct Guard<A> {
    inner: A,
    // This will later allow to avoid reabsorbing messages.
    observed: bool,
}

impl<A> Guard<A> {
    pub(crate) fn new(inner: A) -> Self {
        Self {
            inner,
            observed: false,
        }
    }

    /*fn new_observed(inner: A) -> Self {
        Self {
            inner,
            observed: true,
        }
    }*/

    pub fn open(self) -> A {
        let Self { inner, observed } = self;
        assert!(observed);
        inner
    }

    pub fn open_ref(&self) -> &A {
        assert!(self.observed);
        &self.inner
    }

    pub fn map<B, F: Fn(A) -> B>(self, f: F) -> Guard<B> {
        let Self { inner, observed } = self;
        assert!(!observed);
        let inner = f(inner);
        Guard { inner, observed }
    }
}

/// The interaction transcript, which allows prover and verifier to
/// send an receive messages through its methods.
/// It also prevents any interaction that deviates from that defined
/// in the reduction.
pub struct Transcript<F, S> {
    sponge: S,
    rounds: IntoIter<Round>,
    _f: PhantomData<F>,
}

impl<F: Field, S: Duplex<F>> Transcript<F, S> {
    pub(crate) fn new(sponge: S, rounds: IntoIter<Round>) -> Self {
        Self {
            sponge,
            rounds,
            _f: PhantomData,
        }
    }

    /// Send message M to verifier and get back N challenges.
    pub fn send_message<M, const N: usize>(&mut self, message: &M, params: &M::Params) -> [F; N]
    where
        M: Any + Message<F>,
    {
        let id = message.type_id();

        let round = match self.rounds.next() {
            Some(round) => round,
            None => {
                panic!("Unexpected Message");
            }
        };

        let elems = match message.to_field_elements(params) {
            Ok(elems) => elems,
            Err(err) => {
                panic!("Call to to_field_elements() returned error: \n {:?}", err);
            }
        };

        assert_eq!(
            id,
            round.id,
            "Unexpected type of message\n expected:\n {}\ngot:\n {} ",
            round.name,
            type_name::<M>()
        );
        assert_eq!(
            elems.len(),
            round.message_len,
            "Unexpected number of elements"
        );
        assert_eq!(
            N, round.challenges,
            "Unexpected number of challenges requested"
        );

        for elem in elems.into_iter() {
            // This shouldn't fail as we are checking length before.
            self.sponge.absorb(elem).unwrap();
        }

        // This also shouldn't fail as we check the length.
        [(); N].map(|_| self.sponge.squeeze().unwrap())
    }

    /// Receive challenge multivariate point from the verifier.
    pub fn point(&mut self) -> Vec<F> {
        let round = match self.rounds.next() {
            Some(round) => round,
            None => {
                panic!("Unexpected Message");
            }
        };
        let id = TypeId::of::<PointRound>();
        assert_eq!(
            round.id, id,
            "Requesting a point was not expected at this round"
        );
        // Shouldn't fail as the length was checked.
        let challenges = (0..round.challenges).map(|_| self.sponge.squeeze().unwrap());
        challenges.into_iter().collect()
    }

    pub(crate) fn finish(self) {
        self.sponge.finish().unwrap()
    }
}

pub struct VerifierTranscript<F, S> {
    sponge: S,
    rounds: IntoIter<Round>,
    _f: PhantomData<F>,
}

impl<F, S> VerifierTranscript<F, S>
where
    F: Field,
    S: Duplex<F>,
{
    /// Receive message from the prover and respond with N challenges.
    pub fn receive_message<M, P, Q, const N: usize>(
        &mut self,
        query: Q,
        proof: &GuardedProof<P>,
        params: &M::Params,
    ) -> Result<(M, [F; N]), M::Error>
    where
        M: Message<F>,
        Q: Fn(&P) -> M,
    {
        let message: M = query(proof.inner());
        self.unwrap_guard(Guard::new(message), params)
    }

    /// Send challenge multivariate point.
    pub fn point(&mut self) -> Vec<F> {
        let round = match self.rounds.next() {
            Some(round) => round,
            None => {
                panic!("Unexpected Message");
            }
        };
        let id = TypeId::of::<PointRound>();
        assert_eq!(
            round.id, id,
            "Requesting a point was not expected at this round"
        );
        // Shouldn't fail as the length was checked.
        let challenges = (0..round.challenges).map(|_| self.sponge.squeeze().unwrap());
        challenges.into_iter().collect()
    }

    /// Like [Self::receive_message], but when you already have the message
    /// under some [Guard].
    pub fn unwrap_guard<M: Message<F>, const N: usize>(
        &mut self,
        message: Guard<M>,
        params: &M::Params,
    ) -> Result<(M, [F; N]), M::Error> {
        let message = message.inner;

        let id = message.type_id();

        let round = match self.rounds.next() {
            Some(round) => round,
            None => {
                panic!("Unexpected Message");
            }
        };

        let elems = message.to_field_elements(params)?;

        assert_eq!(
            id,
            round.id,
            "Unexpected type of message\n expected:\n {}\ngot:\n {} ",
            round.name,
            type_name::<M>()
        );
        assert_eq!(
            elems.len(),
            round.message_len,
            "Unexpected number of elements"
        );
        assert_eq!(
            N, round.challenges,
            "Unexpected number of challenges requested"
        );

        for elem in elems.into_iter() {
            // This shouldn't fail as we are checking the length before.
            self.sponge.absorb(elem).unwrap();
        }

        // This also shouldn't fail as we checked the length.
        let challenges = [(); N].map(|_| self.sponge.squeeze().unwrap());

        Ok((message, challenges))
    }

    /// Wrap some message into a [Guard].
    pub fn wrap<M: Message<F>>(&self, message: M) -> Guard<M> {
        Guard::new(message)
    }

    pub(crate) fn new(transcript: Transcript<F, S>) -> Self {
        let Transcript { sponge, rounds, _f } = transcript;
        Self { sponge, rounds, _f }
    }

    pub(crate) fn finish(self) -> Result<(), Error> {
        let Self {
            sponge,
            mut rounds,
            _f,
        } = self;

        sponge.finish().map_err(Error::SpongeError)?;

        if rounds.next().is_some() {
            return Err(Error::UnexpectedFinish);
        }

        Ok(())
    }
}
