use crate::extensions::Extension;
use alloc::vec::Vec;
use ark_ff::Field;
use commit::{CommitmentScheme, OpenInstance, OpeningRelation};
use core::marker::PhantomData;
use reduction::{
    GuardedProof, NoError, ProverOutput, Reduction, Relation, Transcript, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;

pub struct AggregationRelation<F, C, R>(PhantomData<(F, C, R)>);

impl<F, C, R> Relation for AggregationRelation<F, C, R>
where
    F: Field,
    C: CommitmentScheme<F>,
    R: Relation,
{
    type Structure = (C, R::Structure);

    type Instance = (OpenInstance<F, C>, R::Instance);

    type Witness = (Vec<F>, R::Witness);

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        if !OpeningRelation::check(&structure.0, &instance.0, &witness.0) {
            return false;
        }
        if !R::check(&structure.1, &instance.1, &witness.1) {
            return false;
        }
        true
    }
}

pub(crate) mod sealed {

    use super::*;
    // A reduction which can aggregate the output of an extension into
    // the core lileum argument.
    // It is implemented for supported relations, it shouldn't be implemented
    // outside of this crate.
    pub trait Aggregate<F: Field, C: CommitmentScheme<F>, R: Relation>:
        Reduction<F, AggregationRelation<F, C, R>, OpeningRelation<F, C>>
    {
        fn structure(pcs: C) -> R::Structure;
    }
}

pub type AggregationVerifierKey<F, C, E> =
    <<E as Extension<F, C>>::AgregationScheme as Reduction<
        F,
        AggregationRelation<F, C, <E as Extension<F, C>>::R3>,
        OpeningRelation<F, C>,
    >>::VerifierKey;

pub type AggregationProverKey<F, C, E> = <<E as Extension<F, C>>::AgregationScheme as Reduction<
    F,
    AggregationRelation<F, C, <E as Extension<F, C>>::R3>,
    OpeningRelation<F, C>,
>>::ProverKey;

pub type AggregationProof<F, C, E> = <<E as Extension<F, C>>::AgregationScheme as Reduction<
    F,
    AggregationRelation<F, C, <E as Extension<F, C>>::R3>,
    OpeningRelation<F, C>,
>>::Proof;

pub struct UnitAggregation;

impl<F: Field, C: CommitmentScheme<F>>
    Reduction<F, AggregationRelation<F, C, ()>, OpeningRelation<F, C>> for UnitAggregation
{
    type ProverKey = ();

    type VerifierKey = ();

    type Proof = ();

    type Error = NoError;

    type Params = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        builder
    }

    fn verifier_key(_: &(C, ())) -> Self::VerifierKey {}

    fn key_pair(_: &(C, ())) -> (Self::VerifierKey, Self::ProverKey) {
        ((), ())
    }

    fn params(_: &()) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        instance: (OpenInstance<F, C>, ()),
        witness: (Vec<F>, ()),
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        let (instance, ()) = instance;
        let (witness, ()) = witness;
        ProverOutput {
            instance,
            witness,
            proof: (),
        }
    }

    fn verify<S: Duplex<F>>(
        _key: &Self::VerifierKey,
        instance: (OpenInstance<F, C>, ()),
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        Ok(instance.0)
    }
}

impl<F: Field, C: CommitmentScheme<F>> sealed::Aggregate<F, C, ()> for UnitAggregation {
    fn structure(_: C) {}
}
