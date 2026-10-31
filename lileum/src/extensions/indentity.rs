use crate::extensions::{
    Extension, ExtensionRelation, FoldableExtension, aggregation::UnitAggregation,
};
use alloc::vec::Vec;
use ark_ff::Field;
use commit::CommitmentScheme;
use core::marker::PhantomData;
use reduction::{
    GuardedProof, NoError, ProverOutput, Reduction, Relation, TranscriptBuilder, VerifierTranscript,
};

pub struct IdentityRelation<F, C>(PhantomData<(F, C)>);

impl<F, C> Relation for IdentityRelation<F, C>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Structure = ();

    type Instance = (C::Commitment, ());

    type Witness = (Vec<F>, ());

    fn check(_: &(), _: &(C::Commitment, ()), _: &(Vec<F>, ())) -> bool {
        true
    }
}

impl<F, C> ExtensionRelation<F, C> for IdentityRelation<F, C>
where
    F: Field,
    C: CommitmentScheme<F>,
{
}

pub struct IdentityReduction;

impl<F, C> Reduction<F, IdentityRelation<F, C>, ()> for IdentityReduction
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = ();

    type Proof = ();

    type Error = NoError;

    type Params = ();

    fn transcript_pattern(_: &Self::VerifierKey, builder: TranscriptBuilder) -> TranscriptBuilder {
        builder
    }

    fn verifier_key(_: &()) -> Self::VerifierKey {}

    fn key_pair(_: &()) -> (Self::VerifierKey, Self::ProverKey) {
        ((), ())
    }

    fn params(_: &()) -> Self::Params {}

    fn prove<S>(
        _key: &(),
        _instance: (C::Commitment, ()),
        _witness: (Vec<F>, ()),
        _transcript: &mut reduction::Transcript<F, S>,
    ) -> ProverOutput<(), Self::Proof> {
        ProverOutput {
            instance: (),
            witness: (),
            proof: (),
        }
    }

    fn verify<S>(
        _key: &Self::VerifierKey,
        _instance: (C::Commitment, ()),
        _proof: GuardedProof<()>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl<F: Field, C: CommitmentScheme<F>> Extension<F, C> for () {
    type Instance = ();

    type R1 = IdentityRelation<F, C>;

    type R2 = ();

    type R3 = ();

    fn derive_structure(_: &()) {}

    fn commit_witness(_: &C, _: &()) {}

    type Reduction1 = IdentityReduction;

    type Reduction2 = ();

    type AgregationScheme = UnitAggregation;

    type FoldingScheme = ();
}

impl<F: Field, C: CommitmentScheme<F>> FoldableExtension<F, C> for () {}
