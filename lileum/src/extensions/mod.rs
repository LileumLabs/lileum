use alloc::vec::Vec;
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use commit::CommitmentScheme;
use core::{fmt::Debug, marker::PhantomData};
use lcs::extensions::{LcsExtension, Never};
use reduction::{
    FoldingRelation, FoldingScheme, GuardedProof, Message, NoError, ProverOutput, Reduction,
    Relation, TranscriptBuilder, VerifierTranscript,
};

pub mod aggregation;

use crate::extensions::aggregation::{
    AggregationProof, AggregationVerifierKey, UnitAggregation, sealed::Aggregate,
};

pub trait ExtensionRelation<F, C, I = (), W = (), S = ()>:
    Relation<Instance = (C::Commitment, I), Witness = (Vec<F>, W), Structure = S>
where
    F: Field,
    C: CommitmentScheme<F>,
{
}

pub trait Extension<F, C>: LcsExtension<F> + Clone + Debug + 'static
where
    F: Field,
    C: CommitmentScheme<F>,
    <Self::R2 as Relation>::Instance: Clone + Debug + Eq + Message<F, Params = (), Error = NoError>,
    <Self::Reduction2 as Reduction<F, Self::R2, Self::R3>>::VerifierKey:
        Clone + Debug + CanonicalSerialize,
    <Self::Reduction2 as Reduction<F, Self::R2, Self::R3>>::Proof: Clone + Debug,
    <Self::R3 as Relation>::Structure: Clone,
    AggregationVerifierKey<F, C, Self>: Clone + Debug,
    AggregationProof<F, C, Self>: Debug,
{
    type Instance: Clone + Message<F, Params = (), Error = NoError>;

    type R1: ExtensionRelation<F, C, Self::Instance, Self::Witness, Self::Structure>;
    type R2: Relation<Witness = Self::Witness> + Clone + Debug;
    type R3: Relation + Clone + Debug;

    fn derive_structure(r1_structure: &Self::Structure) -> <Self::R2 as Relation>::Structure;

    fn commit_witness(pcs: &C, witness: &Self::Witness) -> Self::Instance;

    type Reduction1: Reduction<
            F,
            Self::R1,
            Self::R2,
            Proof = (),
            Error = NoError,
            VerifierKey = (),
            ProverKey = (),
        >;
    type Reduction2: Reduction<F, Self::R2, Self::R3> + Clone + Debug;
    // Aggregates the R3 instance-witness into the lileum's core
    // argument.
    // The trait can't be implemented outside this crate, one
    // of the available implementations should be chosen from
    // the `aggregation` module.
    // Generally, the intension is to support instances isomorphic
    // to [OpenInstance; N].
    type AgregationScheme: Aggregate<F, C, Self::R3>;

    /// The type `NoFolding` can be used when the extension doesn't support
    /// folding.
    type FoldingScheme: FoldingScheme<
            F,
            Self::R2,
            Proof: Debug + Clone,
            VerifierKey: Debug + Clone + CanonicalSerialize,
        >;
}

pub trait FoldableExtension<F, C>: Extension<F, C>
where
    F: Field,
    C: CommitmentScheme<F>,
{
}

/// A placeholder implementation of FoldingScheme, which works for any relation
/// but can't be instanciated.
pub struct NoFolding;

impl<F: Field, R: Relation> Reduction<F, FoldingRelation<R>, R> for NoFolding {
    type ProverKey = Never;

    type VerifierKey = Never;

    type Proof = Never;

    type Error = Never;

    type Params = Never;

    fn transcript_pattern(key: &Self::VerifierKey, _: TranscriptBuilder) -> TranscriptBuilder {
        match *key {}
    }

    fn verifier_key(_: &R::Structure) -> Self::VerifierKey {
        panic!("This Reduction is a placeholder, it shouldn't be instanciated");
    }

    fn key_pair(_: &R::Structure) -> (Self::VerifierKey, Self::ProverKey) {
        panic!("This Reduction is a placeholder, it shouldn't be instanciated");
    }

    fn params(key: &Never) -> Self::Params {
        match *key {}
    }

    fn prove<S: sponge::sponge::Duplex<F>>(
        key: &Self::ProverKey,
        _: [R::Instance; 2],
        _: [R::Witness; 2],
        _: &mut reduction::Transcript<F, S>,
    ) -> ProverOutput<R, Self::Proof> {
        match *key {}
    }

    fn verify<S: sponge::sponge::Duplex<F>>(
        key: &Self::VerifierKey,
        _: [R::Instance; 2],
        _: GuardedProof<Self::Proof>,
        _: &mut VerifierTranscript<F, S>,
    ) -> Result<<R as Relation>::Instance, Self::Error> {
        match *key {}
    }
}

mod indentity {
    use super::*;

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

        fn transcript_pattern(
            _: &Self::VerifierKey,
            builder: TranscriptBuilder,
        ) -> TranscriptBuilder {
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
}
