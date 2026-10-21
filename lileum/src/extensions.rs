use alloc::vec::Vec;
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use commit::CommitmentScheme;
use core::{fmt::Debug, marker::PhantomData};
use lcs::extensions::LcsExtension;
use reduction::{
    GuardedProof, Message, NoError, ProverOutput, Reduction, Relation, VerifierTranscript,
};

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
    type Witness;

    type R1: ExtensionRelation<F, C, Self::Instance, Self::Witness, Self::Structure>;
    type R2: Relation + Clone + Debug;
    type R3: Relation + Clone + Debug;

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
}

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
        builder: reduction::TranscriptBuilder,
    ) -> reduction::TranscriptBuilder {
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

    type Witness = ();

    type R1 = IdentityRelation<F, C>;

    type R2 = ();

    type R3 = ();

    type Reduction1 = IdentityReduction;

    type Reduction2 = ();

    type AgregationScheme = UnitAggregation;
}

pub mod aggregation {
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
        }
    }

    pub type AggregationVerifierKey<F, C, E> =
        <<E as Extension<F, C>>::AgregationScheme as Reduction<
            F,
            AggregationRelation<F, C, <E as Extension<F, C>>::R3>,
            OpeningRelation<F, C>,
        >>::VerifierKey;

    pub type AggregationProverKey<F, C, E> =
        <<E as Extension<F, C>>::AgregationScheme as Reduction<
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

    impl<F: Field, C: CommitmentScheme<F>> sealed::Aggregate<F, C, ()> for UnitAggregation {}
}
