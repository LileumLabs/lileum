use alloc::vec::Vec;
use ark_ff::Field;
use commit::{CommitmentScheme, OpeningRelation};
use core::marker::PhantomData;
use lcs::extensions::LcsExtension;
use reduction::{GuardedProof, NoError, Reduction, Relation, VerifierTranscript};

pub trait ExtensionRelation<F, C, I = (), W = (), S = ()>:
    Relation<Instance = (C::Commitment, I), Witness = (Vec<F>, W), Structure = S>
where
    F: Field,
    C: CommitmentScheme<F>,
{
}

pub trait Extension<F: Field, C: CommitmentScheme<F>>: LcsExtension<F> {
    type Instance;
    type Witness;
    type Structure;

    type R1: ExtensionRelation<F, C, Self::Instance, Self::Witness, Self::Structure>;
    type R2: Relation;

    type Reduction1: Reduction<F, Self::R1, Self::R2>;
    type Reduction2: Reduction<F, Self::R2, OpeningRelation<F, C>>;
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

impl<F, C> Reduction<F, IdentityRelation<F, C>, OpeningRelation<F, C>> for IdentityReduction
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
    ) -> reduction::ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        panic!("() shouldn't actually be used as an extension")
    }

    fn verify<S>(
        _key: &Self::VerifierKey,
        _instance: (C::Commitment, ()),
        _proof: GuardedProof<()>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<<OpeningRelation<F, C> as Relation>::Instance, Self::Error> {
        panic!("() shouldn't actually be used as an extension")
    }
}

impl<F: Field, C: CommitmentScheme<F>> Extension<F, C> for () {
    type Instance = ();

    type Witness = ();

    type Structure = ();

    type R1 = IdentityRelation<F, C>;

    type R2 = OpeningRelation<F, C>;

    type Reduction1 = IdentityReduction;

    type Reduction2 = ();
}
