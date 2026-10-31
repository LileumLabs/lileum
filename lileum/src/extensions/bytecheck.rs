use crate::extensions::{
    Extension, ExtensionRelation, NoFolding, aggregation::SingleCommitAggregation,
};
use alloc::vec::Vec;
use ark_ff::{BigInteger, Field, PrimeField};
use commit::{CommitmentScheme, OpenInstance, OpeningRelation};
use core::marker::PhantomData;
use lcs::{circuit::Var, extensions::LcsExtension, structure::WitnessIndex};
use reduction::{
    GuardedProof, NoError, ProverOutput, Reduction, Relation, Transcript, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;

/// An extension providing an 8 bits range check.
#[derive(Clone, Debug, Default)]
pub struct ByteCheck;

impl<F: Field> LcsExtension<F> for ByteCheck {
    type Constraint = ();

    type StructureBuilder = Vec<Var<WitnessIndex>>;

    type WitnessBuilder = (Self::StructureBuilder, Vec<u8>);

    type Structure = Vec<bool>;

    // too constrained to be this for now
    // type Witness = ();
    type Witness = Vec<F>;

    fn process_structure(_builder: Self::StructureBuilder) -> Self::Structure {
        todo!()
    }

    fn process_witness(_builder: Self::WitnessBuilder) -> Self::Witness {
        todo!()
    }

    fn record_constraint<const N: usize>(
        builder: &mut Self::StructureBuilder,
        vars: [Var<WitnessIndex>; N],
        _: (),
    ) {
        assert_eq!(N, 1);
        let var = vars[0];
        builder.push(var);
    }

    fn compute_constraint<const N: usize>(witness: &mut Self::WitnessBuilder, vars: [F; N], _: ()) {
        assert_eq!(N, 1);
        assert!(vars[0] >= F::from(u8::MIN));
        assert!(vars[0] <= F::from(u8::MAX));
        let v = vars[0].to_base_prime_field_elements().next().unwrap();
        let v = v.into_bigint().to_bytes_le()[0];
        witness.1.push(v);
    }
}

pub struct ByteCheckRel1<F, C>(PhantomData<(F, C)>);

impl<F: Field, C: CommitmentScheme<F>> Relation for ByteCheckRel1<F, C> {
    type Structure = Vec<bool>;

    type Instance = (C::Commitment, ());

    type Witness = (Vec<F>, Vec<F>);

    fn check(structure: &Self::Structure, _: &Self::Instance, witness: &Self::Witness) -> bool {
        assert_eq!(witness.0, witness.1);
        if structure.len() != witness.0.len() {
            return false;
        }
        for (w, constrained) in witness.0.iter().zip(structure) {
            if *constrained {
                let ge = *w >= F::from(u8::MIN);
                let le = *w <= F::from(u8::MAX);
                if !(ge && le) {
                    return false;
                }
            }
        }
        true
    }
}

//TODO: maybe better for the generics to be S, I, W
impl<F: Field, C: CommitmentScheme<F>> ExtensionRelation<F, C, (), Vec<F>, Vec<bool>>
    for ByteCheckRel1<F, C>
{
}

#[derive(Clone, Debug)]
pub struct ByteCheckRel2<F, C>(PhantomData<(F, C)>);

impl<F: Field, C: CommitmentScheme<F>> Relation for ByteCheckRel2<F, C> {
    type Structure = Vec<bool>;

    type Instance = C::Commitment;

    type Witness = Vec<F>;

    fn check(
        _structure: &Self::Structure,
        _instance: &Self::Instance,
        _witness: &Self::Witness,
    ) -> bool {
        todo!()
    }
}

pub struct BytecheckReduction1;

impl<F, C> Reduction<F, ByteCheckRel1<F, C>, ByteCheckRel2<F, C>> for BytecheckReduction1
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = ();

    type Proof = ();

    type Error = NoError;

    type Params = ();

    fn transcript_pattern(_key: &(), builder: TranscriptBuilder) -> TranscriptBuilder {
        builder
    }

    fn verifier_key(_structure: &Vec<bool>) -> Self::VerifierKey {}

    fn key_pair(_structure: &Vec<bool>) -> (Self::VerifierKey, Self::ProverKey) {
        ((), ())
    }

    fn params(_key: &Self::VerifierKey) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: (C::Commitment, ()),
        _witness: (Vec<F>, Vec<F>),
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<ByteCheckRel2<F, C>, Self::Proof> {
        todo!()
    }

    fn verify<S: Duplex<F>>(
        _key: &Self::VerifierKey,
        _instance: (C::Commitment, ()),
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<C::Commitment, Self::Error> {
        todo!()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BytecheckReduction2;

impl<F, C> Reduction<F, ByteCheckRel2<F, C>, OpeningRelation<F, C>> for BytecheckReduction2
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = ();

    type Proof = ();

    type Error = NoError;

    type Params = ();

    fn transcript_pattern(_key: &(), builder: TranscriptBuilder) -> TranscriptBuilder {
        builder
    }

    fn verifier_key(_structure: &Vec<bool>) -> Self::VerifierKey {}

    fn key_pair(_structure: &Vec<bool>) -> (Self::VerifierKey, Self::ProverKey) {
        ((), ())
    }

    fn params(_key: &Self::VerifierKey) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: C::Commitment,
        _witness: Vec<F>,
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        todo!()
    }

    fn verify<S: Duplex<F>>(
        _key: &Self::VerifierKey,
        _instance: C::Commitment,
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        todo!()
    }
}

impl<F: Field, C: CommitmentScheme<F>> Extension<F, C> for ByteCheck {
    type Instance = ();

    type R1 = ByteCheckRel1<F, C>;

    type R2 = ByteCheckRel2<F, C>;

    type R3 = OpeningRelation<F, C>;

    fn derive_structure(_r1_structure: &Self::Structure) -> <Self::R2 as Relation>::Structure {
        todo!()
    }

    fn commit_witness(_pcs: &C, _witness: &Self::Witness) -> Self::Instance {
        todo!()
    }

    type Reduction1 = BytecheckReduction1;

    type Reduction2 = BytecheckReduction2;

    type AgregationScheme = SingleCommitAggregation;

    type FoldingScheme = NoFolding;
}
