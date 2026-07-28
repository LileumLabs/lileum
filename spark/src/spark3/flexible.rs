use crate::spark3::{
    prove,
    reduction::{self, SparkError},
    sumcheck_argument::SparkEvals,
    FlexibleSparkRelation, FlexibleSparkStructure, SparkInstance, SparkReduction, SparseMle,
    StaticSparkStructure,
};
use ark_ff::Field;
use commit::commit2::{CommitmentScheme, OpenInstance, OpeningRelation};
use sponge::sponge::Duplex;
use std::rc::Rc;
use transcript::reduction2::{
    GuardedProof, ProverOutput, Reduction, Transcript, TranscriptBuilder, VerifierTranscript,
};

/// Wrapper which dynamically chooses N as required, currently implemented up to
/// 64 bits/8 segments.
#[derive(Clone, Copy, Debug)]
pub enum FlexibleSpark<F: Field, C: CommitmentScheme<F>> {
    S1(SparkReduction<F, C, 1>),
    S2(SparkReduction<F, C, 2>),
    S3(SparkReduction<F, C, 3>),
    S4(SparkReduction<F, C, 4>),
    S5(SparkReduction<F, C, 5>),
    S6(SparkReduction<F, C, 6>),
    S7(SparkReduction<F, C, 7>),
    S8(SparkReduction<F, C, 8>),
}

pub enum VerifierKey<F, C>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    S1(reduction::Key<F, C, SparkEvals<(), 1>, 1>),
    S2(reduction::Key<F, C, SparkEvals<(), 2>, 2>),
    S3(reduction::Key<F, C, SparkEvals<(), 3>, 3>),
    S4(reduction::Key<F, C, SparkEvals<(), 4>, 4>),
    S5(reduction::Key<F, C, SparkEvals<(), 5>, 5>),
    S6(reduction::Key<F, C, SparkEvals<(), 6>, 6>),
    S7(reduction::Key<F, C, SparkEvals<(), 7>, 7>),
    S8(reduction::Key<F, C, SparkEvals<(), 8>, 8>),
}

pub enum ProverKey<F, C>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    S1(prove::ProverKey<F, C, 1>),
    S2(prove::ProverKey<F, C, 2>),
    S3(prove::ProverKey<F, C, 3>),
    S4(prove::ProverKey<F, C, 4>),
    S5(prove::ProverKey<F, C, 5>),
    S6(prove::ProverKey<F, C, 6>),
    S7(prove::ProverKey<F, C, 7>),
    S8(prove::ProverKey<F, C, 8>),
}

#[derive(Clone, Debug)]
pub enum Proof<F: Field, C: CommitmentScheme<F>> {
    S1(reduction::Proof<F, C, 1>),
    S2(reduction::Proof<F, C, 2>),
    S3(reduction::Proof<F, C, 3>),
    S4(reduction::Proof<F, C, 4>),
    S5(reduction::Proof<F, C, 5>),
    S6(reduction::Proof<F, C, 6>),
    S7(reduction::Proof<F, C, 7>),
    S8(reduction::Proof<F, C, 8>),
}

type Rel1<F> = FlexibleSparkRelation<F>;
type Rel2<F, C> = OpeningRelation<F, C>;

#[derive(Clone, Copy, Debug)]
pub enum FlexibleSparkError {
    UnexpectedProofSize,
    Spark(SparkError),
}

impl<F, C> Reduction<F, Rel1<F>, Rel2<F, C>> for FlexibleSpark<F, C>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ProverKey<F, C>;

    type VerifierKey = VerifierKey<F, C>;

    type Proof = Proof<F, C>;

    type Error = FlexibleSparkError;

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        use VerifierKey::*;
        match key {
            S1(key) => SparkReduction::transcript_pattern(key, builder),
            S2(key) => SparkReduction::transcript_pattern(key, builder),
            S3(key) => SparkReduction::transcript_pattern(key, builder),
            S4(key) => SparkReduction::transcript_pattern(key, builder),
            S5(key) => SparkReduction::transcript_pattern(key, builder),
            S6(key) => SparkReduction::transcript_pattern(key, builder),
            S7(key) => SparkReduction::transcript_pattern(key, builder),
            S8(key) => SparkReduction::transcript_pattern(key, builder),
        }
    }

    fn verifier_key(structure: &FlexibleSparkStructure<F>, pcs: &C) -> Self::VerifierKey {
        let FlexibleSparkStructure { evals } = structure;
        assert!(evals.len().is_power_of_two());
        let max: u64 = evals
            .iter()
            .fold(0, |acc, (addr, _)| std::cmp::max(acc, *addr));
        let bits = max.next_power_of_two().ilog2();

        use VerifierKey::*;
        if bits == 0 {
            let structure = structure.static_structure();
            return S1(SparkReduction::verifier_key(&structure, pcs));
        }

        match bits - 1 {
            0..8 => S1(SparkReduction::verifier_key(
                &structure.static_structure(),
                pcs,
            )),
            8..16 => S2(SparkReduction::verifier_key(
                &structure.static_structure(),
                pcs,
            )),
            16..24 => S3(SparkReduction::verifier_key(
                &structure.static_structure(),
                pcs,
            )),
            24..32 => S4(SparkReduction::verifier_key(
                &structure.static_structure(),
                pcs,
            )),
            32..40 => S5(SparkReduction::verifier_key(
                &structure.static_structure(),
                pcs,
            )),
            40..48 => S6(SparkReduction::verifier_key(
                &structure.static_structure(),
                pcs,
            )),
            48..56 => S7(SparkReduction::verifier_key(
                &structure.static_structure(),
                pcs,
            )),
            56..64 => S8(SparkReduction::verifier_key(
                &structure.static_structure(),
                pcs,
            )),
            _ => panic!("unsupported (and impossible) size"),
        }
    }

    fn key_pair(
        structure: &FlexibleSparkStructure<F>,
        pcs: &C,
    ) -> (Self::VerifierKey, Self::ProverKey) {
        macro_rules! key_pair {
            ($vk_variant: path, $pk_variant: path) => {{
                let structure = structure.static_structure();
                let (vk, pk) = SparkReduction::key_pair(&structure, pcs);
                ($vk_variant(vk), $pk_variant(pk))
            }};
        }

        let FlexibleSparkStructure { evals } = structure;
        assert!(evals.len().is_power_of_two());
        let max: u64 = evals
            .iter()
            .fold(0, |acc, (addr, _)| std::cmp::max(acc, *addr));
        let bits = max.next_power_of_two().ilog2();

        if bits == 0 {
            let structure = structure.static_structure();
            let (vk, pk) = SparkReduction::key_pair(&structure, pcs);
            return (VerifierKey::S1(vk), ProverKey::S1(pk));
        }

        match bits - 1 {
            0..8 => {
                key_pair!(VerifierKey::S1, ProverKey::S1)
            }
            8..16 => {
                key_pair!(VerifierKey::S2, ProverKey::S2)
            }
            16..24 => {
                key_pair!(VerifierKey::S3, ProverKey::S3)
            }
            24..32 => {
                key_pair!(VerifierKey::S4, ProverKey::S4)
            }
            32..40 => {
                key_pair!(VerifierKey::S5, ProverKey::S5)
            }
            40..48 => {
                key_pair!(VerifierKey::S6, ProverKey::S6)
            }
            48..56 => {
                key_pair!(VerifierKey::S7, ProverKey::S7)
            }
            56..64 => {
                key_pair!(VerifierKey::S8, ProverKey::S8)
            }
            _ => panic!("unsupported (and impossible) size"),
        }
    }

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: SparkInstance<F>,
        _: (),
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<Rel2<F, C>, Self::Proof> {
        macro_rules! prove {
            ($variant:path,$key:ident) => {{
                let ProverOutput {
                    instance,
                    witness,
                    proof,
                } = SparkReduction::prove($key, instance, (), transcript);
                let proof = $variant(proof);
                ProverOutput {
                    instance,
                    witness,
                    proof,
                }
            }};
        }

        match key {
            ProverKey::S1(key) => {
                prove!(Proof::S1, key)
            }
            ProverKey::S2(key) => {
                prove!(Proof::S2, key)
            }
            ProverKey::S3(key) => {
                prove!(Proof::S3, key)
            }
            ProverKey::S4(key) => {
                prove!(Proof::S4, key)
            }
            ProverKey::S5(key) => {
                prove!(Proof::S5, key)
            }
            ProverKey::S6(key) => {
                prove!(Proof::S6, key)
            }
            ProverKey::S7(key) => {
                prove!(Proof::S7, key)
            }
            ProverKey::S8(key) => {
                prove!(Proof::S8, key)
            }
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: SparkInstance<F>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        use VerifierKey::*;

        macro_rules! verify {
            ($variant:path,$key:ident) => {{
                let proof = proof.try_map(|proof| {
                    if let $variant(proof) = proof {
                        Some(proof)
                    } else {
                        None
                    }
                });
                let proof = proof.map_err(|_| FlexibleSparkError::UnexpectedProofSize)?;
                let res = SparkReduction::verify($key, instance, proof, transcript);
                res.map_err(FlexibleSparkError::Spark)
            }};
        }

        match key {
            S1(key) => verify!(Proof::S1, key),
            S2(key) => verify!(Proof::S2, key),
            S3(key) => verify!(Proof::S3, key),
            S4(key) => verify!(Proof::S4, key),
            S5(key) => verify!(Proof::S5, key),
            S6(key) => verify!(Proof::S6, key),
            S7(key) => verify!(Proof::S7, key),
            S8(key) => verify!(Proof::S8, key),
        }
    }
}

impl<F: Field> FlexibleSparkStructure<F> {
    fn static_structure<const N: usize>(&self) -> StaticSparkStructure<F, N> {
        let (addresses, values) = self
            .evals
            .iter()
            .map(|(addr, val)| {
                let bytes: [u8; 8] = addr.to_le_bytes();
                let mut address_segments = [0; N];
                address_segments.copy_from_slice(&bytes[0..N]);
                (address_segments, val)
            })
            .unzip();
        let mle = SparseMle { addresses, values };
        StaticSparkStructure { mle: Rc::new(mle) }
    }
}
