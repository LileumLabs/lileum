use crate::lilium2::oracles::{MatrixOracleQuery, MatrixProductInstance, MatrixProductOracle};
use ark_ff::Field;
use commit::commit2::{CommitmentScheme, OpenInstance, OpeningRelation};
use sponge::sponge::Duplex;
use std::marker::PhantomData;
use sumcheck::sumcheck2::oracles::{partial::PartialQueryInstance, SumcheckFunction};
use transcript::reduction2::{
    GuardedProof, ProverOutput, Reduction, Transcript, TranscriptBuilder, VerifierTranscript,
};

#[allow(dead_code)]
pub struct MatrixProductReduction;

pub struct VerifierKey<F, C, SF, const N: usize>(PhantomData<(F, C, SF)>);

impl<F, C, SF, const N: usize> Reduction<F, MatrixOracleQuery<F, C, SF, N>, OpeningRelation<F, C>>
    for MatrixProductReduction
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F>,
{
    type ProverKey = ();

    type VerifierKey = VerifierKey<F, C, SF, N>;

    type Proof = ();

    type Error = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        _builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        todo!()
    }

    fn verifier_key(
        _structure_1: &MatrixProductOracle<F, C, SF, N>,
        _structure_2: &C,
    ) -> Self::VerifierKey {
        todo!()
    }

    fn key_pair(
        _structure_1: &MatrixProductOracle<F, C, SF, N>,
        _structure_2: &C,
    ) -> (Self::VerifierKey, Self::ProverKey) {
        todo!()
    }

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: PartialQueryInstance<F, SF, MatrixProductInstance<F, C>>,
        _witness: Vec<SF::Mles<F>>,
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        todo!()
    }

    fn verify<S: Duplex<F>>(
        _key: &Self::VerifierKey,
        _instance: PartialQueryInstance<F, SF, MatrixProductInstance<F, C>>,
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        todo!()
    }
}
