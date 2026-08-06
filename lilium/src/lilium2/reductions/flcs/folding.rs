use crate::lilium2::{
    oracles::FlcsOracle,
    reductions::flcs::{compute_sumcheck_witness, FlcsEvals},
    relations::{FlcsInstance, FlcsRelation, FlcsStructure},
};
use ark_ff::Field;
use ccs::matrix::Matrix;
use commit::commit2::CommitmentScheme;
use sponge::sponge::Duplex;
use std::rc::Rc;
use sumcheck::{
    folding::{ZeroFold, ZeroFoldKey},
    oracles::{partial::OracleParams, Oracle},
    SumcheckError, SumcheckMessage,
};
use transcript::{
    FoldingRelation, GuardedProof, ProverOutput, Reduction, Transcript, TranscriptBuilder,
    VerifierTranscript,
};

#[derive(Clone, Copy, Debug)]
/// FLCS x FLCS -> FLCS
pub struct FlcsFoldingScheme;

pub struct ProverKey<F, C, const IO: usize, const S: usize, const I: usize>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    structure: Rc<Vec<FlcsEvals<F, IO, S, I>>>,
    matrices: [Rc<Matrix>; IO],
    zerofold: ZeroFoldKey<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>,
}

#[derive(Clone, Debug)]
pub struct FoldingProof<F>(SumcheckMessage<F>);

#[derive(Clone, Copy, Debug)]
pub struct FoldingError(pub SumcheckError);

impl<F, C, const I: usize, const IO: usize, const S: usize>
    Reduction<F, FoldingRelation<FlcsRelation<F, C, I, IO, S>>, FlcsRelation<F, C, I, IO, S>>
    for FlcsFoldingScheme
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ProverKey<F, C, IO, S, I>;

    type VerifierKey = ZeroFoldKey<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>;

    type Proof = FoldingProof<F>;

    type Error = FoldingError;

    type Params = (OracleParams, OracleParams);

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        builder.subprotocol::<ZeroFold<F, _>, _, _, _>(key)
    }

    fn verifier_key(structure: &FlcsStructure<F, C, IO, S, I>) -> Self::VerifierKey {
        let oracle = &structure.oracle;
        ZeroFold::verifier_key(oracle)
    }

    fn key_pair(structure: &FlcsStructure<F, C, IO, S, I>) -> (Self::VerifierKey, Self::ProverKey) {
        let oracle = &structure.oracle;
        let verifier_key = ZeroFold::verifier_key(oracle);

        let matrices = structure.ccs_structure.io_matrices.clone().map(Rc::new);
        let structure = oracle.structure();
        let prover_key = ProverKey {
            structure,
            matrices,
            zerofold: verifier_key.clone(),
        };

        (verifier_key, prover_key)
    }

    fn params(key: &Self::VerifierKey) -> Self::Params {
        let oracle_params = key.params();
        (oracle_params, oracle_params)
    }

    fn prove<D: Duplex<F>>(
        key: &Self::ProverKey,
        instance: [FlcsInstance<F, C, IO, S, I>; 2],
        witness: [Vec<F>; 2],
        transcript: &mut Transcript<F, D>,
    ) -> ProverOutput<FlcsRelation<F, C, I, IO, S>, Self::Proof> {
        let instances = instance.map(|instance| instance.0);
        let core_instances = instances
            .each_ref()
            .map(|instance| &instance.oracle_instance().oracle1_instance);

        let [w1, w2] = witness;
        let [c1, c2] = core_instances;

        let witnesses = [(w1, c1), (w2, c2)].map(|(witness, core_instance)| {
            compute_sumcheck_witness(&key.structure, &key.matrices, &witness, core_instance)
        });

        ZeroFold::prove(&key.zerofold, instances, witnesses, transcript)
            .map_proof(FoldingProof)
            .map_rel::<FlcsRelation<F, C, I, IO, S>, _, _>(FlcsInstance, |witness| {
                witness.into_iter().map(|witness| witness.w()).collect()
            })
    }

    fn verify<D: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: [FlcsInstance<F, C, IO, S, I>; 2],
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, D>,
    ) -> Result<FlcsInstance<F, C, IO, S, I>, Self::Error> {
        let instances = instance.map(|instance| instance.0);
        let instance = ZeroFold::verify(key, instances, proof.map(|proof| proof.0), transcript)
            .map_err(FoldingError)?;
        Ok(FlcsInstance(instance))
    }
}
