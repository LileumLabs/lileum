use crate::{
    extensions::Extension,
    oracles::FlcsOracle,
    reductions::flcs::{FlcsEvals, compute_sumcheck_witness},
    relations::{FlcsInstance, FlcsRelation, FlcsStructure},
};
use alloc::{rc::Rc, vec::Vec};
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use commit::CommitmentScheme;
use lcs::matrix::Matrix;
use reduction::{
    FoldingRelation, GuardedProof, ProverOutput, Reduction, Relation, Transcript,
    TranscriptBuilder, VerifierTranscript,
};
use sponge::sponge::Duplex;
use sumcheck::{
    SumcheckError, SumcheckMessage,
    folding::{ZeroFold, ZeroFoldKey},
    oracles::{Oracle, partial::OracleParams},
};

#[derive(Clone, Copy, Debug)]
/// FLCS x FLCS -> FLCS
pub struct FlcsFoldingScheme;

pub struct ProverKey<F, C, const IO: usize, const S: usize, const I: usize, E = ()>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    structure: Rc<Vec<FlcsEvals<F, IO, S, I>>>,
    matrices: [Rc<Matrix>; IO],
    zerofold: ZeroFoldKey<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>,
    extension: <E::FoldingScheme as Reduction<F, FoldingRelation<E::R2>, E::R2>>::ProverKey,
}

#[derive(Clone, Debug, CanonicalSerialize)]
pub struct VerifierKey<F, C, const IO: usize, const S: usize, const I: usize, E = ()>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    folding: ZeroFoldKey<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>,
    extension: <E::FoldingScheme as Reduction<F, FoldingRelation<E::R2>, E::R2>>::VerifierKey,
}

#[derive(Debug)]
pub struct FoldingProof<F, C, E = ()>(
    SumcheckMessage<F>,
    <E::FoldingScheme as Reduction<F, FoldingRelation<E::R2>, E::R2>>::Proof,
)
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>;

impl<F: Clone, C: Clone, E: Clone> Clone for FoldingProof<F, C, E>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
    E::R2: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone())
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FoldingError(pub SumcheckError);

impl<F, C, E, const I: usize, const IO: usize, const S: usize>
    Reduction<F, FoldingRelation<FlcsRelation<F, C, I, IO, S, E>>, FlcsRelation<F, C, I, IO, S, E>>
    for FlcsFoldingScheme
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    type ProverKey = ProverKey<F, C, IO, S, I, E>;

    type VerifierKey = VerifierKey<F, C, IO, S, I, E>;

    type Proof = FoldingProof<F, C, E>;

    type Error = FoldingError;

    type Params = (OracleParams, OracleParams);

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        builder
            .subprotocol::<ZeroFold<F, _>, _, _, _>(&key.folding)
            .subprotocol::<E::FoldingScheme, _, _, _>(&key.extension)
    }

    fn verifier_key(structure: &FlcsStructure<F, C, IO, S, I, E>) -> Self::VerifierKey {
        let oracle = &structure.oracle;
        let folding = ZeroFold::verifier_key(oracle);
        let extension = E::FoldingScheme::verifier_key(&structure.extended);

        VerifierKey { folding, extension }
    }

    fn key_pair(
        structure: &FlcsStructure<F, C, IO, S, I, E>,
    ) -> (Self::VerifierKey, Self::ProverKey) {
        let oracle = &structure.oracle;
        let zerofold = ZeroFold::verifier_key(oracle);

        let (extension_verifier, extension) = E::FoldingScheme::key_pair(&structure.extended);
        let verifier_key = VerifierKey {
            folding: zerofold.clone(),
            extension: extension_verifier,
        };

        let matrices = structure.lcs_structure.io_matrices.clone().map(Rc::new);
        let structure = oracle.structure();
        let prover_key = ProverKey {
            structure,
            matrices,
            zerofold,
            extension,
        };

        (verifier_key, prover_key)
    }

    fn params(key: &Self::VerifierKey) -> Self::Params {
        let oracle_params = key.folding.params();
        (oracle_params, oracle_params)
    }

    fn prove<D: Duplex<F>>(
        key: &Self::ProverKey,
        instance: [FlcsInstance<F, C, IO, S, I, E>; 2],
        witness: [(Vec<F>, <E::R2 as Relation>::Witness); 2],
        transcript: &mut Transcript<F, D>,
    ) -> ProverOutput<FlcsRelation<F, C, I, IO, S, E>, Self::Proof> {
        let (instances, extended_instances) = {
            let [FlcsInstance(i1, ei1), FlcsInstance(i2, ei2)] = instance;
            ([i1, i2], [ei1, ei2])
        };
        let (witnesses, extended_witnesses) = {
            let [(w1, ew1), (w2, ew2)] = witness;
            ([w1, w2], [ew1, ew2])
        };

        let core_instances = instances
            .each_ref()
            .map(|instance| &instance.oracle_instance().oracle1_instance);

        let [w1, w2] = witnesses;
        let [c1, c2] = core_instances;

        let witnesses = [(w1, c1), (w2, c2)].map(|(witness, core_instance)| {
            compute_sumcheck_witness(&key.structure, &key.matrices, &witness, core_instance)
        });

        let ProverOutput {
            instance,
            witness,
            proof,
        } = ZeroFold::prove(&key.zerofold, instances, witnesses, transcript);
        let witness = witness.into_iter().map(|witness| witness.w()).collect();

        let ProverOutput {
            instance: extended_instance,
            witness: extended_witness,
            proof: extended_proof,
        } = E::FoldingScheme::prove(
            &key.extension,
            extended_instances,
            extended_witnesses,
            transcript,
        );

        let instance = FlcsInstance(instance, extended_instance);
        let witness = (witness, extended_witness);
        let proof = FoldingProof(proof, extended_proof);

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    fn verify<D: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: [FlcsInstance<F, C, IO, S, I, E>; 2],
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, D>,
    ) -> Result<FlcsInstance<F, C, IO, S, I, E>, Self::Error> {
        let instances = instance.each_ref().map(|instance| instance.0.clone());
        let extended_instances = instance.map(|instance| instance.1);
        let instance = ZeroFold::verify(
            &key.folding,
            instances,
            proof.clone().map(|proof| proof.0),
            transcript,
        )
        .map_err(FoldingError)?;
        //TODO:handle
        let extended_instance = E::FoldingScheme::verify(
            &key.extension,
            extended_instances,
            proof.map(|proof| proof.1),
            transcript,
        )
        .unwrap();
        Ok(FlcsInstance(instance, extended_instance))
    }
}
