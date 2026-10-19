use crate::{
    extensions::Extension,
    oracles::{FlcsOracle, MatrixProductInstance},
    reductions::flcs::FlcsEvals,
    relations::{ClcsInstance, ClcsRelation, ClcsStructure, FlcsInstance, FlcsRelation},
};
use alloc::vec::Vec;
use ark_ff::Field;
use commit::CommitmentScheme;
use reduction::{
    GuardedProof, NoError, ProverOutput, Reduction, Transcript, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;
use sumcheck::{
    oracles::{composite::CompositeOracleInstance, core::CoreOracleInstance},
    zerocheck::ZerocheckReduction,
};

#[derive(Clone, Debug)]
/// CLCS -> FLCS
pub struct ToFlcs;

impl<F, C, E, const I: usize, const IO: usize, const S: usize>
    Reduction<F, ClcsRelation<F, C, I, IO, S, E>, FlcsRelation<F, C, I, IO, S, E>> for ToFlcs
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    type ProverKey = usize;

    type VerifierKey = usize;

    type Proof = ();

    type Error = NoError;

    type Params = ();

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        type Oracle<F, C, const IO: usize, const S: usize, const I: usize> =
            FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>;
        builder
            .round::<F, (), 1>(&())
            .subprotocol::<ZerocheckReduction<F, Oracle<F, C, IO, S, I>>, _, _, _>(key)
    }

    fn verifier_key(structure: &ClcsStructure<F, C, IO, S, E>) -> Self::VerifierKey {
        let ClcsStructure { lcs_structure, .. } = structure;
        lcs_structure.vars()
    }

    fn key_pair(structure: &ClcsStructure<F, C, IO, S, E>) -> (Self::VerifierKey, Self::ProverKey) {
        let vars =
            <Self as Reduction<F, ClcsRelation<F, C, I, IO, S, E>, _>>::verifier_key(structure);
        (vars, vars)
    }

    fn params(_: &Self::VerifierKey) -> Self::Params {}

    fn prove<D: Duplex<F>>(
        key: &Self::ProverKey,
        instance: ClcsInstance<F, C, I, E>,
        witness: (Vec<F>, E::Witness),
        transcript: &mut Transcript<F, D>,
    ) -> ProverOutput<FlcsRelation<F, C, I, IO, S, E>, Self::Proof> {
        let vars = key;
        let [challenge] = transcript.send_message(&(), &());

        let (witness, extended_witness) = witness;
        let extended_witness = (witness.clone(), extended_witness);

        let ClcsInstance {
            witness_commit,
            public_inputs,
            extended_instance,
        } = instance;

        let coefficients = FlcsEvals::coefficients(public_inputs, challenge);
        let core_oracle_instance = CoreOracleInstance::new(&coefficients, *vars);
        let matrix_product_instance = MatrixProductInstance(witness_commit.clone());
        let oracle_instance = CompositeOracleInstance {
            oracle1_instance: core_oracle_instance,
            oracle2_instance: matrix_product_instance,
        };

        // As Flcs computes the full sumcheck witness from the Vec<F> witness, doing
        // it here would be a waste as we can only throw it away.
        // Taking advantage of the fact that this prover just returns the same witness
        // without doing anything with it. We instead give it an empty witness and then
        // ignore it in the result.
        let ProverOutput {
            instance,
            witness: _,
            proof,
        } = ZerocheckReduction::prove(key, oracle_instance, Vec::new(), transcript);

        let extended_instance = (witness_commit, extended_instance);
        let ProverOutput {
            instance: extended_instance,
            witness: extended_witness,
            proof: (),
        } = E::Reduction1::prove(&(), extended_instance, extended_witness, transcript);

        let instance = FlcsInstance(instance, extended_instance);
        let witness = (witness, extended_witness);

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    fn verify<D: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: ClcsInstance<F, C, I, E>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, D>,
    ) -> Result<FlcsInstance<F, C, IO, S, I, E>, Self::Error> {
        let vars = key;
        let Ok(((), [challenge])) = transcript.receive_message(|_| (), &proof, &());
        let ClcsInstance {
            witness_commit,
            public_inputs,
            extended_instance,
        } = instance;

        let coefficients = FlcsEvals::coefficients(public_inputs, challenge);
        let core_oracle_instance = CoreOracleInstance::new(&coefficients, *vars);
        let matrix_product_instance = MatrixProductInstance(witness_commit.clone());
        let oracle_instance = CompositeOracleInstance {
            oracle1_instance: core_oracle_instance,
            oracle2_instance: matrix_product_instance,
        };

        let Ok(instance) =
            ZerocheckReduction::verify(vars, oracle_instance, GuardedProof::empty(), transcript);

        let extended_instance = (witness_commit, extended_instance);
        let Ok(extended_instance) =
            E::Reduction1::verify(&(), extended_instance, GuardedProof::empty(), transcript);

        Ok(FlcsInstance(instance, extended_instance))
    }
}
