use crate::lilium2::{
    oracles::{FlcsOracle, MatrixProductInstance},
    reductions::flcs::FlcsEvals,
    relations::{FlcsInstance, FlcsRelation, LcsInstance, LcsRelation, LcsStructure},
};
use ark_ff::Field;
use commit::commit2::CommitmentScheme;
use sponge::sponge::Duplex;
use sumcheck::{
    oracles::{composite::CompositeOracleInstance, core::CoreOracleInstance},
    zerocheck::ZerocheckReduction,
};
use transcript::reduction2::{
    GuardedProof, NoError, ProverOutput, Reduction, Transcript, TranscriptBuilder,
    VerifierTranscript,
};

#[derive(Clone, Debug)]
/// LCS -> FLCS
pub struct ToFlcs;

impl<F, C, const I: usize, const IO: usize, const S: usize>
    Reduction<F, LcsRelation<F, C, I, IO, S>, FlcsRelation<F, C, I, IO, S>> for ToFlcs
where
    F: Field,
    C: CommitmentScheme<F>,
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

    fn verifier_key(structure: &LcsStructure<F, C, IO, S>) -> Self::VerifierKey {
        let LcsStructure { ccs_structure, .. } = structure;
        ccs_structure.vars()
    }

    fn key_pair(structure: &LcsStructure<F, C, IO, S>) -> (Self::VerifierKey, Self::ProverKey) {
        let vars = <Self as Reduction<F, LcsRelation<F, C, I, IO, S>, _>>::verifier_key(structure);
        (vars, vars)
    }

    fn params(_: &Self::VerifierKey) -> Self::Params {}

    fn prove<D: Duplex<F>>(
        key: &Self::ProverKey,
        instance: LcsInstance<F, C, I>,
        witness: Vec<F>,
        transcript: &mut Transcript<F, D>,
    ) -> ProverOutput<FlcsRelation<F, C, I, IO, S>, Self::Proof> {
        let vars = key;
        let [challenge] = transcript.send_message(&(), &());

        let LcsInstance {
            witness_commit,
            public_inputs,
        } = instance;

        let coefficients = FlcsEvals::coefficients(public_inputs, challenge);
        let core_oracle_instance = CoreOracleInstance::new(&coefficients, *vars);
        let matrix_product_instance = MatrixProductInstance(witness_commit);
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
        } = ZerocheckReduction::prove(key, oracle_instance, vec![], transcript);

        ProverOutput {
            instance: FlcsInstance(instance),
            witness,
            proof,
        }
    }

    fn verify<D: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: LcsInstance<F, C, I>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, D>,
    ) -> Result<FlcsInstance<F, C, IO, S, I>, Self::Error> {
        let vars = key;
        let Ok(((), [challenge])) = transcript.receive_message(|_| (), &proof, &());
        let LcsInstance {
            witness_commit,
            public_inputs,
        } = instance;

        let coefficients = FlcsEvals::coefficients(public_inputs, challenge);
        let core_oracle_instance = CoreOracleInstance::new(&coefficients, *vars);
        let matrix_product_instance = MatrixProductInstance(witness_commit);
        let oracle_instance = CompositeOracleInstance {
            oracle1_instance: core_oracle_instance,
            oracle2_instance: matrix_product_instance,
        };

        let Ok(instance) =
            ZerocheckReduction::verify(vars, oracle_instance, GuardedProof::empty(), transcript);
        Ok(FlcsInstance(instance))
    }
}
