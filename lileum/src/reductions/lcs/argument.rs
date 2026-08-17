use crate::{
    oracles::MatrixProductOracle,
    reductions::{
        FlcsArgument, ToFlcs,
        flcs::{
            FlcsData, FlcsEvals,
            argument::{Error, Proof},
        },
    },
    relations::{FlcsRelation, FlcsStructure, LcsInstance, LcsRelation, LcsStructure},
};
use ark_ff::Field;
use commit::{CommitmentScheme, oracle::CommittedOracle};
use lcs::structure::LcsCircuit;
use reduction::{
    Argument, GuardedProof, ProverOutput, Reduction, Transcript, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;
use std::rc::Rc;
use sumcheck::oracles::{composite::CompositeOracle, core::CoreOracle};

#[derive(Clone, Debug)]
/// LCS -> ()
pub struct LcsArgument;

impl<F, C, const I: usize, const IO: usize, const S: usize>
    Reduction<F, LcsRelation<F, C, I, IO, S>, ()> for LcsArgument
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = (
        <FlcsArgument as Reduction<F, FlcsRelation<F, C, I, IO, S>, ()>>::ProverKey,
        usize,
    );

    type VerifierKey = (
        <FlcsArgument as Reduction<F, FlcsRelation<F, C, I, IO, S>, ()>>::VerifierKey,
        usize,
    );

    type Proof = Proof<F, C, IO>;

    type Error = Error<F, C>;

    type Params = ();

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        builder
            .subprotocol::<ToFlcs, F, LcsRelation<F, C, I, IO, S>, FlcsRelation<F, C, I, IO, S>>(
                &key.1,
            )
            .subprotocol::<FlcsArgument, F, FlcsRelation<F, C, I, IO, S>, ()>(&key.0)
    }

    fn verifier_key(structure: &LcsStructure<F, C, IO, S>) -> Self::VerifierKey {
        let flcs_structure = structure.to_flcs::<I>();
        let verifier_key = FlcsArgument::verifier_key(&flcs_structure);
        let vars = structure.circuit.vars();
        (verifier_key, vars)
    }

    fn key_pair(structure: &LcsStructure<F, C, IO, S>) -> (Self::VerifierKey, Self::ProverKey) {
        let flcs_structure = structure.to_flcs::<I>();
        let (verifier_key, prover_key) = FlcsArgument::key_pair(&flcs_structure);
        let vars = structure.circuit.vars();
        ((verifier_key, vars), (prover_key, vars))
    }

    fn params(_: &Self::VerifierKey) -> Self::Params {}

    fn prove<D: Duplex<F>>(
        key: &Self::ProverKey,
        instance: LcsInstance<F, C, I>,
        witness: Vec<F>,
        transcript: &mut Transcript<F, D>,
    ) -> ProverOutput<(), Self::Proof> {
        let ProverOutput {
            instance,
            witness,
            proof: (),
        } = ToFlcs::prove(&key.1, instance, witness, transcript);
        FlcsArgument::prove(&key.0, instance, witness, transcript)
    }

    fn verify<D: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: LcsInstance<F, C, I>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, D>,
    ) -> Result<(), Self::Error> {
        let Ok(instance) = ToFlcs::verify(&key.1, instance, GuardedProof::empty(), transcript);
        FlcsArgument::verify(&key.0, instance, proof, transcript)
    }
}

impl<F, C, const I: usize, const IO: usize, const S: usize> Argument<F, LcsRelation<F, C, I, IO, S>>
    for LcsArgument
where
    F: Field,
    C: CommitmentScheme<F>,
{
}

impl<F, C, const IO: usize, const S: usize> LcsStructure<F, C, IO, S>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    pub fn to_flcs<const I: usize>(&self) -> FlcsStructure<F, C, IO, S, I> {
        use sumcheck::oracles::partial::PartialOracle;
        let LcsStructure { circuit, pcs } = self;
        let (circuit, pcs) = (circuit.clone(), pcs.clone());

        let gates = circuit
            .gates
            .iter()
            .map(|gate| Vec::from(gate.clone()))
            .collect();

        //TODO: allow true
        let multi_constraint = false;
        let data = FlcsData::new(gates, multi_constraint);

        let matrices = circuit.io_matrices.clone().map(Rc::new);
        let mles = Rc::new(structure(circuit.clone()));

        let functions = FlcsEvals::functions();

        let builder1: CoreOracle<F, _> = CoreOracle::new(functions);
        let committed_oracle = CommittedOracle::<F, C, FlcsEvals<(), IO, S, I>>::build(
            pcs.clone(),
            &data,
            Rc::clone(&mles),
        );
        let builder2 = MatrixProductOracle::new(
            matrices,
            FlcsEvals::vector(),
            committed_oracle,
            pcs.clone(),
            circuit.vars(),
        );
        let oracle = CompositeOracle::new(data, mles, builder1, builder2);

        FlcsStructure {
            circuit,
            pcs,
            oracle,
        }
    }
}

fn structure<F: Field, const IO: usize, const S: usize, const I: usize>(
    circuit: LcsCircuit<F, IO, S>,
) -> Vec<FlcsEvals<F, IO, S, I>> {
    let mut mles = Vec::with_capacity(1 << circuit.vars());
    //TODO: use next_power_of_two(max(trace,constraints))
    for i in 0..circuit.trace_len {
        let is_input = i < circuit.input_len;

        let active_selector = circuit.gate_selectors.get(i);
        // Selecting any value outside of the 0..S range will result
        // in FlcsEvals::structure(..) setting all zeros.
        let selector = active_selector.cloned().unwrap_or(S);

        let constant = circuit.constants.get(&i).cloned().unwrap_or(F::zero());

        let row = FlcsEvals::structure(is_input, selector, constant);
        mles.push(row)
    }
    let padding_row = FlcsEvals::structure(false, S, F::ZERO);
    mles.resize(1 << circuit.vars(), padding_row);
    mles
}
