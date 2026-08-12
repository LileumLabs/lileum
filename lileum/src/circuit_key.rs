use crate::{
    reductions::{
        FlcsArgument, FlcsFoldingScheme, ToFlcs,
        flcs::{self, folding},
    },
    relations::{FlcsInstance, FlcsRelation, LcsInstance, LcsRelation, LcsStructure},
};
use ark_ff::Field;
use commit::CommitmentScheme;
use lcs::{
    circuit::{BuildStructure, Circuit, Prove},
    structure::CcsStructure,
    witness::Witness,
};
use reduction::{FoldingRelation, Prover, ProverOutput, Verifier};
use sponge::sponge::Duplex;
use std::marker::PhantomData;

type FoldingProver<F, D, R> = Prover<F, D, FoldingRelation<R>, R, FlcsFoldingScheme>;
type FoldingVerifier<F, D, R> = Verifier<F, D, FoldingRelation<R>, R, FlcsFoldingScheme>;

/// key to create and verify proofs for a given circuit
pub struct CircuitKey<
    F: Field,
    D: Duplex<F>,
    C,
    CS: CommitmentScheme<F>,
    const I: usize,
    const IO: usize = 0,
    const S: usize = 0,
> {
    _circuit: PhantomData<C>,
    to_flcs: Verifier<F, D, LcsRelation<F, CS, I, IO, S>, FlcsRelation<F, CS, I, IO, S>, ToFlcs>,
    flcs_prover: Prover<F, D, FlcsRelation<F, CS, I, IO, S>, (), FlcsArgument>,
    flcs_verifier: Verifier<F, D, FlcsRelation<F, CS, I, IO, S>, (), FlcsArgument>,
    folding_prover: FoldingProver<F, D, FlcsRelation<F, CS, I, IO, S>>,
    folding_verifier: FoldingVerifier<F, D, FlcsRelation<F, CS, I, IO, S>>,
    pcs: CS,
}

#[derive(Clone)]
pub enum Proof<F: Field, C: CommitmentScheme<F>, const IO: usize> {
    Flcs(flcs::argument::Proof<F, C, IO>),
}

pub struct FoldingProof<F: Field, C>(folding::FoldingProof<F>, PhantomData<C>);

impl<F, T, C, CS, const I: usize, const IO: usize, const S: usize> CircuitKey<F, T, C, CS, I, IO, S>
where
    F: Field,
    T: Duplex<F>,
    CS: CommitmentScheme<F>,
{
    pub fn new<const IN: usize, const OUT: usize, const PRIV_OUT: usize>() -> Self
    where
        C: Circuit<F, IN, OUT, PRIV_OUT>,
        CS: 'static,
    {
        let ccs_structure: CcsStructure<F, IO, S> = C::structure();
        let vars = ccs_structure.vars();

        let pcs = CS::new(vars);
        let structure = LcsStructure { ccs_structure, pcs };
        let flcs_structure = structure.to_flcs();

        let to_flcs = Verifier::new(&structure);

        let flcs_prover = Prover::new(&flcs_structure);

        let flcs_verifier = Verifier::new(&flcs_structure);

        let folding_prover = Prover::new(&flcs_structure);

        let folding_verifier = Verifier::new(&flcs_structure);

        Self {
            to_flcs,
            flcs_prover,
            flcs_verifier,
            folding_prover,
            folding_verifier,
            pcs: structure.pcs.clone(),
            _circuit: PhantomData,
        }
    }

    pub fn prove(
        &self,
        instance: impl Into<Instance<F, CS, IO, S, I>>,
        witness: Witness<F>,
    ) -> Proof<F, CS, IO> {
        let instance = match instance.into() {
            Instance::Lcs(lcs_instance) => {
                let Ok(instance) = self.to_flcs.verify(lcs_instance, ());
                instance
            }
            Instance::Flcs(flcs_instance) => flcs_instance,
        };
        let ProverOutput {
            instance: (),
            witness: (),
            proof,
        } = self.flcs_prover.prove(instance, witness.0);

        Proof::Flcs(proof)
    }

    pub fn verify(
        &self,
        instance: impl Into<Instance<F, CS, IO, S, I>>,
        proof: Proof<F, CS, IO>,
    ) -> bool {
        let instance = match instance.into() {
            Instance::Lcs(lcs_instance) => {
                let Ok(instance) = self.to_flcs.verify(lcs_instance, ());
                instance
            }
            Instance::Flcs(flcs_instance) => flcs_instance,
        };

        let Proof::Flcs(proof) = proof;

        self.flcs_verifier.verify(instance, proof).is_ok()
    }

    pub fn fold_prove(
        &self,
        instance1: impl Into<Instance<F, CS, IO, S, I>>,
        instance2: impl Into<Instance<F, CS, IO, S, I>>,
        witnesses: [Witness<F>; 2],
    ) -> (
        FlcsInstance<F, CS, IO, S, I>,
        Witness<F>,
        FoldingProof<F, C>,
    ) {
        let instances = [instance1.into(), instance2.into()].map(|instance| match instance {
            Instance::Lcs(instance) => {
                let Ok(instance) = self.to_flcs.verify(instance, ());
                instance
            }
            Instance::Flcs(flcs_instance) => flcs_instance,
        });
        let ProverOutput {
            instance,
            witness,
            proof,
        } = self.folding_prover.prove(instances, witnesses.map(|w| w.0));

        (instance, Witness(witness), FoldingProof(proof, PhantomData))
    }

    pub fn fold_verify(
        &self,
        instance1: impl Into<Instance<F, CS, IO, S, I>>,
        instance2: impl Into<Instance<F, CS, IO, S, I>>,
        proof: FoldingProof<F, C>,
    ) -> Option<FlcsInstance<F, CS, IO, S, I>> {
        let instances = [instance1.into(), instance2.into()].map(|instance| match instance {
            Instance::Lcs(instance) => {
                let Ok(instance) = self.to_flcs.verify(instance, ());
                instance
            }
            Instance::Flcs(flcs_instance) => flcs_instance,
        });
        self.folding_verifier.verify(instances, proof.0).ok()
    }

    /// From just the public inputs, it runs the circuit to compute the witness, and
    /// commits to it to create an instance.
    /// Returns the instance-witness pair and the private output if required.
    pub fn commit_witness<const IN: usize, const OUT: usize, const PRIV_OUT: usize>(
        &self,
        inputs: [F; IN],
    ) -> (LcsInstance<F, CS, I>, Witness<F>, C::PrivateOutput)
    where
        C: Circuit<F, IN, OUT, PRIV_OUT>,
    {
        assert_eq!(I, IN + OUT);
        let (mut witness, output) = <C as Prove<_, IN, OUT, PRIV_OUT, IO>>::witness(inputs, true);
        witness.pad_to_power();
        let witness_commit = self.pcs.commit_mle(&witness.0);

        let mut public_inputs = [F::zero(); I];
        assert!(witness.0.len() >= I);
        public_inputs.copy_from_slice(&witness.0[0..I]);

        let instance: LcsInstance<F, CS, I> = LcsInstance {
            witness_commit,
            public_inputs,
        };

        (instance, witness, output)
    }

    /// Calls Self::commit_witness(..) with the inputs, and calls Self::prove(..) with
    /// the returned instance-witness pair.
    pub fn prove_from_inputs<const IN: usize, const OUT: usize, const PRIV_OUT: usize>(
        &self,
        inputs: [F; IN],
    ) -> (LcsInstance<F, CS, I>, Proof<F, CS, IO>, C::PrivateOutput)
    where
        C: Circuit<F, IN, OUT, PRIV_OUT>,
    {
        let (instance, witness, output) = self.commit_witness(inputs);

        let proof = self.prove(instance.clone(), witness);
        (instance, proof, output)
    }
}

#[derive(Clone, Debug)]
pub enum Instance<F, C, const IO: usize, const S: usize, const I: usize>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    Lcs(LcsInstance<F, C, I>),
    Flcs(FlcsInstance<F, C, IO, S, I>),
}

impl<F, C, const IO: usize, const S: usize, const I: usize> From<LcsInstance<F, C, I>>
    for Instance<F, C, IO, S, I>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    fn from(value: LcsInstance<F, C, I>) -> Self {
        Self::Lcs(value)
    }
}

impl<F, C, const IO: usize, const S: usize, const I: usize> From<FlcsInstance<F, C, IO, S, I>>
    for Instance<F, C, IO, S, I>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    fn from(value: FlcsInstance<F, C, IO, S, I>) -> Self {
        Self::Flcs(value)
    }
}
