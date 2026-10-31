use crate::{
    extensions::{Extension, FoldableExtension},
    reductions::{
        FlcsArgument, FlcsFoldingScheme, ToFlcsVerifier,
        flcs::{self, folding},
    },
    relations::{ClcsInstance, ClcsStructure, FlcsInstance, FlcsRelation},
};
use ark_ff::Field;
use commit::CommitmentScheme;
use core::marker::PhantomData;
use lcs::{
    circuit::{BuildStructure, Circuit, Prove},
    structure::LcsStructure,
    witness::Witness,
};
use reduction::{FoldingRelation, Prover, ProverOutput, Verifier};
use sponge::sponge::Duplex;

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
    E: Extension<F, CS> = (),
> {
    _circuit: PhantomData<C>,
    to_flcs: ToFlcsVerifier<F, D, CS, I, IO, S, E>,
    flcs_prover: Prover<F, D, FlcsRelation<F, CS, I, IO, S, E>, (), FlcsArgument>,
    flcs_verifier: Verifier<F, D, FlcsRelation<F, CS, I, IO, S, E>, (), FlcsArgument>,
    folding_prover: FoldingProver<F, D, FlcsRelation<F, CS, I, IO, S, E>>,
    folding_verifier: FoldingVerifier<F, D, FlcsRelation<F, CS, I, IO, S, E>>,
    pcs: CS,
}

#[derive(Clone)]
pub enum Proof<F: Field, C: CommitmentScheme<F>, const IO: usize, E = ()>
where
    E: Extension<F, C>,
{
    Flcs(flcs::argument::Proof<F, C, IO, E>),
}

pub struct FoldingProof<F, CS, C, E = ()>(folding::FoldingProof<F, CS, E>, PhantomData<C>)
where
    F: Field,
    CS: CommitmentScheme<F>,
    E: FoldableExtension<F, CS>;

impl<F, D, C, CS, E, const I: usize, const IO: usize, const S: usize>
    CircuitKey<F, D, C, CS, I, IO, S, E>
where
    F: Field,
    D: Duplex<F>,
    CS: CommitmentScheme<F>,
    E: Extension<F, CS>,
{
    pub fn new<const IN: usize, const OUT: usize, const PRIV_OUT: usize>() -> Self
    where
        C: Circuit<F, IN, OUT, PRIV_OUT, E>,
        CS: 'static,
    {
        let lcs_structure: LcsStructure<F, IO, S, E> = C::structure();
        let vars = lcs_structure.vars();

        let pcs = CS::new(vars);
        let structure = ClcsStructure { lcs_structure, pcs };
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
        instance: impl Into<Instance<F, CS, IO, S, I, E>>,
        witness: Witness<F, E>,
    ) -> Proof<F, CS, IO, E> {
        let instance = match instance.into() {
            Instance::Lcs(lcs_instance) => {
                let Ok(instance) = self.to_flcs.verify(lcs_instance, ());
                instance
            }
            Instance::Flcs(flcs_instance) => flcs_instance,
        };
        let Witness(w, w_ext) = witness;
        let ProverOutput {
            instance: (),
            witness: (),
            proof,
        } = self.flcs_prover.prove(instance, (w, w_ext));

        Proof::Flcs(proof)
    }

    pub fn verify(
        &self,
        instance: impl Into<Instance<F, CS, IO, S, I, E>>,
        proof: Proof<F, CS, IO, E>,
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

    /// From just the public inputs, it runs the circuit to compute the witness, and
    /// commits to it to create an instance.
    /// Returns the instance-witness pair and the private output if required.
    pub fn commit_witness<const IN: usize, const OUT: usize, const PRIV_OUT: usize>(
        &self,
        inputs: [F; IN],
    ) -> (ClcsInstance<F, CS, I, E>, Witness<F, E>, C::PrivateOutput)
    where
        C: Circuit<F, IN, OUT, PRIV_OUT, E>,
    {
        assert_eq!(I, IN + OUT);
        let (mut witness, output) =
            <C as Prove<F, IN, OUT, PRIV_OUT, IO, E>>::witness(inputs, true);
        witness.pad_to_power();
        let witness_commit = self.pcs.commit_mle(&witness.0);

        let mut public_inputs = [F::zero(); I];
        assert!(witness.0.len() >= I);
        public_inputs.copy_from_slice(&witness.0[0..I]);

        let extended_instance = E::commit_witness(&self.pcs, &witness.1);

        let instance: ClcsInstance<F, CS, I, E> = ClcsInstance {
            witness_commit,
            public_inputs,
            extended_instance,
        };

        (instance, witness, output)
    }

    #[allow(clippy::complexity)]
    /// Calls Self::commit_witness(..) with the inputs, and calls Self::prove(..) with
    /// the returned instance-witness pair.
    pub fn prove_from_inputs<const IN: usize, const OUT: usize, const PRIV_OUT: usize>(
        &self,
        inputs: [F; IN],
    ) -> (
        ClcsInstance<F, CS, I, E>,
        Proof<F, CS, IO, E>,
        C::PrivateOutput,
    )
    where
        C: Circuit<F, IN, OUT, PRIV_OUT, E>,
    {
        let (instance, witness, output) = self.commit_witness(inputs);

        let proof = self.prove(instance.clone(), witness);
        (instance, proof, output)
    }
}

impl<F, D, C, CS, E, const I: usize, const IO: usize, const S: usize>
    CircuitKey<F, D, C, CS, I, IO, S, E>
where
    F: Field,
    D: Duplex<F>,
    CS: CommitmentScheme<F>,
    E: FoldableExtension<F, CS>,
{
    #[allow(clippy::complexity)]
    pub fn fold_prove(
        &self,
        instance1: impl Into<Instance<F, CS, IO, S, I, E>>,
        instance2: impl Into<Instance<F, CS, IO, S, I, E>>,
        witnesses: [Witness<F, E>; 2],
    ) -> (
        FlcsInstance<F, CS, IO, S, I, E>,
        Witness<F, E>,
        FoldingProof<F, CS, C, E>,
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
        } = self
            .folding_prover
            .prove(instances, witnesses.map(|w| (w.0, w.1)));

        (
            instance,
            Witness(witness.0, witness.1),
            FoldingProof(proof, PhantomData),
        )
    }

    pub fn fold_verify(
        &self,
        instance1: impl Into<Instance<F, CS, IO, S, I, E>>,
        instance2: impl Into<Instance<F, CS, IO, S, I, E>>,
        proof: FoldingProof<F, CS, C, E>,
    ) -> Option<FlcsInstance<F, CS, IO, S, I, E>> {
        let instances = [instance1.into(), instance2.into()].map(|instance| match instance {
            Instance::Lcs(instance) => {
                let Ok(instance) = self.to_flcs.verify(instance, ());
                instance
            }
            Instance::Flcs(flcs_instance) => flcs_instance,
        });
        self.folding_verifier.verify(instances, proof.0).ok()
    }
}

#[derive(Clone, Debug)]
pub enum Instance<F, C, const IO: usize, const S: usize, const I: usize, E = ()>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    Lcs(ClcsInstance<F, C, I, E>),
    Flcs(FlcsInstance<F, C, IO, S, I, E>),
}

impl<F, C, E, const IO: usize, const S: usize, const I: usize> From<ClcsInstance<F, C, I, E>>
    for Instance<F, C, IO, S, I, E>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    fn from(value: ClcsInstance<F, C, I, E>) -> Self {
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
