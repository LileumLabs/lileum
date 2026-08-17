//! This module has a simplified version of the proof system and most
//! things that could be needed to write circuits and work with them.
//! Circuits are fixed to use up to 10 gates, each with up to 5 inputs/outputs,
//! which should be enough in most cases.  
//!
//! The sponge's permutation is fixed to poseidon2 with a configuration which
//! should work for 256 bits or bigger fields.  
//!
//! For more customization, [circuit_key::CircuitKey] should be used.

// use crate::circuit_key;
use crate::circuit_key;
pub use crate::{
    circuits,
    relations::ClcsInstance,
    // flcs::FoldableLcsInstance,
    // folding::InstancePair,
    // instances::lcs::{verifying::LcsProof, LcsInstance},
    relations::FlcsInstance,
};
pub use ark_ff::{Field, PrimeField};
pub use circuit_key::FoldingProof;
use circuit_key::Instance;
pub use commit::CommitmentScheme;
use lcs::circuit::{BuildStructure, CircuitProfile};
pub use lcs::{
    circuit::{Circuit, Var},
    constraint_system::{ConstraintSystem, Val},
    gates::{self, StandardGates},
    witness::Witness,
};

const IO: usize = 5;
const S: usize = 10;

type Permutation<F> = sponge::poseidon2::PoseidonDefault<F>;
type Sponge<F> = sponge::sponge::Sponge<F, Permutation<F>, 1, 2, 3>;

pub struct CircuitKey<F, C, CS, const I: usize>
where
    F: PrimeField,
    CS: CommitmentScheme<F>,
{
    inner: circuit_key::CircuitKey<F, Sponge<F>, C, CS, I, IO, S>,
}

pub type Proof<F, C> = circuit_key::Proof<F, C, IO>;

impl<F, C, CS, const I: usize> CircuitKey<F, C, CS, I>
where
    F: PrimeField,
    CS: CommitmentScheme<F> + 'static,
{
    pub fn new<const IN: usize, const OUT: usize, const PRIV_OUT: usize>() -> Self
    where
        C: Circuit<F, IN, OUT, PRIV_OUT>,
    {
        Self {
            inner: circuit_key::CircuitKey::new(),
        }
    }

    /// Folds 2 instance-witness pairs into a single instance-witness pair.
    /// Returns (instance, witness, proof).
    /// Each instance may be a `FoldableLcsInstance` or an `LcsInstance`.
    pub fn fold(
        &self,
        instance1: impl Into<Instance<F, CS, IO, S, I>>,
        instance2: impl Into<Instance<F, CS, IO, S, I>>,
        witnesses: [Witness<F>; 2],
    ) -> (
        FlcsInstance<F, CS, IO, S, I>,
        Witness<F>,
        FoldingProof<F, C>,
    ) {
        self.inner.fold_prove(instance1, instance2, witnesses)
    }

    /// Verifier side of `Self::fold`, takes 2 instances and a proof and returns a
    /// a folded instance.
    pub fn fold_instances(
        &self,
        instance1: impl Into<Instance<F, CS, IO, S, I>>,
        instance2: impl Into<Instance<F, CS, IO, S, I>>,
        proof: FoldingProof<F, C>,
    ) -> FlcsInstance<F, CS, IO, S, I> {
        //TODO: should leave panic to the caller.
        self.inner.fold_verify(instance1, instance2, proof).unwrap()
    }

    /// Creates witness from inputs, commits to it, creates instance and proves it.
    /// Returns (instance, proof, private_output)
    pub fn prove_from_inputs<const IN: usize, const OUT: usize, const PRIV_OUT: usize>(
        &self,
        inputs: [F; IN],
    ) -> (ClcsInstance<F, CS, I>, Proof<F, CS>, C::PrivateOutput)
    where
        C: Circuit<F, IN, OUT, PRIV_OUT>,
    {
        self.inner.prove_from_inputs(inputs)
    }

    /// Generates witness from inputs, commits to it, and returns an instance-witness
    /// pair which can be proved or folded.
    /// Returns (instance, witness, private_output)
    pub fn commit_witness<const IN: usize, const OUT: usize, const PRIV_OUT: usize>(
        &self,
        inputs: [F; IN],
    ) -> (ClcsInstance<F, CS, I>, Witness<F>, C::PrivateOutput)
    where
        C: Circuit<F, IN, OUT, PRIV_OUT>,
    {
        self.inner.commit_witness(inputs)
    }

    /// Proves (instance, witness) pair.
    pub fn prove(&self, instance: ClcsInstance<F, CS, I>, witness: Witness<F>) -> Proof<F, CS> {
        self.inner.prove(instance, witness)
    }

    pub fn verify(&self, instance: ClcsInstance<F, CS, I>, proof: Proof<F, CS>) -> bool {
        self.inner.verify(instance, proof)
    }

    pub fn profile<const IN: usize, const OUT: usize, const PRIV_OUT: usize>(
        &self,
    ) -> CircuitProfile
    where
        C: Circuit<F, IN, OUT, PRIV_OUT>,
    {
        <C as BuildStructure<F, IN, OUT, PRIV_OUT, IO>>::profile()
    }
}

#[cfg(feature = "simple")]
pub mod field_and_pcs {
    pub use ark_vesta::Fr;
    use ark_vesta::{Projective, VestaConfig};
    // use commit::ipa::IpaCommitmentScheme;
    use commit::ipa::IpaCommitmentScheme;
    use hash_to_curve::svdw::SvdwMap;

    /// Commitment scheme for [Fr].
    pub type FrScheme = IpaCommitmentScheme<Fr, Projective, SvdwMap<VestaConfig>>;
}
