use crate::{
    SpreadsheetRelation,
    argument::{Proof, SpreadsheetStructure},
    circuit_builder::SpreadsheetBuilder,
};
use alloc::vec::Vec;
use ark_ff::Field;
use commit::CommitmentScheme;
use reduction::{Prover, ProverOutput, Verifier};
use sponge::sponge::Duplex;

mod default_config {
    pub use ark_vesta::Fr;
    use ark_vesta::{Projective, VestaConfig};
    use commit::ipa::IpaCommitmentScheme;
    use hash_to_curve::svdw::SvdwMap;

    /// Commitment scheme for [Fr].
    pub type FrScheme = IpaCommitmentScheme<Fr, Projective, SvdwMap<VestaConfig>>;

    type Permutation<F> = sponge::poseidon2::PoseidonDefault<F>;
    pub type Sponge<F = Fr> = sponge::sponge::Sponge<F, Permutation<F>, 2, 1, 3>;
}

use default_config::{Fr, FrScheme, Sponge};

type Rel<F, C> = SpreadsheetRelation<F, C>;

pub struct SpreadsheetKey<F = Fr, S = Sponge, C = FrScheme>
where
    F: Field,
    S: Duplex<F>,
    C: CommitmentScheme<F>,
{
    prover: Prover<F, S, Rel<F, C>, (), Rel<F, C>>,
    verifier: Verifier<F, S, Rel<F, C>, (), Rel<F, C>>,
}

impl<F, S, C> SpreadsheetKey<F, S, C>
where
    F: Field,
    S: Duplex<F>,
    C: CommitmentScheme<F>,
{
    pub fn new(structure: &SpreadsheetBuilder) -> Self {
        let (input_range, gates) = structure.circuit::<F>(Vec::new());
        let data_table_size = input_range.cells();
        let vars = data_table_size.next_power_of_two().ilog2() as usize;
        let pcs = C::new(vars);

        let structure = SpreadsheetStructure::new(data_table_size, gates, pcs);

        let prover = Prover::new(&structure);
        let verifier = Verifier::new(&structure);

        Self { prover, verifier }
    }

    pub fn prover(&self, data: &[F], committment: C::Commitment) -> Proof<F, C> {
        //TODO: Maybe commit to data again and check they match.
        let instance = committment;
        let ProverOutput {
            instance: (),
            witness: (),
            proof,
        } = self.prover.prove(instance, data.to_vec());
        proof
    }

    pub fn verify(&self, committment: C::Commitment, proof: Proof<F, C>) -> bool {
        let instance = committment;
        match self.verifier.verify(instance, proof) {
            Ok(()) => true,
            Err(_) => false,
        }
    }
}
