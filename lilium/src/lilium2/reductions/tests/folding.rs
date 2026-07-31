use super::{commit_witness, Poseidon};
use crate::{
    lilium2::{
        reductions::{FlcsFoldingScheme, ToFlcs},
        relations::{LcsRelation, LcsStructure},
    },
    testing::utils::HashChain,
};
use ark_ff::{Field, PrimeField};
use ccs::{circuit::BuildStructure, structure::CcsStructure};
use commit::commit2::CommitmentScheme;
use transcript::reduction2::{GuardedProof, Prover, Verifier};

fn test<F, C, const N: usize>()
where
    F: PrimeField,
    C: CommitmentScheme<F>,
{
    let ccs_structure: CcsStructure<F, 4, 5> =
        <HashChain<N> as BuildStructure<F, 1, 1, 1, 4>>::structure();

    let pcs = C::new(ccs_structure.vars());
    let structure = LcsStructure { ccs_structure, pcs };
    // let flcs_structure = structure.to_flcs::<2>();

    // let input = F::from(8u8);
    // let (instance1, witness1) = commit_witness::<F, C, N>(&structure.pcs, [input]);
    // let input = F::from(9u8);
    // let (instance2, witness2) = commit_witness::<F, C, N>(&structure.pcs, [input]);

    // let verifier: Verifier<F, Poseidon<F>, LcsRelation<F, C, 2, 4, 5>, _, ToFlcs> =
    //     Verifier::new(&structure, &flcs_structure, ());
    //
    // let [instance1, instance2] =
    //     [instance1, instance2].map(|instance| verifier.verify(instance, ()).unwrap());
}
