use super::{Poseidon, commit_witness};
use crate::{
    reductions::ClcsArgument,
    relations::{ClcsRelation, ClcsStructure},
    testing::utils::HashChain,
};
use ark_ff::PrimeField;
use commit::CommitmentScheme;
use lcs::{circuit::BuildStructure, structure::LcsStructure};
use reduction::{Prover, ProverOutput, Relation, Verifier};

fn test<F, C, const N: usize>()
where
    F: PrimeField,
    C: CommitmentScheme<F>,
{
    let lcs_structure: LcsStructure<F, 4, 5> =
        <HashChain<N> as BuildStructure<F, 1, 1, 1, 4>>::structure();

    let pcs = C::new(lcs_structure.vars());
    let structure = ClcsStructure { lcs_structure, pcs };

    let prover: Prover<F, Poseidon<F>, ClcsRelation<F, C, 2, 4, 5>, (), ClcsArgument> =
        Prover::new(&structure);

    let verifier: Verifier<F, Poseidon<F>, ClcsRelation<F, C, 2, 4, 5>, (), ClcsArgument> =
        Verifier::new(&structure);

    let input = F::from(8u8);
    let (instance, witness) = commit_witness::<F, C, N>(&structure.pcs, [input]);

    assert!(ClcsRelation::<F, C, 2, 4, 5>::check(
        &structure, &instance, &witness
    ));
    let ProverOutput {
        instance: _,
        witness: _,
        proof,
    } = prover.prove(instance.clone(), witness);

    verifier.verify(instance, proof).unwrap();
}

#[test]
fn lcs_argument() {
    use ark_vesta::{Fr, Projective, VestaConfig};
    use commit::ipa::IpaCommitmentScheme;
    use hash_to_curve::svdw::SvdwMap;

    type Scheme = IpaCommitmentScheme<Fr, Projective, SvdwMap<VestaConfig>>;

    test::<Fr, Scheme, 3>();
}
