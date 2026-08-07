use super::{Poseidon, commit_witness};
use crate::{
    reductions::LcsArgument,
    relations::{LcsRelation, LcsStructure},
    testing::utils::HashChain,
};
use ark_ff::PrimeField;
use ccs::{circuit::BuildStructure, structure::CcsStructure};
use commit::CommitmentScheme;
use reduction::{Prover, ProverOutput, Relation, Verifier};

fn test<F, C, const N: usize>()
where
    F: PrimeField,
    C: CommitmentScheme<F>,
{
    let ccs_structure: CcsStructure<F, 4, 5> =
        <HashChain<N> as BuildStructure<F, 1, 1, 1, 4>>::structure();

    let pcs = C::new(ccs_structure.vars());
    let structure = LcsStructure { ccs_structure, pcs };

    let prover: Prover<F, Poseidon<F>, LcsRelation<F, C, 2, 4, 5>, (), LcsArgument> =
        Prover::new(&structure);

    let verifier: Verifier<F, Poseidon<F>, LcsRelation<F, C, 2, 4, 5>, (), LcsArgument> =
        Verifier::new(&structure);

    let input = F::from(8u8);
    let (instance, witness) = commit_witness::<F, C, N>(&structure.pcs, [input]);

    assert!(LcsRelation::<F, C, 2, 4, 5>::check(
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
