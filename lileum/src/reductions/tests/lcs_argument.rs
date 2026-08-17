use super::{Poseidon, commit_witness};
use crate::{
    reductions::LcsArgument,
    relations::{LcsRelation, LcsStructure},
    testing::utils::HashChain,
};
use ark_ff::PrimeField;
use commit::CommitmentScheme;
use lcs::{circuit::BuildLcs, structure::LcsCircuit};
use reduction::{Prover, ProverOutput, Relation, Verifier};

fn test<F, C, const N: usize>()
where
    F: PrimeField,
    C: CommitmentScheme<F>,
{
    let circuit: LcsCircuit<F, 4, 5> = <HashChain<N> as BuildLcs<F, 1, 1, 1, 4>>::lcs();

    let pcs = C::new(circuit.vars());
    let structure = LcsStructure { circuit, pcs };

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
