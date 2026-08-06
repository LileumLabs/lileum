use super::{commit_witness, Poseidon};
use crate::{
    lilium2::{
        reductions::{FlcsArgument, FlcsFoldingScheme, ToFlcs},
        relations::{FlcsRelation, LcsRelation, LcsStructure},
    },
    testing::utils::HashChain,
};
use ark_ff::PrimeField;
use ccs::{circuit::BuildStructure, structure::CcsStructure};
use commit::commit2::CommitmentScheme;
use transcript::{Prover, ProverOutput, Relation, Verifier};

fn test<F, C, const N: usize>()
where
    F: PrimeField,
    C: CommitmentScheme<F>,
{
    let ccs_structure: CcsStructure<F, 4, 5> =
        <HashChain<N> as BuildStructure<F, 1, 1, 1, 4>>::structure();

    let pcs = C::new(ccs_structure.vars());
    let structure = LcsStructure { ccs_structure, pcs };
    let flcs_structure = structure.to_flcs::<2>();

    let input = F::from(8u8);
    let (instance1, witness1) = commit_witness::<F, C, N>(&structure.pcs, [input]);
    let input = F::from(9u8);
    let (instance2, witness2) = commit_witness::<F, C, N>(&structure.pcs, [input]);

    let verifier: Verifier<F, Poseidon<F>, LcsRelation<F, C, 2, 4, 5>, _, ToFlcs> =
        Verifier::new(&structure);

    let instances = [instance1, instance2].map(|instance| verifier.verify(instance, ()).unwrap());

    let prover: Prover<F, Poseidon<F>, _, FlcsRelation<F, C, 2, 4, 5>, FlcsFoldingScheme> =
        Prover::new(&flcs_structure);
    let verifier: Verifier<F, Poseidon<F>, _, FlcsRelation<F, C, 2, 4, 5>, FlcsFoldingScheme> =
        Verifier::new(&flcs_structure);

    let witnesses = [witness1, witness2];

    let ProverOutput {
        instance,
        witness,
        proof,
    } = prover.prove(instances.clone(), witnesses);

    assert!(FlcsRelation::check(&flcs_structure, &instance, &witness));

    let verifier_instance = verifier.verify(instances, proof).unwrap();

    assert_eq!(verifier_instance, instance);

    let prover: Prover<F, Poseidon<F>, FlcsRelation<F, C, 2, 4, 5>, (), FlcsArgument> =
        Prover::new(&flcs_structure);

    let verifier: Verifier<F, Poseidon<F>, FlcsRelation<F, C, 2, 4, 5>, (), FlcsArgument> =
        Verifier::new(&flcs_structure);

    let ProverOutput {
        instance: _,
        witness: _,
        proof,
    } = prover.prove(instance.clone(), witness);

    let _: () = verifier.verify(instance, proof).unwrap();
}

#[test]
fn flcs_fold() {
    use ark_vesta::{Fr, Projective, VestaConfig};
    use commit::ipa2::IpaCommitmentScheme;
    use hash_to_curve::svdw::SvdwMap;

    type Scheme = IpaCommitmentScheme<Fr, Projective, SvdwMap<VestaConfig>>;

    test::<Fr, Scheme, 3>();
}
