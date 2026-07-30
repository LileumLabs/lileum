use ark_ff::{Field, PrimeField};
use ccs::{circuit::BuildStructure, structure::CcsStructure};
use commit::commit2::CommitmentScheme;
use sponge::{poseidon2::PoseidonDefault, sponge::Sponge};
use transcript::reduction2::{Prover, ProverOutput, Relation, Verifier};

use crate::{
    lilium2::{
        reductions::LcsArgument,
        relations::{LcsInstance, LcsRelation, LcsStructure},
    },
    testing::utils::HashChain,
};

type Poseidon<F> = Sponge<F, PoseidonDefault<F>, 2, 1, 3>;

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
        Prover::new(&structure, &(), ());

    let verifier: Verifier<F, Poseidon<F>, LcsRelation<F, C, 2, 4, 5>, (), LcsArgument> =
        Verifier::new(&structure, &(), ());

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

/// Creates an instance-witness pair from public inputs.
pub fn commit_witness<F, C, const N: usize>(
    pcs: &C,
    inputs: [F; 1],
) -> (LcsInstance<F, C, 2>, Vec<F>)
where
    F: Field,
    C: CommitmentScheme<F>,
{
    use ccs::circuit::Prove;
    let (mut witness, _output) = <HashChain<N> as Prove<F, 1, 1, 1, 5>>::witness(inputs, true);
    witness.pad_to_power();
    let witness_commit = pcs.commit_mle(&witness.0);

    let mut inputs = [F::zero(); 2];
    inputs.copy_from_slice(&witness.0[0..2]);

    let public_inputs = inputs;

    let instance: LcsInstance<F, C, 2> = LcsInstance {
        witness_commit,
        public_inputs,
    };

    (instance, witness.0)
}

#[test]
fn hash_chain_prove() {
    use ark_vesta::{Fr, Projective, VestaConfig};
    use commit::ipa2::IpaCommitmentScheme;
    use hash_to_curve::svdw::SvdwMap;

    type Scheme = IpaCommitmentScheme<Fr, Projective, SvdwMap<VestaConfig>>;

    test::<Fr, Scheme, 3>();
}
