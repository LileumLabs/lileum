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
    // let key = CircuitKey::<Fr, Sponge, HashChain<N>, Scheme, 2, 4, 5>::new();
    let ccs_structure: CcsStructure<F, 4, 5> =
        <HashChain<N> as BuildStructure<F, 1, 1, 1, 4>>::structure();

    let pcs = C::new(ccs_structure.vars());
    let structure = LcsStructure { ccs_structure, pcs };

    let prover: Prover<F, Poseidon<F>, LcsRelation<F, C, 1, 4, 5>, (), LcsArgument> =
        Prover::new(&structure, &(), ());

    let verifier: Verifier<F, Poseidon<F>, LcsRelation<F, C, 1, 4, 5>, (), LcsArgument> =
        Verifier::new(&structure, &(), ());

    let input = F::from(8u8);
    let (instance, witness) = commit_witness::<F, C, N>(&structure.pcs, [input]);

    assert!(LcsRelation::<F, C, 1, 4, 5>::check(
        &structure, &instance, &witness
    ));
    let ProverOutput {
        instance: _,
        witness: _,
        proof,
    } = prover.prove(instance.clone(), witness);

    verifier.verify(instance, proof).unwrap();
}

pub fn commit_witness<F, C, const N: usize>(
    pcs: &C,
    inputs: [F; 1],
) -> (LcsInstance<F, C, 1>, Vec<F>)
where
    F: Field,
    C: CommitmentScheme<F>,
{
    use ccs::circuit::Prove;
    let (mut witness, _output) = <HashChain<N> as Prove<F, 1, 1, 1, 5>>::witness(inputs, true);
    witness.pad_to_power();
    let witness_commit = pcs.commit_mle(&witness.0);

    let mut inputs = [F::zero(); 1];
    inputs.copy_from_slice(&witness.0[0..1]);

    let instance: LcsInstance<F, C, 1> = LcsInstance {
        witness_commit,
        public_inputs: inputs,
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
