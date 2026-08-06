use crate::{relations::LcsInstance, testing::utils::HashChain};
use ark_ff::Field;
use commit::CommitmentScheme;
use sponge::{poseidon2::PoseidonDefault, sponge::Sponge};

mod folding;
mod lcs_argument;

type Poseidon<F> = Sponge<F, PoseidonDefault<F>, 2, 1, 3>;

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
