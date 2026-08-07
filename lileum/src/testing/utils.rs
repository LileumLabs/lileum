use ark_ff::Field;
use ccs::{
    circuit::{Circuit, Var},
    constraint_system::{ConstraintSystem, Val},
    gates::StandardGates,
};

/// Poseidon2 permutation like circuit, 8 external rounds, 40 internal rounds,
/// sbox degree 7, and state size 3.
/// It does the same type and number of operations, but all constants are set to state\[0\].
pub struct TestingHash;

impl<F: Field> Circuit<F, 3, 3, 3> for TestingHash {
    type PrivateInput = ();

    type PrivateOutput = [F; 3];

    fn circuit<V: Val, C: ConstraintSystem<F, V>>(
        cs: &mut C,
        public_input: [Var<V>; 3],
    ) -> ([Var<V>; 3], [Var<V>; 3]) {
        let x = public_input[0].clone();
        let constant = x.clone();
        let mut state = public_input;

        for _ in 0..4 {
            add_constants(cs, &mut state, &constant);
            sbox(cs, &mut state);
            apply_matrix(cs, &mut state);
        }

        for _ in 0..40 {
            state[0] = cs.add(state[0].clone(), constant.clone());
            state[0] = cs.pow::<7>(state[0].clone());
            apply_matrix(cs, &mut state);
        }

        for _ in 0..4 {
            add_constants(cs, &mut state, &constant);
            sbox(cs, &mut state);
            apply_matrix(cs, &mut state);
        }

        (state.clone(), state)
    }

    fn handle_output(out: [F; 3]) -> Self::PrivateOutput {
        out
    }
}

/*
#[test]
fn profile_hash() {
    use ark_vesta::Fr;
    use ccs::circuit::BuildStructure;

    let profile = <TestingHash as BuildStructure<Fr, 3, 3, 3, 5>>::profile();
    println!("{profile}");
}
*/

fn add_constants<F: Field, V: Val, C: ConstraintSystem<F, V>>(
    cs: &mut C,
    state: &mut [Var<V>; 3],
    constant: &Var<V>,
) {
    let new_state = state.clone().map(|x| cs.add(x, constant.clone()));
    *state = new_state;
}

fn sbox<F: Field, V: Val, C: ConstraintSystem<F, V>>(cs: &mut C, state: &mut [Var<V>; 3]) {
    let new_state = state.clone().map(|x| cs.pow::<7>(x));
    *state = new_state;
}

fn apply_matrix<F: Field, V: Val, C: ConstraintSystem<F, V>>(cs: &mut C, state: &mut [Var<V>; 3]) {
    let [s0, s1, s2] = state.clone();
    let sum = cs.add_n::<4, 3>(state.clone());
    let s0 = cs.add(sum.clone(), s0);
    let s1 = cs.add(sum.clone(), s1);
    let double_s2 = cs.double(s2);
    let s2 = cs.add(sum.clone(), double_s2);
    *state = [s0, s1, s2];
}

pub struct HashChain<const N: usize>;

impl<F: Field, const N: usize> Circuit<F, 1, 1, 1> for HashChain<N> {
    type PrivateInput = ();

    type PrivateOutput = F;

    fn circuit<V: Val, C: ConstraintSystem<F, V>>(
        cs: &mut C,
        public_input: [Var<V>; 1],
    ) -> ([Var<V>; 1], [Var<V>; 1]) {
        let [x] = public_input;
        let mut state = [(); 3].map(|_| x.clone());

        for _ in 0..N {
            let (new_state, _) = <TestingHash as Circuit<F, 3, 3, 3>>::circuit(cs, state.clone());
            state = new_state;
        }

        let [out, _, _] = state;
        ([out.clone()], [out])
    }

    fn handle_output([out]: [F; 1]) -> Self::PrivateOutput {
        out
    }
}

/*
#[test]
fn profile_chain() {
    use ark_vesta::Fr;
    use ccs::circuit::BuildStructure;

    let profile = <HashChain<100> as BuildStructure<Fr, 1, 1, 1, 5>>::profile();
    println!("{profile}");
}
*/
