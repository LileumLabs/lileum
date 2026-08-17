use ark_ff::{One, Zero};
use lileum::simple_cs::*;

// Given:
// f(0) = 0
// f(1) = 1
// f(i+2) = f(i) + f(i+1)
// We want to prove that f(1000) = x for some x.
struct MyCircuit;

// The number of iterations to be proved.
// The circuit we will build will starts from f(0) and f(1), then
// applies f N times.
// Thus, for f(1000) we want the recursive part applied 999 times.
const N: usize = 999;

// Now we make use of public inputs and outputs.
// The 2 public inputs are intended to be passed f(0) and f(1).
// The public output will be the value of f(1000).
// Note that this design allows for proving more statements, we could
// pass f(100) and f(101) as inputs instead, and we would be proving
// the value of f(1100).
impl<F: Field> Circuit<F, 2, 1> for MyCircuit {
    // We are still not using these.
    type PrivateInput = ();
    type PrivateOutput = ();

    fn circuit<V: Val, C: ConstraintSystem<F, V>>(
        cs: &mut C,
        public_input: [Var<V>; 2],
    ) -> ([Var<V>; 1], [Var<V>; 0]) {
        let [_, res] = (0..N).fold(public_input, |last_two, _| {
            let [a, b] = last_two;
            let c = cs.add(a, b.clone());
            [b, c]
        });

        ([res], [])
    }

    fn handle_output([]: [F; 0]) -> Self::PrivateOutput {}
}

use field_and_pcs::{Fr, FrScheme};

// This fixes the case where rust analyzer doesn't recognize
// trait implementations, but isn't required to build.
fn main_inner()
where
    Fr: PrimeField,
    FrScheme: CommitmentScheme<Fr>,
{
    let circuit_key: CircuitKey<Fr, MyCircuit, FrScheme, 3> = CircuitKey::new();
    //--------------------
    // Before going into proving, this is another thing we can do with a circuit:
    let profile = circuit_key.profile();
    println!("{:?}", profile);
    // A profile shows what gates are being used in the circuit and the number of variables.
    // Profiling doesn't require a circuit key, the method is just a convenience.
    //--------------------

    // Now we do have inputs, which are [fib(0), fib(1)].
    let inputs = [Fr::zero(), Fr::one()];

    let (instance, proof, _output) = circuit_key.prove_from_inputs(inputs);
    let instance: ClcsInstance<Fr, FrScheme, 3> = instance;
    let proof: Proof<Fr, FrScheme> = proof;

    // Now there is an extra check to do. We want a a valid proof
    // of the instance [fib(0),fib(1),fib(1000)], not just any
    // posible isntance.
    assert_eq!(instance.public_inputs()[0], Fr::zero());
    assert_eq!(instance.public_inputs()[1], Fr::one());
    let res = instance.public_inputs()[2];
    // Now we verify the proof
    assert!(circuit_key.verify(instance, proof));
    println!("fib(1000) = {}", res);
}

fn main() {
    main_inner();
}
