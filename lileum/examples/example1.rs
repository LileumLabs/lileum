use lileum::simple_cs::*;

// A circuit is a trait implementation, to define a circuit we
// first define some type, an empty struct is enough.
struct MyCircuit;

fn my_number<F: Field>() -> F {
    F::from(25u32)
}

// And then implement the Circuit trait.
// For this circuit when don't care about the specific field, we will make
// implement the trait for any field.
impl<F: Field> Circuit<F> for MyCircuit {
    // This is not yet supported, can be any type.
    type PrivateInput = ();

    // This one is supported, but not necessary for this example.
    type PrivateOutput = ();

    // Here 'cs' will allows to create variables and create gates.
    // The second argument are the public inputs of the circuit, which in
    // this case we won't use.
    fn circuit<V: Val, C: ConstraintSystem<F, V>>(
        cs: &mut C,
        []: [Var<V>; 0],
    ) -> ([Var<V>; 0], [Var<V>; 0]) {
        // This method creates a new variable free of any constraint, it can
        // have any posible value.
        // It takes a closure (_,_) -> F, which should return the value of the new
        // variable, the 2 arguments allow to read the value of existing variables,
        // something we don't need in this case.
        let x = cs.free_variable(|_| my_number());
        // As sqrt gives -5, we negate to have a simpler number, but both would work.
        let w = cs.free_variable(|_| -my_number::<F>().sqrt().expect("number is not square"));

        // Gates create new variables from existing variables, and enforce certain
        // constraints between them.
        //
        // "let x = cs.square(y)" for example creates a new variable "x" from a existing
        // variable "y" such that x = y^2.
        //
        // There is the general cs.execute(inputs) method to create an arbitrary gate.
        // But common gates have their own methods through the [StandardGates] trait.

        // Here we create a [gates::Square] gate.
        let w_square = cs.square(w);

        // And a [gates::Equality] gate.
        cs.assert_equals(x, w_square);

        // This are the public and private outputs of the circuit,
        // of which neither is used for this example.
        ([], [])
    }

    // This function will be called with the private output returned above.
    // In this trivial it is just a [F;0] -> () function.
    fn handle_output([]: [F; 0]) -> Self::PrivateOutput {}
}

// Here we act as both prover and verifier, creating a proof and veriying it.
// If Rust Analyzer fails to regonize some methods, the next example will
// show how to fix it.
fn main() {
    // Import a concrete field and a commitment scheme for that field.
    use field_and_pcs::{Fr, FrScheme};

    // Creating a key for the circuit.
    // The key dependes on, Field, circuit, commitment scheme and number of inputs.
    let circuit_key: CircuitKey<Fr, MyCircuit, FrScheme, 0> = CircuitKey::new();

    let inputs = [];
    // Create instance and witness, the instance is a public representation
    // of the statement we want to prove, including public inputs if there were any.
    // The witness is a trace of the computation described in the circuit. It is
    // basically a vector of the values of all variables.
    let (instance, witness, _output) = circuit_key.commit_witness(inputs);
    let instance: LcsInstance<Fr, FrScheme, 0> = instance;
    let witness: Witness<Fr> = witness;

    // Now, we want to prove that the (instance,witness) pair satisfies the constraints
    // of the circuit.
    // The instance is public to both sides, while the witness is to remain only with
    // the prover.
    let proof: Proof<Fr, FrScheme> = circuit_key.prove(instance.clone(), witness);

    // The proof can now be verified without having the witness.
    assert!(circuit_key.verify(instance, proof));
    println!("verification successful");
    // verify(instance, proof) returns true if verification succeeds and false
    // if it fails.
    // I could either fail because a malicious prover created a fake proof, or
    // just because either instance or proof got mixed up with another one at
    // some point.

    // --------------------------------------------------------------------------

    // Here is a simpler way of doing the same in these cases were you want
    // to go directly from inputs to proof.
    let (instance, proof, _output) = circuit_key.prove_from_inputs(inputs);
    let instance: LcsInstance<Fr, FrScheme, 0> = instance;
    let proof: Proof<Fr, FrScheme> = proof;

    assert!(circuit_key.verify(instance, proof));
    println!("verification successful");
}
