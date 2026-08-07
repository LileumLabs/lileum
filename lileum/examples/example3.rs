use ark_ff::BigInteger;
use lileum::{circuits::Uint, simple_cs::*};

// This circuit allows proving that some secret number is greater
// than the value of the single public input provided.
// Given public inputs MIN and secret x, we prove that
// MIN < x < 2^32.
struct MyCircuit;

fn balance<F: Field>() -> F {
    F::from(31_u8)
}

impl<F: Field> Circuit<F, 1, 0, 1> for MyCircuit {
    type PrivateInput = ();

    // This time, we will make use of private outputs just for
    // demonstration, we will output the balance.
    type PrivateOutput = u32;

    fn circuit<V: Val, C: ConstraintSystem<F, V>>(
        cs: &mut C,
        public_input: [Var<V>; 1],
    ) -> ([Var<V>; 0], [Var<V>; 1]) {
        let [minimum] = public_input;

        //TODO: use for private inputs.
        let amount = cs.free_variable(|_| balance());
        // Creating the int is enough to constraint the original value to the
        // be a 32 bits element.
        let _int: Uint<V, 32> = Uint::new(cs, amount.clone());

        // But that is not enough, that only proves our number is greater than 0.
        // How do we actually constraint x > 30?
        // By subtracting 30 and checking x > 0 again, considering that:
        // x > 30 -> x - 30 > 0

        let amount_less_minimum = cs.sub(amount.clone(), minimum);
        let _int: Uint<V, 32> = Uint::new(cs, amount_less_minimum);

        ([], [amount])
    }

    // The purpose of this method is to turn the values of the variables
    // in the private output from circuit() into our Self::PrivateOutput.
    fn handle_output([amount]: [F; 1]) -> Self::PrivateOutput {
        let bigint = amount.to_base_prime_field_elements().next().unwrap();
        let mut bytes = bigint.into_bigint().to_bytes_le();
        bytes.truncate(4);
        u32::from_le_bytes(bytes.try_into().unwrap())
    }
}

// This time we make our own commitment scheme, the result is
// the same, but the process is worth knowing.

// First choose a field.
use ark_vesta::Fr;
// Then a generic commitment scheme that supports our field.
// In this case, IpaCommitmentScheme works for 256 bits or bigger fields
// which are also the scalar field of some elliptic curve.
use commit::ipa::IpaCommitmentScheme;
// Fr is the scalar field of the Vesta cuerve, thus import the types
// representing curve points and the curve itself.
use ark_vesta::{Projective, VestaConfig};
// IpaCommitmentScheme also requires a hash-to-curve function, this
// crate has a geeneric implementation that works with Vesta.
use hash_to_curve::svdw::SvdwMap;

// Define the concrete pcs with the 3 type arguments, being for this particular
// pcs: field, curve, hash-to-curve function.
pub type FrScheme = IpaCommitmentScheme<Fr, Projective, SvdwMap<VestaConfig>>;

fn main_inner()
where
    Fr: PrimeField,
    FrScheme: CommitmentScheme<Fr>,
{
    let circuit_key: CircuitKey<Fr, MyCircuit, FrScheme, 1> = CircuitKey::new();

    // Our circuit allows to set any minumum in the balance, in our case
    // we are interested in the instance [30].
    let inputs = [Fr::from(30)];

    // This time we make use of private outputs, we output the balance, this is a
    // trivial case as we should already know it.
    // But in more complex cases private outputs allow to extract the results of big
    // computations done inside the circuit instead of having do them again
    // outside the circuit.
    let (instance, proof, private_output) = circuit_key.prove_from_inputs(inputs);
    let balance = private_output;
    println!("balance proved: {}", balance);

    // We verify as usual, checking it is the instance we want.
    assert_eq!(instance.public_inputs()[0], Fr::from(30));
    assert!(circuit_key.verify(instance, proof));
}

fn main() {
    main_inner();
}
