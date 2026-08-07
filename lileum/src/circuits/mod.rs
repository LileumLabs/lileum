use ark_ff::{BigInteger, Field, PrimeField, Zero};
use ccs::{
    circuit::Var,
    constraint_system::{ConstraintSystem, Val, WitnessReader},
    gates::{Binary, StandardGates},
};

/// `Var` constrained to be in 0..2^N.
/// Currently the only use is constraining some [Var<V>] to be in
/// the interval, operations may be added in the future.
pub struct Uint<V, const N: usize> {
    val: Var<V>,
}

impl<V: Val, const N: usize> Uint<V, N> {
    /// Creates a new [Uint<V,N>] from an arbitrary [Var<V>].
    pub fn new<F: Field, CS: ConstraintSystem<F, V>>(cs: &mut CS, x: Var<V>) -> Self {
        if N == 0 {
            panic!("tried to create an uint with 0 bits");
        }

        let bits: [usize; N] = (0..N).collect::<Vec<usize>>().try_into().unwrap();
        let bits = bits.map(|i| {
            let bit = cs.free_variable(|reader| {
                // We either get a prime field, or a an extension field with
                // only its first base element being non-zero.
                let mut elements = reader.read(&x).to_base_prime_field_elements();
                let first = elements.next().unwrap();

                // And just panic if a full extension appears.
                for rest in elements {
                    assert!(rest.is_zero());
                }

                let bit = first.into_bigint().get_bit(i);
                if bit {
                    F::one()
                } else {
                    F::zero()
                }
            });
            let [] = cs.execute::<Binary, 1, 1, 0>([bit.clone()]);
            bit
        });
        let mut bits = bits.into_iter().rev();
        let composed = bits.next().unwrap();
        let composed = bits.fold(composed, |acc, bit| {
            //TODO: a mul-constant-and-add gate would require a single gate per bit.
            let acc2 = cs.add(acc.clone(), acc);
            cs.add(acc2, bit)
        });
        cs.assert_equals(composed.clone(), x);
        Self { val: composed }
    }

    /// Returns the inner constrained var.
    pub fn unwrap(self) -> Var<V> {
        let Self { val } = self;
        val
    }
}
