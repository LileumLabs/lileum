use alloc::vec::Vec;
use ark_ff::{BigInteger, Field, PrimeField};
use lcs::{circuit::Var, extensions::LcsExtension, structure::WitnessIndex};

/// An extension providing an 8 bits range check.
#[derive(Clone, Debug, Default)]
pub struct ByteCheck;

impl<F: Field> LcsExtension<F> for ByteCheck {
    type Constraint = ();

    type StructureBuilder = Vec<Var<WitnessIndex>>;

    type WitnessBuilder = (Self::StructureBuilder, Vec<u8>);

    type Structure = Vec<bool>;

    type Witness = ();

    fn process_structure(_builder: Self::StructureBuilder) -> Self::Structure {
        todo!()
    }

    fn process_witness(_builder: Self::WitnessBuilder) -> Self::Witness {
        todo!()
    }

    fn record_constraint<const N: usize>(
        builder: &mut Self::StructureBuilder,
        vars: [Var<WitnessIndex>; N],
        _: (),
    ) {
        assert_eq!(N, 1);
        let var = vars[0];
        builder.push(var);
    }

    fn compute_constraint<const N: usize>(witness: &mut Self::WitnessBuilder, vars: [F; N], _: ()) {
        assert_eq!(N, 1);
        assert!(vars[0] >= F::from(u8::MIN));
        assert!(vars[0] <= F::from(u8::MAX));
        let v = vars[0].to_base_prime_field_elements().next().unwrap();
        let v = v.into_bigint().to_bytes_le()[0];
        witness.1.push(v);
    }
}
