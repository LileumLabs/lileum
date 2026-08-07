use ark_ff::{BigInteger, Field, PrimeField};

/// casts element from one field into the other, assuming that bias
/// is acceptable.
pub fn cycle_cast<F1, F2>(x: F1) -> F2
where
    F1: Field,
    F2: Field,
{
    assert_eq!(
        F1::BasePrimeField::MODULUS_BIT_SIZE,
        F2::BasePrimeField::MODULUS_BIT_SIZE,
        "can't cast between fields of sizes differeing by a bit or more"
    );
    assert_eq!(
        F1::extension_degree(),
        F2::extension_degree(),
        "can't cast between fields of different extension degree"
    );
    let elems: Vec<F2::BasePrimeField> = x
        .to_base_prime_field_elements()
        .map(|x| {
            let bytes = x.into_bigint().to_bytes_le();
            F2::BasePrimeField::from_le_bytes_mod_order(&bytes)
        })
        .collect();
    F2::from_base_prime_field_elems(&elems).unwrap()
}
