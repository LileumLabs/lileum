use crate::NoError;
use alloc::vec::Vec;
use ark_ff::{BigInteger, Field, PrimeField};
use core::{any::Any, fmt::Debug, marker::PhantomData};

/// Any message must consist of a constant number of field elements,
/// or a number which is function of some paramenters.
pub trait Message<F>: Any + Clone + Debug {
    /// The information needed to determine the length of the message.
    /// Use () if it is a constant.
    type Params: Debug + Copy;
    // Possible error when converting element into field elements.
    type Error: Debug;

    /// The message length should be defined by the type and parameters
    /// for all possible valid values.
    /// You may ignore invalid values here as you can output an error
    /// when handling them.
    fn len(params: &Self::Params) -> usize;
    /// This should never panic, if the value is invalid it should
    /// return an error.
    /// Ideally, the type will be designed such that all possible values
    /// are valid. But that isn't always possible, and for such cases,
    /// errors should be used.
    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error>;
}

/// Used internally to handle generating challenge points.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PointRound;

impl<F> Message<F> for PointRound {
    type Params = ();

    type Error = NoError;

    fn len(_params: &()) -> usize {
        0
    }

    fn to_field_elements(&self, _params: &()) -> Result<Vec<F>, Self::Error> {
        Ok(Vec::new())
    }
}

impl<F> Message<F> for () {
    type Params = ();

    type Error = NoError;

    fn len(_params: &()) -> usize {
        0
    }

    fn to_field_elements(&self, _params: &()) -> Result<Vec<F>, Self::Error> {
        Ok(Vec::new())
    }
}

impl<F, T: Message<F>, const N: usize> Message<F> for [T; N] {
    type Params = T::Params;

    type Error = T::Error;

    fn len(params: &Self::Params) -> usize {
        T::len(params) * N
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        let elems: Result<Vec<Vec<F>>, Self::Error> = self
            .iter()
            .map(|elem| elem.to_field_elements(params))
            .collect();
        Ok(elems?.into_iter().flatten().collect())
    }
}

impl<F, T: Message<F, Error = NoError>> Message<F> for Option<T> {
    type Params = T::Params;

    type Error = ();

    fn len(params: &Self::Params) -> usize {
        T::len(params)
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        match self {
            Some(x) => {
                let Ok(elems) = x.to_field_elements(params);
                Ok(elems)
            }
            None => Err(()),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForeignElement<F1, F2> {
    pub value: F1,
    _f2: PhantomData<F2>,
}

impl<F1, F2> From<F1> for ForeignElement<F1, F2>
where
    F1: Field,
    F2: Field,
{
    fn from(value: F1) -> Self {
        let bit_diff = F2::BasePrimeField::MODULUS_BIT_SIZE as i32
            - F1::BasePrimeField::MODULUS_BIT_SIZE as i32;
        let bit_diff = bit_diff.unsigned_abs();
        assert!(bit_diff < 8, "fields differ in size in more than a byte");

        Self {
            value,
            _f2: PhantomData,
        }
    }
}

impl<F1, F2> Message<F2> for ForeignElement<F1, F2>
where
    F1: Field,
    F2: Field,
{
    type Params = ();

    type Error = NoError;

    fn len(_: &()) -> usize {
        2
    }

    fn to_field_elements(&self, _: &()) -> Result<Vec<F2>, Self::Error> {
        let (low, high) = self
            .value
            .to_base_prime_field_elements()
            .map(|x| {
                let mut bytes = x.into_bigint().to_bytes_le();
                let high_byte = bytes.pop().unwrap();
                let low = F2::BasePrimeField::from_le_bytes_mod_order(&bytes);
                let high = F2::BasePrimeField::from_le_bytes_mod_order(&[high_byte]);
                (low, high)
            })
            .unzip::<_, _, Vec<_>, Vec<_>>();
        let low = F2::from_base_prime_field_elems(&low).unwrap();
        let high = F2::from_base_prime_field_elems(&high).unwrap();
        Ok(alloc::vec![low, high])
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SingleElement<F>(pub F);

impl<F: Field> Message<F> for SingleElement<F> {
    type Params = ();

    type Error = NoError;

    fn len(_: &()) -> usize {
        1
    }

    fn to_field_elements(&self, _: &()) -> Result<Vec<F>, Self::Error> {
        Ok(alloc::vec![self.0])
    }
}
