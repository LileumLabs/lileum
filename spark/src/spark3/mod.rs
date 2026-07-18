use ark_ff::Field;
use std::{marker::PhantomData, rc::Rc};
use sumcheck::{eq, polynomials::MultiPoint};
use transcript::reduction2::Relation;

mod committed;
pub mod flexible;
mod prove;
mod reduction;
pub mod sumcheck_argument;

pub use committed::CommittedSparkRelation;
pub use flexible::FlexibleSpark;
pub use reduction::SparkReduction;

const BYTE: usize = 256;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseMle<F, const N: usize> {
    /// Addresses in u8 segments.
    addresses: Vec<[u8; N]>,
    /// The value at given address.
    values: Vec<F>,
}

impl<F: Field, const N: usize> SparseMle<F, N> {
    pub fn eval(&self, point: &MultiPoint<F>) -> F {
        assert_eq!(point.vars(), N * 8);
        assert!(self.values.len().is_power_of_two());
        assert_eq!(self.values.len(), self.addresses.len());
        let segments: [MultiPoint<F>; N] = point
            .inner_ref()
            .chunks(8)
            .map(|segment| MultiPoint::new(segment.to_vec()))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let eqs = segments.map(|segment| eq::eq(&segment));

        self.addresses
            .iter()
            .zip(&self.values)
            .fold(F::ZERO, |acc, (addr, val)| {
                let eq: F = addr
                    .iter()
                    .enumerate()
                    .fold(F::ONE, |acc, (i, addr)| acc * eqs[i][*addr as usize]);
                acc + eq * val
            })
    }
}

// #[derive(Clone, Debug)]
// struct MinorStructure<const N: usize> {
// counts: [Box<[usize; BYTE]>; N],
// }

#[derive(Clone, Debug)]
pub struct StaticSparkStructure<F: Field, const N: usize> {
    // minor_structure: MinorStructure<N>,
    mle: Rc<SparseMle<F, N>>,
}

pub struct StaticSparkRelation<F, const N: usize>(PhantomData<F>);

pub struct SparkInstance<F: Field> {
    point: MultiPoint<F>,
    eval: F,
}

impl<F: Field> SparkInstance<F> {
    pub fn new(point: MultiPoint<F>, eval: F) -> Self {
        Self { point, eval }
    }
}

impl<F, const N: usize> Relation for StaticSparkRelation<F, N>
where
    F: Field,
{
    type Structure = StaticSparkStructure<F, N>;

    type Instance = SparkInstance<F>;

    type Witness = ();

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        _witness: &Self::Witness,
    ) -> bool {
        if instance.point.vars() != N * 8 {
            return false;
        }

        let eval = structure.mle.eval(&instance.point);

        if eval != instance.eval {
            return false;
        }

        true
    }
}

#[derive(Clone, Debug)]
pub struct FlexibleSparkStructure<F: Field> {
    evals: Rc<Vec<(u64, F)>>,
}

impl<F: Field> FlexibleSparkStructure<F> {
    pub fn new(evals: Rc<Vec<(u64, F)>>) -> Self {
        Self { evals }
    }

    pub fn eval(&self, point: MultiPoint<F>) -> F {
        let mut point = point.inner();
        point.resize(u64::BITS as usize, F::ZERO);

        let segments: [MultiPoint<F>; 8] = point
            .chunks(8)
            .map(|segment| MultiPoint::new(segment.to_vec()))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let eqs = segments.map(|segment| eq::eq(&segment));

        self.evals.iter().fold(F::ZERO, |acc, (addr, val)| {
            //TODO: check this
            let addr = addr.to_le_bytes();
            let eq: F = addr
                .iter()
                .enumerate()
                .fold(F::ONE, |acc, (i, addr)| acc * eqs[i][*addr as usize]);
            acc + eq * val
        })
    }
}

pub struct FlexibleSparkRelation<F>(PhantomData<F>);

impl<F: Field> Relation for FlexibleSparkRelation<F> {
    type Structure = FlexibleSparkStructure<F>;

    type Instance = SparkInstance<F>;

    type Witness = ();

    fn check(structure: &Self::Structure, instance: &SparkInstance<F>, _: &()) -> bool {
        let SparkInstance { point, eval } = instance;

        let expected = structure.eval(point.clone());

        *eval == expected
    }
}
// t' = eq(r,x)
// t = (0..256) * t'
// f = addr * eq
//
//      m           1
//  Σ -----  = Σ  -----
//    t + µ       f + µ
//
// for the right:
// r_inv = 1 / (f + µ)
// check that r_inv * (f + µ) == 1
