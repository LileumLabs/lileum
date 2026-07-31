use ark_ff::Field;
use commit::commit2::CommitmentScheme;
use std::{marker::PhantomData, rc::Rc};
use sumcheck::{eq, polynomials::MultiPoint, sumcheck2::oracles::UnexpectedVars};
use transcript::reduction2::{Message, Relation};

mod committed;
pub mod flexible;
mod prove;
mod reduction;
pub mod sumcheck_argument;
#[cfg(test)]
mod tests;

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
    pub fn new(addresses: Vec<[u8; N]>, values: Vec<F>) -> Self {
        Self { addresses, values }
    }

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
pub struct StaticSparkStructure<F: Field, C, const N: usize> {
    mle: Rc<SparseMle<F, N>>,
    pcs: C,
}

#[derive(Clone, Copy, Debug)]
pub struct StaticSparkRelation<F, C, const N: usize>(PhantomData<(F, C)>);

#[derive(Clone, Debug)]
pub struct SparkInstance<F: Field> {
    point: MultiPoint<F>,
    eval: F,
}

impl<F: Field> SparkInstance<F> {
    pub(crate) fn align_to_byte(self) -> Self {
        let Self { point, eval } = self;
        let mut point = point.inner();
        if point.len() % 8 != 0 {
            point.resize((point.len() / 8) * 8 + 8, F::ZERO);
        }
        let point = MultiPoint::new(point);
        Self { point, eval }
    }
}

impl<F: Field> Message<F> for SparkInstance<F> {
    type Params = usize;

    type Error = UnexpectedVars;

    fn len(params: &Self::Params) -> usize {
        MultiPoint::<F>::len(params) + 1
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        let SparkInstance { point, eval } = self;
        let mut elems = point.to_field_elements(params)?;
        elems.push(*eval);
        Ok(elems)
    }
}

impl<F: Field> SparkInstance<F> {
    pub fn new(point: MultiPoint<F>, eval: F) -> Self {
        Self { point, eval }
    }
}

impl<F, C, const N: usize> Relation for StaticSparkRelation<F, C, N>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Structure = StaticSparkStructure<F, C, N>;

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
pub struct FlexibleSparkStructure<F: Field, C> {
    evals: Rc<Vec<(u64, F)>>,
    pcs: C,
}

impl<F: Field, C> FlexibleSparkStructure<F, C> {
    pub fn new(evals: Rc<Vec<(u64, F)>>, pcs: C) -> Self {
        Self { evals, pcs }
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

#[derive(Clone, Copy, Debug)]
pub struct FlexibleSparkRelation<F, C>(PhantomData<(F, C)>);

impl<F: Field, C> Relation for FlexibleSparkRelation<F, C> {
    type Structure = FlexibleSparkStructure<F, C>;

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
