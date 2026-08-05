use crate::spark3::{
    sumcheck_argument::SparkEvals, SparkInstance, SparseMle, StaticSparkRelation,
    StaticSparkStructure, BYTE,
};
use ark_ff::{batch_inversion, Field};
use commit::commit2::{oracle::CommittedOracle, CommitmentScheme};
use std::{marker::PhantomData, rc::Rc};
use sumcheck::{
    eq,
    oracles::{composite::CompositeOracle, core::CoreOracle},
    MultiPoint,
};
use transcript::reduction2::Relation;

pub struct CommittedSparkRelation<F, C, const N: usize>(PhantomData<(F, C)>);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinorStructure<const N: usize> {
    pub counts: [Box<[usize; BYTE]>; N],
}

impl<const N: usize> MinorStructure<N> {
    pub(crate) fn new<F: Field>(mle: &SparseMle<F, N>) -> Self {
        let mut counts: [Box<[usize; 256]>; N] =
            [(); N].map(|_| (vec![0; BYTE]).into_boxed_slice().try_into().unwrap());

        for (i, counts) in counts.iter_mut().enumerate() {
            for addr in mle.addresses.iter() {
                let segment = addr[i];
                counts[segment as usize] += 1;
            }
        }

        Self { counts }
    }

    /// Computes the sums at the left of the equation, thanks to restricting the
    /// lookup table to 8 bits it can be done in about 256 operations.
    pub(crate) fn expected_sums<F: Field>(
        &self,
        point: &[MultiPoint<F>; N],
        lookup_challenge: F,
        compression_challenge: F,
    ) -> [F; N] {
        let mut res = [F::zero(); N];

        #[allow(clippy::needless_range_loop)]
        for i in 0..N {
            let point = &point[i];
            let counts = &self.counts[i];
            let mut denominators = eq::eq(point);
            for (i, e) in denominators.iter_mut().enumerate() {
                let address = F::from(i as u8);
                *e = address * compression_challenge + *e + lookup_challenge;
            }
            batch_inversion(&mut denominators);
            let inverses = denominators;
            res[i] = inverses
                .into_iter()
                .zip(counts.iter())
                .fold(F::zero(), |acc, e| {
                    let (inverse, count) = e;
                    let count = F::from(*count as u64);
                    acc + inverse * count
                });
        }
        res
    }
}

pub type Oracle<F, C, SF> = CompositeOracle<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;
pub type SparkOracle<F, C, const N: usize> = Oracle<F, C, SparkEvals<(), N>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommittedSparkStructure<F: Field, C: CommitmentScheme<F>, const N: usize> {
    oracle: SparkOracle<F, C, N>,
    minor_structure: MinorStructure<N>,
    mle: Rc<SparseMle<F, N>>,
    pcs: C,
}

impl<F, C, const N: usize> Relation for CommittedSparkRelation<F, C, N>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Structure = CommittedSparkStructure<F, C, N>;

    type Instance = SparkInstance<F>;

    type Witness = ();

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let static_spark = StaticSparkStructure {
            mle: Rc::clone(&structure.mle),
            pcs: structure.pcs.clone(),
        };
        if !StaticSparkRelation::check(&static_spark, instance, witness) {
            return false;
        }
        let minor_structure = MinorStructure::new(&structure.mle);
        if minor_structure != structure.minor_structure {
            return false;
        }

        let oracle = oracle(&structure.mle, structure.pcs.clone());
        oracle == structure.oracle
    }
}

fn oracle<F, C, const N: usize>(mles: &SparseMle<F, N>, pcs: C) -> SparkOracle<F, C, N>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    let builder1: CoreOracle<F, SparkEvals<(), N>> = {
        let functions = SparkEvals::small_functions();
        CoreOracle::new(functions)
    };

    let builder2 = { pcs };

    let mles = Rc::new(SparkEvals::structure(mles));

    CompositeOracle::new((), mles, builder1, builder2)
}

impl<F: Field, C: CommitmentScheme<F>, const N: usize> CommittedSparkStructure<F, C, N> {
    pub fn new(mle: Rc<SparseMle<F, N>>, pcs: C) -> Self {
        let minor_structure = MinorStructure::new(&mle);
        let oracle = oracle(&mle, pcs.clone());
        Self {
            oracle,
            minor_structure,
            mle,
            pcs,
        }
    }
}
