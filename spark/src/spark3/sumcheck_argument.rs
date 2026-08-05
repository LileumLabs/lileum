use crate::spark3::SparseMle;
use ark_ff::Field;
use commit::commit2::oracle::CommittedNature;
use std::{fmt::Debug, vec::IntoIter};
use sumcheck::{
    evals::{Evals, EvalsCore},
    oracles::{
        composite::Either,
        core::{Coeffs, CoreNature, Func},
        SumcheckFunction,
    },
    MultiPoint, Var,
};
use sumcheck_derive::EvalsCore;

#[derive(Clone, Default, Copy, Debug, PartialEq, Eq, EvalsCore)]
pub struct DimensionEvals<V: Clone + Debug = ()> {
    address: V,
    pub(crate) eq_lookup: V,
    pub(crate) inverse: V,
}

impl<V: Clone + Debug> DimensionEvals<V> {
    pub fn new(address: V, eq_lookup: V, inverse: V) -> Self {
        Self {
            address,
            eq_lookup,
            inverse,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, EvalsCore)]
pub struct SparkEvals<V: Clone + Debug, const N: usize> {
    pub(crate) dimensions: [DimensionEvals<V>; N],
    value: V,
    pub(crate) zerocheck: V,
    challenges: SparkChallenges<V>,
}

impl<V: Clone + Debug + Default, const N: usize> Default for SparkEvals<V, N> {
    fn default() -> Self {
        let dimensions = [(); N].map(|_| Default::default());
        Self {
            dimensions,
            value: Default::default(),
            zerocheck: Default::default(),
            challenges: Default::default(),
        }
    }
}

impl<F: Field, const N: usize> SparkEvals<Option<Func<F>>, N> {
    pub fn small_functions() -> Self {
        let dimensions = [DimensionEvals::<Option<Func<F>>>::new(None, None, None); N];
        let value = None;
        let zerocheck: Func<F> = |chall: &[F], point: &MultiPoint<F>| {
            assert_eq!(chall.len(), point.vars());
            let chall = MultiPoint::new(chall.to_vec());
            chall.eval_as_eq(point)
        };
        let zerocheck = Some(zerocheck);
        let challenges = SparkChallenges::default();

        Self {
            dimensions,
            value,
            zerocheck,
            challenges,
        }
    }
}

impl<F: Field, const N: usize> SparkEvals<F, N> {
    pub(crate) fn structure(sparse_mle: &SparseMle<F, N>) -> Vec<Self> {
        let SparseMle { addresses, values } = sparse_mle;
        assert_eq!(addresses.len(), values.len());
        assert!(addresses.len().is_power_of_two());

        addresses
            .iter()
            .zip(values)
            .map(|(addresses, val)| {
                let dimensions = addresses.each_ref().map(|addr| DimensionEvals {
                    address: F::from(*addr),
                    eq_lookup: F::ZERO,
                    inverse: F::ZERO,
                });
                let zerocheck = F::ZERO;
                let challenges = SparkChallenges {
                    combination: F::ZERO,
                    compression: F::ZERO,
                    lookup: F::ZERO,
                };
                SparkEvals {
                    dimensions,
                    value: *val,
                    zerocheck,
                    challenges,
                }
            })
            .collect()
    }
}

impl<F: Field, const N: usize> SparkEvals<Vec<F>, N> {
    /// Sets the coefficients expected for the instance of CoreOracle.
    pub fn oracle_instance(
        challenges: &SparkChallenges<F>,
        zerocheck_point: MultiPoint<F>,
    ) -> Self {
        let challenges = SparkChallenges::map_evals(challenges, |c| vec![*c]);
        let zerocheck = zerocheck_point.inner();
        SparkEvals {
            zerocheck,
            challenges,
            ..Default::default()
        }
    }
}

impl<C: Debug + Clone, const N: usize> SparkEvals<Option<C>, N> {
    pub fn arrange_commitments(lookup_commitments: [C; N], inverse_commitments: [C; N]) -> Self {
        let mut dimensions = lookup_commitments.map(|commit| DimensionEvals {
            eq_lookup: Some(commit),
            ..Default::default()
        });
        for (dim, commit) in dimensions.iter_mut().zip(inverse_commitments) {
            dim.inverse = Some(commit)
        }
        SparkEvals {
            dimensions,
            ..Default::default()
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, EvalsCore, Default)]
pub struct SparkChallenges<V: Clone + Debug> {
    combination: V,
    compression: V,
    lookup: V,
}

impl SparkChallenges<Either<CoreNature, CommittedNature>> {
    pub fn natures() -> Self {
        let challenge = Either::Left(CoreNature::Challenge);
        Self {
            combination: challenge,
            compression: challenge,
            lookup: challenge,
        }
    }
}

impl<V: Clone + Debug> SparkChallenges<V> {
    pub fn new(combination: V, compression: V, lookup: V) -> Self {
        Self {
            combination,
            compression,
            lookup,
        }
    }
}

impl<F: Field, const N: usize> SumcheckFunction<F> for SparkEvals<(), N> {
    type Natures = Either<CoreNature, CommittedNature>;
    type Data = ();

    fn natures() -> Self::Mles<Self::Natures> {
        let r = |n| Either::Right(n);

        let dimensions = [(); N].map(|_| DimensionEvals {
            address: r(CommittedNature::Structure),
            eq_lookup: r(CommittedNature::Witness),
            inverse: r(CommittedNature::Witness),
        });
        SparkEvals {
            dimensions,
            value: r(CommittedNature::Structure),
            zerocheck: Either::Left(CoreNature::SmallInstance(Coeffs::PerVariable)),
            challenges: SparkChallenges::natures(),
        }
    }

    fn function<V: Var<F> + Debug>(_: &(), evals: &Self::Mles<V>) -> V {
        let SparkEvals {
            dimensions,
            value,
            zerocheck,
            challenges,
        } = &evals;

        let dimensions: &[DimensionEvals<V>; N] = dimensions;

        let mut checks = form_check::<F, V>(&dimensions[0], challenges);
        let mut eq = dimensions[0].eq_lookup.clone();

        for dimension in &dimensions[1..] {
            let check = form_check(dimension, challenges);
            checks = checks * &challenges.combination + check;
            let eq_segment = &dimension.eq_lookup;
            eq = eq * eq_segment;
        }

        let eval = eq * value;

        let zerocheck = checks * zerocheck;
        let mut inverse_sums = zerocheck;

        for dimension in dimensions {
            let inverse = &dimension.inverse;
            inverse_sums = inverse_sums * &challenges.combination + inverse;
        }

        inverse_sums * &challenges.combination + eval
    }
}

fn form_check<F, V>(dim: &DimensionEvals<V>, challenges: &SparkChallenges<V>) -> V
where
    F: Field,
    V: Var<F> + Debug,
{
    let indexed_lookup = dim.address.clone() * &challenges.compression + &dim.eq_lookup;

    let product = (indexed_lookup + &challenges.lookup) * &dim.inverse;

    product - F::one()
}
