use crate::{MultiPoint, eq::eq};
use ark_ff::Field;
use std::{fmt::Debug, vec::IntoIter};

/// A trait that defines an abstract set of multilinear extensions.
/// The convention is to have an struct generic over V, which implements
/// EvalsCore for any V, and then implement Evals for Type<()>.
/// The derive macro will implement Evals and EvalsCore automatically,
/// instanciating V with () as mentioned.
pub trait Evals: Debug + Clone + 'static {
    type Mles<V: Clone + Debug>: EvalsCore<V>;

    fn map_evals<A, B, M>(evals: &Self::Mles<A>, f: M) -> Self::Mles<B>
    where
        A: Clone + Debug,
        B: Clone + Debug,
        M: Fn(&A) -> B;

    fn combine<A, B, C, M>(a: &Self::Mles<A>, b: &Self::Mles<B>, f: M) -> Self::Mles<C>
    where
        A: Clone + Debug,
        B: Clone + Debug,
        C: Clone + Debug,
        M: Fn(&A, &B) -> C;

    fn apply<A, M>(a: &mut Self::Mles<A>, f: M)
    where
        A: Clone + Debug,
        M: Fn(&mut A);

    fn combine_mut_conditional<A, B, M>(
        a: &mut Self::Mles<A>,
        b: &Self::Mles<B>,
        c: Self::Mles<bool>,
        f: M,
    ) where
        A: Clone + Debug,
        B: Clone + Debug,
        M: Fn(&mut A, &B, bool);

    fn combine3<A, B, C, M>(a: [&Self::Mles<A>; 2], b: &Self::Mles<B>, f: M) -> Self::Mles<C>
    where
        A: Clone + Debug,
        B: Clone + Debug,
        C: Clone + Debug,
        M: Fn(&A, &A, &B) -> C;
}

pub type Mles<E, V> = <E as Evals>::Mles<V>;

pub trait EvalsCore<V: Clone + Debug>: Sized + Clone + Debug {
    /// should combine 2 [Self] into one by using `f` to combine each element
    fn combine<C: Fn(&V, &V) -> V>(&self, other: &Self, f: C) -> Self;
    /// Flatten all elements into a vec, each element should be pushed into the vec.
    fn flatten(self, vec: &mut Vec<V>);
    /// Unflatten Self from elems, can be assumed to be the output of flatten.
    fn unflatten(elems: &mut IntoIter<V>) -> Self;
    fn flatten_vec(self) -> Vec<V> {
        let mut vec = vec![];
        self.flatten(&mut vec);
        vec
    }
    fn unflatten_vec(vec: Vec<V>) -> Self {
        let mut iter = vec.into_iter();
        Self::unflatten(&mut iter)
    }
}

pub trait EvalsExt<F: Field>: EvalsCore<F> {
    fn eval(mles: &[Self], point: &MultiPoint<F>) -> Self {
        use std::iter::Iterator;
        assert_eq!(
            mles.len().ilog2() as usize,
            point.vars(),
            "number of variables mismatch"
        );
        let eq: Vec<F> = eq(point);
        let dummy = mles[0].clone().flatten_vec();
        let dummy: Self = Self::unflatten_vec(vec![F::zero(); dummy.len()]);

        eq.into_iter().zip(mles).fold(dummy.clone(), |acc, x| {
            let acc: Self = acc;
            let (eq_eval, eval): (F, &Self) = x;
            acc.combine(eval, |a, b| *a + *b * eq_eval)
        })
    }
}

/// Evaluates the provided mle in the provided point, panics
/// if the number of variables don't match.
pub fn eval_simple_mle<F: Field>(mle: &[F], point: &MultiPoint<F>) -> F {
    assert_eq!(
        mle.len().ilog2() as usize,
        point.vars(),
        "number of variables mismatch"
    );
    let eq: Vec<F> = eq(point);
    eq.into_iter()
        .zip(mle)
        .fold(F::ZERO, |acc, (eq, e)| acc + eq * e)
}

impl<F: Field, E: EvalsCore<F>> EvalsExt<F> for E {}
