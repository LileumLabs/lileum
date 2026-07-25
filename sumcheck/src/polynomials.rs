use crate::eq::eq;
use ark_ff::Field;
use std::vec::IntoIter;
use transcript::Message;

/// A point with `n` variables
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultiPoint<F: Field>(Vec<F>);

impl<F: Field> Message<F> for MultiPoint<F> {
    fn len(vars: usize, _param_resolver: &transcript::params::ParamResolver) -> usize {
        vars
    }

    fn to_field_elements(&self) -> Vec<F> {
        self.0.clone()
    }
}

impl<F: Field> From<Vec<F>> for MultiPoint<F> {
    fn from(value: Vec<F>) -> Self {
        Self(value)
    }
}

impl<F: Field> From<&[F]> for MultiPoint<F> {
    fn from(value: &[F]) -> Self {
        Self(value.to_vec())
    }
}

impl<F: Field> AsRef<[F]> for MultiPoint<F> {
    fn as_ref(&self) -> &[F] {
        &self.0
    }
}

impl<F: Field> MultiPoint<F> {
    pub fn new(vars: Vec<F>) -> Self {
        MultiPoint(vars)
    }
    pub fn new_from_index(mut index: usize, vars: usize) -> Self {
        let vars = (0..vars)
            .map(|_| {
                let var = if index & 0b1 == 1 { F::ONE } else { F::ZERO };
                index >>= 1;
                var
            })
            .collect();
        MultiPoint::new(vars)
    }
    pub(crate) fn pop(mut self) -> (Self, F) {
        let var = self.0.pop().unwrap();
        (self, var)
    }
    pub(crate) fn pop_mut(&mut self) -> F {
        self.0.pop().unwrap()
    }
    pub fn vars(&self) -> usize {
        self.0.len()
    }
    pub fn inner(self) -> Vec<F> {
        self.0
    }
    pub fn inner_ref(&self) -> &[F] {
        &self.0
    }
    /// eval self as eq poly with point
    pub fn eval_as_eq(&self, point: &Self) -> F {
        assert_eq!(self.0.len(), point.0.len());
        self.0
            .iter()
            .zip(point.0.iter())
            .fold(F::one(), |acc, (a, b)| {
                let var = *a * b + (F::one() - a) * (F::one() - b);
                acc * var
            })
    }
}

/// must be some wrapper over `F`, representing all the evaluations at some
/// point of the domain
pub trait Evals<V>: Sized + Clone {
    type Idx: Copy;
    fn index(&self, index: Self::Idx) -> &V;
    /// should combine 2 [Self] into one by using `f` to combine each element
    fn combine<C: Fn(V, V) -> V>(&self, other: &Self, f: C) -> Self;
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

pub trait EvalsExt<F: Field>: Evals<F> + Sized {
    fn fix_var(mut mle: Vec<Self>, var: F) -> Vec<Self> {
        let half_len = mle.len() / 2;
        let one_minus_var = F::one() - var;
        let (left, right) = mle.split_at_mut(half_len);

        let f = |a, b| one_minus_var * a + var * b;
        for (left, right) in left.iter_mut().zip(right) {
            let left: &mut Self = left;
            let comb = left.combine(right, f);
            *left = comb;
        }
        mle.truncate(half_len);
        mle
    }
    /// recursive n log n method of evaluation
    fn eval_slow(mle: Vec<Self>, point: MultiPoint<F>) -> Self {
        assert_eq!(
            mle.len().ilog2() as usize,
            point.vars(),
            "number of variables mismatch"
        );
        let (point, var) = point.pop();
        let mle = Self::fix_var(mle, var);
        if point.vars() == 0 {
            mle.into_iter().next().unwrap()
        } else {
            Self::eval_slow(mle, point)
        }
    }

    // TODO: 1 optimization to be done
    // 1) add method that allows to filter out mles for cases where only a
    // subset of the evaluations are needed.
    /// Fast iterative O(n) evaluation.
    fn eval(mles: &[Self], point: MultiPoint<F>) -> Self {
        use std::iter::Iterator;
        assert_eq!(
            mles.len().ilog2() as usize,
            point.vars(),
            "number of variables mismatch"
        );
        let eq: Vec<F> = eq(&point);
        let dummy = mles[0].clone().flatten_vec();
        let dummy: Self = Self::unflatten_vec(vec![F::zero(); dummy.len()]);

        eq.into_iter().zip(mles).fold(dummy.clone(), |acc, x| {
            let acc: Self = acc;
            let (eq_eval, eval): (F, &Self) = x;
            acc.combine(eval, |a, b| a + b * eq_eval)
        })
    }

    /// Evaluates MLE given by an iterator.
    /// Should have the same result as collecting the iterator and calling
    /// `EvalsExt::eval`.
    fn eval_iter<M>(mut mles: M, point: MultiPoint<F>) -> Self
    where
        M: Iterator<Item = Self>,
    {
        let mut eq = eq(&point).into_iter();

        let first: Self = mles.next().unwrap();
        let first_eq = eq.next().unwrap();
        let mut res = first.combine(&first, |e, _| e * first_eq);

        loop {
            match (mles.next(), eq.next()) {
                (None, None) => {
                    break;
                }
                (None, Some(_)) | (Some(_), None) => {
                    panic!("unexpected number of evaluations")
                }
                (Some(e), Some(eq_eval)) => {
                    res = res.combine(&e, |a, b| a + b * eq_eval);
                }
            }
        }
        todo!()
    }
}

impl<F, T> EvalsExt<F> for T
where
    T: Evals<F> + Sized,
    F: Field,
{
}

#[derive(Clone)]
pub struct SingleEval<F>(pub F);

impl<F> SingleEval<F> {
    pub fn from_vec(mle: Vec<F>) -> Vec<Self> {
        mle.into_iter().map(Self).collect()
    }
}

impl<V: Copy> Evals<V> for SingleEval<V> {
    type Idx = ();

    fn combine<C: Fn(V, V) -> V>(&self, other: &Self, f: C) -> Self {
        SingleEval(f(self.0, other.0))
    }

    fn index(&self, _index: Self::Idx) -> &V {
        &self.0
    }
    fn flatten(self, vec: &mut Vec<V>) {
        vec.push(self.0);
    }

    fn unflatten(elems: &mut IntoIter<V>) -> Self {
        Self(elems.next().unwrap())
    }
}
impl<F: Clone> SingleEval<F> {
    pub fn from_field_elements(evals: &[F]) -> Vec<Self> {
        evals.iter().cloned().map(SingleEval).collect()
    }
}

pub mod simple_eval {
    use super::Evals;
    use crate::utils::ZeroCheckAvailable;
    use std::fmt::Debug;

    #[derive(Clone, Copy, Debug)]
    pub struct SimpleEval<F, const N: usize>([F; N]);

    impl<F, const N: usize> SimpleEval<F, N> {
        pub const fn new(inner: [F; N]) -> Self {
            Self(inner)
        }

        pub fn map<V, M>(self, f: M) -> SimpleEval<V, N>
        where
            M: Fn(F) -> V,
        {
            SimpleEval(self.0.map(f))
        }

        pub fn inner(&self) -> &[F; N] {
            &self.0
        }
    }

    impl ZeroCheckAvailable for usize {
        /// This fixes the index to be 0
        fn zerocheck_eq() -> Self {
            0
        }
    }

    impl<V: Copy + Debug, const N: usize> Evals<V> for SimpleEval<V, N> {
        type Idx = usize;

        fn index(&self, index: Self::Idx) -> &V {
            &self.0[index]
        }

        fn combine<C: Fn(V, V) -> V>(&self, other: &Self, f: C) -> Self {
            let mut res = self.0;
            for (i, res) in res.iter_mut().enumerate() {
                *res = f(*res, other.0[i]);
            }
            Self(res)
        }

        fn flatten(self, vec: &mut Vec<V>) {
            for i in 0..N {
                vec.push(self.0[i]);
            }
        }

        fn unflatten(elems: &mut std::vec::IntoIter<V>) -> Self {
            let elems: Vec<V> = elems.take(N).collect();
            Self(elems.try_into().unwrap())
        }
    }
}
