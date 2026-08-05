use crate::sumcheck2::{
    evals::{Evals, EvalsCore},
    oracles::{partial::Nature, EvalLocation, SumcheckFunction},
    Var,
};
use ark_ff::Field;
use std::fmt::Debug;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
pub struct ZeroCheckEvals<V, I> {
    pub(crate) zerocheck: V,
    pub(crate) inner: I,
}

impl<V, I> EvalsCore<V> for ZeroCheckEvals<V, I>
where
    V: Clone + Debug,
    I: EvalsCore<V>,
{
    fn combine<C: Fn(&V, &V) -> V>(&self, other: &Self, f: C) -> Self {
        let zerocheck = f(&self.zerocheck, &other.zerocheck);
        let inner = self.inner.combine(&other.inner, f);
        Self { zerocheck, inner }
    }

    fn flatten(self, vec: &mut Vec<V>) {
        let Self { zerocheck, inner } = self;
        vec.push(zerocheck);
        inner.flatten(vec);
    }

    fn unflatten(elems: &mut std::vec::IntoIter<V>) -> Self {
        let zerocheck = elems.next().unwrap();
        let inner = I::unflatten(elems);
        Self { zerocheck, inner }
    }
}

impl<I> Evals for ZeroCheckEvals<(), I>
where
    I: Evals + 'static,
{
    type Mles<V: Clone + Debug> = ZeroCheckEvals<V, I::Mles<V>>;

    fn map_evals<A, B, M>(evals: &Self::Mles<A>, f: M) -> Self::Mles<B>
    where
        A: Clone + Debug,
        B: Clone + Debug,
        M: Fn(&A) -> B,
    {
        let ZeroCheckEvals { zerocheck, inner } = evals;
        let zerocheck = f(zerocheck);
        let inner = I::map_evals(inner, f);
        ZeroCheckEvals { zerocheck, inner }
    }

    fn combine<A, B, C, M>(a: &Self::Mles<A>, b: &Self::Mles<B>, f: M) -> Self::Mles<C>
    where
        A: Clone + Debug,
        B: Clone + Debug,
        C: Clone + Debug,
        M: Fn(&A, &B) -> C,
    {
        let zerocheck = f(&a.zerocheck, &b.zerocheck);
        let inner = I::combine(&a.inner, &b.inner, f);
        ZeroCheckEvals { zerocheck, inner }
    }

    fn apply<A, M>(a: &mut Self::Mles<A>, f: M)
    where
        A: Clone + Debug,
        M: Fn(&mut A),
    {
        let ZeroCheckEvals { zerocheck, inner } = a;
        f(zerocheck);
        I::apply(inner, f);
    }

    fn combine_mut_conditional<A, B, M>(
        a: &mut Self::Mles<A>,
        b: &Self::Mles<B>,
        c: Self::Mles<bool>,
        f: M,
    ) where
        A: Clone + Debug,
        B: Clone + Debug,
        M: Fn(&mut A, &B, bool),
    {
        f(&mut a.zerocheck, &b.zerocheck, c.zerocheck);
        I::combine_mut_conditional(&mut a.inner, &b.inner, c.inner, f);
    }

    fn combine3<A, B, C, M>(a: [&Self::Mles<A>; 2], b: &Self::Mles<B>, f: M) -> Self::Mles<C>
    where
        A: Clone + Debug,
        B: Clone + Debug,
        C: Clone + Debug,
        M: Fn(&A, &A, &B) -> C,
    {
        let zerocheck = f(&a[0].zerocheck, &a[1].zerocheck, &b.zerocheck);
        let inner = [&a[0].inner, &a[1].inner];
        let inner = I::combine3(inner, &b.inner, f);
        ZeroCheckEvals { zerocheck, inner }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ZerocheckNature<I> {
    Zerocheck,
    Inner(I),
}

impl<I: Clone + Copy + Debug + Into<EvalLocation> + 'static> Nature for ZerocheckNature<I> {}

impl<I: Into<EvalLocation>> From<ZerocheckNature<I>> for EvalLocation {
    fn from(val: ZerocheckNature<I>) -> Self {
        match val {
            ZerocheckNature::Zerocheck => EvalLocation::Witness,
            ZerocheckNature::Inner(i) => i.into(),
        }
    }
}

impl<F, I> SumcheckFunction<F> for ZeroCheckEvals<(), I>
where
    F: Field,
    I: SumcheckFunction<F>,
{
    type Natures = ZerocheckNature<I::Natures>;
    type Data = I::Data;

    fn natures() -> Self::Mles<Self::Natures> {
        let inner = I::natures();
        let inner = I::map_evals(&inner, |nature| ZerocheckNature::Inner(*nature));
        let zerocheck = ZerocheckNature::Zerocheck;
        ZeroCheckEvals { zerocheck, inner }
    }

    fn function<V: Var<F> + Debug>(data: &Self::Data, evals: &Self::Mles<V>) -> V {
        let ZeroCheckEvals { zerocheck, inner } = evals;
        I::function(data, inner) * zerocheck
    }
}
