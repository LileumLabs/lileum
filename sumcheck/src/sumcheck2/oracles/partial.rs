use crate::{
    polynomials::MultiPoint,
    sumcheck2::oracles::{
        composite::{CompositeOracleInstance, Either},
        EvalLocation, SumcheckFunction,
    },
};
use ark_ff::Field;
use std::{any::Any, fmt::Debug, marker::PhantomData, rc::Rc};
use transcript::reduction2::{Message, Relation};

#[derive(Clone, Debug)]
pub struct PartialQueryInstance<F, SF, O>
where
    F: Field,
    SF: SumcheckFunction<F>,
{
    evals: SF::Mles<Option<F>>,
    oracle_instance: O,
    point: MultiPoint<F>,
}

impl<F, SF, O> PartialQueryInstance<F, SF, O>
where
    F: Field,
    SF: SumcheckFunction<F>,
{
    pub fn new(evals: SF::Mles<Option<F>>, oracle_instance: O, point: &MultiPoint<F>) -> Self {
        Self {
            evals,
            oracle_instance,
            point: point.clone(),
        }
    }

    pub fn evals(&self) -> &SF::Mles<Option<F>> {
        &self.evals
    }

    pub fn oracle_instance(&self) -> &O {
        &self.oracle_instance
    }

    pub fn point(&self) -> &MultiPoint<F> {
        &self.point
    }
}

#[derive(Clone, Copy, Debug)]
pub struct OracleParams {
    pub vars: usize,
}

#[derive(Clone, Copy, Debug)]
pub enum OracleEval<F> {
    Computed(F),
    ProverProvided,
    None,
}

/// Dynamically typed nature which can be downcasted into any nature.
pub struct DynamicNature(Box<dyn Any>);

impl DynamicNature {
    pub fn into<T: Any>(self) -> Option<T> {
        self.0.downcast::<T>().ok().map(|boxed| *boxed)
    }
}

pub trait Nature: Copy + Debug + Into<EvalLocation> + 'static {
    /// Do not implement, the default implementation is correct
    /// for any type.
    fn into_dynamic(self) -> DynamicNature {
        DynamicNature(Box::new(self))
    }

    /// Wheter the MLE for the given nature has its evaluation provided
    /// by the prover instead of being computed by the verifier.
    fn prover_provided(self) -> bool {
        false
    }
}

impl<A: Nature, B: Nature> Nature for Either<A, B> {
    fn into_dynamic(self) -> DynamicNature {
        // Either branches towards the leaves, while any other
        // type returns self.
        match self {
            Either::Left(x) => x.into_dynamic(),
            Either::Right(x) => x.into_dynamic(),
        }
    }

    fn prover_provided(self) -> bool {
        match self {
            Either::Left(x) => x.prover_provided(),
            Either::Right(x) => x.prover_provided(),
        }
    }
}

pub trait PartialOracle<F, SF>: 'static + Clone + Debug
where
    F: Field,
    SF: SumcheckFunction<F>,
    <Self::Instance as Message<F>>::Error: Clone,
{
    type Instance: Message<F, Params = OracleParams> + Clone;
    type VerifierKey: From<Self> + Clone;
    type Builder: Debug;

    type Nature: Into<EvalLocation> + Copy + Debug + Nature;

    type QueryRelation: Relation<
        Structure = Self,
        Instance = PartialQueryInstance<F, SF, Self::Instance>,
        Witness = Vec<SF::Mles<F>>,
    >;

    fn build(builder: Self::Builder, data: &SF::Data, structure: Rc<Vec<SF::Mles<F>>>) -> Self;

    fn instance_evals(instance: &Self::Instance) -> SF::Mles<F>;
    fn evals(
        key: &Self::VerifierKey,
        instance: &Self::Instance,
        point: &MultiPoint<F>,
    ) -> SF::Mles<OracleEval<F>>;
}

impl<F, SF, P1, P2> PartialQueryInstance<F, SF, CompositeOracleInstance<F, SF, P1, P2>>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    /// Splits a PartialQueryInstance over a composite oracle into 2 instances over the
    /// suboracles.
    pub(crate) fn split(
        self,
        natures: &SF::Mles<Either<(), ()>>,
    ) -> <PartialQueryRelation<F, SF, P1, P2> as Relation>::Instance {
        let left = SF::combine(&self.evals, natures, |eval, nature| match nature {
            Either::Left(()) => *eval,
            Either::Right(()) => None,
        });
        let right = SF::combine(&self.evals, natures, |eval, nature| match nature {
            Either::Left(()) => None,
            Either::Right(()) => *eval,
        });

        let CompositeOracleInstance {
            oracle1_instance,
            oracle2_instance,
        } = self.oracle_instance;

        let left = PartialQueryInstance {
            evals: left,
            oracle_instance: oracle1_instance,
            point: self.point.clone(),
        };
        let right = PartialQueryInstance {
            evals: right,
            oracle_instance: oracle2_instance,
            point: self.point,
        };

        (left, right)
    }
}

pub struct PartialQueryRelation<F, SF, P1, P2>(PhantomData<(F, SF, P1, P2)>);

impl<F, SF, P1, P2> Relation for PartialQueryRelation<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    type Structure = (P1, P2);

    type Instance = (
        PartialQueryInstance<F, SF, P1::Instance>,
        PartialQueryInstance<F, SF, P2::Instance>,
    );

    type Witness = Vec<SF::Mles<F>>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let check1 = P1::QueryRelation::check(&structure.0, &instance.0, witness);
        let check2 = P2::QueryRelation::check(&structure.1, &instance.1, witness);
        check1 && check2
    }
}

/// Merges the 3 evals on one according to the provided
/// location.
pub fn merge<F: Field, SF: SumcheckFunction<F>>(
    structure: &SF::Mles<F>,
    instance: &SF::Mles<F>,
    witness: &SF::Mles<F>,
    locations: &SF::Mles<EvalLocation>,
) -> SF::Mles<F> {
    use EvalLocation::*;

    let evals: SF::Mles<F> = SF::combine3(
        [structure, instance],
        locations,
        |s: &F, i, l: &EvalLocation| match l {
            Structure => *s,
            Instance => *i,
            Witness => F::ZERO,
        },
    );

    SF::combine3(
        [&evals, witness],
        locations,
        |e: &F, w, l: &EvalLocation| match l {
            Structure | Instance => *e,
            Witness => *w,
        },
    )
}
