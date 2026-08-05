use crate::{
    polynomials::MultiPoint,
    sumcheck2::{evals::Mles, Var},
};
use ark_ff::Field;
use std::{fmt::Debug, marker::PhantomData, rc::Rc};
use transcript::reduction2::{Message, Relation};

pub mod composite;
pub mod core;
pub mod empty;
mod function;
pub mod partial;
pub mod small;
pub mod testing;

pub use function::SumcheckFunction;

#[derive(Clone, Debug, PartialEq, Eq)]
/// An instance in the QueryRelation, made up of an instance of
/// the oracle, an evaluation point, and an evaluation.
pub struct OracleQueryInstance<F: Field, O> {
    pub oracle_instance: O,
    pub point: MultiPoint<F>,
    pub eval: F,
}

#[derive(Clone, Copy, Debug)]
/// Unexpected number of variables
pub struct UnexpectedVars;

impl<F: Field> Message<F> for MultiPoint<F> {
    type Params = usize;

    type Error = UnexpectedVars;

    fn len(params: &Self::Params) -> usize {
        *params
    }

    fn to_field_elements(&self, params: &usize) -> Result<Vec<F>, Self::Error> {
        if self.vars() == *params {
            Ok(self.clone().inner())
        } else {
            Err(UnexpectedVars)
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum QueryInstanceError<F: Field, O: Message<F>> {
    Point(UnexpectedVars),
    Oracle(O::Error),
}

impl<F, O> Message<F> for OracleQueryInstance<F, O>
where
    F: Field,
    O: Message<F>,
{
    type Params = (O::Params, usize);

    type Error = QueryInstanceError<F, O>;

    fn len(params: &Self::Params) -> usize {
        O::len(&params.0) + MultiPoint::<F>::len(&params.1) + 1
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        let mut elems = self
            .oracle_instance
            .to_field_elements(&params.0)
            .map_err(QueryInstanceError::Oracle)?;
        let point = match self.point.to_field_elements(&params.1) {
            Ok(point) => point,
            Err(err) => return Err(QueryInstanceError::Point(err)),
        };
        elems.extend(point);
        elems.push(self.eval);
        Ok(elems)
    }
}

/// The oracle query relation.
/// To be in the relation means that evaluating the given oracle
/// on the given point, results in the given evaluation.
#[derive(Clone, Copy, Debug)]
pub struct QueryRelation<F, O>(PhantomData<(F, O)>);

impl<F: Field, O: Oracle<F>> Relation for QueryRelation<F, O> {
    type Structure = O;

    type Instance = OracleQueryInstance<F, O::Instance>;

    type Witness = O::Witness;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let OracleQueryInstance {
            oracle_instance,
            point,
            eval,
        } = instance;
        assert_eq!(point.vars(), structure.vars());
        let evals = structure.eval(point, oracle_instance, witness);
        *eval == O::Function::function(structure.data(), &evals)
    }
}

#[derive(Clone, Copy, Debug)]
/// The location where the given multilinear polynomial is.
/// It may be part of the structure, it may be part of the witness,
/// or it may be part of the instance.
/// The instance tends to be for degree 0 polynomials, like challenges.
pub enum EvalLocation {
    Structure,
    Instance,
    Witness,
}

pub trait Oracle<F: Field>: 'static + Clone + Debug
where
    <Self::Instance as Message<F>>::Error: Clone,
{
    type Function: SumcheckFunction<F>;
    type Instance: Message<F> + Clone;
    type Witness;

    /// Each multilinear polynomial that goes into creating the multivariate
    /// polynomial used in sumcheck has some nature.
    /// Some may be part of the structure, some multilinear, some constant,
    /// some may have a small representation, others may be under a commitment.
    /// Each oracle may have its own supported natures, the only thing they all
    /// need to do is let sumcheck the location of each.
    type Nature: Into<EvalLocation> + Copy + Debug;

    // many of these things would be better in the key than in the oracle.
    fn instance_evals(instance: &Self::Instance) -> Mles<Self::Function, F>;
    fn structure(&self) -> Rc<Vec<Mles<Self::Function, F>>>;
    fn data(&self) -> &<Self::Function as SumcheckFunction<F>>::Data;
    fn vars(&self) -> usize;
    fn oracle_params(&self) -> <Self::Instance as Message<F>>::Params;
    fn eval(
        &self,
        point: &MultiPoint<F>,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> Mles<Self::Function, F>;
    fn witness_from_evals(evals: Vec<Mles<Self::Function, F>>) -> Self::Witness;
    fn natures(&self) -> Mles<Self::Function, Self::Nature>;
    fn call_function<V: Var<F> + Debug>(&self, evals: &Mles<Self::Function, V>) -> V {
        let data = self.data();
        Self::Function::function(data, evals)
    }
}

pub type OracleData<F, O> = <<O as Oracle<F>>::Function as SumcheckFunction<F>>::Data;
