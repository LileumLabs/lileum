use crate::sumcheck2::{
    evals::Mles,
    oracles::{partial::OracleParams, Oracle},
    relation::oracle_evals,
    zerocheck::ZeroSumcheckInstance,
};
use ark_ff::Field;
use std::marker::PhantomData;
use transcript::reduction2::{Message, Relation};

/// The sumcheck relation over a given oracle.
#[derive(Clone, Copy, Debug)]
pub struct Zerocheck<F, O>(PhantomData<(F, O)>);

impl<F: Field, O: Oracle<F>> Relation for Zerocheck<F, O> {
    type Structure = O;

    type Instance = O::Instance;

    type Witness = Vec<Mles<O::Function, F>>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        oracle_evals(structure, instance, witness)
            .iter()
            .all(F::is_zero)
    }
}

/// A special case of sumcheck for zerocheck to be reduced into.
#[derive(Clone, Copy, Debug)]
pub struct ZeroSumcheck<F, O>(PhantomData<(F, O)>);

#[derive(Clone, Copy, Debug)]
pub enum ZerocheckError<I> {
    Zerocheck,
    Inner(I),
}

impl<I> From<I> for ZerocheckError<I> {
    fn from(value: I) -> Self {
        Self::Inner(value)
    }
}

impl<F: Field, O: Oracle<F>> Message<F> for ZeroSumcheckInstance<F, O> {
    type Params = (OracleParams, <O::Instance as Message<F>>::Params);

    type Error = ZerocheckError<<O::Instance as Message<F>>::Error>;

    fn len(params: &Self::Params) -> usize {
        2 * params.0.vars + O::Instance::len(&params.1)
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        if self.zerocheck_powers.factors().len() != params.0.vars {
            return Err(ZerocheckError::Zerocheck);
        }
        let mut elems: Vec<F> = self
            .zerocheck_powers
            .factors()
            .iter()
            .flat_map(|x| [x.0, x.1])
            .collect();
        elems.append(&mut self.oracle_instance.to_field_elements(&params.1)?);
        Ok(elems)
    }
}

impl<F: Field, O: Oracle<F>> Relation for ZeroSumcheck<F, O> {
    type Structure = O;

    type Instance = ZeroSumcheckInstance<F, O>;

    type Witness = Vec<Mles<O::Function, F>>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let powers = instance.zerocheck_powers.eval_over_domain();
        oracle_evals(structure, &instance.oracle_instance, witness)
            .into_iter()
            .zip(powers)
            .fold(F::ZERO, |acc, (eval, power)| acc + eval * power)
            .is_zero()
    }
}
