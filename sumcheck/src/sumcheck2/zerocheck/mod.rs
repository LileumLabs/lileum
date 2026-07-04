use crate::{sumcheck2::oracles::Oracle, zerocheck::CompactPowers};
use ark_ff::Field;

pub use reduction::{ZerocheckReduction, ZerocheckSumcheckReduction};
pub use relation::{ZeroSumcheck, Zerocheck};

//TODO: delete module
mod evals;
mod reduction;
mod relation;

#[derive(Clone, Debug)]
pub struct ZeroSumcheckInstance<F: Field, O: Oracle<F>> {
    /// Same sum as in sumcheck, with the particularity that it will be
    /// zero unless the instance is the result of folding.
    pub(crate) sum: F,
    pub(crate) zerocheck_powers: CompactPowers<F>,
    pub(crate) oracle_instance: O::Instance,
}

impl<F: Field, O: Oracle<F>> ZeroSumcheckInstance<F, O> {
    pub fn oracle_instance(&self) -> &O::Instance {
        &self.oracle_instance
    }
}
