mod argument;
mod reduction;
mod sumcheck;

pub use argument::FlcsArgument;
pub use reduction::FlcsReduction;
pub use sumcheck::{compute_sumcheck_witness, FlcsEvals};
