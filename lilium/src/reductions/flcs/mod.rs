pub mod argument;
pub mod folding;
pub mod reduction;
mod sumcheck;

pub use argument::FlcsArgument;
pub use folding::FlcsFoldingScheme;
pub use reduction::FlcsReduction;
pub use sumcheck::{compute_sumcheck_witness, FlcsData, FlcsEvals};
