pub(crate) mod flcs;
pub(crate) mod lcs;
pub(crate) mod matrix_product;

pub use flcs::{FlcsArgument, FlcsFoldingScheme, FlcsReduction};
pub use lcs::{LcsArgument, ToFlcs};
