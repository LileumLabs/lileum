pub(crate) mod flcs;
pub(crate) mod lcs;
pub(crate) mod matrix_product;

pub use flcs::{FlcsArgument, FlcsReduction};
pub use lcs::{LcsArgument, ToFlcs};
