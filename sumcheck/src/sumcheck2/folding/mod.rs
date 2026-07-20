use crate::folding::utils::FieldFolder;

mod degree;
mod reduction;
mod zerofold;

pub(crate) use degree::folding_degree;
pub use reduction::SumFold;
pub use zerofold::{ZeroFold, ZeroFoldKey};

pub trait Foldable<F> {
    fn fold(folder: &FieldFolder<F>, a: Self, b: Self) -> Self;
}
