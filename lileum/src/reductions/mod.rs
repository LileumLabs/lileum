pub(crate) mod flcs;
pub(crate) mod lcs;
pub(crate) mod matrix_product;
#[cfg(test)]
mod tests;

pub use flcs::{FlcsArgument, FlcsFoldingScheme, FlcsReduction};
pub use lcs::{ClcsArgument, ToFlcs};

// NOTE: Papers:
// Hypernova:   https://eprint.iacr.org/2023/573.pdf
// NeutronNova: https://eprint.iacr.org/2024/1606.pdf
// CCS:         https://eprint.iacr.org/2023/552.pdf
//
// The main reductions here are a sumcheck and spark based argument
// for LCS and a folding scheme for LCS, which was originally going to be based
// on Hypernova, but it is now closer to NeutronNova, as it uses sumfold.
// LCS is our variant of CCS, which was the originally the constraint system
// being used, but evolved during the development to the point it can't really
// be called CCS anymore.
// The remain equivalent in power, both allowing arbitrary degree constraints
// and deduplicated copy constraints. But LCS prioritizes performance and
// implementation simplicity over compatibility with other constraint systems.
// Most LCS circuits can likely be translated into CCS circuits, but only a subset
// of CCS can be translated into LCS.
