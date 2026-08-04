//! A linear sumcheck prover

mod barycentric_eval;
pub mod eq;
mod eval_check;
mod eval_impls;
pub mod folding;
mod message;
pub mod polynomials;
pub mod sumcheck;
pub mod sumcheck2;
// mod symbolic;
pub mod utils;
mod zerocheck;

#[derive(Debug, Clone)]
pub enum SumcheckError {
    /// Message has incorrect degree
    MessageDegree,
    /// The sum of both halves differ from the claimed sum
    RoundSum,
    // Transcript error
    TranscriptError(transcript::Error),
}
