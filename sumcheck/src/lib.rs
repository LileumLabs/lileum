//! A linear sumcheck prover

mod barycentric_eval;
pub mod eq;
mod eval_check;
mod message;
pub mod polynomials;
pub mod sumcheck2;
// Currently unused but may be used again in the future.
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
