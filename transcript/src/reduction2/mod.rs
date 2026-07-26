pub mod composition;
pub mod message;
mod proof;
mod prover;
mod reduction;
mod relations;
mod transcript;
mod transcript_builder;
mod verifier;

#[derive(Debug, Clone, Copy)]
pub enum NoError {}

#[derive(Debug, Clone)]
pub enum Error {
    SpongeError(sponge::error::Error),
    /// Attempt to send a message when no more messages were expected
    TranscriptFinished,
    /// Unexpected message or number of challenges generated.
    UnexpectedMessage,
    /// The transcript was finished when more messsages were still expected.
    UnexpectedFinish,
}

pub use message::Message;
pub use proof::GuardedProof;
pub use prover::Prover;
pub use reduction::{Argument, FoldingScheme, ProverOutput, Reduction};
pub use relations::{FoldingRelation, Relation};
pub use transcript::{Guard, Transcript, VerifierTranscript};
pub use transcript_builder::TranscriptBuilder;
pub use verifier::{UnsafeVerifier, Verifier};
