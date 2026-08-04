pub mod circuits;
pub mod lilium2;
pub mod simple_cs;
pub mod testing;

/*
#[derive(Debug, Clone)]
pub enum Error<F: Field, C: CommmitmentScheme<F>> {
    TranscriptError(transcript::Error),
    /// Committed spark error
    Spark(spark::committed_spark::Error<F, C>),
    Pcs(C::Error),
    Sumcheck(SumcheckError),
    /// Polynomial doesn't evaluate to the expected value at the point
    /// given by sumcheck
    EvalCheck,
    Batching(BatchingError<F, C>),
}

impl<F: Field, C: CommmitmentScheme<F>> From<transcript::Error> for Error<F, C> {
    fn from(value: transcript::Error) -> Self {
        Self::TranscriptError(value)
    }
}

impl<F: Field, C: CommmitmentScheme<F>> From<spark::committed_spark::Error<F, C>> for Error<F, C> {
    fn from(value: spark::committed_spark::Error<F, C>) -> Self {
        Self::Spark(value)
    }
}

impl<F: Field, C: CommmitmentScheme<F>> From<SumcheckError> for Error<F, C> {
    fn from(value: SumcheckError) -> Self {
        Self::Sumcheck(value)
    }
}

impl<F: Field, C: CommmitmentScheme<F>> From<BatchingError<F, C>> for Error<F, C> {
    fn from(value: BatchingError<F, C>) -> Self {
        Self::Batching(value)
    }
}
*/
