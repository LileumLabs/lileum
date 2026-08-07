#[derive(Clone, Copy, Debug)]
pub struct GuardedProof<P>(P);

#[derive(Clone, Copy, Debug)]
pub struct MapError;

impl<P> GuardedProof<P> {
    pub fn map<P2, F: FnOnce(P) -> P2>(self, f: F) -> GuardedProof<P2> {
        GuardedProof(f(self.0))
    }

    /// Fallible alternative to [Self::map], reductions calling this method
    /// should return an error immediately upon receiving [Err(MapError)]
    /// in return.
    pub fn try_map<P2, F: FnOnce(P) -> Option<P2>>(
        self,
        f: F,
    ) -> Result<GuardedProof<P2>, MapError> {
        match f(self.0) {
            Some(x) => Ok(GuardedProof(x)),
            None => Err(MapError),
        }
    }

    pub(crate) fn inner(&self) -> &P {
        &self.0
    }

    pub(crate) fn new(proof: P) -> Self {
        GuardedProof(proof)
    }
}

impl GuardedProof<()> {
    /// Creates an empty proof for protocols without prover
    /// messages.
    pub fn empty() -> Self {
        Self(())
    }
}

impl<A, B> GuardedProof<(A, B)> {
    pub(crate) fn split(self) -> (GuardedProof<A>, GuardedProof<B>) {
        let GuardedProof((a, b)) = self;
        (GuardedProof(a), GuardedProof(b))
    }
}
