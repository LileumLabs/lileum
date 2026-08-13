use crate::SumcheckMessage;
use crate::barycentric_eval::BarycentricWeights;
use ark_ff::Field;
use std::ops::Mul;

impl<F: Field> SumcheckMessage<F> {
    pub fn zero(degree: usize) -> Self {
        Self(vec![F::ZERO; degree + 1])
    }

    pub(crate) fn new_degree_n(eval_at_0: F, eval_at_1: F, degree: usize) -> Self {
        assert!(degree >= 1, "degree should be >= 1");
        // e0, e1
        // P(x) = (e1 - e0)x + e0
        // TODO: it may be possible to exploit this structure further
        let mut message = Vec::with_capacity(degree + 1);
        let diff = eval_at_1 - eval_at_0;
        let mut last = F::zero();
        //as x is 0..d multiplication is unnecessary
        for _ in 0..=degree {
            message.push(last + eval_at_0);
            last += diff;
        }
        Self(message)
    }

    /// Adds an extra evaluation to handle a bigger degree.
    pub(crate) fn extend(self, weights: &BarycentricWeights<F>) -> Self {
        assert_eq!(self.0.len(), weights.domain_size());
        // The message length equals the weights length, so the next point is the constant
        // out-of-domain point that weights.extend(...) has already been precomputed for
        let message_extra_eval = weights.extend(&self.0);
        let evals = self.0.into_iter().chain([message_extra_eval]);
        Self(evals.collect())
    }

    pub(crate) fn inner(&self) -> &[F] {
        &self.0
    }

    pub(crate) fn new(evals: Vec<F>) -> Self {
        Self(evals)
    }

    pub fn eval_at_0(&self) -> F {
        self.0[0]
    }
    pub fn eval_at_1(&self) -> F {
        self.0[1]
    }
    pub(crate) fn eval_at_x(&self, x: F, weights: &BarycentricWeights<F>) -> F {
        weights.evaluate(&self.0, x)
    }
}

impl<F: Field> Mul for SumcheckMessage<F> {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.0.len(), rhs.0.len());
        for ab in self.0.iter_mut().zip(rhs.0.iter()) {
            let (a, b): (&mut F, &F) = ab;
            *a *= b;
        }
        self
    }
}
