//! implementation of barycentric evaluation, to evaluate polynomials
//! represented as a set of evaluations without requiring interpolation.
//! O(d^2) once per domain precomputation
//! O(d) cost of evaluation at arbitrary point
//!
//! While any domain could be supported, right now only the inplicit domain
//! 0..d will be used

use ark_ff::{Field, fields::batch_inversion};

/// Weights that can be used to evaluate polynomials defined by
/// n evaluation points over the implicit 0..n domain
#[derive(Clone, Debug)]
pub(crate) struct BarycentricWeights<F: Field> {
    weights: Vec<F>,
    neg_domain: Vec<F>,
    ext_coeffs: Vec<F>,
}

impl<F: Field> BarycentricWeights<F> {
    /// computes the weights for the inplicit domain 0..n
    pub(crate) fn compute(degree: u32) -> Self {
        let domain: Vec<F> = (0..=degree).map(F::from).collect();
        let neg_domain: Vec<F> = domain.iter().cloned().map(|x| -x).collect();
        let degree = degree as usize;

        let mut weights = Vec::with_capacity(degree + 1);
        for (i, x) in domain[0..=degree].iter().enumerate() {
            let weight = neg_domain
                .iter()
                .enumerate()
                .map(|(j, neg_x)| if i == j { F::one() } else { *neg_x + x })
                .fold(F::one(), |acc, x| acc * x);
            weights.push(weight);
        }

        // Precompute extend coefficients at constant point = degree + 1.
        // This is safe because this point lies outside the domain and we
        // have the invariant that no term is zero.
        let ext_point = F::from(degree as u32 + 1);
        let vanishing_factors: Vec<F> = neg_domain.iter().map(|neg_x| *neg_x + ext_point).collect();
        let vanishing_eval = vanishing_factors.iter().fold(F::one(), |acc, t| acc * t);
        let mut ext_coeffs: Vec<F> = vanishing_factors
            .iter()
            .zip(&weights)
            .map(|(f, w)| *f * w)
            .collect();
        batch_inversion(&mut ext_coeffs);
        for c in ext_coeffs.iter_mut() {
            *c *= vanishing_eval;
        }

        Self {
            weights,
            neg_domain,
            ext_coeffs,
        }
    }

    pub(crate) fn evaluate(&self, evals: &[F], point: F) -> F {
        assert_eq!(self.weights.len(), evals.len());
        let terms: Vec<F> = self.neg_domain.iter().map(|neg_x| *neg_x + point).collect();
        // for the cases where the evaluation point is part of the domain
        for (i, term) in terms.iter().enumerate() {
            if term.is_zero() {
                return evals[i];
            }
        }
        let m = terms.iter().fold(F::one(), |acc, t| acc * t);
        let mut denominators = terms;
        for (d, w) in denominators.iter_mut().zip(&self.weights) {
            *d *= w;
        }
        batch_inversion(&mut denominators);
        let eval = denominators
            .into_iter()
            .zip(evals.iter())
            .fold(F::zero(), |acc, (d, e)| acc + d * e);
        m * eval
    }

    /// Number of evaluation points in the domain, degree + 1.
    pub fn domain_size(&self) -> usize {
        self.weights.len()
    }

    /// Returns evaluation for x = evals.len().
    pub fn extend(&self, evals: &[F]) -> F {
        assert_eq!(self.ext_coeffs.len(), evals.len());
        // Shortcut by evaluating p(x) = sum_i ext_coeffs[i] * evals[i] with
        // precomputed coefficients, thus avoiding batch_inversions in evaluate()
        self.ext_coeffs
            .iter()
            .zip(evals)
            .fold(F::zero(), |acc, (c, e)| acc + *c * e)
    }
}

#[cfg(test)]
mod tests {
    use super::BarycentricWeights;
    use ark_ff::Field;
    use ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
    use ark_vesta::Fr;
    use rand::{Rng, thread_rng};

    #[test]
    fn test_barycentric_eval() {
        let evals = 16;
        let degree = evals - 1;
        let weights = BarycentricWeights::<Fr>::compute(degree);

        let mut rng = thread_rng();
        for _ in 0..16 {
            let poly = DensePolynomial::<Fr>::rand(degree as usize, &mut rng);
            let bytes: [u8; 30] = rng.r#gen();
            let point = Fr::from_random_bytes(&bytes).unwrap();
            let true_eval = poly.evaluate(&point);

            let evals: Vec<Fr> = (0..evals).map(|i| poly.evaluate(&Fr::from(i))).collect();
            let check_eval = weights.evaluate(&evals, point);
            assert_eq!(true_eval, check_eval);
            let eval1 = evals[1];
            let check_eval = weights.evaluate(&evals, Fr::from(1));
            assert_eq!(eval1, check_eval);
        }
    }
}
