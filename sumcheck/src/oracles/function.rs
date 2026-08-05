use crate::{evals::Evals, oracles::partial::Nature, Var};
use ark_ff::Field;
use std::fmt::Debug;

/// The definition of a multivariate polynomial as some function
/// of multilinear polynomials.
pub trait SumcheckFunction<F: Field>: Evals {
    type Natures: Copy + Debug + Nature;
    type Data: Clone + Debug;

    fn natures() -> Self::Mles<Self::Natures>;

    fn function<V: Var<F> + Debug>(data: &Self::Data, evals: &Self::Mles<V>) -> V;

    /// Given 2 evals `[p(0), p(1)]`, computes Self::function(p) writting
    /// the resut to `res`.
    /// The number of evals of the resulting univariate polynomial is
    /// given by `res.len()`.
    fn eval_into(data: &Self::Data, res: &mut [F], evals: [&Self::Mles<F>; 2]) {
        let [left, right] = evals;
        // The last evaluations, and what is needed to compute the next.
        let mut e = Self::combine::<F, F, _, _>(left, right, |e0, e1| {
            let coeff = *e1 - e0;
            let last_eval = e0;
            (*last_eval, coeff)
        });

        for m in res.iter_mut() {
            let evals = Self::map_evals(&e, |(eval, _)| *eval);
            let eval: F = Self::function(data, &evals);

            *m = eval;
            Self::apply(&mut e, |(last, coeff)| {
                *last += coeff;
            });
        }
    }

    /// Same as [Self::eval_into], but adds to `res` instead.
    fn eval_add(data: &Self::Data, res: &mut [F], evals: [&Self::Mles<F>; 2]) {
        let [left, right] = evals;
        // The last evaluations, and what is needed to compute the next.
        let mut e = Self::combine::<F, F, _, _>(left, right, |e0, e1| {
            let coeff = *e1 - e0;
            let last_eval = e0;
            (*last_eval, coeff)
        });

        for m in res.iter_mut() {
            let evals = Self::map_evals(&e, |(eval, _)| *eval);
            let eval: F = Self::function(data, &evals);

            *m += eval;
            Self::apply(&mut e, |(last, coeff)| {
                *last += coeff;
            });
        }
    }
}
