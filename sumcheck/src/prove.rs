use crate::{
    MultiPoint, SumcheckMessage, degree,
    evals::{Evals, Mles},
    oracles::{EvalLocation, Oracle, OracleData, SumcheckFunction},
};
use alloc::{rc::Rc, vec::Vec};
use ark_ff::Field;
use reduction::Transcript;
use sponge::sponge::Duplex;

pub struct ProverKey<F: Field, O: Oracle<F>> {
    degree: usize,
    vars: usize,
    structure_evals: Rc<Vec<Mles<O::Function, F>>>,
    data: <O::Function as SumcheckFunction<F>>::Data,
    structure_filter: Mles<O::Function, bool>,
    instance_filter: Mles<O::Function, bool>,
}

impl<F: Field, O: Oracle<F>> ProverKey<F, O> {
    pub(crate) fn new(oracle: &O) -> Self {
        let vars = oracle.vars();
        let degree = degree::sumcheck_degree(oracle);

        let structure_evals = oracle.structure();

        let data = oracle.data().clone();

        let natures = oracle.natures();

        let structure_filter = <O::Function as Evals>::map_evals(&natures, |nature: &O::Nature| {
            let location: EvalLocation = (*nature).into();
            matches!(location, EvalLocation::Structure)
        });

        let instance_filter = <O::Function as Evals>::map_evals(&natures, |nature: &O::Nature| {
            let location: EvalLocation = (*nature).into();
            matches!(location, EvalLocation::Instance)
        });

        Self {
            degree,
            vars,
            structure_evals,
            data,
            structure_filter,
            instance_filter,
        }
    }

    /// Merges evals from the structure, instance and witness.
    fn merge_evals(
        &self,
        witness: &mut Mles<O::Function, F>,
        structure: &Mles<O::Function, F>,
        instance: &Mles<O::Function, F>,
    ) {
        <O::Function as Evals>::combine_mut_conditional(
            witness,
            structure,
            self.structure_filter.clone(),
            |w: &mut F, s: &F, is_structure| {
                if is_structure {
                    *w = *s;
                }
            },
        );

        <O::Function as Evals>::combine_mut_conditional(
            witness,
            instance,
            self.instance_filter.clone(),
            |w: &mut F, i: &F, is_instance| {
                if is_instance {
                    *w = *i;
                }
            },
        );
    }

    pub(crate) fn prove<S: Duplex<F>>(
        &self,
        mut witness: Vec<Mles<O::Function, F>>,
        transcript: &mut Transcript<F, S>,
    ) -> (Vec<SumcheckMessage<F>>, MultiPoint<F>, F) {
        let mut vars = alloc::vec![];
        let mut messages = alloc::vec![];

        for _ in 0..self.vars {
            let message = self.message(&witness);
            let [r] = transcript.send_message(&message, &self.degree);

            self.bind_variable(&mut witness, r);
            vars.push(r);
            messages.push(message);
        }

        assert_eq!(witness.len(), 1);

        let eval: F = O::Function::function(&self.data, &witness[0]);

        vars.reverse();
        let point = MultiPoint::new(vars);

        (messages, point, eval)
    }

    /// Adds witness and structure evals to the witness.
    pub(crate) fn prepare_witness(
        &self,
        mut witness: Vec<Mles<O::Function, F>>,
        instance_evals: Mles<O::Function, F>,
    ) -> Vec<Mles<O::Function, F>> {
        for (witness, structure) in witness.iter_mut().zip(self.structure_evals.as_ref()) {
            self.merge_evals(witness, structure, &instance_evals);
        }
        witness
    }

    /// Computes the round's sumcheck message.
    fn message(&self, mles: &[Mles<O::Function, F>]) -> SumcheckMessage<F> {
        assert!(mles.len().is_power_of_two());

        let degree = self.degree;

        // All evals start as a bunch of degree 1 polynomials.
        // A degree 1 polynomial can be cheaply evluated over an arbitrary
        // domain with FFTs or anything.
        // If the domain is 0..=d then it is just an addition per evaluation.
        // Given eval at 0 e0 and eval at 1 e1, the polynomial looks like this:
        // e0 + e1x - e0x
        // or alternatively:
        // e0 + x(e1 - e0)
        // And the evaluations:
        // f(0) = e0
        // f(1) = e0 + (e1 - e0) = f(0) + (e1 - e0)
        // f(2) = e0 + (e1 - e0) + (e1 - e0) = f(1) + (e1 - e0)
        // f(3) = f(2) + (e1 - e0)
        //
        // As you can see, to compute f(x), we only need 2 elements,
        // e1 - e0 and the f(x-1).
        let (left, right) = mles.split_at(mles.len() / 2);

        let mut message = alloc::vec![F::zero(); degree + 1];
        for (left, right) in left.iter().zip(right) {
            Self::eval_acc(&self.data, &mut message, [left, right]);
        }

        SumcheckMessage(message)
    }

    pub(crate) fn eval_acc(
        data: &OracleData<F, O>,
        acc: &mut [F],
        evals: [&Mles<O::Function, F>; 2],
    ) {
        let [left, right] = evals;
        // The last evaluations, and what is needed to compute the next.
        let mut e = <O::Function as Evals>::combine::<F, F, _, _>(left, right, |e0, e1| {
            let coeff = *e1 - e0;
            let last_eval = e0;
            (*last_eval, coeff)
        });

        for m in acc.iter_mut() {
            let evals = <O::Function as Evals>::map_evals(&e, |(eval, _)| *eval);
            let eval: F = O::Function::function(data, &evals);

            *m += eval;
            <O::Function as Evals>::apply(&mut e, |(last, coeff)| {
                *last += coeff;
            });
        }
    }

    pub(crate) fn bind_variable(&self, mles: &mut Vec<Mles<O::Function, F>>, var: F) {
        assert!(mles.len().is_power_of_two());
        let len = mles.len();
        let (left, right) = mles.split_at_mut(len / 2);

        for (left, right) in left.iter_mut().zip(right) {
            *left = <O::Function as Evals>::combine::<F, F, F, _>(left, right, |e0, e1| {
                *e0 + var * (*e1 - e0)
            });
        }

        mles.truncate(len / 2);
    }

    pub(crate) fn degree(&self) -> usize {
        self.degree
    }

    pub(crate) fn vars(&self) -> usize {
        self.vars
    }

    pub(crate) fn data(&self) -> &OracleData<F, O> {
        &self.data
    }

    /// Increases the degree by 1, to be used by zerocheck
    /// which adds an extra multiplication at the end.
    pub(crate) fn increase_degree(mut self) -> Self {
        self.degree += 1;
        self
    }

    pub fn structure(&self) -> &[<<O as Oracle<F>>::Function as Evals>::Mles<F>] {
        &self.structure_evals
    }
}
