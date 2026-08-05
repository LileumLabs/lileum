use crate::{
    degree::Degree,
    evals::{Evals, Mles},
    oracles::{EvalLocation, Oracle},
};
use ark_ff::Field;

pub fn folding_degree<F: Field, O: Oracle<F>>(oracle: &O) -> usize {
    let natures: Mles<O::Function, O::Nature> = oracle.natures();

    let intitial_degrees = <O::Function as Evals>::map_evals(&natures, |nature: &O::Nature| {
        let location: EvalLocation = (*nature).into();
        // What matters ultimately, is if the multilinear polynomial is multilinear
        // in the variable being bound during a sumcheck round.
        // For sumfold, that comes down to comparing evaluations between the 2 polynomials
        // being folded, if the they are the same, degree is 0, otherwise 1.
        // Witness and instance evaluation are generally different, thus degree 1.
        // Structure is the same for both, and thus degree 0.
        match location {
            EvalLocation::Structure => Degree(0),
            EvalLocation::Instance => Degree(1),
            EvalLocation::Witness => Degree(1),
        }
    });

    let degree: Degree = oracle.call_function(&intitial_degrees);
    degree.0
}
