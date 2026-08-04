//! An environment to check the function of evaluations in a point.
//! At the end of sumcheck G(x) has to be checked at a point r, as
//! G is merely a composition of several multilinear polynomials, we instead
//! evaluate each of those polynomials at r and then apply the function
//! to get the evaluation. For example:
//! G(r) = f_0(r) * f_1(r) + f_2(r)

use crate::sumcheck::Var;
use ark_ff::Field;

impl<F: Field> Var<F> for F {}
