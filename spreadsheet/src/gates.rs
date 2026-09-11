use ark_ff::Field;
use sumcheck::Var;

pub trait BinaryGate<F: Field> {
    fn compute(a: F, b: F) -> F;
    fn check<V: Var<F>>(a: &V, b: &V, c: &V) -> V;
}

pub struct Add;
pub struct Eq;

impl<F: Field> BinaryGate<F> for Add {
    fn compute(a: F, b: F) -> F {
        a + b
    }

    fn check<V: Var<F>>(a: &V, b: &V, c: &V) -> V {
        a.clone() + b - c
    }
}

impl<F: Field> BinaryGate<F> for Eq {
    fn compute(_: F, _: F) -> F {
        F::ZERO
    }

    fn check<V: Var<F>>(a: &V, b: &V, _: &V) -> V {
        a.clone() - b
    }
}
