use ark_ff::Field;

use crate::{circuit::Var, structure::WitnessIndex};
use core::fmt::Debug;

pub trait LcsExtension<F: Field>: Debug + Default {
    type Constraint;
    type StructureBuilder: Default;
    type Witness: Default;

    /// Records the application of a constraint during structure
    /// generation.
    fn record_constraint<const N: usize>(
        builder: &mut Self::StructureBuilder,
        vars: [Var<WitnessIndex>; N],
        constraint: Self::Constraint,
    );

    /// Extends the extension's witness with the given
    /// constriant.
    fn compute_constraint<const N: usize>(
        witness: &mut Self::Witness,
        vars: [F; N],
        constraint: Self::Constraint,
    );
}

pub enum Never {}

impl<F: Field> LcsExtension<F> for () {
    type Constraint = Never;
    type StructureBuilder = ();
    type Witness = ();

    fn record_constraint<const N: usize>(_: &mut (), _: [Var<WitnessIndex>; N], _: Never) {}

    fn compute_constraint<const N: usize>(_: &mut (), _: [F; N], _: Never) {}
}
