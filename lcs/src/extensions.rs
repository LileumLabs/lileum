use ark_ff::Field;
use ark_serialize::CanonicalSerialize;

use crate::{circuit::Var, structure::WitnessIndex};
use core::fmt::Debug;

pub trait LcsExtension<F: Field>: Debug + Default {
    type Constraint;
    type StructureBuilder: Default;
    type WitnessBuilder: Default;

    type Structure: Clone;
    type Witness;

    fn process_structure(builder: Self::StructureBuilder) -> Self::Structure;
    fn process_witness(builder: Self::WitnessBuilder) -> Self::Witness;

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
        witness: &mut Self::WitnessBuilder,
        vars: [F; N],
        constraint: Self::Constraint,
    );
}

#[derive(Clone, Copy, Debug)]
pub enum Never {}

impl CanonicalSerialize for Never {
    fn serialize_with_mode<W: ark_serialize::Write>(
        &self,
        _: W,
        _: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        match *self {}
    }

    fn serialized_size(&self, _: ark_serialize::Compress) -> usize {
        match *self {}
    }
}

impl<F: Field> LcsExtension<F> for () {
    type Constraint = Never;
    type StructureBuilder = ();
    type Structure = ();
    type Witness = ();
    type WitnessBuilder = ();

    fn process_structure(_: ()) -> Self::Structure {}

    fn process_witness(_: ()) -> Self::Witness {}

    fn record_constraint<const N: usize>(_: &mut (), _: [Var<WitnessIndex>; N], _: Never) {}

    fn compute_constraint<const N: usize>(_: &mut (), _: [F; N], _: Never) {}
}
