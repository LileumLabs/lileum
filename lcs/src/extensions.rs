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

    // An additional instance-witness brought from outside the circuit.
    type ExternalInstance;
    type ExternalWitness;

    fn process_structure<R: Fn(Var<WitnessIndex>) -> usize>(
        builder: Self::StructureBuilder,
        var_reader: R,
    ) -> Self::Structure;
    fn process_witness(builder: Self::WitnessBuilder) -> Self::Witness;

    /// Records the application of a constraint during structure
    /// generation.
    fn record_constraint<const N: usize, R: Fn(Var<WitnessIndex>) -> usize>(
        builder: &mut Self::StructureBuilder,
        var_reader: R,
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

    /// More general version of compute_constraint which allows access
    /// to external instance and witness for extensions that make use of
    /// them.
    fn compute_constraint_ex<const N: usize>(
        witness: &mut Self::WitnessBuilder,
        vars: [F; N],
        constraint: Self::Constraint,
        external_instance: &Self::ExternalInstance,
        external_witness: &Self::ExternalWitness,
    ) {
        let _ = external_instance;
        let _ = external_witness;
        Self::compute_constraint(witness, vars, constraint);
    }
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
    type ExternalInstance = ();
    type ExternalWitness = ();
    type WitnessBuilder = ();

    fn process_structure<R>(_: (), _: R) -> Self::Structure {}

    fn process_witness(_: ()) -> Self::Witness {}

    fn record_constraint<const N: usize, R>(_: &mut (), _: R, _: [Var<WitnessIndex>; N], _: Never) {
    }

    fn compute_constraint<const N: usize>(_: &mut (), _: [F; N], _: Never) {}
}
