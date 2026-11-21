use ark_ff::Field;
use lcs::{circuit::Var, extensions::LcsExtension, structure::WitnessIndex};

/// An extension which allows to lookup values from an externally committed table.
#[derive(Clone, Debug, Default)]
pub struct Dataset;

impl<F: Field> LcsExtension<F> for Dataset {
    type Constraint = ();

    type StructureBuilder = ();

    type WitnessBuilder = ();

    type Structure = ();

    type Witness = ();

    type ExternalInstance = ();

    type ExternalWitness = ();

    fn process_structure<R: Fn(Var<WitnessIndex>) -> usize>(
        _builder: Self::StructureBuilder,
        _var_reader: R,
    ) -> Self::Structure {
        todo!()
    }

    fn process_witness(_builder: Self::WitnessBuilder) -> Self::Witness {
        todo!()
    }

    fn record_constraint<const N: usize, R: Fn(Var<WitnessIndex>) -> usize>(
        _builder: &mut Self::StructureBuilder,
        _var_reader: R,
        _vars: [Var<WitnessIndex>; N],
        _constraint: Self::Constraint,
    ) {
        todo!()
    }

    fn compute_constraint<const N: usize>(
        _witness: &mut Self::WitnessBuilder,
        _vars: [F; N],
        _constraint: Self::Constraint,
    ) {
        todo!()
    }
}
