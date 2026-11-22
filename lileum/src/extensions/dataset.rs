use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use ark_ff::Field;
use commit::CommitmentScheme;
use core::marker::PhantomData;
use lcs::{circuit::Var, extensions::LcsExtension, structure::WitnessIndex};

/// An extension which allows to lookup values from an externally committed table.
#[derive(Clone, Debug)]
pub struct Dataset<F, C>(PhantomData<(F, C)>);

impl<F, C> Default for Dataset<F, C> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<F: Field, C: CommitmentScheme<F>> LcsExtension<F> for Dataset<F, C> {
    type Constraint = usize;

    type StructureBuilder = BTreeMap<usize, usize>;

    type WitnessBuilder = ();

    type Structure = BTreeMap<usize, usize>;

    type Witness = Vec<F>;

    type ExternalInstance = C::Commitment;

    type ExternalWitness = Vec<F>;

    fn process_structure<R: Fn(Var<WitnessIndex>) -> usize>(
        builder: Self::StructureBuilder,
        _var_reader: R,
    ) -> Self::Structure {
        builder
    }

    fn process_witness(_builder: Self::WitnessBuilder) -> Self::Witness {
        panic!("Shouldn't be called, this extension uses _ex");
    }

    fn process_witness_ex(
        _builder: Self::WitnessBuilder,
        _external_instance: Self::ExternalInstance,
        external_witness: Self::ExternalWitness,
    ) -> Self::Witness {
        external_witness
    }

    fn record_constraint<const N: usize, R: Fn(Var<WitnessIndex>) -> usize>(
        builder: &mut Self::StructureBuilder,
        var_reader: R,
        vars: [Var<WitnessIndex>; N],
        constraint: Self::Constraint,
    ) {
        assert_eq!(N, 1);
        let var = var_reader(vars[0]);

        assert!(
            !builder.contains_key(&var),
            "only one lookup is allowed per variable"
        );

        // TODO: maybe check out of bounds.
        builder.insert(var, constraint);
    }

    fn compute_constraint<const N: usize>(
        _witness: &mut Self::WitnessBuilder,
        _vars: [F; N],
        _constraint: Self::Constraint,
    ) {
        panic!("Shouldn't be called, this extension uses _ex");
    }

    fn compute_constraint_ex<const N: usize>(
        _witness: &mut Self::WitnessBuilder,
        vars: [F; N],
        constraint: Self::Constraint,
        _external_instance: &Self::ExternalInstance,
        external_witness: &Self::ExternalWitness,
    ) {
        assert_eq!(N, 1);
        let var = vars[0];

        assert_eq!(var, external_witness[constraint])
    }
}
