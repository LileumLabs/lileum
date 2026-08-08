use crate::{
    constraint_system::{ConstraintSystem, Val},
    structure::{CcsStructure, StructureBuilder},
    witness::{unwrap_output, Witness, WitnessGenerator},
};
use ark_ff::Field;
use std::fmt::Display;

#[derive(Clone, Copy, Debug)]
/// Symbolic circuit variable.
pub struct Var<V>(pub(crate) V);

impl<F> Var<F> {
    pub(crate) fn unwrap(self) -> F {
        self.0
    }
}

/// Circuit definition, with generics for field, public inputs, and public and private outputs.
/// Private outputs being just a convenience to take value produced in the circuit out.
/// `Self::PrivateOutput` is to be generated from the private outputs when possible.
pub trait Circuit<F: Field, const IN: usize = 0, const OUT: usize = 0, const PRIV_OUT: usize = 0> {
    ///() if you don't care
    /// TODO: not currently usable.
    type PrivateInput;
    ///() if you don't care
    type PrivateOutput;

    fn circuit<V: Val, C: ConstraintSystem<F, V>>(
        cs: &mut C,
        public_input: [Var<V>; IN],
    ) -> ([Var<V>; OUT], [Var<V>; PRIV_OUT]);
    fn handle_output(out: [F; PRIV_OUT]) -> Self::PrivateOutput;
}

pub trait BuildStructure<
    F: Field,
    const IN: usize,
    const OUT: usize,
    const PRIV_OUT: usize,
    const IO: usize,
>: Circuit<F, IN, OUT, PRIV_OUT>
{
    fn structure<const S: usize>() -> CcsStructure<F, IO, S> {
        let (mut cs, public_input) = StructureBuilder::<F, IO>::with_inputs::<IN>();
        cs.reserve_outputs::<OUT>();
        let (public_out, private_out) = Self::circuit(&mut cs, public_input.map(Var));
        //unnecessary for this
        let _ = private_out;
        cs.link_outputs::<IN, OUT>(public_out.map(Var::unwrap));

        cs.build::<S>(IN + OUT)
    }

    fn profile() -> CircuitProfile {
        let (mut cs, public_input) = StructureBuilder::<F, IO>::with_inputs::<IN>();
        cs.reserve_outputs::<OUT>();
        let (public_out, _) = Self::circuit(&mut cs, public_input.map(Var));
        cs.link_outputs::<IN, OUT>(public_out.map(Var::unwrap));
        let gate_counts = cs.gate_counts();
        let witness_length = cs.vars().len();
        CircuitProfile {
            gate_counts,
            witness_length,
        }
    }
}

#[derive(Debug)]
pub struct CircuitProfile {
    pub witness_length: usize,
    pub gate_counts: Vec<(&'static str, usize)>,
}

impl Display for CircuitProfile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "CircuitProfile\n")?;
        writeln!(f, "witness length: {}", self.witness_length)?;
        writeln!(f, "gates used:")?;
        for (gate, count) in &self.gate_counts {
            writeln!(f, "{}: {}", gate, count)?;
        }
        Ok(())
    }
}

impl<T, F: Field, const IN: usize, const OUT: usize, const PRIV_OUT: usize, const IO: usize>
    BuildStructure<F, IN, OUT, PRIV_OUT, IO> for T
where
    T: Circuit<F, IN, OUT, PRIV_OUT>,
{
}

pub trait Prove<F: Field, const IN: usize, const OUT: usize, const PRIV_OUT: usize, const IO: usize>:
    Circuit<F, IN, OUT, PRIV_OUT>
{
    fn witness(inputs: [F; IN], check: bool) -> (Witness<F>, Self::PrivateOutput) {
        let (mut cs, public_input) = WitnessGenerator::<F, IO>::with_io::<IN, OUT>(check, inputs);
        let (public_out, private_out) = Self::circuit(&mut cs, public_input.map(Var));
        let private_out = unwrap_output(private_out.map(Var::unwrap));

        cs.link_outputs::<IN, OUT>(public_out.map(Var::unwrap));
        (cs.witness(), Self::handle_output(private_out))
    }
}

impl<T, F: Field, const IN: usize, const OUT: usize, const PRIV_OUT: usize, const IO: usize>
    Prove<F, IN, OUT, PRIV_OUT, IO> for T
where
    T: Circuit<F, IN, OUT, PRIV_OUT>,
{
}
