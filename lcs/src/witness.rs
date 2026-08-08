use crate::{
    circuit::Var,
    constraint_system::{ConstraintSystem, Gate, Val, WitnessReader},
    matrix::Matrix,
};
use ark_ff::Field;
use std::{
    collections::BTreeSet,
    ops::{Add, Index, Mul, Sub},
};

#[derive(Clone, Copy, Debug)]
/// `Field` wrapper which implements `Var`.
pub struct Fi<F: Field>(F);

impl<F: Field> Add for Fi<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl<F: Field> Sub for Fi<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

impl<F: Field> Mul for Fi<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0)
    }
}

impl<F: Field> Val for Fi<F> {}

pub struct WitnessGenerator<F: Field, const IO: usize> {
    witness: Vec<Fi<F>>,
    constants: BTreeSet<F>,
    check: bool,
}

#[derive(Clone, Debug)]
pub struct Witness<F: Field>(pub Vec<F>);

impl<F: Field> Witness<F> {
    /// Pad with 0s to the next power of 2.
    pub fn pad_to_power(&mut self) {
        let len = self.0.len().next_power_of_two();
        self.0.resize(len, F::zero());
    }
}

impl<F: Field, const MAX_IO: usize> ConstraintSystem<F, Fi<F>> for WitnessGenerator<F, MAX_IO> {
    fn execute<G, const IO: usize, const I: usize, const O: usize>(
        &mut self,
        i: [Var<Fi<F>>; I],
    ) -> [Var<Fi<F>>; O]
    where
        G: Gate<IO, I, O> + 'static,
    {
        let i = i.map(Var::unwrap);
        let out = G::gate(i);
        for o in out.iter() {
            self.witness.push(*o);
        }
        if self.check {
            let constraints = G::check(i, out);
            for constraint in constraints {
                if !constraint.0.is_zero() {
                    // It may be better to store all errors and report at the end instead of this.
                    panic!("constraint evaluates to non zero");
                }
            }
        }
        out.map(Var)
    }

    type Reader<'a> = VarReader<MAX_IO>;

    fn free_variable<W>(&mut self, value: W) -> Var<Fi<F>>
    where
        W: for<'a> Fn(Self::Reader<'a>) -> F,
    {
        let reader = VarReader;
        let value = value(reader);
        self.witness.push(Fi(value));
        Var(Fi(value))
    }

    fn constant(&mut self, value: F) -> Var<Fi<F>> {
        //TODO: maybe check against structure
        if self.constants.contains(&value) {
            // If the constant has been seen, just return it.
            Var(Fi(value))
        } else {
            // If not, add it to the witness and mark it as seen.
            self.witness.push(Fi(value));
            self.constants.insert(value);
            Var(Fi(value))
        }
    }
}

pub struct VarReader<const IO: usize>;
// Will be useful later
// pub struct VarReader<'a, F: Field, const IO: usize>(&'a WitnessGenerator<F, IO>);

impl<'a, F: Field, const IO: usize> WitnessReader<'a, F, Fi<F>> for VarReader<IO> {
    fn read(&self, var: &Var<Fi<F>>) -> F {
        var.0 .0
    }
}

impl<F: Field, const MAX_IO: usize> WitnessGenerator<F, MAX_IO> {
    fn new(check: bool) -> Self {
        let witness = vec![];
        Self {
            witness,
            check,
            constants: BTreeSet::default(),
        }
    }

    pub fn with_io<const I: usize, const O: usize>(
        check: bool,
        inputs: [F; I],
    ) -> (Self, [Fi<F>; I]) {
        let mut new = Self::new(check);
        let input = inputs.map(|x| Fi(x));
        new.witness.extend(input.iter().cloned());
        //just fill with some arbitrary element, will later be replaced
        new.witness.extend([Fi(F::zero()); O]);
        (new, input)
    }

    pub fn link_outputs<const I: usize, const O: usize>(&mut self, outputs: [Fi<F>; O]) {
        for (i, b) in outputs.into_iter().enumerate() {
            let i = i + I;
            self.witness[i] = b;
        }
    }

    pub fn witness(self) -> Witness<F> {
        Witness(self.witness.into_iter().map(|x| x.0).collect())
    }
}

pub fn unwrap_output<F: Field, const O: usize>(o: [Fi<F>; O]) -> [F; O] {
    o.map(|x| x.0)
}

/// Representation of all linear combinations from N tables.
/// Can be used to compute linear combinations with a witness.
pub struct LinearCombinations<const N: usize> {
    /// As length-value sequences
    combinations: Vec<usize>,
}

impl<const N: usize> LinearCombinations<N> {
    pub fn from_tables(matrices: [&Matrix; N]) -> Self {
        let mut combinations = vec![];
        let len = *matrices.map(Matrix::len).iter().max().unwrap();

        for i in 0..len {
            for matrix in matrices {
                let row = matrix.get_row(i).unwrap_or(&[]);
                combinations.push(row.len());
                combinations.extend_from_slice(row);
            }
        }

        Self { combinations }
    }

    /// Compute linear combinations with given witness.
    pub fn compute<'a, F>(&'a self, witness: &'a [F]) -> WitnessLcIter<'a, F, N> {
        WitnessLcIter {
            combinations: self,
            witness,
            next: 0,
        }
    }
}

impl<const N: usize> Index<usize> for LinearCombinations<N> {
    type Output = usize;

    fn index(&self, index: usize) -> &Self::Output {
        &self.combinations[index]
    }
}

/// Iterator over rows of linear combinations
pub struct WitnessLcIter<'a, F, const N: usize> {
    combinations: &'a LinearCombinations<N>,
    witness: &'a [F],
    next: usize,
}

impl<F, const N: usize> Iterator for WitnessLcIter<'_, F, N>
where
    F: Field,
{
    type Item = [F; N];

    fn next(&mut self) -> Option<Self::Item> {
        let mut i = self.next;
        let _ = self.combinations.combinations.get(i)?;

        let mut res = [F::zero(); N];
        for c in res.iter_mut() {
            let n = self.combinations[i];
            i += 1;
            for _ in 0..n {
                c.add_assign(self.witness[self.combinations[i]]);
                i += 1;
            }
        }
        self.next = i;

        Some(res)
    }
}
