pub use crate::matrix::Matrix;
use crate::{
    circuit::Var,
    constraint_system::{ConstraintSystem, Constraints, Gate, GateRegistry, Val, WitnessReader},
    gates::{Constant, Equality},
};
use ark_ff::Field;
use std::{
    any::TypeId,
    cmp::Ordering,
    collections::BTreeMap,
    fmt::Display,
    ops::{Add, Mul, Sub},
};

/// With key being the variable and the value the number of times it appears (or its exponent).
#[derive(Clone, Debug)]
pub struct MultiSet<T>(BTreeMap<T, usize>);

impl<T> Default for MultiSet<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

#[derive(PartialEq, Eq, Clone)]
pub enum MatrixIndex {
    Io(usize),
    Selector(usize),
}

impl MatrixIndex {
    fn order(&self, b: &Self) -> Ordering {
        use MatrixIndex::{Io, Selector};
        match (self, b) {
            (Io(_), Selector(_)) => Ordering::Less,
            (Selector(_), Io(_)) => Ordering::Greater,
            (Io(a), Io(b)) | (Selector(a), Selector(b)) => a.cmp(b),
        }
    }
}

impl PartialOrd for MatrixIndex {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MatrixIndex {
    fn cmp(&self, other: &Self) -> Ordering {
        self.order(other)
    }
}

#[derive(Clone, Debug)]
pub struct LcsCircuit<F, const IO: usize, const S: usize> {
    pub io_matrices: [Matrix; IO],
    /// Where each entry is in 0..S reprensenting the gate to active.
    pub gate_selectors: Vec<usize>,
    pub input_len: usize,
    //with each multiset representing a term, and with corresponding constant coefficient
    pub gates: Vec<Constraints<Exp<usize>>>,
    /// public_io + witness
    pub trace_len: usize,
    /// Maps Constant constraints to their constant.
    pub constants: BTreeMap<usize, F>,
}

impl<F, const IO: usize, const S: usize> LcsCircuit<F, IO, S> {
    /// vars needed to fir the trace
    pub fn vars(&self) -> usize {
        let len_padded = self.trace_len.next_power_of_two();
        len_padded.ilog2() as usize
    }
}

#[derive(Debug)]
/// An individual instance of a gate, contains the variables and the id of the gate.
struct Constraint<T, const IO: usize> {
    ///It's probably better to just fill unused space with zeros than to have a bunch of `Vec`s
    io: [T; IO],
    /// Length of `io`.
    len: usize,
    selector: usize,
}

/// Builder creates a [`LcsCircuit`] from a circuit through symbolic variables.
#[derive(Debug, Default)]
pub struct LcsBuilder<F: Field, const IO: usize> {
    next: usize,
    vars: Vec<usize>,
    registry: GateRegistry,
    constraints: Vec<Constraint<WitnessIndex, IO>>,
    constant_table: BTreeMap<F, WitnessIndex>,
}

#[derive(Clone, Copy, Debug)]
/// Variable that points to a position in the witness.
pub struct WitnessIndex(usize);

impl Add for WitnessIndex {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        panic!(
            "tried to add {:?} and {:?}, this type of var should never be added",
            self, rhs
        );
    }
}

impl Sub for WitnessIndex {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        panic!(
            "tried to subtract {:?} and {:?}, this type of var should never be subtracted",
            self, rhs
        );
    }
}

impl Mul for WitnessIndex {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        panic!(
            "tried to multiply {:?} and {:?}, this type of var should never be multiplied",
            self, rhs
        );
    }
}

impl Val for WitnessIndex {}

impl<F: Field, const MAX_IO: usize> LcsBuilder<F, MAX_IO> {
    pub(crate) fn vars(&self) -> &[usize] {
        &self.vars
    }

    pub fn gate_counts(&self) -> Vec<(&'static str, usize)> {
        let registry = &self.registry;
        let constraints = &self.constraints;
        let mut counts = vec![0; registry.gate_registry.len()];

        for constraint in constraints {
            counts[constraint.selector] += 1;
        }

        let mut named_counts = counts.into_iter().map(|c| ("", c)).collect::<Vec<_>>();

        for gate in registry.gate_registry.values() {
            named_counts[gate.0].0 = gate.2;
        }

        named_counts
    }

    /// Allocate new variable, returning its index.
    fn var(&mut self) -> WitnessIndex {
        let v = self.next;
        self.next += 1;
        self.vars.push(v);
        WitnessIndex(v)
    }

    pub fn with_inputs<const I: usize>() -> (Self, [WitnessIndex; I]) {
        let mut new = Self::default();
        let inputs = [(); I].map(|_| new.var());
        (new, inputs)
    }

    /// reserve space for the public output
    pub fn reserve_outputs<const O: usize>(&mut self) {
        for _ in 0..O {
            let _ = self.var();
        }
    }

    pub fn link_outputs<const I: usize, const O: usize>(&mut self, outputs: [WitnessIndex; O]) {
        for (i, b) in outputs.into_iter().enumerate() {
            let a = WitnessIndex(i + I);
            <Self as ConstraintSystem<F, WitnessIndex>>::execute::<Equality, 2, 2, 0>(
                self,
                [a, b].map(Var),
            );
        }
    }

    pub fn build<const S: usize>(self, public_io_len: usize) -> LcsCircuit<F, MAX_IO, S> {
        let Self {
            registry,
            constraints,
            constant_table,
            ..
        } = self;

        let mut io_matrices = [(); MAX_IO].map(|_| Matrix::with_capacity(constraints.len()));
        let mut gate_selectors = vec![];

        let constant_selector = registry.gate_registry.iter().find_map(|(id, gate)| {
            if TypeId::of::<Constant>() == *id {
                assert!(matches!(gate.1, Constraints::Constraint(Exp::Constant)));
                Some(gate.0)
            } else {
                None
            }
        });

        let reverse_constant_table: BTreeMap<usize, F> = constant_table
            .into_iter()
            .map(|(constant, index)| (index.0, constant))
            .collect();

        let mut constants: BTreeMap<usize, F> = BTreeMap::new();

        for (i, constraint) in constraints.into_iter().enumerate() {
            let constraint: Constraint<WitnessIndex, MAX_IO> = constraint;
            let Constraint { io, len, selector } = constraint;

            if let Some(constant_selector) = constant_selector
                && constant_selector == selector
            {
                let constant = reverse_constant_table.get(&io[0].0).unwrap();
                constants.insert(i, *constant);
            }
            for i in 0..len {
                io_matrices[i].push_row_single_value(io[i].0);
            }
            (len..MAX_IO).for_each(|i| {
                io_matrices[i].push_row_empty();
            });
            gate_selectors.push(selector);
            // let selector = Self::bit_decomposition::<S>(selector);

            //TODO: for now using simpler linear selectors

            if selector >= S {
                panic!("not enough selectors for all gates, increase S");
            }
        }

        let gates = registry.expressions_sorted();

        let trace_len = self.vars.len();
        assert_eq!(trace_len, self.next);
        LcsCircuit {
            input_len: public_io_len,
            io_matrices,
            gate_selectors,
            gates,
            trace_len,
            constants,
        }
    }
}

impl<F: Field, const MAX_IO: usize> ConstraintSystem<F, WitnessIndex> for LcsBuilder<F, MAX_IO> {
    fn execute<G, const IO: usize, const I: usize, const O: usize>(
        &mut self,
        inputs: [Var<WitnessIndex>; I],
    ) -> [Var<WitnessIndex>; O]
    where
        G: Gate<IO, I, O> + 'static,
    {
        let inputs = inputs.map(Var::unwrap);
        let mut io = [WitnessIndex(0); MAX_IO];
        io[..I].copy_from_slice(&inputs[..I]);

        let output = [(); O].map(|_| self.var());
        io[I..(I + O)].copy_from_slice(&output[..O]);

        let selector = self.registry.selector::<G, IO, I, O>();

        let constraint = Constraint {
            io,
            len: IO,
            selector,
        };
        self.constraints.push(constraint);
        output.map(Var)
    }

    type Reader<'a> = EmptyReader;

    fn free_variable<W>(&mut self, _value: W) -> Var<WitnessIndex>
    where
        W: for<'a> Fn(Self::Reader<'a>) -> F,
    {
        Var(self.var())
    }

    fn constant(&mut self, value: F) -> Var<WitnessIndex> {
        let existing = self.constant_table.get(&value);
        match existing {
            Some(v) => Var(*v),
            None => {
                let var = self.var();
                self.execute::<Constant, 1, 1, 0>([Var(var)]);
                let existing = self.constant_table.insert(value, var);
                assert!(existing.is_none());
                Var(var)
            }
        }
    }
}

#[derive(Clone, Copy)]
/// A a value of such type can't exist, it can implement most
/// traits trivially.
pub enum EmptyReader {}

impl<'a, F, V> WitnessReader<'a, F, V> for EmptyReader {
    fn read(&self, _var: &Var<V>) -> F {
        match *self {}
    }
}

#[derive(Debug, Clone)]
pub enum Exp<T> {
    Atom(T),
    Add(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    /// Variant to identify the constant gate.
    Constant,
}

impl<T> Add<Self> for Exp<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::Add(Box::new(self), Box::new(rhs))
    }
}

impl<T> Mul<Self> for Exp<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::Mul(Box::new(self), Box::new(rhs))
    }
}

impl<T> Sub<Self> for Exp<T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::Sub(Box::new(self), Box::new(rhs))
    }
}

impl<T: Clone> Val for Exp<T> {}

impl<T: Display> Display for MultiSet<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, n) in self.0.iter() {
            for _ in 0..*n {
                write!(f, "v{i}")?;
            }
        }
        writeln!(f)
    }
}

impl<T: Ord + Clone> Exp<T> {
    pub fn map<V, F>(self, f: &F) -> Exp<V>
    where
        F: Fn(T) -> V,
    {
        use Exp::*;
        match self {
            Atom(v) => Atom(f(v)),
            Add(e1, e2) => Add(Box::new(e1.map(f)), Box::new(e2.map(f))),
            Mul(e1, e2) => Mul(Box::new(e1.map(f)), Box::new(e2.map(f))),
            Sub(e1, e2) => Sub(Box::new(e1.map(f)), Box::new(e2.map(f))),
            Constant => Constant,
        }
    }
}

/*#[test]
fn exp_to_multiset() {
    use ark_vesta::Fr;
    let a = Exp::Atom(0);
    let b = Exp::Atom(1);
    let c = Exp::Atom(2);
    let s1 = Exp::Atom(3);
    let s2 = Exp::Atom(4);
    let add = (a.clone() + b.clone() - c.clone()) * s1;
    let mul = (a * b - c) * s2;
    let exp = add + mul;
    println!("exp:\n{:#?}", exp);
    let multisets = exp.to_multisets::<Fr>();
    // println!("multisets:\n{}", multisets);
    for multiset in multisets {
        println!("{} * {} +", multiset.0, multiset.1);
    }
}*/

impl GateRegistry {
    fn expressions_sorted(self) -> Vec<Constraints<Exp<usize>>> {
        let mut gates: Vec<(usize, Constraints<Exp<usize>>)> = self
            .gate_registry
            .into_values()
            .map(|(id, c, _)| (id, c))
            .collect();
        gates.sort_by_key(|x| x.0);
        for (i1, (i2, _)) in gates.iter().enumerate() {
            assert_eq!(i1, *i2, "unexpected index");
        }
        gates.into_iter().map(|(_, exp)| exp).collect()
    }
}
