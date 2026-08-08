use crate::{circuit::Var, gates::Constant, structure::Exp};
use ark_ff::Field;
use std::{
    any::{type_name, Any, TypeId},
    collections::BTreeMap,
    ops,
};

pub trait WitnessReader<'a, F, V> {
    /// Read the witness value under the variable.
    fn read(&self, var: &Var<V>) -> F;
}

pub trait ConstraintSystem<F: Field, V> {
    fn execute<G, const IO: usize, const I: usize, const O: usize>(
        &mut self,
        i: [Var<V>; I],
    ) -> [Var<V>; O]
    where
        G: Gate<IO, I, O> + 'static,
        V: Val;

    type Reader<'a>: WitnessReader<'a, F, V>;

    /// Creates a new variable with the provided value.
    /// The variable is not constrained to have the provided value, or any
    /// particular value at all.
    /// The value is provided through a function which receives a [Self::Reader]
    /// and may use it to call [WitnessReader::read] to access the value
    /// behind a [Var<F>].
    fn free_variable<W>(&mut self, value: W) -> Var<V>
    where
        W: for<'a> Fn(Self::Reader<'a>) -> F;

    /// Creates a variable with a constant value, the method
    /// is idempotent over the value.
    /// Multiple calls with the same constant value will allocate
    /// a single variable.
    fn constant(&mut self, value: F) -> Var<V>;
}

pub trait Val:
    ops::Add<Output = Self> + ops::Mul<Output = Self> + ops::Sub<Output = Self> + Clone + Sized
{
}

/// A non-empty list of constraints.
#[derive(Debug, Clone)]
pub enum Constraints<V> {
    Constraint(V),
    Append(Box<Self>, V),
    Empty,
}

impl<V> From<V> for Constraints<V> {
    fn from(value: V) -> Self {
        Self::Constraint(value)
    }
}

impl<V: Copy> Iterator for Constraints<V> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Constraints::Constraint(c) => {
                let c = *c;
                *self = Constraints::Empty;
                Some(c)
            }
            Constraints::Append(constraints, c) => {
                let c = *c;
                let dummy = Box::new(Constraints::Constraint(c));
                let constraints = *std::mem::replace(constraints, dummy);
                *self = constraints;
                Some(c)
            }
            Constraints::Empty => None,
        }
    }
}

impl<V, const N: usize> From<[V; N]> for Constraints<V> {
    fn from(value: [V; N]) -> Self {
        assert!(N > 0, "must have at least one constraint");
        let mut values = value.into_iter();
        let first: Self = values.next().unwrap().into();
        values.fold(first, |acc, c| Constraints::Append(Box::new(acc), c))
    }
}

impl<V> From<Constraints<V>> for Vec<V> {
    fn from(value: Constraints<V>) -> Self {
        // Not the most efficient, but it isn't performance critical anyway.
        match value {
            Constraints::Constraint(c) => vec![c],
            Constraints::Append(tail, head) => {
                let mut constraints: Vec<V> = From::from(*tail);
                constraints.push(head);
                constraints
            }
            Constraints::Empty => vec![],
        }
    }
}

/// A gate, which maps inputs to outputs, and defines one or more constraints
/// between both inputs and outputs.
/// `Self::gate` deals only with witness generation, while `Self::check` defines
/// the actual constraints to be enforced.
pub trait Gate<const IO: usize, const I: usize, const O: usize>: Sized + 'static {
    /// Computes outputs from inputs.
    fn gate<V: Val>(i: [V; I]) -> [V; O];
    /// The output should be zero when the constraint is satisfied.
    /// use `into()` to convert either `V` or `[V;N]` into required output.
    fn check<V: Val>(i: [V; I], o: [V; O]) -> Constraints<V>;
}

fn eval_gate_constraints<G, const IO: usize, const I: usize, const O: usize>(
) -> Constraints<Exp<usize>>
where
    G: Gate<IO, I, O>,
{
    let mut i = 0;
    let mut var = |_| {
        let e = Exp::Atom(i);
        i += 1;
        e
    };
    let i = [(); I].map(&mut var);
    let o = [(); O].map(&mut var);
    G::check(i, o)
}

#[derive(Debug)]
/// Keeps track of used gates, and assigns a unique id to each of them.
pub struct GateRegistry {
    pub(crate) gate_registry: BTreeMap<TypeId, (usize, Constraints<Exp<usize>>, &'static str)>,
    next_selector: usize,
}

impl Default for GateRegistry {
    fn default() -> Self {
        let gate_registry = BTreeMap::new();
        Self {
            gate_registry,
            //TODO: may reserve 0 for equality
            next_selector: 0,
        }
    }
}

impl GateRegistry {
    pub fn selector<G, const IO: usize, const I: usize, const O: usize>(&mut self) -> usize
    where
        G: Any + Gate<IO, I, O>,
    {
        let id = TypeId::of::<G>();
        let entry = self.gate_registry.entry(id);
        let entry = entry.or_insert_with(|| {
            self.next_selector += 1;
            let exp = if id == TypeId::of::<Constant>() {
                // Special case for constants
                Constraints::from(Exp::Constant)
            } else {
                eval_gate_constraints::<G, IO, I, O>()
            };
            (self.next_selector - 1, exp, type_name::<G>())
        });
        entry.0
    }
}
