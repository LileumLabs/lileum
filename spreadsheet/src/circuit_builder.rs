use crate::gates::{self, BinaryGate, GateType};
use alloc::{collections::btree_map::BTreeMap, vec::Vec};
use ark_ff::Field;

/// (row, column)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Address(usize, usize);

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Range(Address, Address);

impl From<Address> for Range {
    fn from(value: Address) -> Self {
        Range(value, value)
    }
}

impl Range {
    pub fn is_subset_of(&self, other: &Self) -> bool {
        self.0.0 >= other.0.0
            && self.0.1 >= other.0.1
            && self.1.0 <= other.1.0
            && self.1.1 <= other.1.1
    }

    pub fn rows(&self) -> usize {
        let Self(from, to) = self;
        to.0 - from.0
    }

    pub fn colums(&self) -> usize {
        let Self(from, to) = self;
        to.1 - from.1
    }

    pub fn cells(&self) -> usize {
        self.rows() * self.colums()
    }

    pub fn iter(&self) -> RangeIter<'_> {
        RangeIter {
            current: 0,
            range: self,
        }
    }

    fn flat_index(&self, address: &Address) -> usize {
        assert!(Range::from(*address).is_subset_of(self));
        let Address(row, colum) = address;
        row * self.colums() + colum
    }
}

impl core::ops::Add<&Self> for Address {
    type Output = Self;

    fn add(mut self, rhs: &Self) -> Self::Output {
        self.0 += rhs.0;
        self.1 += rhs.1;
        self
    }
}

pub struct RangeIter<'a> {
    current: usize,
    range: &'a Range,
}

impl<'a> Iterator for RangeIter<'a> {
    type Item = Address;

    fn next(&mut self) -> Option<Self::Item> {
        if self.range.cells() >= self.current {
            None
        } else {
            let row = self.current / self.range.colums();
            let column = self.current % self.range.colums();
            self.current += 1;
            // Adress relative to the start of the range.
            let relative_address = Address(row, column);
            // Make absolute.
            Some(relative_address + &self.range.0)
        }
    }
}

/// Where the input to some formula is located.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DataOrTrace {
    /// The range is part of the committed data.
    Data,
    /// The range is part of the trace, it is the output of other gates.
    Trace,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FormulaType {
    Sum,
    Eq,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Formula {
    ty: FormulaType,
    input: Range,
    input_location: DataOrTrace,
}

pub struct SpreadsheetStructure {
    input_range: Range,
    formulas: BTreeMap<Address, Formula>,
}

impl SpreadsheetStructure {
    pub fn new(input_range: Range) -> Self {
        Self {
            input_range,
            formulas: BTreeMap::new(),
        }
    }

    pub fn add_formula(&mut self, formula: Formula, location: Address) {
        let old = self.formulas.insert(location, formula);
        assert!(old.is_none(), "Can't set 2 formulas in the same cell");
    }

    fn sort_formulas(&self) -> Vec<(Address, Formula)> {
        //TODO: Actually topological sort
        self.formulas.clone().into_iter().collect()
    }

    pub fn circuit<F: Field>(&self, selected_assertions: Vec<Address>) -> Vec<WiredGate> {
        // For now we take all of them, but we should filter out
        // unreachable formulas.
        let _ = selected_assertions;

        let formulas = self.sort_formulas();

        let mut builder = CircuitBuilder::new(self.input_range);
        for (addres, formula) in formulas {
            let val = formula.implement::<F>(&mut builder);
            if let Some(val) = val {
                let old = builder.address_map.insert(addres, val);
                assert!(old.is_none());
            }
        }
        builder.gates
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Var(pub usize, pub DataOrTrace);

#[derive(Clone, Copy, Debug)]
pub struct WiredGate {
    io: [Var; 3],
    gate: GateType,
}

impl WiredGate {
    pub fn compute_trace<F: Field>(gates: &[Self], data: &[F]) -> Vec<F> {
        let mut trace = Vec::new();
        for gate in gates {
            let WiredGate {
                io: [a, b, _],
                gate,
            } = gate;
            let [a, b] = [a, b].map(|var: &Var| match var.1 {
                DataOrTrace::Data => data[var.0],
                DataOrTrace::Trace => trace[var.0],
            });
            let c = gate.compute(a, b);
            trace.push(c);
        }
        trace
    }

    pub fn check<F: Field>(gates: &[Self], data: &[F]) -> bool {
        let trace = Self::compute_trace(gates, data);
        for gate in gates {
            let WiredGate { io, gate } = gate;
            let io = io.each_ref().map(|var| match var.1 {
                DataOrTrace::Data => data[var.0],
                DataOrTrace::Trace => trace[var.0],
            });
            if !gate.check(&io) {
                return false;
            }
        }
        true
    }

    pub(crate) fn io(&self) -> [Var; 3] {
        self.io
    }
}

#[derive(Clone, Debug, Default)]
struct CircuitBuilder {
    input_range: Range,
    gates: Vec<WiredGate>,
    next_var: usize,
    /// Maps cells to the variable corresponding to evaluation of the
    /// formula in that cell.
    address_map: BTreeMap<Address, Var>,
}

impl CircuitBuilder {
    fn new(input_range: Range) -> Self {
        Self {
            input_range,
            ..Default::default()
        }
    }

    fn new_var(&mut self) -> Var {
        let var = Var(self.next_var, DataOrTrace::Trace);
        self.next_var += 1;
        var
    }

    fn add_binary_gate<F: Field, G: BinaryGate<F>>(&mut self, a: Var, b: Var) -> Var {
        let c = self.new_var();
        self.gates.push(WiredGate {
            io: [a, b, c],
            gate: G::TYPE,
        });
        c
    }

    fn read_cell(&self, address: &Address, location: DataOrTrace) -> Var {
        match location {
            DataOrTrace::Data => Var(self.input_range.flat_index(address), location),
            DataOrTrace::Trace => *self.address_map.get(address).unwrap(),
        }
    }
}

impl Formula {
    fn implement<F: Field>(&self, builder: &mut CircuitBuilder) -> Option<Var> {
        let Self {
            ty,
            input,
            input_location,
        } = self;
        let formula_evaluation: Option<Var> = match ty {
            FormulaType::Sum => {
                Self::chain_gates::<F, gates::Add>(builder, input, *input_location).into()
            }
            FormulaType::Eq => {
                let mut range = input.iter();
                let first = range.next();
                if let Some(a) = first {
                    let a = builder.read_cell(&a, *input_location);
                    for b in range {
                        let b = builder.read_cell(&b, *input_location);
                        let _ = builder.add_binary_gate::<F, gates::Eq>(a, b);
                    }
                }
                None
            }
        };
        formula_evaluation
    }

    fn chain_gates<F: Field, G: BinaryGate<F>>(
        builder: &mut CircuitBuilder,
        range: &Range,
        location: DataOrTrace,
    ) -> Var {
        let mut range = range.iter();
        let first_two = (range.next(), range.next());

        match first_two {
            // forbid for now, maybe allow in the future.
            (None, None) | (None, Some(_)) | (Some(_), None) => {
                panic!("Range should have at least 2 cells")
            }
            (Some(a), Some(b)) => {
                let a = builder.read_cell(&a, location);
                let b = builder.read_cell(&b, location);
                let c = builder.add_binary_gate::<F, G>(a, b);
                range.fold(c, |a, b| {
                    let b = builder.read_cell(&b, location);
                    builder.add_binary_gate::<F, G>(a, b)
                })
            }
        }
    }
}
