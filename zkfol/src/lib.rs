use ark_ff::Field;
use reduction::{Argument, Prover, Relation, Verifier};
use sponge::sponge::Duplex;

/// This type will implement Relation, ROWS has been made a constant
/// for readability, but it could be done more flexible too.
pub struct ZkFol<const ROWS: usize = 100>;

/// A simple expression which will be used to define constraints.
#[derive(Clone, Debug)]
pub enum Exp<T> {
    Add(Box<(Self, Self)>),
    Sub(Box<(Self, Self)>),
    Mul(Box<(Self, Self)>),
    Var(T),
    Const(i64),
}

impl<A> Exp<A> {
    fn map<B, F: Fn(&A) -> B>(&self, f: &F) -> Exp<B> {
        use Exp::*;
        let map_subexprs = |(a, b): &(Self, Self)| (a.map(f), b.map(f));
        match self {
            Add(x) => Add(Box::new(map_subexprs(x))),
            Sub(x) => Sub(Box::new(map_subexprs(x))),
            Mul(x) => Mul(Box::new(map_subexprs(x))),
            Var(x) => Var(f(x)),
            Const(x) => Const(*x),
        }
    }
}

impl Exp<i64> {
    fn eval(self) -> i64 {
        match self {
            Exp::Add(x) => x.0.eval() + x.1.eval(),
            Exp::Sub(x) => x.0.eval() - x.1.eval(),
            Exp::Mul(x) => x.0.eval() * x.1.eval(),
            Exp::Var(x) => x,
            Exp::Const(x) => x,
        }
    }
}

/// An index to a particular row.
#[derive(Clone, Copy, Debug, Default)]
pub struct Index<const ROWS: usize>(usize);

impl<const ROWS: usize> Index<ROWS> {
    pub fn new(x: usize) -> Self {
        assert!(x < ROWS);
        Self(x)
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Cell<const ROWS: usize> {
    row: Index<ROWS>,
    column: usize,
}

impl<const ROWS: usize> Cell<ROWS> {
    fn unflatten(i: i64) -> Self {
        let i = i as usize;
        Cell {
            row: Index::new(i % ROWS),
            column: i / ROWS,
        }
    }
}

/// An equality assertion between 2 arbitrary cells.
#[derive(Clone, Debug, Default)]
pub struct CopyConstraint<const ROWS: usize> {
    pub from: Cell<ROWS>,
    pub to: Cell<ROWS>,
}

/// A dynamic address read lookup, similar to
/// CopyConstraint but 1 address is taken from
/// the witness instead of being fixed.
// to == witness[from]
#[derive(Clone, Debug, Default)]
pub struct ReadLookup<const ROWS: usize> {
    // This is the address of the address.
    pub from: Cell<ROWS>,
    pub to: Cell<ROWS>,
}

#[derive(Clone, Debug, Default)]
pub struct SetMembershipConstraint<const ROWS: usize> {
    // The location of the element.
    pub element: Cell<ROWS>,
    // The index of the set in which we want to check membership.
    pub set: usize,
}

// The constraint should be understood as reading the value from some
// address, copying such value into some cell of the table, and then
// writting a value from another cell to that same address.
// From this it is possible to only read, only write, read and then write,
// and also use the same cell for both operands if there is any use for it.
#[derive(Clone, Debug, Default)]
pub struct MemoryOperation<const ROWS: usize> {
    pub memory_address: usize,
    pub read_to: Option<Cell<ROWS>>,
    pub write_from: Option<Cell<ROWS>>,
}

#[derive(Clone, Debug)]
pub struct ZkFolStructure<const ROWS: usize = 100> {
    pub arithmetic_constraints: Vec<Exp<Index<ROWS>>>,
    pub copy_constraints: Vec<CopyConstraint<ROWS>>,
    pub reads: Vec<ReadLookup<ROWS>>,
    pub columns: usize,
    pub sets: Vec<Vec<i64>>,
    pub membership_constraints: Vec<SetMembershipConstraint<ROWS>>,
    pub memory_operations: Vec<MemoryOperation<ROWS>>,
}

impl<const ROWS: usize> Relation for ZkFol<ROWS> {
    type Structure = ZkFolStructure<ROWS>;

    // For a more concrete implementation this will likely
    // have at least a commitment to the witness.
    type Instance = ();

    // Using i64 for simplicity, but we will likely want
    // some arbitrary precision integer or some Q-like type.
    type Witness = Vec<[i64; ROWS]>;

    fn check(
        structure: &Self::Structure,
        _instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let ZkFolStructure {
            arithmetic_constraints,
            copy_constraints,
            columns,
            reads,
            sets,
            membership_constraints,
            memory_operations,
        } = structure;

        // Check that the witness has the expected number of columns.
        if witness.len() <= *columns {
            return false;
        }

        // To make implementing the reduction easier, but not a fundamental
        // restriction.
        if sets.iter().fold(0, |acc, set| acc + set.len()) > columns * ROWS {
            return false;
        }

        // Enforce arithmetic constraints on each column.
        for column in witness {
            for constraint in arithmetic_constraints {
                // Substitute in the values from the column.
                let exp: Exp<i64> = constraint.map(&|i| column[i.0]);
                // Assert it evaluates to 0.
                if exp.eval() != 0 {
                    return false;
                }
            }
        }

        // Enforce copy constraits between cells.
        for constraint in copy_constraints {
            let CopyConstraint { from, to } = constraint;
            let bound1 = &from.column < columns;
            let bound2 = &to.column < columns;
            let from = witness[from.column][from.row.0];
            let to = witness[to.column][to.row.0];

            if from != to {
                return false;
            }

            if let (true, true) = (bound1, bound2) {
            } else {
                return false;
            }
        }

        // Enforce read lookups.
        for constraint in reads {
            let ReadLookup { from, to } = constraint;

            let bound1 = &from.column < columns;
            let bound2 = &to.column < columns;
            let addr = witness[from.column][from.row.0];
            let to = witness[to.column][to.row.0];

            // Later on we will ideally just flatten the matrix, so that
            // a witness value can be directly used to index the witness.
            // For now we use this unflatten function which just vaguely
            // behaves as expected.
            let addr = Cell::<ROWS>::unflatten(addr);

            let from = witness[addr.column][addr.row.0];

            if from != to {
                return false;
            }

            if let (true, true) = (bound1, bound2) {
            } else {
                return false;
            }
        }

        for constraint in membership_constraints {
            let SetMembershipConstraint { element, set } = constraint;
            let bound = &element.column < columns;

            if !bound {
                return false;
            }

            let element = &witness[element.column][element.row.0];

            if let Some(set) = sets.get(*set) {
                if !set.contains(element) {
                    return false;
                }
            } else {
                return false;
            }
        }

        // Memory is initialized as 0s.
        let mut memory = vec![0; columns * ROWS];

        for operation in memory_operations {
            let MemoryOperation {
                memory_address,
                read_to,
                write_from,
            } = operation;

            // Address out of bounds.
            if *memory_address >= *columns * ROWS {
                return false;
            }

            let bound1 = read_to.map(|c| &c.column < columns).unwrap_or(true);
            let bound2 = write_from.map(|c| &c.column < columns).unwrap_or(true);

            if !(bound1 && bound2) {
                return false;
            }

            // Read.
            if let Some(addr) = read_to {
                let value = witness[addr.column][addr.row.0];

                if value != memory[*memory_address] {
                    return false;
                }
            }

            // Write.
            if let Some(addr) = write_from {
                let value = witness[addr.column][addr.row.0];
                memory[*memory_address] = value;
            }
        }

        true
    }
}

// This an example of what can done once you have an argument
// for ZkFol.
// F and S are requirements of the interface, they aren't very
// relevant to the example.
#[allow(dead_code)]
fn example<F, R, S>()
where
    F: Field,
    R: Argument<F, ZkFol, Params = ()>,
    S: Duplex<F>,
{
    // An example constraint a + b = c -> a + b - c = 0
    let constraint: Exp<usize> = {
        let a: Exp<usize> = Exp::Var(0);
        let b = Exp::Var(1);
        let c = Exp::Var(2);
        // Alternatively if we implement the arithmetic traits for Exp, it
        // could just be:
        // a + b - c
        let ab = Exp::Add(Box::new((a, b)));
        Exp::Sub(Box::new((ab, c)))
    };

    // We create the structure once.
    let structure: ZkFolStructure = ZkFolStructure {
        arithmetic_constraints: vec![constraint.map(&|i| Index::new(*i))],
        copy_constraints: vec![CopyConstraint {
            from: Cell {
                row: Index::new(0),
                column: 0,
            },
            to: Cell {
                row: Index::new(2),
                column: 1,
            },
        }],
        reads: vec![],
        columns: 3,
        sets: vec![],
        membership_constraints: vec![],
        memory_operations: vec![],
    };

    // We can now instanciate a prover and verifier for this structure.
    // This process may be expensive (a few seconds) but is a one-time
    // cost. Due to that you want to move as much as possible from the
    // instance to the witness, while keeping the structure general
    // enough to work for all your instances.
    let prover = Prover::<F, S, ZkFol, (), R>::new(&structure);
    let verifier = Verifier::<F, S, ZkFol, (), R>::new(&structure);

    // Now, if we have a witness.
    let witness: Vec<[i64; 100]> = Vec::default();
    //NOTE: As we don't have a valid instance-witness pair, we expect
    //this example to either panic on prove() or return an error on verify().

    // We can prove an instance-witness pair, with the instance being just ()
    // in this case.
    let proof: R::Proof = prover.prove((), witness).proof;

    // And verify the proof with the verifier.
    match verifier.verify((), proof) {
        Ok(()) => {
            println!("valid witness");
        }
        Err(_) => {
            panic!("Failed to verify with error");
        }
    }

    // The same prover and verifier can be used to prove other instance-witness
    // pairs that share the same structure.
}
