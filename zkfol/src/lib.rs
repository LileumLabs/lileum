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

type Address = usize;

fn out_of_bounds<const N: usize>(addresses: [Address; N], witness_len: usize) -> bool {
    !addresses.into_iter().all(|address| address < witness_len)
}

/// A dynamic address read lookup, similar to
/// CopyConstraint but 1 address is taken from
/// the witness instead of being fixed.
// to == witness[from]
#[derive(Clone, Debug, Default)]
pub struct ReadLookup {
    // This is the address of the address.
    pub from: Address,
    pub to: Address,
}

#[derive(Clone, Debug, Default)]
pub struct SetMembershipConstraint {
    // The location of the element.
    pub element: Address,
    // The index of the set in which we want to check membership.
    pub set: usize,
}

// The constraint should be understood as reading the value from some
// address, copying such value into some cell of the table, and then
// writting a value from another cell to that same address.
// From this it is possible to only read, only write, read and then write,
// and also use the same cell for both operands if there is any use for it.
// #[derive(Clone, Debug, Default)]
// pub struct MemoryOperation<const ROWS: usize> {
//     pub memory_address: usize,
//     pub read_to: Option<Cell<ROWS>>,
//     pub write_from: Option<Cell<ROWS>>,
// }

#[derive(Clone, Copy, Debug)]
pub enum GateType {
    Add,
    Mul,
    Sub,
    Eq,
    AddConst(i64),
}

#[derive(Clone, Copy, Debug)]
pub struct Gate {
    a: Address,
    b: Address,
    c: Address,
    ty: GateType,
}

impl Gate {
    fn eval(&self, witness: &[i64]) -> i64 {
        let Self { a, b, c, ty } = self;
        let [a, b, c] = [a, b, c].map(|i| witness[*i]);
        match ty {
            GateType::Add => a + b - c,
            GateType::Mul => a * b - c,
            GateType::Sub => a - b - c,
            GateType::Eq => a - b,
            GateType::AddConst(cons) => a + cons - c,
        }
    }

    fn out_of_bounds(&self, witness_len: usize) -> bool {
        let Self { a, b, c, ty: _ } = *self;
        out_of_bounds([a, b, c], witness_len)
    }
}

#[derive(Clone, Debug)]
pub struct ZkFolStructure {
    pub witness_len: usize,
    pub arithmetic_constraints: Vec<Gate>,
    pub reads: Vec<ReadLookup>,
    pub sets: Vec<Vec<i64>>,
    pub membership_constraints: Vec<SetMembershipConstraint>,
    pub sign_constraints: Vec<Address>,
}

impl Relation for ZkFol {
    type Structure = ZkFolStructure;

    // For a more concrete implementation this will likely
    // have at least a commitment to the witness.
    type Instance = ();

    // Using i64 for simplicity, but we will likely want
    // some arbitrary precision integer or some Q-like type.
    type Witness = Vec<i64>;

    fn check(
        structure: &Self::Structure,
        _instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let ZkFolStructure {
            witness_len,
            arithmetic_constraints,
            reads,
            sets,
            membership_constraints,
            sign_constraints,
        } = structure;

        if witness.len() != *witness_len {
            return false;
        }
        // To make implementing the reduction easier, but not a fundamental
        // restriction.
        if sets.iter().fold(0, |acc, set| acc + set.len()) > *witness_len {
            return false;
        }

        // Enforce arithmetic constraints on each column.
        for gate in arithmetic_constraints {
            if gate.out_of_bounds(witness.len()) {
                return false;
            }

            if gate.eval(witness) != 0 {
                return false;
            }
        }

        // Enforce read lookups.
        for constraint in reads {
            let ReadLookup { from, to } = *constraint;

            if out_of_bounds([from, to], witness.len()) {
                return false;
            }
            let addr = witness[from];
            let to = witness[to];

            let addr = addr as usize;
            if out_of_bounds([addr], witness.len()) {
                return false;
            }

            let from = witness[addr];

            if from != to {
                return false;
            }
        }

        for constraint in membership_constraints {
            let SetMembershipConstraint { element, set } = *constraint;

            if out_of_bounds([element], witness.len()) {
                return false;
            }

            let element = &witness[element];

            if let Some(set) = sets.get(set) {
                if !set.contains(element) {
                    return false;
                }
            } else {
                return false;
            }
        }

        // Enforces that selected cells are naturals.
        for address in sign_constraints {
            if out_of_bounds([*address], witness.len()) {
                return false;
            }

            let value = witness[*address];
            if value < 0 {
                return false;
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
    let rows: usize = 3;
    let columns: usize = 5;

    let column_constraint = |i| Gate {
        a: i * rows,
        b: i * rows + 1,
        c: i * rows + 2,
        ty: GateType::Add,
    };

    let column_copy_constaint = |i| Gate {
        a: i * rows,
        // next column, last row.
        b: i * rows + rows + 2,
        c: 0,
        ty: GateType::Eq,
    };

    // We create the structure once.
    let structure: ZkFolStructure = ZkFolStructure {
        witness_len: rows * columns,
        arithmetic_constraints: (0..columns)
            .map(column_constraint)
            .chain((0..columns).map(column_copy_constaint))
            .collect(),
        reads: vec![],
        sets: vec![],
        membership_constraints: vec![],
        sign_constraints: vec![],
    };

    // We can now instanciate a prover and verifier for this structure.
    // This process may be expensive (a few seconds) but is a one-time
    // cost. Due to that you want to move as much as possible from the
    // instance to the witness, while keeping the structure general
    // enough to work for all your instances.
    let prover = Prover::<F, S, ZkFol, (), R>::new(&structure);
    let verifier = Verifier::<F, S, ZkFol, (), R>::new(&structure);

    // Now, if we have a witness.
    let witness: Vec<i64> = Vec::default();
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
