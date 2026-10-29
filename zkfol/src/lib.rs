use ark_ff::Field;
use reduction::{Argument, Prover, Relation, Verifier};
use sponge::sponge::Duplex;
use std::ops::{Add, Mul, Sub};

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
        }
    }
}

impl<T: Add<Output = T> + Sub<Output = T> + Mul<Output = T>> Exp<T> {
    fn eval(self) -> T {
        match self {
            Exp::Add(x) => x.0.eval() + x.1.eval(),
            Exp::Sub(x) => x.0.eval() - x.1.eval(),
            Exp::Mul(x) => x.0.eval() * x.1.eval(),
            Exp::Var(x) => x,
        }
    }
}

/// An index to a particular row.
#[derive(Clone, Debug, Default)]
pub struct Index<const ROWS: usize>(usize);

impl<const ROWS: usize> Index<ROWS> {
    pub fn new(x: usize) -> Self {
        assert!(x < ROWS);
        Self(x)
    }
}

#[derive(Clone, Debug, Default)]
pub struct Cell<const ROWS: usize> {
    row: Index<ROWS>,
    column: usize,
}

/// An equality assertion between 2 arbitrary cells.
#[derive(Clone, Debug, Default)]
pub struct CopyConstraint<const ROWS: usize> {
    pub from: Cell<ROWS>,
    pub to: Cell<ROWS>,
}

#[derive(Clone, Debug)]
pub struct ZkFolStructure<const ROWS: usize = 100> {
    pub arithmetic_constraints: Vec<Exp<Index<ROWS>>>,
    pub copy_constraints: Vec<CopyConstraint<ROWS>>,
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
        } = structure;

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
            let from = witness[from.column][from.row.0];
            let to = witness[to.column][to.row.0];

            if from != to {
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
