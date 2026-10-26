use reduction::Relation;
use std::ops::{Add, Mul, Sub};

/// This type will implement Relation, ROWS has been made a constant
/// for readability, but it could be done more flexible too.
pub struct ZkFol<const ROWS: usize = 100>;

/// A simple expression which will be used to define constraints.
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
pub struct Index<const ROWS: usize>(usize);

impl<const ROWS: usize> Index<ROWS> {
    pub fn new(x: usize) -> Self {
        assert!(x < ROWS);
        Self(x)
    }
}

/// An equality assertion between a cell in the current column
/// and another cell in the next column
pub struct CopyConstraint<const ROWS: usize> {
    pub current: Index<ROWS>,
    pub next: Index<ROWS>,
}

pub struct ZkFolStructure<const ROWS: usize> {
    pub arithmetic_constraints: Vec<Exp<Index<ROWS>>>,
    pub copy_constraints: Vec<CopyConstraint<ROWS>>,
}

impl<const ROWS: usize> Relation for ZkFol<ROWS> {
    type Structure = ZkFolStructure<ROWS>;

    type Instance = ();

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

        // Enforce copy constrait between each column and its next column,
        // expect for the last one, which doesn't have a next.
        for [current, next] in witness.array_windows::<2>() {
            for constraint in copy_constraints {
                let current = current[constraint.current.0];
                let next = next[constraint.next.0];
                if current != next {
                    return false;
                }
            }
        }

        true
    }
}
