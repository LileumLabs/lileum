use crate::{
    circuit::Var,
    constraint_system::{ConstraintSystem, Constraints, Gate, Val},
};
use ark_ff::Field;

pub enum AddN<const IO: usize, const I: usize> {}

impl<const IO: usize, const I: usize> Gate<IO, I, 1> for AddN<IO, I> {
    fn gate<V: Val>(i: [V; I]) -> [V; 1] {
        debug_assert_eq!(IO, I + 1);
        let mut sum = i[0].clone();
        for i in i.into_iter().skip(1) {
            sum = sum + i;
        }
        [sum]
    }

    fn check<V: Val>(i: [V; I], o: [V; 1]) -> Constraints<V> {
        debug_assert_eq!(IO, I + 1);
        let [out] = o;
        let mut sum = i[0].clone();
        for i in i.into_iter().skip(1) {
            sum = sum + i;
        }
        Constraints::from(sum - out)
    }
}

pub enum SubN<const IO: usize, const I: usize> {}

impl<const IO: usize, const I: usize> Gate<IO, I, 1> for SubN<IO, I> {
    fn gate<V: Val>(i: [V; I]) -> [V; 1] {
        debug_assert_eq!(IO, I + 1);
        let mut sub = i[0].clone();
        for i in i.into_iter().skip(1) {
            sub = sub - i;
        }
        [sub]
    }

    fn check<V: Val>(i: [V; I], o: [V; 1]) -> Constraints<V> {
        debug_assert_eq!(IO, I + 1);
        let [out] = o;
        let mut sub = i[0].clone();
        for i in i.into_iter().skip(1) {
            sub = sub - i;
        }
        Constraints::from(sub - out)
    }
}

pub enum MulN<const IO: usize, const I: usize> {}

impl<const IO: usize, const I: usize> Gate<IO, I, 1> for MulN<IO, I> {
    fn gate<V: Val>(i: [V; I]) -> [V; 1] {
        debug_assert_eq!(IO, I + 1);
        let mut product = i[0].clone();
        for i in i.into_iter().skip(1) {
            product = product * i;
        }
        [product]
    }

    fn check<V: Val>(i: [V; I], o: [V; 1]) -> Constraints<V> {
        debug_assert_eq!(IO, I + 1);
        let [out] = o;
        let mut product = i[0].clone();
        for i in i.into_iter().skip(1) {
            product = product * i;
        }
        Constraints::from(product - out)
    }
}

pub type Add2 = AddN<3, 2>;
pub type Sub2 = SubN<3, 2>;
pub type Mul2 = MulN<3, 2>;

pub enum Equality {}

impl Gate<2, 2, 0> for Equality {
    fn gate<V: Val>(_i: [V; 2]) -> [V; 0] {
        []
    }

    fn check<V: Val>(i: [V; 2], _o: [V; 0]) -> Constraints<V> {
        let [a, b] = i;
        Constraints::from(a - b)
    }
}

pub enum Zero {}

impl Gate<1, 1, 0> for Zero {
    fn gate<V: Val>(_i: [V; 1]) -> [V; 0] {
        []
    }

    fn check<V: Val>(i: [V; 1], _o: [V; 0]) -> Constraints<V> {
        let [x] = i;
        Constraints::from(x)
    }
}

pub enum Double {}

impl Gate<2, 1, 1> for Double {
    fn gate<V: Val>(i: [V; 1]) -> [V; 1] {
        let [x] = i;
        [x.clone() + x]
    }

    fn check<V: Val>(i: [V; 1], o: [V; 1]) -> Constraints<V> {
        let ([x], [expected]) = (i, o);
        let x2 = x.clone() + x;
        Constraints::from(x2 - expected)
    }
}

pub enum Square {}

impl Gate<2, 1, 1> for Square {
    fn gate<V: Val>(i: [V; 1]) -> [V; 1] {
        let [x] = i;
        [x.clone() * x]
    }

    fn check<V: Val>(i: [V; 1], o: [V; 1]) -> Constraints<V> {
        let ([x], [expected]) = (i, o);
        let xx = x.clone() * x;
        Constraints::from(xx - expected)
    }
}

pub enum Pow<const EXP: u8> {}

impl<const EXP: u8> Gate<2, 1, 1> for Pow<EXP> {
    fn gate<V: Val>(i: [V; 1]) -> [V; 1] {
        let [x] = i;
        let zeros = EXP.leading_zeros() as u8;

        let mut res = x.clone();
        for i in (zeros + 1)..8 {
            let bit = (EXP >> (7 - i)) & 0b1;
            res = res.clone() * res;
            if bit == 1 {
                res = res * x.clone();
            }
        }
        [res]
    }

    fn check<V: Val>(i: [V; 1], o: [V; 1]) -> Constraints<V> {
        let [x] = i;
        let zeros = EXP.leading_zeros() as u8;

        let mut res = x.clone();
        for i in (zeros + 1)..8 {
            let bit = (EXP >> (7 - i)) & 0b1;
            res = res.clone() * res;
            if bit == 1 {
                res = res * x.clone();
            }
        }
        let [power] = o;
        Constraints::from(res - power)
    }
}

/// Constraints the input to be either 0 or 1.
pub struct Binary;

impl Gate<1, 1, 0> for Binary {
    fn gate<V: Val>(_: [V; 1]) -> [V; 0] {
        []
    }

    fn check<V: Val>([x]: [V; 1], _: [V; 0]) -> Constraints<V> {
        // (x - 1) * (x - 0)
        // x^2 - x
        Constraints::from(x.clone() * x.clone() - x)
    }
}

/// Gate used to introduce constants to the circuit, it is handled
/// in a special way and it shouldn't be manually instantiated.
pub struct Constant;

impl Gate<1, 1, 0> for Constant {
    fn gate<V: Val>(_: [V; 1]) -> [V; 0] {
        []
    }

    fn check<V: Val>(_: [V; 1], _: [V; 0]) -> Constraints<V> {
        // This will be replaced by Exp::Constant
        Constraints::Empty
    }
}

//TODO: this requires constants
/*
/// Gate to enforce its only input is 0 or 1.
pub enum Binary {}

impl Gate<1, 1, 0> for Binary {
    fn gate<V: Val>(_i: [V; 1]) -> [V; 0] {
        todo!()
    }

    fn check<V: Val>(i: [V; 1], o: [V; 0]) -> Constraints<V> {
        todo!()
    }
}
*/

/// Trait providing easier use of standard gates, implemented for any `ConstraintSystem`.
pub trait StandardGates<F, V> {
    /// Makes use of `Add2`
    fn add(&mut self, a: Var<V>, b: Var<V>) -> Var<V>;
    /// Makes use of `AddN<IO,I>'
    fn add_n<const IO: usize, const I: usize>(&mut self, operands: [Var<V>; I]) -> Var<V>;
    /// Makes use of `Sub2`
    fn sub(&mut self, a: Var<V>, b: Var<V>) -> Var<V>;
    /// Makes use of `SubN<IO,I>'
    fn sub_n<const IO: usize, const I: usize>(&mut self, operands: [Var<V>; I]) -> Var<V>;
    /// Makes use of `Mul2`
    fn mul(&mut self, a: Var<V>, b: Var<V>) -> Var<V>;
    /// Makes use of `MulN<IO,I>'
    fn mul_n<const IO: usize, const I: usize>(&mut self, operands: [Var<V>; I]) -> Var<V>;
    /// Makes use of `Equality'
    fn assert_equals(&mut self, a: Var<V>, b: Var<V>);
    /// Makes use of `Double'
    fn double(&mut self, x: Var<V>) -> Var<V>;
    /// Makes use of `Square'
    fn square(&mut self, x: Var<V>) -> Var<V>;
    /// Makes use of `Pow<EXP>'
    fn pow<const EXP: u8>(&mut self, x: Var<V>) -> Var<V>;
}

impl<F, V, T> StandardGates<F, V> for T
where
    F: Field,
    T: ConstraintSystem<F, V>,
    V: Val,
{
    fn add(&mut self, a: Var<V>, b: Var<V>) -> Var<V> {
        let [res] = self.execute::<Add2, 3, 2, 1>([a, b]);
        res
    }

    fn add_n<const IO: usize, const I: usize>(&mut self, operands: [Var<V>; I]) -> Var<V> {
        let [res] = self.execute::<AddN<IO, I>, IO, I, 1>(operands);
        res
    }

    fn sub(&mut self, a: Var<V>, b: Var<V>) -> Var<V> {
        let [res] = self.execute::<Sub2, 3, 2, 1>([a, b]);
        res
    }

    fn sub_n<const IO: usize, const I: usize>(&mut self, operands: [Var<V>; I]) -> Var<V> {
        let [res] = self.execute::<SubN<IO, I>, IO, I, 1>(operands);
        res
    }

    fn mul(&mut self, a: Var<V>, b: Var<V>) -> Var<V> {
        let [res] = self.execute::<Mul2, 3, 2, 1>([a, b]);
        res
    }

    fn mul_n<const IO: usize, const I: usize>(&mut self, operands: [Var<V>; I]) -> Var<V> {
        let [res] = self.execute::<MulN<IO, I>, IO, I, 1>(operands);
        res
    }

    fn assert_equals(&mut self, a: Var<V>, b: Var<V>) {
        let _ = self.execute::<Equality, 2, 2, 0>([a, b]);
    }

    fn double(&mut self, x: Var<V>) -> Var<V> {
        let [res] = self.execute::<Double, 2, 1, 1>([x]);
        res
    }

    fn square(&mut self, x: Var<V>) -> Var<V> {
        let [res] = self.execute::<Square, 2, 1, 1>([x]);
        res
    }

    fn pow<const EXP: u8>(&mut self, x: Var<V>) -> Var<V> {
        let [res] = self.execute::<Pow<EXP>, 2, 1, 1>([x]);
        res
    }
}
