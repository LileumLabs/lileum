use ark_ff::Field;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub};

pub trait Var<F: Field>:
    Sized
    + Add<Self, Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + Sub<Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + Mul<Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + Add<F, Output = Self>
    + Sub<F, Output = Self>
    + Mul<F, Output = Self>
    + for<'a> AddAssign<&'a Self>
    + MulAssign<F>
    + Clone
{
}
