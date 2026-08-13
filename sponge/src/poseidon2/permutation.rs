use crate::{
    constants_generation::ConstantGenerator,
    permutation::Permutation,
    poseidon2::{internal_matrix::InternalMatrix3, small_pow},
};
use ark_ff::{Field, PrimeField};
use std::marker::PhantomData;

pub trait ExternalMatrix<F: Field, const N: usize> {
    fn apply(state: &mut [F; N]);
}
pub trait InternalMatrix<F: Field, const N: usize> {
    fn apply(state: &mut [F; N]);
}

/// Poseidon2 permutation
#[derive(Debug)]
pub struct PoseidonPermutation<
    F,
    const S: usize,
    // External matrix.
    E,
    // Internal matrix.
    I,
    // Half external rounds.
    const HER: usize,
    // Internal rounds.
    const IR: usize,
    // Sbox degree.
    const SBOX: u8,
> where
    F: Field,
    E: ExternalMatrix<F, S>,
    I: InternalMatrix<F, S>,
{
    _phantom: PhantomData<(F, E, I)>,
    external_first_half: [[F; S]; HER],
    internal_constants: [F; IR],
    external_second_half: [[F; S]; HER],
}

impl<
    F: Default,
    const S: usize,
    E: Default,
    I: Default,
    const HER: usize,
    const IR: usize,
    const SBOX: u8,
> Default for PoseidonPermutation<F, S, E, I, HER, IR, SBOX>
where
    F: Field,
    E: ExternalMatrix<F, S>,
    I: InternalMatrix<F, S>,
    F: PrimeField,
{
    fn default() -> Self {
        Self::new()
    }
}

pub type PoseidonDefault<F> = PoseidonPermutation<F, 3, InternalMatrix3, InternalMatrix3, 4, 40, 7>;

impl<F, const S: usize, E, I, const HER: usize, const IR: usize, const SBOX: u8>
    PoseidonPermutation<F, S, E, I, HER, IR, SBOX>
where
    F: Field,
    E: ExternalMatrix<F, S>,
    I: InternalMatrix<F, S>,
{
    pub fn new() -> Self
    where
        F: PrimeField,
    {
        let mut constant_generator =
            ConstantGenerator::<F>::new(S as u16, (HER * 2) as u16, IR as u16);
        let external_first_half = [(); HER].map(|_| [(); S].map(|_| constant_generator.constant()));
        let internal_constants = [(); IR].map(|_| constant_generator.constant());
        let external_second_half =
            [(); HER].map(|_| [(); S].map(|_| constant_generator.constant()));

        Self {
            _phantom: PhantomData,
            external_first_half,
            internal_constants,
            external_second_half,
        }
    }
    fn sbox(state: &mut [F; S]) {
        for e in state {
            let elem: &mut F = e;
            *elem = small_pow::pow::<F, SBOX>(*elem);
        }
    }
    fn sbox_partial(state: &mut [F; S]) {
        state[0] = small_pow::pow::<F, SBOX>(state[0]);
    }
    fn add_constants(state: &mut [F; S], constants: &[F; S]) {
        for i in 0..S {
            state[i] += constants[i];
        }
    }
    pub fn apply(&self, state: &mut [F; S]) {
        for i in 0..HER {
            let constants = &self.external_first_half[i];
            Self::add_constants(state, constants);
            Self::sbox(state);
            E::apply(state);
        }
        for i in 0..IR {
            state[0] += self.internal_constants[i];
            Self::sbox_partial(state);
            I::apply(state);
        }
        for i in 0..HER {
            let constants = &self.external_second_half[i];
            Self::add_constants(state, constants);
            Self::sbox(state);
            E::apply(state);
        }
    }
}

impl<F, const S: usize, E, I, const HER: usize, const IR: usize, const SBOX: u8> Permutation<F, S>
    for PoseidonPermutation<F, S, E, I, HER, IR, SBOX>
where
    F: PrimeField,
    E: ExternalMatrix<F, S>,
    I: InternalMatrix<F, S>,
{
    fn new() -> Self {
        PoseidonPermutation::new()
    }

    fn permute_mut(&self, state: &mut [F; S]) {
        self.apply(state);
    }
}
