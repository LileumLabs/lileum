use crate::{
    error::{Error, Mismatch},
    permutation::{Permutation, UnsafePermutation},
};
use alloc::{boxed::Box, vec::Vec};
use ark_ff::{Field, PrimeField};
use core::{fmt::Display, marker::PhantomData};

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) enum Pattern {
    Absorb(u32),
    Squeeze(u32),
}

impl Display for Pattern {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Pattern::Absorb(n) => {
                write!(f, "A{}", n)
            }
            Pattern::Squeeze(n) => {
                write!(f, "S{}", n)
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct SpongeBuilder {
    pattern: Vec<Pattern>,
}

// duplex sponge
pub struct Sponge<F: Field, P: Permutation<F, T>, const R: usize, const C: usize, const T: usize> {
    pattern: Vec<Pattern>,
    running_pattern: Vec<Pattern>,
    permutation: P,
    state: [F; T],
    absorb_pos: usize,
    squeeze_pos: usize,
    /// disables check on each absorb/squeeze
    disable_check: bool,
}

/// Initial state to instantiate sponges with
pub struct SpongeInitializer<
    F: Field,
    P: Permutation<F, T>,
    const R: usize,
    const C: usize,
    const T: usize,
> {
    pattern: Vec<Pattern>,
    state: [F; T],
    _permutation: PhantomData<P>,
}

impl SpongeBuilder {
    pub fn new() -> Self {
        Self {
            pattern: Vec::new(),
        }
    }
    pub fn absorb(self, elements: u32) -> Self {
        assert!(elements <= (u32::MAX >> 1), "can absorb at most 2^31 - 1");
        let Self { mut pattern } = self;
        pattern.push(Pattern::Absorb(elements));
        Self { pattern }
    }
    pub fn squeeze(self, elements: u32) -> Self {
        assert!(elements <= (u32::MAX >> 1), "can squeeze at most 2^31 - 1");
        let Self { mut pattern } = self;
        pattern.push(Pattern::Squeeze(elements));
        Self { pattern }
    }
    fn pack_pattern(pattern: Vec<Pattern>) -> Vec<Pattern> {
        let mut packed_pattern = Vec::with_capacity(pattern.len());
        for pattern in pattern.into_iter() {
            match pattern {
                Pattern::Absorb(n) | Pattern::Squeeze(n) => {
                    if n == 0 {
                        continue;
                    }
                }
            }
            let top = packed_pattern.pop();
            match (top, pattern) {
                (None, p @ Pattern::Absorb(_)) | (None, p @ Pattern::Squeeze(_)) => {
                    packed_pattern.push(p);
                }
                (Some(Pattern::Absorb(n1)), Pattern::Absorb(n2)) => {
                    packed_pattern.push(Pattern::Absorb(n1 + n2));
                }
                (Some(p1 @ Pattern::Squeeze(_)), p2 @ Pattern::Absorb(_)) => {
                    packed_pattern.push(p1);
                    packed_pattern.push(p2);
                }
                (Some(Pattern::Squeeze(n1)), Pattern::Squeeze(n2)) => {
                    packed_pattern.push(Pattern::Squeeze(n1 + n2));
                }
                (Some(p1 @ Pattern::Absorb(_)), p2 @ Pattern::Squeeze(_)) => {
                    packed_pattern.push(p1);
                    packed_pattern.push(p2);
                }
            }
        }
        packed_pattern
    }
    fn encode_iv<F: Field>(pattern: &[Pattern]) -> Vec<F> {
        let base_field_bits = <F::BasePrimeField as PrimeField>::MODULUS_BIT_SIZE;
        let bits = base_field_bits + F::extension_degree() as u32;
        let mut elems = Vec::new();
        for phase in pattern.iter() {
            let msb: u32 = 0x80_00_00_00;
            let int = match phase {
                Pattern::Absorb(n) => {
                    assert!(n < &msb);
                    n | msb
                }
                Pattern::Squeeze(n) => {
                    assert!(n < &msb);
                    *n
                }
            };
            //TODO: should handle all cases but could be more optimal
            if bits > 32 {
                elems.push(F::from(int));
            } else {
                let bytes = int.to_le_bytes();
                for byte in bytes {
                    elems.push(F::from(byte));
                }
            }
        }
        elems
    }
    fn iv<F, P, const R: usize, const C: usize, const T: usize>(
        elems: &[F],
        permutation: &P,
    ) -> [F; T]
    where
        F: Field,
        P: Permutation<F, T>,
    {
        let mut state = [F::zero(); T];
        let n = F::from(elems.len() as u32);
        state[0] += n;
        let mut i = 1;
        for elem in elems.iter() {
            if i == R {
                permutation.permute_mut(&mut state);
                i = 0;
            }
            state[i] += elem;
            i += 1;
        }
        //permute
        permutation.permute_mut(&mut state);
        state
    }
    pub fn sponge<
        F: Field,
        P: Permutation<F, T>,
        const R: usize,
        const C: usize,
        const T: usize,
    >(
        self,
    ) -> SpongeInitializer<F, P, R, C, T> {
        let Self { pattern } = self;
        let permutation = P::new();
        let pattern = Self::pack_pattern(pattern);
        let elems = Self::encode_iv(&pattern);
        let state = Self::iv::<F, P, R, C, T>(&elems, &permutation);
        SpongeInitializer {
            pattern,
            state,
            _permutation: PhantomData,
        }
    }
}

impl<F, P, const R: usize, const C: usize, const T: usize> Drop for Sponge<F, P, R, C, T>
where
    F: Field,
    P: Permutation<F, T>,
{
    fn drop(&mut self) {
        assert_eq!(
            &self.pattern, &self.running_pattern,
            "sponge dropped with a partial or incorrect pattern"
        );

        // panic can be avoided for debugging
        // TODO: find a more debugging friendly approach.
        // if self.pattern != self.running_pattern {
        // println!("sponge dropped with a partial or incorrect pattern");
        // }
    }
}

impl<F, P, const R: usize, const C: usize, const T: usize> Sponge<F, P, R, C, T>
where
    F: Field,
    P: Permutation<F, T>,
{
    pub fn absorb(&mut self, elem: F) -> Result<(), Error> {
        assert_eq!(R + C, T);
        self.absorb_mode()?;
        self.check_pattern()?;

        if self.absorb_pos == R {
            self.permutation.permute_mut(&mut self.state);
            self.absorb_pos = 0;
        }
        self.state[self.absorb_pos] += elem;
        self.absorb_pos += 1;
        Ok(())
    }
    pub fn squeeze(&mut self) -> Result<F, Error> {
        assert_eq!(R + C, T);
        self.squeeze_mode()?;
        self.check_pattern()?;

        if self.squeeze_pos == R {
            self.permutation.permute_mut(&mut self.state);
            self.squeeze_pos = 0;
            self.absorb_pos = 0;
        }
        let squeezed = self.state[self.squeeze_pos];
        self.squeeze_pos += 1;
        Ok(squeezed)
    }
    fn absorb_mode(&mut self) -> Result<(), Error> {
        let current = self.running_pattern.pop();
        let i = self.running_pattern.len();
        let to_push = match current {
            Some(Pattern::Absorb(n)) => Pattern::Absorb(n + 1),
            Some(p @ Pattern::Squeeze(_)) => {
                if p != self.pattern[i] {
                    return Err(Error::UnexpectedAbsorb);
                }
                self.running_pattern.push(p);
                Pattern::Absorb(1)
            }
            None => Pattern::Absorb(1),
        };
        self.running_pattern.push(to_push);
        Ok(())
    }
    fn squeeze_mode(&mut self) -> Result<(), Error> {
        let current = self.running_pattern.pop();
        let i = self.running_pattern.len();
        let to_push = match current {
            Some(p @ Pattern::Absorb(_)) => {
                self.running_pattern.push(p);
                self.squeeze_pos = R;
                if p != self.pattern[i] {
                    return Err(Error::UnexpectedSqueeze);
                }
                Pattern::Squeeze(1)
            }
            Some(Pattern::Squeeze(n)) => Pattern::Squeeze(n + 1),
            None => {
                // Due to a lack of legit reasons to do this, it will be allowed
                // only for tests.
                cfg_select! {
                    //TODO: this may not be the ideal way to use it. It may be better
                    //to use a feature.
                    debug_assertions => {
                        self.squeeze_pos = R;
                        Pattern::Squeeze(1)
                    },
                    _ => {
                        // As I don't think there is any reason to start with squeezing.
                        return Err(Error::SqueezeBeforeAbsorb);
                    }
                }
            }
        };
        self.running_pattern.push(to_push);
        Ok(())
    }
    pub fn finish(mut self) -> Result<(), Error> {
        if self.pattern == self.running_pattern {
            Ok(())
        } else {
            let expected = self.pattern.clone();
            let found = self.running_pattern.clone();
            let error = Mismatch::new(expected, found);

            // so that it doesn't pannic when dropped
            self.running_pattern = self.pattern.clone();
            Err(Error::FinishMismatch(Box::new(error)))
        }
    }
    /// checks the patterns are compatible
    fn check_pattern(&self) -> Result<(), Error> {
        if self.disable_check {
            return Ok(());
        }
        let running_len = self.running_pattern.len();
        let i = running_len - 1;
        match (&self.running_pattern[i], &self.pattern[i]) {
            (Pattern::Absorb(running), Pattern::Absorb(pattern))
            | (Pattern::Squeeze(running), Pattern::Squeeze(pattern)) => {
                if running <= pattern {
                    Ok(())
                } else {
                    Err(Error::PatternOutOfBound)
                }
            }
            (Pattern::Absorb(_), Pattern::Squeeze(_)) => Err(Error::UnexpectedAbsorb),
            (Pattern::Squeeze(_), Pattern::Absorb(_)) => Err(Error::UnexpectedSqueeze),
        }
    }
}

/// High level duplex abstraction
pub trait Duplex<F: Field> {
    /// Intermediate type holding any expensive initialization
    type Initializer;
    /// Initializes a sponge for a given io pattern
    fn from_builder(builder: SpongeBuilder) -> Self::Initializer;
    /// Instanciates a sponge from the initializer
    fn instantiate(init: &Self::Initializer) -> Self;
    fn absorb(&mut self, elem: F) -> Result<(), Error>;
    fn squeeze(&mut self) -> Result<F, Error>;
    fn finish(self) -> Result<(), Error>;
    /// Prints the state, for debugging purposes.
    #[cfg(test)]
    fn print(&self);
}

impl<F, P, const R: usize, const C: usize, const T: usize> Duplex<F> for Sponge<F, P, R, C, T>
where
    F: Field,
    P: Permutation<F, T>,
{
    type Initializer = SpongeInitializer<F, P, R, C, T>;
    fn from_builder(builder: SpongeBuilder) -> Self::Initializer {
        builder.sponge()
    }

    fn instantiate(init: &Self::Initializer) -> Self {
        let pattern = init.pattern.clone();
        //TODO: avoiding this may prove desirable in the future
        let permutation = P::new();
        let state = init.state;
        Sponge {
            pattern,
            running_pattern: Vec::new(),
            permutation,
            state,
            absorb_pos: 0,
            squeeze_pos: 0,
            disable_check: false,
        }
    }

    fn absorb(&mut self, elem: F) -> Result<(), Error> {
        Sponge::absorb(self, elem)
    }

    fn squeeze(&mut self) -> Result<F, Error> {
        Sponge::squeeze(self)
    }

    fn finish(self) -> Result<(), Error> {
        Sponge::finish(self)
    }

    #[cfg(test)]
    fn print(&self) {
        std::println!("s: {:?}", self.state);
    }
}

pub struct UnsafeSponge<F: Field> {
    inner: Sponge<F, UnsafePermutation<F, 3>, 2, 1, 3>,
}

impl<F: Field> Duplex<F> for UnsafeSponge<F> {
    type Initializer = SpongeInitializer<F, UnsafePermutation<F, 3>, 2, 1, 3>;

    fn from_builder(builder: SpongeBuilder) -> Self::Initializer {
        Sponge::from_builder(builder)
    }

    fn instantiate(init: &Self::Initializer) -> Self {
        Self {
            inner: Sponge::instantiate(init),
        }
    }

    fn absorb(&mut self, elem: F) -> Result<(), Error> {
        self.inner.absorb(elem)
    }

    fn squeeze(&mut self) -> Result<F, Error> {
        self.inner.squeeze()
    }

    fn finish(self) -> Result<(), Error> {
        self.inner.finish()
    }

    #[cfg(test)]
    fn print(&self) {
        self.inner.print();
    }
}
