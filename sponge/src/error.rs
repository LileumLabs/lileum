use crate::sponge::Pattern;
use alloc::{boxed::Box, fmt::Write, string::String, vec::Vec};

#[derive(Debug, Clone)]
pub enum Error {
    /// attempted to squeeze an element before any previous absorb
    SqueezeBeforeAbsorb,
    /// attempted to squeeze or abosorb more elements than expected
    PatternOutOfBound,
    /// attempt to absorb when squeeze was expected
    UnexpectedAbsorb,
    /// attempt to squeeze when absorb was expected
    UnexpectedSqueeze,
    /// unexpected pattern on finish
    FinishMismatch(Box<Mismatch>),
}

#[derive(Clone)]
pub struct Mismatch {
    expected: Vec<Pattern>,
    found: Vec<Pattern>,
}

impl core::fmt::Debug for Mismatch {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let expected = Mismatch::debug_pattern(&self.expected)?;
        let found = Mismatch::debug_pattern(&self.found)?;
        f.debug_struct("Mismatch")
            .field("expected", &expected)
            .field("found   ", &found)
            .finish()
    }
}

impl Mismatch {
    pub(crate) fn new(expected: Vec<Pattern>, found: Vec<Pattern>) -> Self {
        Self { expected, found }
    }
    fn debug_pattern(pattern: &[Pattern]) -> Result<String, core::fmt::Error> {
        let mut string = String::new();
        for p in pattern {
            match p {
                Pattern::Absorb(n) => {
                    write!(&mut string, "A{:02} ", n)?;
                }
                Pattern::Squeeze(n) => {
                    write!(&mut string, "S{:02} ", n)?;
                }
            }
        }
        Ok(string)
    }
}
