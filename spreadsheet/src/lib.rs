#![no_std]
extern crate alloc;
#[cfg(test)]
extern crate std;

mod argument;
pub mod circuit_builder;
mod gates;
mod key;

pub use argument::{Proof, SpreadsheetRelation};
pub use key::SpreadsheetKey;

pub mod parsing;
