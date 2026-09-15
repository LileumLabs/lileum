#![no_std]
extern crate alloc;
#[cfg(test)]
extern crate std;

mod argument;
pub mod circuit_builder;
mod gates;

lalrpop_util::lalrpop_mod!(a1_parser);

pub use argument::SpreadsheetRelation;
