#![no_std]
extern crate alloc;
#[cfg(test)]
extern crate std;

mod argument;
pub mod circuit_builder;
mod gates;
mod key;

pub mod parsers {
    lalrpop_util::lalrpop_mod!(a1_parser);
    pub use a1_parser::{A1CellParser, A1RangeParser};
}

pub use argument::SpreadsheetRelation;
pub use key::SpreadsheetKey;
