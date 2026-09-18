pub use a1_parser::{
    A1AreaParser, A1CellParser, A1ColumnParser, A1ReferenceParser, A1RowParser, AtoDParser,
    AtoWParser, SingleSheetReferenceParser,
};

lalrpop_util::lalrpop_mod!(pub a1_parser);

pub fn compose_column<const N: usize>(digits: [char; N]) -> u32 {
    let mut val = 0_u32;
    for digit in digits {
        val *= 26;
        val += (digit as u8 - b'A' + 1) as u32;
    }
    val -= 1;
    val
}

pub fn compose_decimal<I: Iterator<Item = u8>>(iter: I) -> u32 {
    let mut val = 0_u32;
    for digit in iter {
        val *= 10;
        val += digit as u32;
    }
    val
}

pub fn digit(char: &str) -> u8 {
    char.as_bytes()[0] - b'0'
}

pub type Arr2<T> = [T; 2];
pub type Arr3<T> = [T; 3];
pub type Arr4<T> = [T; 4];
// pub type Arr5<T> = [T; 5];

#[test]
fn parse() {
    use std::dbg;
    let input = "sheet1!AA2:C33";
    // let input = "A2:C3";
    // let input = "22";
    dbg!(input);
    let parsed = SingleSheetReferenceParser::new().parse(input);
    // let parsed = A1ReferenceParser::new().parse(input);
    // let parsed = A1AreaParser::new().parse(input);
    // let parsed = A1RowParser::new().parse(input);
    dbg!(parsed);
}
