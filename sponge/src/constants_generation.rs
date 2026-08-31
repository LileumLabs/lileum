use crate::grain::Grain;
use alloc::vec::Vec;
use ark_ff::{BigInteger, PrimeField};
use automata::FiniteAutomaton;
use core::{cmp::Ordering, marker::PhantomData};

pub enum Field {
    Prime,
    //TODO: support
    #[allow(unused)]
    Extension,
}
pub enum Sbox {
    Positive,
    //TODO: support
    #[allow(unused)]
    Negative,
}
pub struct PoseidonEncoding {
    pub field: Field,
    pub sbox: Sbox,
    /// field bits
    pub n: u16,
    /// state width
    pub t: u16,
    pub full_rounds: u16,
    pub partial_rounds: u16,
}

fn bound<const N: usize>(x: u16) {
    let max = 1 << N;
    assert!(x < max, "must not be more than {} bits", N);
}

impl PoseidonEncoding {
    fn into_init(self) -> (u64, u16) {
        let mut low = 0u64;
        let Self {
            field,
            sbox,
            n,
            t,
            full_rounds,
            partial_rounds,
        } = self;
        bound::<12>(n);
        bound::<12>(t);
        bound::<10>(full_rounds);
        bound::<10>(partial_rounds);

        let mut write = |x: u16, n| {
            // to be consistent with the sage script which seems to write integers
            // as big endian
            let x = x.reverse_bits() >> (16 - n);
            low <<= n;
            low |= x as u64;
        };
        write(partial_rounds, 10);
        write(full_rounds, 10);
        write(t, 12);
        write(n, 12);
        let sbox = match sbox {
            Sbox::Positive => 0,
            Sbox::Negative => 1,
        };
        write(sbox, 4);
        let field = match field {
            Field::Prime => 1,
            Field::Extension => 0,
        };
        write(field, 2);
        //pad with 1s
        let padding = u64::MAX << 50;
        low |= padding;
        // Grain::new(low, u16::MAX)
        (low, u16::MAX)
    }
}
/*struct PoseidonEncoding {
    //0..3
    field: [bool; 2],
    //3..6
    sbox: [bool; 4],
    //6..18
    n: [bool; 12],
    //18..30
    t: [bool; 12],
    //30..40
    rf: [bool; 10],
    //40..50
    rp: [bool; 10],
    //50..80 set to 1
}*/

/// Produces bits in pairs, outputting the second if the first is 1,
/// discarding otherwise, and repeating until having an output.
struct BitMachine {
    grain: Grain,
}
impl FiniteAutomaton for BitMachine {
    type Init = PoseidonEncoding;

    type State = Grain;

    type Input = ();

    type Output = bool;

    fn init(init: Self::Init) -> Self {
        let init = init.into_init();
        let mut grain = Grain::init(init);
        // discard first 160
        for _ in 0..160 {
            let _ = grain.transition_mut(());
        }
        BitMachine { grain }
    }

    fn transition_mut(&mut self, _input: Self::Input) -> Self::Output {
        loop {
            let first = self.grain.transition_mut(());
            let second = self.grain.transition_mut(());
            if first {
                return second;
            }
        }
    }
}

/// Generates enough bits for a field element, discading them if the
/// value is not smaller than the given prime, returning it otherwise.
struct FieldMachine {
    bit_machine: BitMachine,
    /// big endian
    // TODO: number of bits to generate may not be implicit in the size
    // of the prime
    prime: Vec<bool>,
}

impl FieldMachine {
    fn try_field(&mut self) -> Option<Vec<bool>> {
        let len = self.prime.len();
        let mut bits = Vec::with_capacity(len);
        let mut ordering = Ordering::Equal;
        for i in 0..len {
            let bit = self.bit_machine.transition_mut(());
            let bit_order = self.prime[i].cmp(&bit);
            bits.push(bit);
            ordering = ordering.then(bit_order);
        }
        match ordering {
            Ordering::Greater => Some(bits),
            _ => None,
        }
    }
}

impl FiniteAutomaton for FieldMachine {
    type Init = (PoseidonEncoding, Vec<bool>);

    type State = ();

    type Input = ();

    type Output = Vec<bool>;

    fn init(init: Self::Init) -> Self {
        let (init, prime) = init;
        let bit_machine = BitMachine::init(init);
        FieldMachine { bit_machine, prime }
    }

    fn transition_mut(&mut self, _input: Self::Input) -> Self::Output {
        loop {
            if let Some(x) = self.try_field() {
                return x;
            }
        }
    }
}

/// parse hex string into bits
#[cfg(test)]
pub fn parse_field(string: &str) -> Vec<bool> {
    string
        .chars()
        .flat_map(|char| {
            let byte = char.to_digit(16).unwrap();
            alloc::vec![
                byte & 0b1000 != 0,
                byte & 0b0100 != 0,
                byte & 0b0010 != 0,
                byte & 0b0001 != 0,
            ]
        })
        .collect()
}

// comparing against the last constant produced by
// sage generate_params_poseidon.sage 1 0 252 3 3 128 0x800000000000011000000000000000000000000000000000000000000000001
#[test]
fn constant_generator() {
    let instance = PoseidonEncoding {
        field: Field::Prime,
        sbox: Sbox::Positive,
        n: 252,
        t: 3,
        full_rounds: 8,
        partial_rounds: 83,
    };
    let field = "800000000000011000000000000000000000000000000000000000000000001";
    let field = parse_field(field);

    // println!("len: {}", field.len());

    let init = (instance, field);
    let mut generator = FieldMachine::init(init);

    for i in 0..280 {
        let field = generator.transition_mut(());
        if i == 272 {
            // print_integer_big_endian(&field);
            // last constant generated by the script
            let compare = "7d0557a56ef4ca1ebf374e3e552e0a5f47f0b4cd0babe352c573bac0919535f";
            let compare = parse_field(compare);
            assert_eq!(compare, field);
        }
    }
}

pub struct ConstantGenerator<F: PrimeField> {
    machine: FieldMachine,
    _f: PhantomData<F>,
}

impl<F: PrimeField> ConstantGenerator<F> {
    pub fn new(t: u16, full_rounds: u16, partial_rounds: u16) -> Self {
        let field = Field::Prime;
        let n = F::MODULUS_BIT_SIZE;
        let n: u16 = n.try_into().unwrap();

        let encoding = PoseidonEncoding {
            field,
            //TODO:support the negative one
            sbox: Sbox::Positive,
            n,
            t,
            full_rounds,
            partial_rounds,
        };
        // Removes leading zeros as to_bits_be pads to the limb size.
        let bits: Vec<bool> = (F::MODULUS)
            .to_bits_be()
            .into_iter()
            .skip_while(|b| !b)
            .collect();
        assert_eq!(bits.len(), n as usize);
        let init = (encoding, bits);
        let machine = FieldMachine::init(init);
        Self {
            machine,
            _f: PhantomData,
        }
    }
    pub fn constant(&mut self) -> F {
        let bits = self.machine.transition_mut(());
        //shouldn't fail
        F::from_bigint(F::BigInt::from_bits_be(&bits)).unwrap()
    }
}
