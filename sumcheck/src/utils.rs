pub use test_field::Fm;

mod test_field {
    #![allow(non_local_definitions)]
    use ark_ff::{Fp64, MontBackend, MontConfig};

    #[derive(MontConfig)]
    #[modulus = "4294967291"]
    #[generator = "3"]
    pub struct M32Config;

    /// Small field based on the prime 2^31-1. Intended for testing
    /// as it is too small to be secure in most applications.
    pub type Fm = Fp64<MontBackend<M32Config, 1>>;
}
