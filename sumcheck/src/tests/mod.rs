use sponge::{poseidon2::PoseidonDefault, sponge::Sponge};

/// A sponge with rate 2 and capacity 1 over the poseidon2 permutation.
type Poseidon<F> = Sponge<F, PoseidonDefault<F>, 2, 1, 3>;

mod composite;
mod sum_of_products;
mod sumfold;
mod zerocheck;
mod zerofold;
