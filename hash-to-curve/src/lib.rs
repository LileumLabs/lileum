use ark_ec::CurveGroup;
use ark_serialize::CanonicalSerialize;
use std::fmt::Debug;

pub mod svdw;
pub trait CurveMap<G: CurveGroup>: Debug + Clone + CanonicalSerialize {
    fn new() -> Self;
    fn map_to_curve(&self, u: G::BaseField) -> G;
}
