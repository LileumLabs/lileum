use crate::spark3::{
    SparkInstance, SparkReduction, SparseMle, StaticSparkRelation, StaticSparkStructure,
};
use ark_ff::PrimeField;
use commit::commit2::{CommitmentScheme, OpeningRelation};
use hash_to_curve::svdw::SvdwMap;
use rand::{rngs::StdRng, SeedableRng};
use sponge::{poseidon2::PoseidonDefault, sponge::Sponge};
use std::{iter::repeat, rc::Rc};
use sumcheck::polynomials::MultiPoint;
use transcript::reduction2::{Prover, ProverOutput, Relation, Verifier};

type Poseidon<F> = Sponge<F, PoseidonDefault<F>, 2, 1, 3>;

const VARS: usize = 8;

fn single_dimension_test<F, C>()
where
    F: PrimeField,
    C: CommitmentScheme<F>,
{
    let mut rng = StdRng::seed_from_u64(0);

    // let addresses: Vec<[u8; 1]> = repeat(()).map(|_| [rng.gen()]).take(1 << VARS).collect();
    let addresses: Vec<[u8; 1]> = repeat(())
        .enumerate()
        .map(|(i, _)| [i as u8])
        .take(1 << VARS)
        .collect();
    let values: Vec<F> = repeat(())
        .map(|_| F::rand(&mut rng))
        .take(1 << VARS)
        .collect();
    let mle = Rc::new(SparseMle::new(addresses, values));
    let mle = StaticSparkStructure { mle: mle.clone() };

    let pcs = C::new(VARS);
    let prover = Prover::<F, Poseidon<F>, _, _, SparkReduction<F, C, 1>>::new(&mle, &pcs, VARS);
    let verifier = Verifier::<F, Poseidon<F>, _, _, SparkReduction<F, C, 1>>::new(&mle, &pcs, VARS);

    let point = [(); VARS].map(|_| F::rand(&mut rng)).to_vec();
    let point = MultiPoint::new(point);

    let eval = mle.mle.eval(&point);

    let instance = SparkInstance::new(point, eval);

    assert!(StaticSparkRelation::check(&mle, &instance, &()));

    let ProverOutput {
        instance: open_instance,
        witness,
        proof,
    } = prover.prove(instance.clone(), ());

    assert!(OpeningRelation::check(&pcs, &open_instance, &witness));

    let verifier_instance = verifier.verify(instance, proof).unwrap();

    assert_eq!(open_instance, verifier_instance);
}

#[test]
fn single_dimension() {
    use ark_vesta::{Fr, Projective, VestaConfig};
    use commit::ipa2::IpaCommitmentScheme;
    // pub type FrScheme = IpaCommitmentScheme<Fr, Projective, SvdwMap<VestaConfig>>;
    type Scheme = IpaCommitmentScheme<Fr, Projective, SvdwMap<VestaConfig>>;
    single_dimension_test::<Fr, Scheme>();
}
