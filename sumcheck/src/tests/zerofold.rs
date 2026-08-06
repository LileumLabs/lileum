use super::Poseidon;
use crate::{
    evals::{Evals, EvalsCore},
    folding::ZeroFold,
    oracles::{
        testing::{TestingNature, TestingOracle},
        SumcheckFunction,
    },
    zerocheck::{ZeroSumcheck, Zerocheck, ZerocheckReduction},
    Var,
};
use ark_ff::{Field, PrimeField};
use rand::{rngs::StdRng, SeedableRng};
use std::{fmt::Debug, vec::IntoIter};
use sumcheck_derive::EvalsCore;
use transcript::{FoldingRelation, Prover, ProverOutput, Relation, Verifier};

// As the folding scheme is [ZeroSumcheck;2] -> ZeroSumcheck, but we start
// with [Zerocheck;2], we need first to reduce [Zerocheck;2] -> [ZeroSumcheck;2].
type Reduction1<F> = ZerocheckReduction<F, TestingOracle<F, ProductGate<()>>>;

type FoldingScheme<F> = ZeroFold<F, TestingOracle<F, ProductGate<()>>>;

const VARS: usize = 4;

fn product_zerofold_test<F: PrimeField>() {
    let oracle = TestingOracle::new(VARS, ());

    let verifier = Verifier::<F, Poseidon<F>, _, _, Reduction1<F>>::new(&oracle);

    let mut rng = StdRng::seed_from_u64(0);
    let mut witness = |_| {
        let a = F::rand(&mut rng);
        let b = F::rand(&mut rng);
        let c = a * b;
        ProductGate { factors: [a, b, c] }
    };
    let witness1: Vec<ProductGate<F>> = (0..(1 << VARS)).map(&mut witness).collect();
    let witness2: Vec<ProductGate<F>> = (0..(1 << VARS)).map(witness).collect();

    // Two oracle instances of the TestingOracle, which are just ().
    let instances = [(); 2];
    assert!(Zerocheck::check(&oracle, &(), &witness1));
    assert!(Zerocheck::check(&oracle, &(), &witness2));

    let instances = instances.map(|instance| verifier.verify(instance, ()).unwrap());

    // They each individually belong to ZeroSumcheck.
    assert!(ZeroSumcheck::check(&oracle, &instances[0], &witness1));
    assert!(ZeroSumcheck::check(&oracle, &instances[1], &witness2));

    let witnesses = [witness1, witness2];

    // And by extension the 2 together belong to FoldingRelation<ZeroSumcheck> too.
    assert!(FoldingRelation::<ZeroSumcheck<F, _>>::check(
        &oracle, &instances, &witnesses
    ));

    // Now we create a folding prover and verifier.
    let prover = Prover::<F, Poseidon<F>, _, _, FoldingScheme<F>>::new(&oracle);
    let verifier = Verifier::<F, Poseidon<F>, _, _, FoldingScheme<F>>::new(&oracle);

    let ProverOutput {
        instance: prover_instance,
        witness,
        proof,
    } = prover.prove(instances.clone(), witnesses);

    // From 2 ZeroSumcheck instance-witness pairs, we know have only 1 left.
    assert!(ZeroSumcheck::check(&oracle, &prover_instance, &witness));

    let verifier_instance = verifier.verify(instances, proof).unwrap();
    assert_eq!(prover_instance, verifier_instance);
}

#[derive(Clone, Copy, Debug, EvalsCore)]
struct ProductGate<V: Clone + Debug> {
    factors: [V; 3],
}

impl<F: Field> SumcheckFunction<F> for ProductGate<()> {
    type Natures = TestingNature;

    type Data = ();

    fn natures() -> Self::Mles<Self::Natures> {
        ProductGate {
            factors: [TestingNature; 3],
        }
    }

    fn function<V: Var<F> + Debug>(_: &(), evals: &Self::Mles<V>) -> V {
        let [a, b, c] = &evals.factors;
        a.clone() * b - c
    }
}

#[test]
fn product_zerofold() {
    use ark_vesta::Fr;
    product_zerofold_test::<Fr>();
}
