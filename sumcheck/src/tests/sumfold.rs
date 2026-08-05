use super::Poseidon;
use crate::{
    evals::{Evals, EvalsCore},
    folding::SumFold,
    oracles::{
        testing::{TestingNature, TestingOracle},
        SumcheckFunction,
    },
    SumcheckInstance, SumcheckRelation, Var,
};
use ark_ff::{Field, PrimeField};
use rand::{rngs::StdRng, SeedableRng};
use std::{fmt::Debug, vec::IntoIter};
use sumcheck_derive::EvalsCore;
use transcript::reduction2::{FoldingRelation, Prover, ProverOutput, Relation, Verifier};

type FoldingScheme<F> = SumFold<F, TestingOracle<F, ProductSum<()>>>;

const VARS: usize = 4;

fn product_sumfold_test<F: PrimeField>() {
    let oracle = TestingOracle::new(VARS, ());

    let prover = Prover::<F, Poseidon<F>, _, _, FoldingScheme<F>>::new(&oracle);
    let verifer = Verifier::<F, Poseidon<F>, _, _, FoldingScheme<F>>::new(&oracle);

    let mut rng = StdRng::seed_from_u64(0);
    let mut witness = |_| {
        let factors: [F; 3] = [(); 3].map(|_| F::rand(&mut rng));
        ProductSum { factors }
    };
    let witness1: Vec<ProductSum<F>> = (0..(1 << VARS)).map(&mut witness).collect();
    let witness2: Vec<ProductSum<F>> = (0..(1 << VARS)).map(witness).collect();

    let sum = |acc: F, e: &ProductSum<F>| {
        let [a, b, c] = e.factors;
        acc + a * b * c
    };

    let sum1: F = witness1.iter().fold(F::ZERO, sum);
    let sum2: F = witness2.iter().fold(F::ZERO, sum);

    let witness = [witness1, witness2];
    let instance = [sum1, sum2].map(|sum| SumcheckInstance::new(sum, ()));

    assert!(FoldingRelation::<SumcheckRelation<F, _>>::check(
        &oracle, &instance, &witness
    ));

    let ProverOutput {
        instance: sumcheck_instance,
        witness,
        proof,
    } = prover.prove(instance.clone(), witness);

    let reduced = verifer.verify(instance, proof).unwrap();

    assert!(SumcheckRelation::check(
        &oracle,
        &sumcheck_instance,
        &witness
    ));

    assert_eq!(sumcheck_instance.sum, reduced.sum);
}

#[derive(Clone, Copy, Debug, EvalsCore)]
struct ProductSum<V: Clone + Debug> {
    factors: [V; 3],
}

impl<F: Field> SumcheckFunction<F> for ProductSum<()> {
    type Natures = TestingNature;

    type Data = ();

    fn natures() -> Self::Mles<Self::Natures> {
        ProductSum {
            factors: [TestingNature; 3],
        }
    }

    fn function<V: Var<F> + Debug>(_: &(), evals: &Self::Mles<V>) -> V {
        let [a, b, c] = &evals.factors;
        a.clone() * b * c
    }
}

#[test]
fn product_sumfold() {
    use ark_vesta::Fr;
    product_sumfold_test::<Fr>();
}
