use crate::{
    sumcheck::Var,
    sumcheck2::{
        evals::{Evals, EvalsCore},
        oracles::{
            testing::{TestingNature, TestingOracle},
            QueryRelation, SumcheckFunction,
        },
        SumcheckInstance, SumcheckReduction,
    },
};
use ark_ff::{Field, PrimeField};
use sponge::{poseidon2::PoseidonDefault, sponge::Sponge};
use std::{fmt::Debug, vec::IntoIter};
use sumcheck_derive::EvalsCore;
use transcript::reduction2::{Prover, ProverOutput, Relation, Verifier};

type Poseidon<F> = Sponge<F, PoseidonDefault<F>, 2, 1, 3>;
type Sumcheck<F> = SumcheckReduction<F, TestingOracle<F, ProductSum<()>>>;

const VARS: usize = 4;
fn product_sumcheck_test<F: PrimeField>() {
    let oracle = TestingOracle::new(VARS, ());
    let params = ();
    let prover = Prover::<F, Poseidon<F>, _, _, Sumcheck<F>>::new(&oracle, &oracle, params);
    let verifier = Verifier::<F, Poseidon<F>, _, _, Sumcheck<F>>::new(&oracle, &oracle, params);

    let witness = ProductSum {
        factors: [2_u8, 3, 5].map(F::from),
    };
    let witness = vec![witness; 1 << VARS];

    let sum: u64 = (2 * 3 * 5) * (1 << VARS);
    let sumcheck_instance = SumcheckInstance::new(F::from(sum), ());

    let ProverOutput {
        instance: query_instance,
        witness,
        proof,
    } = prover.prove(sumcheck_instance.clone(), witness);

    assert!(QueryRelation::check(&oracle, &query_instance, &witness));

    let reduced = verifier.verify(sumcheck_instance, proof).unwrap();
    assert_eq!(reduced.eval, query_instance.eval);
    assert_eq!(reduced.point, query_instance.point);
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
fn product_sumcheck() {
    use ark_vesta::Fr;
    product_sumcheck_test::<Fr>();
}
