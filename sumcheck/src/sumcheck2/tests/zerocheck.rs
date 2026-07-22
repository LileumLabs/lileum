use super::Poseidon;
use crate::{
    sumcheck::Var,
    sumcheck2::{
        evals::{Evals, EvalsCore},
        oracles::{
            partial::OracleParams,
            testing::{TestingNature, TestingOracle},
            Oracle, QueryRelation, SumcheckFunction,
        },
        zerocheck::{ZeroSumcheck, Zerocheck, ZerocheckReduction, ZerocheckSumcheckReduction},
    },
};
use ark_ff::{Field, PrimeField};
use std::{fmt::Debug, vec::IntoIter};
use sumcheck_derive::EvalsCore;
use transcript::reduction2::{Prover, ProverOutput, Relation, Verifier};

type Reduction1<F> = ZerocheckReduction<F, TestingOracle<F, ProductGate<()>>>;
type Reduction2<F> = ZerocheckSumcheckReduction<F, TestingOracle<F, ProductGate<()>>>;

const VARS: usize = 4;

// In this test we will make use of 2 reductions:
// ZerocheckReduction: Zerocheck -> ZeroSumcheck
// ZerocheckSumcheckReduction: ZeroSumcheck -> QueryRelation
// Remember that for normal sumcheck:
// SumcheckReduction: SumcheckRelation -> QueryRelation
fn product_zerocheck_test<F: PrimeField>() {
    let oracle = TestingOracle::new(VARS, ());
    let params = ();

    let prover1 = Prover::<F, Poseidon<F>, _, _, Reduction1<F>>::new(&oracle, &oracle, params);
    let verifier1 = Verifier::<F, Poseidon<F>, _, _, Reduction1<F>>::new(&oracle, &oracle, params);

    let witness = ProductGate {
        factors: [2_u8, 3, 6].map(F::from),
    };
    let witness = vec![witness; 1 << VARS];

    // The instance of zerocheck is just an instance of the corresponding oracle.
    // There is no sum like with a SumcheckInstance as the only valid sum is 0.
    let zerocheck_instance: <TestingOracle<F, ProductGate<()>> as Oracle<F>>::Instance = ();

    assert!(Zerocheck::check(&oracle, &zerocheck_instance, &witness));

    // ZerocheckReduction just samples some challenges and transforms the instance.
    // There is no communication and for that reason the proof is ().
    // For this reduction, the prover and verifier do essentially the same work.
    let ProverOutput {
        instance: zerosumcheck_instance,
        witness,
        proof,
    } = prover1.prove(zerocheck_instance, witness);

    // We check that the resulting instance-witness pair is in R2.
    assert!(ZeroSumcheck::check(
        &oracle,
        &zerosumcheck_instance,
        &witness
    ));

    let reduced = verifier1.verify(zerocheck_instance, proof).unwrap();
    assert_eq!(reduced, zerosumcheck_instance);

    // Now the second reduction, which leaves use in a similar point to
    // sumcheck, with a instance in the QueryRelation.

    //TODO: The number of variables should likely be part of the structure
    // like with normal sumcheck.

    // The instance of the ZeroSumcheck relation does have params, it wants
    // to know how many variables your polynomial has.
    let params = (OracleParams { vars: VARS }, ());

    let prover2 = Prover::<F, Poseidon<F>, _, _, Reduction2<F>>::new(&oracle, &oracle, params);
    let verifier2 = Verifier::<F, Poseidon<F>, _, _, Reduction2<F>>::new(&oracle, &oracle, params);

    let ProverOutput {
        instance: query_instance,
        witness,
        proof,
    } = prover2.prove(zerosumcheck_instance.clone(), witness);

    assert!(QueryRelation::check(&oracle, &query_instance, &witness));

    let reduced = verifier2.verify(zerosumcheck_instance, proof).unwrap();

    assert_eq!(reduced, query_instance);
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
fn product_zerocheck() {
    use ark_vesta::Fr;
    product_zerocheck_test::<Fr>();
}
