use super::Poseidon;
use crate::{
    SumcheckInstance, SumcheckReduction, Var,
    evals::{Evals, EvalsCore},
    oracles::{
        QueryRelation, SumcheckFunction,
        testing::{TestingNature, TestingOracle},
    },
};
use alloc::{
    fmt::Debug,
    vec::{IntoIter, Vec},
};
use ark_ff::{Field, PrimeField};
use rand::{SeedableRng, rngs::StdRng};
use reduction::{Prover, ProverOutput, Relation, Verifier};
use sumcheck_derive::EvalsCore;

/// The concrete reduction to be used in this test, being the SumcheckReduction
/// instanciated with the TestingOracle oracle over the ProductSum polynomial.
/// TestingOracle is an Oracle implementation that supports just plain dense
/// polynomials, something that isn't particularly useful for succinct reductions,
/// but is ideal for tests due to its simplicity.
type Sumcheck<F> = SumcheckReduction<F, TestingOracle<F, ProductSum<()>>>;

const VARS: usize = 4;
fn product_sumcheck_test<F: PrimeField>() {
    // We create an oracle, the structure of the Sumcheck reduction.
    let oracle = TestingOracle::new(VARS, ());

    // Create a prover for the SumcheckReduction, both relations have the same structure.
    let prover = Prover::<F, Poseidon<F>, _, _, Sumcheck<F>>::new(&oracle);
    // The verifier works the same.
    let verifier = Verifier::<F, Poseidon<F>, _, _, Sumcheck<F>>::new(&oracle);

    // Create a sample witness.
    let mut rng = StdRng::seed_from_u64(0);
    let witness: Vec<ProductSum<F>> = (0..(1 << VARS))
        .map(|_| {
            let factors: [F; 3] = [(); 3].map(|_| F::rand(&mut rng));
            ProductSum { factors }
        })
        .collect();

    // The expected sum.
    let sum: F = witness.iter().fold(F::ZERO, |acc, e| {
        let [a, b, c] = e.factors;
        acc + a * b * c
    });
    // A sumcheck instance is the expected sum and an instance of the underlying oracle.
    // In this case the oracle used (TestingOracle) as no instance.
    let sumcheck_instance = SumcheckInstance::new(sum, ());

    // prover.prove() takes an instance-witness in R1 pair and returns an
    // instance-witness pair in R2, plus a proof of the reduction.
    let ProverOutput {
        instance: query_instance,
        witness,
        proof,
    } = prover.prove(sumcheck_instance.clone(), witness);

    // We check that the resulting instance-witness pair is in R2.
    assert!(QueryRelation::check(&oracle, &query_instance, &witness));

    // verifier.verify() takes the same instance as prove(), but instead of
    // of the witness it takes the proof, and returns an instance on R2
    // or an error.
    let reduced = verifier.verify(sumcheck_instance, proof).unwrap();
    // As expected both prover and verifier should result in the same
    // instance.
    assert_eq!(reduced.eval, query_instance.eval);
    assert_eq!(reduced.point, query_instance.point);
}

#[derive(Clone, Copy, Debug, EvalsCore)]
/// The type that will define the polynomial over which sumcheck operates.
/// Sumcheck polynomials are defined as some function of multilinear polynomials,
/// or their multilinear extensions (MLEs) more specifically.
/// This type represents each individual multilinear extension, Evals and EvalsCore
/// derive a set of generic operations over this type.
struct ProductSum<V: Clone + Debug> {
    factors: [V; 3],
}

/// SumcheckFunction defines how the MLEs are combined into the arbitrary degree
/// polynomial to be used in sumcheck.
impl<F: Field> SumcheckFunction<F> for ProductSum<()> {
    // Each MLE can have a different nature, the nature defines relevant information
    // about the MLE that sumcheck will require.
    // In this case the Orale we use supports only this nature.
    type Natures = TestingNature;

    // Extra data to allow runtime configuration, not used in this case.
    type Data = ();

    // This function is to define the nature of each MLE, as there only 1
    // option available, there isn't much to choose.
    fn natures() -> Self::Mles<Self::Natures> {
        ProductSum {
            factors: [TestingNature; 3],
        }
    }

    // This is the definition of our polynomial as function of the individual
    // MLEs.
    // In this example we have for multilinear polynomials A, B and C the polynomial
    // f = A * B * C.
    // The unused parameter is Self::Data.
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
