use super::Poseidon;
use crate::{
    Var,
    evals::{Evals, EvalsCore},
    folding::ZeroFold,
    oracles::{
        SumcheckFunction,
        testing::{TestingNature, TestingOracle},
    },
    zerocheck::{ZeroSumcheck, Zerocheck, ZerocheckReduction},
};
use alloc::{
    fmt::Debug,
    vec::{IntoIter, Vec},
};
use ark_ff::{Field, PrimeField};
use rand::{SeedableRng, rngs::StdRng};
use reduction::{FoldingRelation, Prover, ProverOutput, Relation, Verifier};
use sumcheck_derive::EvalsCore;

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

// ZeroSumcheckInstance claimed sum soundness test. A prover can forge the claimed sums
// of 2 folded instances and the folding verifier accepts a fold of two false instances.
//
// Attack: from an honest fold, proof(0) = s1 * (1 - beta) and proof(1) = s2 * beta, so beta can
// be recovered as proof(1)/s2. The verifier's only check on the input sums is the
// line (1 - beta) * T1 + beta * T2 == proof(0) + proof(1); we place forged sums T1' != s1,
// T2' != s2 on that line. Without the fix beta is independent of the sums, so the
// forged pair passes and the verifier accepts -> assertion fails (soundness issue caught).
// With the fix, absorbing the forged sums changes beta and the verifier rejects -> sound.
#[test]
fn zerofold_rejects_forged_input_sums() {
    use crate::{powers::CompactPowers, zerocheck::ZeroSumcheckInstance};
    use ark_ff::UniformRand;
    use ark_vesta::Fr;

    type Gate = ProductGate<Fr>;
    type Instance = ZeroSumcheckInstance<Fr, TestingOracle<Fr, ProductGate<()>>>;

    let oracle = TestingOracle::<Fr, ProductGate<()>>::new(VARS, ());

    // Arbitrary zerocheck challenge for the instances' powers
    let powers = CompactPowers::new(Fr::from(46u64), VARS);
    let domain_pows = powers.eval_over_domain();

    // Weighted hypercube sum_x f(w(x)) * beta^x with f(a,b,c) = a * b − c exactly the
    // quantity ZeroSumcheck::check compares against `sum`, in the same index order.
    let weighted_sum = |w: &Vec<Gate>| -> Fr {
        w.iter()
            .zip(&domain_pows)
            .map(|(g, p)| (g.factors[0] * g.factors[1] - g.factors[2]) * *p)
            .fold(Fr::from(0u64), |acc, x| acc + x)
    };

    // Random witnesses (doesn't satisfy the zerocheck) with their true weighted sums,
    // so both are genuine ZeroSumcheck instances the honest prover will fold.
    let mut rng = StdRng::seed_from_u64(1);
    let rand_witness = |rng: &mut StdRng| -> Vec<Gate> {
        (0..(1 << VARS))
            .map(|_| ProductGate {
                factors: [Fr::rand(rng), Fr::rand(rng), Fr::rand(rng)],
            })
            .collect()
    };
    let witness1 = rand_witness(&mut rng);
    let witness2 = rand_witness(&mut rng);
    let sum1 = weighted_sum(&witness1);
    let sum2 = weighted_sum(&witness2);

    let make = |sum: Fr| -> Instance {
        ZeroSumcheckInstance {
            sum,
            zerocheck_powers: powers.clone(),
            oracle_instance: (),
        }
    };
    let inst1 = make(sum1);
    let inst2 = make(sum2);
    assert!(ZeroSumcheck::check(&oracle, &inst1, &witness1));
    assert!(ZeroSumcheck::check(&oracle, &inst2, &witness2));

    let prover = Prover::<Fr, Poseidon<Fr>, _, _, FoldingScheme<Fr>>::new(&oracle);
    let verifier = Verifier::<Fr, Poseidon<Fr>, _, _, FoldingScheme<Fr>>::new(&oracle);

    // Honest fold; the honest instances verify (baseline)
    let ProverOutput { proof, .. } = prover.prove(
        [inst1.clone(), inst2.clone()],
        [witness1.clone(), witness2.clone()],
    );
    assert!(
        verifier.verify([inst1, inst2], proof.clone()).is_ok(),
        "sanity: the honest fold should verify"
    );

    // Recover beta from the honest message, then forge on-line sums
    let beta = proof.eval_at_1() * sum2.inverse().unwrap();
    let one_minus_beta = Fr::from(1u64) - beta;
    let delta = Fr::from(1u64);
    let t1 = sum1 + delta * beta * one_minus_beta.inverse().unwrap();
    let t2 = sum2 - delta;
    let forged1 = make(t1);
    let forged2 = make(t2);

    // The forged instances are false (their true weighted sums are sum1, ssum2 != t1, t2)
    assert!(!ZeroSumcheck::check(&oracle, &forged1, &witness1));
    assert!(!ZeroSumcheck::check(&oracle, &forged2, &witness2));

    // The verifier MUST reject the forged sums with the honest proof
    let res = verifier.verify([forged1, forged2], proof);
    assert!(
        res.is_err(),
        "soundness: folding verifier accepted two instances with forged claimed sums"
    );
}
