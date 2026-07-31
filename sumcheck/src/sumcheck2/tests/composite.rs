use super::Poseidon;
use crate::{
    polynomials::MultiPoint,
    sumcheck::Var,
    sumcheck2::{
        evals::{Evals, EvalsCore},
        oracles::{
            composite::{CompositeOracle, CompositeOracleInstance, Either},
            core::{Coeffs, CoreNature, CoreOracle, CoreOracleInstance, CoreQueryRelation},
            empty::{EmptyInstance, EmptyRelation, NoNature},
            partial::PartialQueryRelation,
            QueryRelation, SumcheckFunction,
        },
        SumcheckInstance, SumcheckReduction, SumcheckRelation,
    },
};
use ark_ff::{Field, PrimeField};
use rand::{rngs::StdRng, SeedableRng};
use std::{fmt::Debug, iter::successors, rc::Rc, vec::IntoIter};
use sumcheck_derive::EvalsCore;
use transcript::reduction2::{Prover, ProverOutput, Relation, UnsafeVerifier, Verifier};

type Oracle<F, SF = SmallEvals<()>> = CompositeOracle<F, SF, CoreOracle<F, SF>, ()>;
type Sumcheck<F> = SumcheckReduction<F, Oracle<F>>;

const VARS: usize = 4;

fn composite_sumcheck_test<F: PrimeField>() {
    let structure = (0..(1 << VARS))
        .map(|i: u64| SmallEvals {
            challenge: F::ZERO,
            powers: F::ZERO,
            range: F::from(i),
        })
        .collect();
    let structure: Rc<Vec<SmallEvals<F>>> = Rc::new(structure);

    let core_oracle = CoreOracle::new(SmallEvals {
        challenge: None,
        powers: Some(eval_powers as fn(&[F], &MultiPoint<F>) -> F),
        range: Some(eval_range),
    });
    let oracle: Oracle<F> = Oracle::new((), structure.clone(), core_oracle, ());

    // Create a prover for the SumcheckReduction, both relations have the same structure.
    let prover = Prover::<F, Poseidon<F>, _, _, Sumcheck<F>>::new(&oracle, &oracle);
    // The verifier works the same.
    let verifier = Verifier::<F, Poseidon<F>, _, _, Sumcheck<F>>::new(&oracle, &oracle);

    let mut rng = StdRng::seed_from_u64(0);

    let chall = F::rand(&mut rng);
    let chall2 = F::rand(&mut rng);
    let powers = successors(Some(chall2), |x| Some(x.square()))
        .take(4)
        .collect::<Vec<F>>();

    let witness: Vec<SmallEvals<F>> = structure
        .iter()
        .enumerate()
        .map(|(i, eval)| {
            let range = eval.range;
            let point = MultiPoint::new_from_index(i, VARS);
            let challenge = chall;
            let powers = eval_powers(&powers, &point);
            SmallEvals {
                challenge,
                powers,
                range,
            }
        })
        .collect();

    let core_instance = CoreOracleInstance::<F, SmallEvals<()>>::new(
        &SmallEvals {
            challenge: vec![chall],
            powers,
            range: vec![],
        },
        VARS,
    );

    let oracle_instance = CompositeOracleInstance {
        oracle1_instance: core_instance,
        oracle2_instance: EmptyInstance,
    };

    let sum = witness.iter().fold(F::ZERO, |acc, eval| {
        let SmallEvals {
            challenge,
            powers,
            range,
        } = eval;
        acc + *challenge * powers * range
    });
    let instance = SumcheckInstance::new(sum, oracle_instance);

    assert!(SumcheckRelation::check(&oracle, &instance, &witness));

    let ProverOutput {
        instance: query_instance,
        witness,
        proof,
    } = prover.prove(instance.clone(), witness);

    assert!(QueryRelation::check(&oracle, &query_instance, &witness));

    let verifier_instance = verifier.verify(instance, proof).unwrap();

    assert_eq!(verifier_instance, query_instance);

    let prover = Prover::<F, Poseidon<F>, _, _, Oracle<F>>::new(&oracle, oracle.inner_oracles());
    let verifier =
        Verifier::<F, Poseidon<F>, _, _, Oracle<F>>::new(&oracle, oracle.inner_oracles());

    let ProverOutput {
        instance: partial_query_instance,
        witness,
        proof,
    } = prover.prove(query_instance.clone(), witness);

    assert!(PartialQueryRelation::check(
        oracle.inner_oracles(),
        &partial_query_instance,
        &witness
    ));

    let (core_instance, empty) = partial_query_instance;

    assert!(EmptyRelation::check(&(), &empty, &witness));
    assert!(CoreQueryRelation::check(
        &oracle.inner_oracles().0,
        &core_instance,
        &witness
    ));

    let verifier_instance = verifier.verify(query_instance, proof).unwrap();

    assert_eq!(core_instance, verifier_instance.0);

    let verifier = UnsafeVerifier::<F, Poseidon<F>, _, _, CoreOracle<F, SmallEvals<()>>>::new(
        &oracle.inner_oracles().0,
        &(),
    );

    verifier.verify(core_instance, ());
}

fn eval_powers<F: Field>(coeffs: &[F], point: &MultiPoint<F>) -> F {
    assert_eq!(coeffs.len(), point.vars());
    coeffs
        .iter()
        .zip(point.inner_ref())
        .fold(F::ONE, |acc, (coeff, v)| acc * (*coeff * v + (-F::ONE + v)))
}

fn eval_range<F: Field>(coeffs: &[F], point: &MultiPoint<F>) -> F {
    assert_eq!(coeffs.len(), 0);
    point
        .inner_ref()
        .iter()
        .rev()
        .fold(F::ZERO, |acc, v| acc.double() + v)
}

#[derive(Clone, Copy, Debug, EvalsCore, PartialEq, Eq)]
struct SmallEvals<V: Clone + Debug> {
    challenge: V,
    powers: V,
    range: V,
}

impl<F: Field> SumcheckFunction<F> for SmallEvals<()> {
    type Natures = Either<CoreNature, NoNature>;

    type Data = ();

    fn natures() -> Self::Mles<Self::Natures> {
        let core = |x| Either::Left(x);
        SmallEvals {
            challenge: core(CoreNature::Challenge),
            powers: core(CoreNature::SmallInstance(Coeffs::PerVariable)),
            range: core(CoreNature::SmallStructure),
        }
    }

    fn function<V: Var<F> + Debug>(_: &(), evals: &Self::Mles<V>) -> V {
        let SmallEvals {
            challenge,
            powers,
            range,
        } = evals;
        challenge.clone() * powers * range
    }
}

#[test]
fn composite_sumcheck() {
    use ark_vesta::Fr;
    composite_sumcheck_test::<Fr>();
}
