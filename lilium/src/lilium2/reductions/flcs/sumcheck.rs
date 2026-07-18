use crate::lilium2::oracles::MatrixNature;
use ark_ff::Field;
use ccs::{matrix::Matrix, structure::Exp};
use commit::commit2::oracle::CommittedNature;
use std::{fmt::Debug, rc::Rc, vec::IntoIter};
use sumcheck::{
    sumcheck::Var,
    sumcheck2::{
        evals::{Evals, EvalsCore},
        oracles::{
            composite::Either,
            core::{Coeffs, CoreNature, CoreOracle, CoreOracleInstance},
            SumcheckFunction,
        },
    },
};
use sumcheck_derive::EvalsCore;

#[derive(Clone, Copy, Debug, EvalsCore)]
pub struct FlcsEvals<V: Debug + Clone, const IO: usize, const S: usize, const I: usize> {
    /// matrix vector products M(x)z(x)
    products: [V; IO],
    w: V,
    inputs: V,
    input_selector: V,
    gate_selectors: [V; S],
    constants: V,
    /// Constraint combination challenge.
    challenge: V,
}

impl<V: Debug + Copy + Default, const IO: usize, const S: usize, const I: usize> Default
    for FlcsEvals<V, IO, S, I>
{
    fn default() -> Self {
        Self {
            products: [Default::default(); IO],
            w: Default::default(),
            inputs: Default::default(),
            input_selector: Default::default(),
            gate_selectors: [Default::default(); S],
            constants: Default::default(),
            challenge: Default::default(),
        }
    }
}

type Natures = Either<CoreNature, Either<CommittedNature, MatrixNature>>;

#[derive(Clone, Debug)]
pub struct FlcsData {
    gates: Vec<Vec<Exp<usize>>>,
    multi_constraint: bool,
    // inputs: usize,
}

impl<F: Field, const IO: usize, const S: usize, const I: usize> SumcheckFunction<F>
    for FlcsEvals<(), IO, S, I>
{
    type Natures = Natures;

    type Data = FlcsData;

    fn natures() -> Self::Mles<Self::Natures> {
        use Either::*;

        let products = [Right(Right(MatrixNature)); IO];
        let w = Right(Left(CommittedNature::Witness));
        let inputs = Left(CoreNature::SmallInstance(Coeffs::Fixed(I)));
        let input_selector = Left(CoreNature::SmallStructure);
        let gate_selectors = [Right(Left(CommittedNature::Structure)); S];
        let constants = Right(Left(CommittedNature::Structure));
        let challenge = Left(CoreNature::Challenge);

        FlcsEvals {
            products,
            w,
            inputs,
            input_selector,
            gate_selectors,
            constants,
            challenge,
        }
    }

    fn function<V: Var<F> + Debug>(data: &Self::Data, evals: &Self::Mles<V>) -> V {
        let FlcsEvals {
            products,
            w,
            inputs,
            input_selector,
            gate_selectors,
            constants,
            challenge,
        } = evals;

        let inputs_check = { input_selector.clone() - inputs.clone() * w };

        let mut acc = inputs_check;

        for (i, constraints) in data.gates.iter().enumerate() {
            let selector = &gate_selectors[i];

            for constraint in constraints {
                let exp = if matches!(constraint, Exp::Constant) {
                    let product = products[0].clone();
                    product - constants
                } else {
                    let exp = constraint;
                    eval_exp(evals, exp)
                };
                acc = if data.multi_constraint {
                    acc * challenge + exp * selector
                } else {
                    acc + exp * selector
                };
            }
        }

        acc
    }
}

fn eval_exp<F, V, const IO: usize, const S: usize, const I: usize>(
    evals: &FlcsEvals<V, IO, S, I>,
    exp: &Exp<usize>,
) -> V
where
    F: Field,
    V: Var<F> + Debug,
{
    match exp {
        Exp::Atom(i) => evals.products[*i].clone(),
        Exp::Add(e1, e2) => eval_exp(evals, e1) + eval_exp(evals, e2),
        Exp::Mul(e1, e2) => eval_exp(evals, e1) * eval_exp(evals, e2),
        Exp::Sub(e1, e2) => eval_exp(evals, e1) - eval_exp(evals, e2),
        Exp::Constant => evals.constants.clone(),
    }
}

#[test]
fn print_natures() {
    use ark_vesta::Fr;
    use sumcheck::sumcheck2::oracles::EvalLocation;

    let natures = <FlcsEvals<(), 4, 3, 3> as SumcheckFunction<Fr>>::natures();
    let natures = FlcsEvals::map_evals(&natures, |nature| EvalLocation::from(*nature));
    dbg!(natures);
}

pub fn compute_sumcheck_witness<F, const IO: usize, const S: usize, const I: usize>(
    structure: &[FlcsEvals<F, IO, S, I>],
    matrices: &[Rc<Matrix>; IO],
    witness: &[F],
    core_instance: &CoreOracleInstance<F, FlcsEvals<(), IO, S, I>>,
) -> Vec<FlcsEvals<F, IO, S, I>>
where
    F: Field,
{
    let mut sumcheck_witness: Vec<FlcsEvals<F, IO, S, I>> = structure
        .iter()
        .zip(witness)
        .map(|(structure, witness)| {
            let mut eval = *structure;
            eval.w = *witness;
            eval
        })
        .collect();
    let filter = FlcsEvals {
        inputs: true,
        ..Default::default()
    };
    CoreOracle::set_witness(
        core_instance,
        &mut sumcheck_witness,
        filter,
        |inputs, witness| {
            for (input, witness) in inputs.iter().zip(witness) {
                witness.inputs = *input;
            }
        },
    );

    for (i, matrix) in matrices.iter().enumerate() {
        let product = matrix.as_ref() * witness;

        for (witness, product) in sumcheck_witness.iter_mut().zip(product) {
            witness.products[i] = product;
        }
    }

    sumcheck_witness
}
