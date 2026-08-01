use crate::lilium2::oracles::MatrixNature;
use ark_ff::Field;
use ccs::{matrix::Matrix, structure::Exp};
use commit::commit2::oracle::CommittedNature;
use std::{fmt::Debug, rc::Rc, vec::IntoIter};
use sumcheck::{
    eq::eq_subset,
    polynomials::MultiPoint,
    sumcheck::Var,
    sumcheck2::{
        evals::{Evals, EvalsCore},
        oracles::{
            composite::Either,
            core::{Coeffs, CoreNature, CoreOracle, CoreOracleInstance, Func},
            SumcheckFunction,
        },
    },
};
use sumcheck_derive::EvalsCore;

#[derive(Clone, Copy, Debug, EvalsCore, PartialEq, Eq)]
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

impl<F: Field, const IO: usize, const S: usize, const I: usize> FlcsEvals<Vec<F>, IO, S, I> {
    pub fn coefficients(inputs: [F; I], challenge: F) -> Self {
        Self {
            inputs: inputs.to_vec(),
            products: [(); IO].map(|_| vec![]),
            w: vec![],
            input_selector: vec![],
            gate_selectors: [(); S].map(|_| vec![]),
            constants: vec![],
            challenge: vec![challenge],
        }
    }
}

impl<F: Field, const IO: usize, const S: usize, const I: usize> FlcsEvals<F, IO, S, I> {
    pub fn structure(is_input: bool, selector: usize, constant: F) -> Self {
        let mut gate_selectors = [F::ZERO; S];
        for (i, selector_eval) in gate_selectors.iter_mut().enumerate() {
            if i == selector {
                *selector_eval = F::ONE;
            }
        }
        Self {
            input_selector: if is_input { F::ONE } else { F::ZERO },
            gate_selectors,
            constants: constant,
            ..Default::default()
        }
    }

    pub fn w(&self) -> F {
        self.w
    }
}

impl<const IO: usize, const S: usize, const I: usize> FlcsEvals<bool, IO, S, I> {
    pub fn vector() -> Self {
        Self {
            w: true,
            ..Default::default()
        }
    }
}

fn eval_input_selector<F: Field>(point: &MultiPoint<F>, input_len: usize) -> F {
    let log_input = input_len.next_power_of_two().ilog2().max(1);
    let eq_evals = eq_subset(point, log_input as usize);
    // Given that we multiply by either 1 or 0, we can just add the 1s and
    // ignore the zeros.
    eq_evals
        .into_iter()
        .take(input_len)
        .fold(F::zero(), |acc, e| acc + e)
}

fn eval_inputs<F: Field>(inputs: &[F], point: &MultiPoint<F>) -> F {
    let log_input = inputs.len().next_power_of_two().ilog2().max(1);
    let eq_evals = eq_subset(point, log_input as usize);
    inputs
        .iter()
        .zip(eq_evals)
        .fold(F::zero(), |acc, (e, eq)| acc + eq * e)
}

impl<const IO: usize, const S: usize, const I: usize> FlcsEvals<(), IO, S, I> {
    pub fn functions<F: Field>() -> FlcsEvals<Option<Func<F>>, IO, S, I> {
        let default = FlcsEvals::map_evals(&FlcsEvals::vector(), |_| None);

        let inputs: Func<F> = eval_inputs;
        let inputs = Some(inputs);

        let input_selector: Func<F> = |_, point| eval_input_selector(point, I);
        let input_selector = Some(input_selector);

        FlcsEvals {
            inputs,
            input_selector,
            ..default
        }
    }
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

impl FlcsData {
    pub fn new(gates: Vec<Vec<Exp<usize>>>, multi_constraint: bool) -> Self {
        Self {
            gates,
            multi_constraint,
        }
    }
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

        let inputs_check = { (inputs.clone() - w) * input_selector };

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
