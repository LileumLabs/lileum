use crate::{
    oracles::{FlcsOracle, FlcsOracleParams},
    reductions::flcs::{FlcsEvals, compute_sumcheck_witness},
};
use ark_ff::Field;
use commit::CommitmentScheme;
use lcs::{
    constraint_system::Constraints,
    matrix::Matrix,
    structure::{CcsStructure, Exp},
    witness::LinearCombinations,
};
use reduction::{Message, NoError, Relation};
use std::marker::PhantomData;
use sumcheck::{
    oracles::{Oracle, partial::OracleParams},
    zerocheck::{ZeroSumcheck, ZeroSumcheckInstance},
};

#[derive(Clone, Copy, Debug)]
pub struct ClcsRelation<F, C, const I: usize, const IO: usize, const S: usize>(PhantomData<(F, C)>);

#[derive(Clone, Debug)]
pub struct ClcsInstance<F: Field, C: CommitmentScheme<F>, const I: usize> {
    pub(crate) witness_commit: C::Commitment,
    pub(crate) public_inputs: [F; I],
}

impl<F: Field, C: CommitmentScheme<F>, const I: usize> ClcsInstance<F, C, I> {
    pub fn public_inputs(&self) -> &[F; I] {
        &self.public_inputs
    }
}

impl<F: Field, C: CommitmentScheme<F>, const I: usize> Message<F> for ClcsInstance<F, C, I> {
    type Params = ();

    type Error = NoError;

    fn len(_: &()) -> usize {
        C::Commitment::len(&()) + I
    }

    fn to_field_elements(&self, _: &()) -> Result<Vec<F>, Self::Error> {
        let Ok(mut elems) = self.witness_commit.to_field_elements(&());
        elems.extend(self.public_inputs.iter().cloned());
        Ok(elems)
    }
}

pub struct ClcsStructure<F: Field, C: CommitmentScheme<F>, const IO: usize, const S: usize> {
    pub(crate) ccs_structure: CcsStructure<F, IO, S>,
    pub(crate) pcs: C,
}

impl<F, C, const I: usize, const IO: usize, const S: usize> Relation
    for ClcsRelation<F, C, I, IO, S>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Structure = ClcsStructure<F, C, IO, S>;

    type Instance = ClcsInstance<F, C, I>;

    type Witness = Vec<F>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let CcsStructure {
            io_matrices,
            gate_selectors,
            input_len,
            gates,
            trace_len: _,
            constants,
        } = &structure.ccs_structure;

        let ClcsInstance {
            witness_commit,
            public_inputs,
        } = instance;

        let expected_commit = structure.pcs.commit_mle(witness);

        if witness_commit != &expected_commit {
            return false;
        }

        if witness.len() != (1 << structure.ccs_structure.vars()) {
            return false;
        }

        if *input_len != I {
            return false;
        }

        for (witness, input) in witness.iter().zip(public_inputs) {
            if witness != input {
                return false;
            }
        }

        let matrices: [&Matrix; IO] = io_matrices.each_ref();
        let linear_combinations = LinearCombinations::from_tables(matrices);
        let mut linear_combinations = linear_combinations.compute(witness);

        for (i, selector) in gate_selectors.iter().enumerate() {
            let io: [F; IO] = linear_combinations.next().unwrap_or([F::ZERO; IO]);
            let constant = constants.get(&i).cloned();
            let gate = &gates[*selector];
            if !check_gate(gate, io, constant) {
                return false;
            }
        }

        true
    }
}

fn check_gate<F: Field, const IO: usize>(
    gate: &Constraints<Exp<usize>>,
    io: [F; IO],
    constant: Option<F>,
) -> bool {
    match gate {
        Constraints::Constraint(exp) => eval_exp(exp, io, constant).is_zero(),
        Constraints::Append(constraints, exp) => {
            eval_exp(exp, io, constant).is_zero() && check_gate(constraints, io, constant)
        }
        Constraints::Empty => true,
    }
}

fn eval_exp<F: Field, const IO: usize>(exp: &Exp<usize>, io: [F; IO], constant: Option<F>) -> F {
    match exp {
        Exp::Atom(i) => io[*i],
        Exp::Add(a, b) => eval_exp(a, io, constant) + eval_exp(b, io, constant),
        Exp::Mul(a, b) => eval_exp(a, io, constant) * eval_exp(b, io, constant),
        Exp::Sub(a, b) => eval_exp(a, io, constant) - eval_exp(b, io, constant),
        Exp::Constant => constant.unwrap(),
    }
}

pub struct FlcsStructure<F, C, const IO: usize, const S: usize, const I: usize>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    pub ccs_structure: CcsStructure<F, IO, S>,
    pub pcs: C,
    pub oracle: FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>,
}

#[derive(Clone, Debug)]
pub struct FlcsRelation<F, C, const I: usize, const IO: usize, const S: usize>(PhantomData<(F, C)>);

type ZeroInstance<F, C, const IO: usize, const S: usize, const I: usize> =
    ZeroSumcheckInstance<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlcsInstance<F, C, const IO: usize, const S: usize, const I: usize>(
    pub ZeroInstance<F, C, IO, S, I>,
)
where
    F: Field,
    C: CommitmentScheme<F>;

impl<F, C, const IO: usize, const S: usize, const I: usize> Message<F>
    for FlcsInstance<F, C, IO, S, I>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Params = (
        OracleParams,
        FlcsOracleParams<F, C, FlcsEvals<(), IO, S, I>, IO>,
    );

    type Error = <ZeroInstance<F, C, IO, S, I> as Message<F>>::Error;

    fn len(params: &Self::Params) -> usize {
        ZeroSumcheckInstance::<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>::len(params)
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        self.0.to_field_elements(params)
    }
}

impl<F, C, const I: usize, const IO: usize, const S: usize> Relation
    for FlcsRelation<F, C, I, IO, S>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Structure = FlcsStructure<F, C, IO, S, I>;

    type Instance = FlcsInstance<F, C, IO, S, I>;

    type Witness = Vec<F>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let oracle = &structure.oracle;
        let core = &instance.0.oracle_instance().oracle1_instance;
        let matrices = oracle.inner_oracles().1.matrices();
        let witness = compute_sumcheck_witness(&oracle.structure(), matrices, witness, core);
        ZeroSumcheck::check(oracle, &instance.0, &witness)
    }
}
