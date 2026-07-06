use crate::lilium2::{
    oracles::FlcsOracle,
    reductions::flcs::{compute_sumcheck_witness, FlcsEvals},
};
use ark_ff::Field;
use ccs::{
    constraint_system::Constraints,
    matrix::Matrix,
    structure::{CcsStructure, Exp},
    witness::LinearCombinations,
};
use commit::commit2::CommitmentScheme;
use std::marker::PhantomData;
use sumcheck::sumcheck2::{
    oracles::Oracle,
    zerocheck::{ZeroSumcheck, ZeroSumcheckInstance},
};
use transcript::reduction2::Relation;

pub struct LcsRelation<F, C, const I: usize, const IO: usize, const S: usize>(PhantomData<(F, C)>);

pub struct LcsInstance<F: Field, C: CommitmentScheme<F>, const I: usize> {
    witness_commit: C::Commitment,
    public_inputs: [F; I],
}

pub struct LcsStructure<F: Field, C: CommitmentScheme<F>, const IO: usize, const S: usize> {
    ccs_structure: CcsStructure<F, IO, S>,
    pcs: C,
}

impl<F, C, const I: usize, const IO: usize, const S: usize> Relation for LcsRelation<F, C, I, IO, S>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Structure = LcsStructure<F, C, IO, S>;

    type Instance = LcsInstance<F, C, I>;

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
            trace_len,
            constants,
        } = &structure.ccs_structure;

        let LcsInstance {
            witness_commit,
            public_inputs,
        } = instance;

        let expected_commit = structure.pcs.commit_mle(witness);
        if witness_commit != &expected_commit {
            return false;
        }

        if *trace_len != witness.len() {
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

pub struct FlcsStructure<F: Field, C: CommitmentScheme<F>, const IO: usize, const S: usize> {
    _ccs_structure: CcsStructure<F, IO, S>,
    _pcs: C,
    oracle: FlcsOracle<F, C, FlcsEvals<(), IO, S>, IO>,
}

pub struct FlcsRelation<F, C, const I: usize, const IO: usize, const S: usize>(PhantomData<(F, C)>);

pub struct FlcsInstance<F, C, const IO: usize, const S: usize>(
    pub ZeroSumcheckInstance<F, FlcsOracle<F, C, FlcsEvals<(), IO, S>, IO>>,
)
where
    F: Field,
    C: CommitmentScheme<F>;

impl<F, C, const I: usize, const IO: usize, const S: usize> Relation
    for FlcsRelation<F, C, I, IO, S>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Structure = FlcsStructure<F, C, IO, S>;

    type Instance = FlcsInstance<F, C, IO, S>;

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
