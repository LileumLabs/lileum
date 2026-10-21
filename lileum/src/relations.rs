use crate::{
    extensions::Extension,
    oracles::{FlcsOracle, FlcsOracleParams},
    reductions::flcs::{FlcsEvals, compute_sumcheck_witness},
};
use alloc::vec::Vec;
use ark_ff::Field;
use commit::CommitmentScheme;
use core::marker::PhantomData;
use lcs::{
    constraint_system::Constraints,
    matrix::Matrix,
    structure::{Exp, LcsStructure},
    witness::LinearCombinations,
};
use reduction::{Message, NoError, Relation};
use sumcheck::{
    oracles::{Oracle, partial::OracleParams},
    zerocheck::{ZeroSumcheck, ZeroSumcheckInstance},
};

#[derive(Clone, Copy, Debug)]
pub struct ClcsRelation<F, C, const I: usize, const IO: usize, const S: usize, E = ()>(
    PhantomData<(F, C, E)>,
);

#[derive(Clone, Debug)]
pub struct ClcsInstance<F: Field, C: CommitmentScheme<F>, const I: usize, E: Extension<F, C> = ()> {
    pub(crate) witness_commit: C::Commitment,
    pub(crate) public_inputs: [F; I],
    pub(crate) extended_instance: E::Instance,
}

impl<F: Field, C: CommitmentScheme<F>, const I: usize> ClcsInstance<F, C, I> {
    pub fn public_inputs(&self) -> &[F; I] {
        &self.public_inputs
    }
}

impl<F, C, E, const I: usize> Message<F> for ClcsInstance<F, C, I, E>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    type Params = ();

    type Error = NoError;

    fn len(_: &()) -> usize {
        C::Commitment::len(&()) + I + E::Instance::len(&())
    }

    fn to_field_elements(&self, _: &()) -> Result<Vec<F>, Self::Error> {
        let Self {
            witness_commit,
            public_inputs,
            extended_instance,
        } = self;
        let Ok(mut elems) = witness_commit.to_field_elements(&());
        elems.extend(public_inputs.iter().cloned());
        let Ok(extended) = extended_instance.to_field_elements(&());
        elems.extend(extended);
        Ok(elems)
    }
}

pub struct ClcsStructure<F, C, const IO: usize, const S: usize, E = ()>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    pub(crate) lcs_structure: LcsStructure<F, IO, S, E>,
    pub(crate) pcs: C,
}

impl<F, C, E, const I: usize, const IO: usize, const S: usize> Relation
    for ClcsRelation<F, C, I, IO, S, E>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    type Structure = ClcsStructure<F, C, IO, S, E>;

    type Instance = ClcsInstance<F, C, I, E>;

    type Witness = (Vec<F>, E::Witness);

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let LcsStructure {
            io_matrices,
            gate_selectors,
            input_len,
            gates,
            trace_len: _,
            constants,
            extended,
        } = &structure.lcs_structure;

        let ClcsInstance {
            witness_commit,
            public_inputs,
            extended_instance,
        } = instance;

        let expected_commit = structure.pcs.commit_mle(&witness.0);

        if witness_commit != &expected_commit {
            return false;
        }

        if witness.0.len() != (1 << structure.lcs_structure.vars()) {
            return false;
        }

        if *input_len != I {
            return false;
        }

        for (witness, input) in witness.0.iter().zip(public_inputs) {
            if witness != input {
                return false;
            }
        }

        let matrices: [&Matrix; IO] = io_matrices.each_ref();
        let linear_combinations = LinearCombinations::from_tables(matrices);
        let mut linear_combinations = linear_combinations.compute(&witness.0);

        for (i, selector) in gate_selectors.iter().enumerate() {
            let io: [F; IO] = linear_combinations.next().unwrap_or([F::ZERO; IO]);
            let constant = constants.get(&i).cloned();
            let gate = &gates[*selector];
            if !check_gate(gate, io, constant) {
                return false;
            }
        }

        // Checking extensions
        {
            let instance = (witness_commit.clone(), extended_instance.clone());
            let structure = &extended;
            if !E::R1::check(structure, &instance, witness) {
                return false;
            }
        };

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

pub struct FlcsStructure<F, C, const IO: usize, const S: usize, const I: usize, E = ()>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    pub lcs_structure: LcsStructure<F, IO, S, E>,
    pub pcs: C,
    pub oracle: FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>,
    pub extended: <E::R2 as Relation>::Structure,
    pub aggregation: <E::R3 as Relation>::Structure,
}

#[derive(Clone, Debug)]
pub struct FlcsRelation<F, C, const I: usize, const IO: usize, const S: usize, E = ()>(
    PhantomData<(F, C, E)>,
);

type ZeroInstance<F, C, const IO: usize, const S: usize, const I: usize> =
    ZeroSumcheckInstance<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlcsInstance<F, C, const IO: usize, const S: usize, const I: usize, E = ()>(
    pub ZeroInstance<F, C, IO, S, I>,
    pub <E::R2 as Relation>::Instance,
)
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>;

impl<F, C, E, const IO: usize, const S: usize, const I: usize> Message<F>
    for FlcsInstance<F, C, IO, S, I, E>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    type Params = (
        OracleParams,
        FlcsOracleParams<F, C, FlcsEvals<(), IO, S, I>, IO>,
    );

    type Error = <ZeroInstance<F, C, IO, S, I> as Message<F>>::Error;

    fn len(params: &Self::Params) -> usize {
        ZeroSumcheckInstance::<F, FlcsOracle<F, C, FlcsEvals<(), IO, S, I>, IO>>::len(params)
            + <E::R2 as Relation>::Instance::len(&())
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        let mut elems = self.0.to_field_elements(params)?;
        elems.extend(self.1.to_field_elements(&()).unwrap());
        Ok(elems)
    }
}

impl<F, C, E, const I: usize, const IO: usize, const S: usize> Relation
    for FlcsRelation<F, C, I, IO, S, E>
where
    F: Field,
    C: CommitmentScheme<F>,
    E: Extension<F, C>,
{
    type Structure = FlcsStructure<F, C, IO, S, I, E>;

    type Instance = FlcsInstance<F, C, IO, S, I, E>;

    // NOTE: It may be better to have a dedicated witness type later on.
    type Witness = (Vec<F>, <E::R2 as Relation>::Witness);

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let oracle = &structure.oracle;
        let core = &instance.0.oracle_instance().oracle1_instance;
        let matrices = oracle.inner_oracles().1.matrices();
        let (witness, extended_witness) = witness;
        let witness = compute_sumcheck_witness(&oracle.structure(), matrices, witness, core);
        if !ZeroSumcheck::check(oracle, &instance.0, &witness) {
            return false;
        }
        E::R2::check(&structure.extended, &instance.1, extended_witness)
    }
}
