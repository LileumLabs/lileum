use crate::commit2::{
    oracle::{self, CommittedNature, CommittedOracle, CommittedOracleInstance},
    CommitmentScheme, OpenInstance, OpeningRelation,
};
use ark_ff::Field;
use sponge::sponge::Duplex;
use std::{fmt::Debug, marker::PhantomData, vec::IntoIter};
use sumcheck::{
    polynomials::MultiPoint,
    sumcheck::Var,
    sumcheck2::{
        evals::{Evals, EvalsCore},
        oracles::{
            composite::{
                CompositeOracle, CompositeOracleInstance, CompositeReductionKey, Either,
                ProverEvals,
            },
            core::{Coeffs, CoreNature, CoreOracle, CoreOracleInstance},
            SumcheckFunction,
        },
        SumcheckInstance, SumcheckMessage, SumcheckReduction, SumcheckVerifierKey,
    },
};
use sumcheck_derive::EvalsCore;
use transcript::reduction2::{
    GuardedProof, ProverOutput, Reduction, Relation, Transcript, TranscriptBuilder,
    VerifierTranscript,
};

pub struct MultipointBatching<F, C, const N: usize>(PhantomData<(F, C)>);

pub struct VerifierKey<F, C, SF>
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F>,
{
    sumcheck: SumcheckVerifierKey<F>,
    vars: usize,
    composite: CompositeReductionKey<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>,
    core_oracle: CoreOracle<F, SF>,
    committed_oracle: oracle::VerifierKey<F, C>,
}

impl<F, C, const N: usize> Relation for MultipointBatching<F, C, N>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Structure = (C, usize);

    type Instance = [OpenInstance<F, C>; N];

    type Witness = [Vec<F>; N];

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let (pcs, vars) = structure;

        for (instance, witness) in instance.iter().zip(witness) {
            let expected_vars = witness.len().next_power_of_two().ilog2() as usize;
            if expected_vars != *vars {
                return false;
            }
            if !OpeningRelation::check(pcs, instance, witness) {
                return false;
            }
        }
        true
    }
}

#[derive(Clone, Debug)]
pub struct Proof<F: Field> {
    sumcheck: Vec<SumcheckMessage<F>>,
    prover_evals: ProverEvals<F>,
}

impl<F, C, const N: usize> Reduction<F, Self, OpeningRelation<F, C>> for MultipointBatching<F, C, N>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = C::ProverKey;

    type VerifierKey = VerifierKey<F, C, MultipointEvals<(), N>>;

    type Proof = Proof<F>;

    type Error = ();

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        builder
            .round::<F, (), 1>(&())
            .subprotocol::<SumcheckReduction<F, Oracle<F, C, MultipointEvals<(), N>, N>>, _, _, _>(
                &key.sumcheck,
            )
            .subprotocol::<CompositeOracle<F, _, _, _>, _, _, _>(&key.composite)
            .subprotocol::<CoreOracle<F, _>, _, _, _>(&key.core_oracle)
            .subprotocol::<CommittedOracle<F, C, MultipointEvals<(), N>>, _, _, _>(
                &key.committed_oracle,
            )
    }

    fn verifier_key(_structure_1: &(C, usize), _structure_2: &C) -> Self::VerifierKey {
        todo!()
    }

    fn key_pair(
        _structure_1: &(C, usize),
        _structure_2: &C,
    ) -> (Self::VerifierKey, Self::ProverKey) {
        todo!()
    }

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: [OpenInstance<F, C>; N],
        _witness: [Vec<F>; N],
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        todo!()
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: [OpenInstance<F, C>; N],
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        let (_, [challenge]) = transcript
            .receive_message(|_| (), &GuardedProof::empty(), &())
            .unwrap();

        let sum = instance
            .iter()
            .fold(F::ZERO, |acc, instance| acc * challenge + instance.eval);

        let points = instance.each_ref().map(|instance| instance.point.clone());
        let core_instance = core_instance(points, challenge, key.vars);

        let commits = instance.each_ref().map(|instance| instance.commit.clone());
        let commits = MultipointEvals {
            committments: commits.map(Some),
            eqs: [(); N].map(|_| None),
            challenge: None,
        };
        let committed_instance =
            CommittedOracleInstance::<F, C, MultipointEvals<(), N>>::new(commits);

        let oracle_instance = CompositeOracleInstance {
            oracle1_instance: core_instance,
            oracle2_instance: committed_instance,
        };
        let instance = SumcheckInstance::new(sum, oracle_instance);

        let red = SumcheckReduction::<F, Oracle<F, C, _, N>>::verify(
            &key.sumcheck,
            instance,
            proof.clone().map(|proof| proof.sumcheck),
            transcript,
        )
        //TODO:handle
        .unwrap();

        let (core, committed) = CompositeOracle::verify(
            &key.composite,
            red,
            proof.map(|proof| proof.prover_evals),
            transcript,
        )
        //TODO:handle
        .unwrap();

        //TODO:handle
        CoreOracle::verify(&key.core_oracle, core, GuardedProof::empty(), transcript).unwrap();

        let Ok(open_instance) = CommittedOracle::verify(
            &key.committed_oracle,
            committed,
            GuardedProof::empty(),
            transcript,
        );

        Ok(open_instance)
    }
}

type Oracle<F, C, SF, const N: usize> =
    CompositeOracle<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

fn core_instance<F: Field, const N: usize>(
    points: [MultiPoint<F>; N],
    challenge: F,
    vars: usize,
) -> CoreOracleInstance<F, MultipointEvals<(), N>> {
    let coefficients = MultipointEvals {
        committments: [(); N].map(|_| vec![]),
        eqs: points.map(|point| point.inner()),
        challenge: vec![challenge],
    };
    CoreOracleInstance::new(&coefficients, vars)
}

#[derive(Clone, Copy, Debug, EvalsCore)]
pub struct MultipointEvals<V: Clone + Debug, const N: usize> {
    committments: [V; N],
    eqs: [V; N],
    challenge: V,
}

impl<F: Field, const N: usize> SumcheckFunction<F> for MultipointEvals<(), N> {
    type Natures = Either<CoreNature, CommittedNature>;

    type Data = ();

    fn natures() -> Self::Mles<Self::Natures> {
        use Either::*;
        MultipointEvals {
            committments: [Right(CommittedNature::Witness); N],
            eqs: [Left(CoreNature::SmallInstance(Coeffs::PerVariable)); N],
            challenge: Left(CoreNature::Challenge),
        }
    }

    fn function<V: Var<F> + Debug>(_: &Self::Data, evals: &Self::Mles<V>) -> V {
        let MultipointEvals {
            committments,
            eqs,
            challenge,
        } = evals;

        let first = eqs[0].clone() * &committments[0];

        eqs[1..]
            .iter()
            .zip(&committments[1..])
            .fold(first, |acc, e| {
                let (eq, commit) = e;
                acc * challenge + eq.clone() * commit
            })
    }
}
