use crate::{
    CommitmentScheme, OpenInstance, OpeningRelation,
    oracle::{self, CommittedNature, CommittedOracle, CommittedOracleInstance},
};
use alloc::{
    rc::Rc,
    vec::{IntoIter, Vec},
};
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use core::{fmt::Debug, marker::PhantomData};
use reduction::{
    GuardedProof, ProverOutput, Reduction, Relation, Transcript, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;
use sumcheck::{
    MultiPoint, ProverKey as SumcheckProverKey, SumcheckError, SumcheckInstance, SumcheckMessage,
    SumcheckReduction, SumcheckVerifierKey, Var,
    eq::eq,
    evals::{Evals, EvalsCore},
    oracles::{
        SumcheckFunction,
        composite::{
            CompositeOracle, CompositeOracleInstance, CompositeReductionKey, Either, ProverEvals,
        },
        core::{Coeffs, CoreNature, CoreOracle, CoreOracleInstance, SmallFunctions},
    },
};
use sumcheck_derive::EvalsCore;

pub struct MultipointBatching<F, C, const N: usize>(PhantomData<(F, C)>);

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

type Oracle<F, C, SF> = CompositeOracle<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

#[derive(Clone, Debug)]
pub struct VerifierKey<F, C, const N: usize, SF = MultipointEvals<(), N>>
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F, Natures = Either<CoreNature, CommittedNature>>,
    SF: SmallFunctions<F>,
{
    sumcheck: SumcheckVerifierKey<F, Oracle<F, C, SF>>,
    vars: usize,
    composite: CompositeReductionKey<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>,
}

impl<F, C, const N: usize, SF: CanonicalSerialize> CanonicalSerialize for VerifierKey<F, C, N, SF>
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F, Natures = Either<CoreNature, CommittedNature>>,
    SF: SmallFunctions<F>,
    SF::Mles<Either<(), ()>>: CanonicalSerialize,
{
    fn serialize_with_mode<W: ark_serialize::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        let Self {
            sumcheck,
            vars,
            composite,
        } = self;
        sumcheck.serialize_with_mode(&mut writer, compress)?;
        vars.serialize_with_mode(&mut writer, compress)?;
        composite.serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        let Self {
            sumcheck,
            vars,
            composite,
        } = self;
        sumcheck.serialized_size(compress)
            + vars.serialized_size(compress)
            + composite.serialized_size(compress)
    }
}

pub struct ProverKey<F, C, const N: usize, SF = MultipointEvals<(), N>>
where
    F: Field,
    C: CommitmentScheme<F>,
    SF: SumcheckFunction<F, Natures = Either<CoreNature, CommittedNature>>,
    SF: SmallFunctions<F>,
{
    vars: usize,
    sumcheck: SumcheckProverKey<F, Oracle<F, C, SF>>,
    composite: CompositeReductionKey<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>,
    committed_oracle: oracle::ProverKey<F, SF, C>,
}

#[derive(Clone, Debug)]
pub enum Error {
    Sumcheck(SumcheckError),
    /// Error during the CompositeOracle reduction.
    Composite,
    /// Error during the CoreOracle reduction.
    Core,
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
    type ProverKey = ProverKey<F, C, N>;

    type VerifierKey = VerifierKey<F, C, N>;

    type Proof = Proof<F>;

    type Error = Error;

    type Params = ();

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        let VerifierKey {
            sumcheck,
            composite,
            ..
        } = key;
        builder
            .round::<F, (), 1>(&())
            .subprotocol::<SumcheckReduction<F, Oracle<F, C, MultipointEvals<(), N>>>, _, _, _>(
                sumcheck,
            )
            .subprotocol::<CompositeOracle<F, _, _, _>, _, _, _>(composite)
            .subprotocol::<CoreOracle<F, MultipointEvals<(), N>>, _, _, _>(composite.p1_key())
            .subprotocol::<CommittedOracle<F, C, MultipointEvals<(), N>>, _, _, _>(
                composite.p2_key(),
            )
    }

    fn verifier_key(structure_1: &(C, usize)) -> Self::VerifierKey {
        let (pcs, vars) = structure_1;

        let mles = alloc::vec![MultipointEvals::<F, N>::zero(); 1 << vars];
        let mles = Rc::new(mles);
        let oracle = Oracle::new((), mles, (), pcs.clone());

        let composite = CompositeOracle::verifier_key(&oracle);

        let sumcheck = SumcheckReduction::verifier_key(&oracle);

        VerifierKey {
            sumcheck,
            vars: *vars,
            composite,
        }
    }

    fn key_pair(structure: &(C, usize)) -> (Self::VerifierKey, Self::ProverKey) {
        let verifier_key = Self::verifier_key(structure);
        let (pcs, vars) = structure;

        let mles = alloc::vec![MultipointEvals::<F, N>::zero(); 1 << vars];
        let mles = Rc::new(mles);
        let oracle = Oracle::new((), mles, (), pcs.clone());

        let (_, sumcheck) = SumcheckReduction::key_pair(&oracle);

        let (_, committed_oracle) = CommittedOracle::key_pair(&oracle.inner_oracles().1);

        let prover_key = ProverKey {
            vars: *vars,
            sumcheck,
            composite: verifier_key.composite.clone(),
            committed_oracle,
        };

        (verifier_key, prover_key)
    }

    fn params(_: &Self::VerifierKey) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: [OpenInstance<F, C>; N],
        witness: [Vec<F>; N],
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        let [challenge] = transcript.send_message(&(), &());

        let sum = instance
            .iter()
            .fold(F::ZERO, |acc, instance| acc * challenge + instance.eval);

        let points = instance.each_ref().map(|instance| instance.point.clone());

        let witness = sumcheck_witness(witness, &points);

        let core_instance = core_instance(points, challenge, key.vars);

        let commits = instance.each_ref().map(|instance| instance.commit.clone());
        let commits = MultipointEvals {
            commitments: commits.map(Some),
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

        let reduced = SumcheckReduction::prove(&key.sumcheck, instance, witness, transcript);

        let ProverOutput {
            instance,
            witness,
            proof: sumcheck_proof,
        } = reduced;

        let reduced = CompositeOracle::prove(&key.composite, instance, witness, transcript);
        let ProverOutput {
            instance: (core, committed),
            witness,
            proof: prover_evals,
        } = reduced;

        CoreOracle::<F, MultipointEvals<(), N>>::prove(
            key.composite.p1_key(),
            core,
            witness.clone(),
            transcript,
        );

        let reduced = CommittedOracle::prove(&key.committed_oracle, committed, witness, transcript);
        let ProverOutput {
            instance,
            witness,
            proof: (),
        } = reduced;

        let proof = Proof {
            sumcheck: sumcheck_proof,
            prover_evals,
        };

        ProverOutput {
            instance,
            witness,
            proof,
        }
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
            commitments: commits.map(Some),
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

        let red = SumcheckReduction::<F, Oracle<F, C, _>>::verify(
            &key.sumcheck,
            instance,
            proof.clone().map(|proof| proof.sumcheck),
            transcript,
        )
        .map_err(Error::Sumcheck)?;

        let (core, committed) = CompositeOracle::verify(
            &key.composite,
            red,
            proof.map(|proof| proof.prover_evals),
            transcript,
        )
        .map_err(|()| Error::Composite)?;

        CoreOracle::<F, MultipointEvals<(), N>>::verify(
            key.composite.p1_key(),
            core,
            GuardedProof::empty(),
            transcript,
        )
        .map_err(|()| Error::Core)?;

        let Ok(open_instance) = CommittedOracle::verify(
            key.composite.p2_key(),
            committed,
            GuardedProof::empty(),
            transcript,
        );

        Ok(open_instance)
    }
}

fn core_instance<F: Field, const N: usize>(
    points: [MultiPoint<F>; N],
    challenge: F,
    vars: usize,
) -> CoreOracleInstance<F, MultipointEvals<(), N>> {
    let coefficients = MultipointEvals {
        commitments: [(); N].map(|_| Vec::new()),
        eqs: points.map(|point| point.inner()),
        challenge: alloc::vec![challenge],
    };
    CoreOracleInstance::new(&coefficients, vars)
}

#[derive(Clone, Copy, Debug, EvalsCore)]
pub struct MultipointEvals<V: Clone + Debug, const N: usize> {
    commitments: [V; N],
    eqs: [V; N],
    challenge: V,
}

impl<V: Clone + Debug + CanonicalSerialize, const N: usize> CanonicalSerialize
    for MultipointEvals<V, N>
{
    fn serialize_with_mode<W: ark_serialize::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        let Self {
            commitments,
            eqs,
            challenge,
        } = self;
        commitments.serialize_with_mode(&mut writer, compress)?;
        eqs.serialize_with_mode(&mut writer, compress)?;
        challenge.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        let Self {
            commitments,
            eqs,
            challenge,
        } = self;
        commitments.serialized_size(compress)
            + eqs.serialized_size(compress)
            + challenge.serialized_size(compress)
    }
}

impl<F: Field, const N: usize> MultipointEvals<F, N> {
    pub fn zero() -> Self {
        Self {
            commitments: [F::ZERO; N],
            eqs: [F::ZERO; N],
            challenge: F::ZERO,
        }
    }
}

impl<F: Field, const N: usize> SumcheckFunction<F> for MultipointEvals<(), N> {
    type Natures = Either<CoreNature, CommittedNature>;

    type Data = ();

    fn natures() -> Self::Mles<Self::Natures> {
        use Either::*;
        MultipointEvals {
            commitments: [Right(CommittedNature::Witness); N],
            eqs: [Left(CoreNature::SmallInstance(Coeffs::PerVariable)); N],
            challenge: Left(CoreNature::Challenge),
        }
    }

    fn function<V: Var<F> + Debug>(_: &Self::Data, evals: &Self::Mles<V>) -> V {
        let MultipointEvals {
            commitments,
            eqs,
            challenge,
        } = evals;

        let first = eqs[0].clone() * &commitments[0];

        eqs[1..]
            .iter()
            .zip(&commitments[1..])
            .fold(first, |acc, e| {
                let (eq, commit) = e;
                acc * challenge + eq.clone() * commit
            })
    }
}

impl<F: Field, const N: usize> SmallFunctions<F> for MultipointEvals<(), N> {
    fn small_functions() -> MultipointEvals<Option<fn(&[F], &MultiPoint<F>) -> F>, N> {
        let eq_func: fn(&[F], &MultiPoint<F>) -> F = |eq, p| {
            let eq = MultiPoint::new(eq.to_vec());
            eq.eval_as_eq(p)
        };
        MultipointEvals {
            commitments: [None; N],
            eqs: [Some(eq_func); N],
            challenge: None,
        }
    }
}

fn sumcheck_witness<F: Field, const N: usize>(
    witness: [Vec<F>; N],
    points: &[MultiPoint<F>; N],
) -> Vec<MultipointEvals<F, N>> {
    let len = witness[0].len();
    for witness in &witness {
        assert_eq!(witness.len(), len);
    }
    let mut res = alloc::vec![MultipointEvals::zero(); len];

    for (i, witness) in witness.into_iter().enumerate() {
        for (eval, w) in res.iter_mut().zip(witness) {
            eval.commitments[i] = w;
        }
    }

    for (i, point) in points.iter().enumerate() {
        let eq = eq(point);

        for (eval, eq) in res.iter_mut().zip(eq) {
            eval.eqs[i] = eq;
        }
    }

    res
}
