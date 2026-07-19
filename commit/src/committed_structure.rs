use crate::{
    batching::{
        self,
        structured::{PointEvals, StructureLength, StructuredBatchEval, StructuredBatchReduction},
        BatchEval, CommitsNumber,
    },
    CommmitmentScheme, OpenInstance,
};
use ark_ff::Field;
use sponge::sponge::Duplex;
use std::{marker::PhantomData, rc::Rc};
use sumcheck::{
    polynomials::{Evals, EvalsExt, MultiPoint},
    sumcheck::{CommitType, EvalKind, SumcheckFunction},
};
use transcript::{params::ParamResolver, protocols::Reduction, Transcript};

//TODO: split into prover and verifier to save memory
/// type generalizing the handling of commitment to structures, allowing
/// to commit to a strucuture based on a [SumcheckFunction] implementor.
/// Also allows to open all the commitments in a given point and verify
/// the opening proofs.
#[derive(Clone, Debug)]
pub struct CommittedStructure<F, SF, CS>
where
    F: Field,
    SF: SumcheckFunction<F>,
    CS: CommmitmentScheme<F>,
{
    mles: Rc<Vec<SF::Mles<F>>>,
    structure_len: usize,
    instance_len: usize,
    batch_commitment: StructuredBatchReduction<F, CS>,
    _phantom: PhantomData<SF>,
}

#[derive(Clone, Debug)]
pub struct MultiCommit<F, SF, CS>
where
    F: Field,
    SF: SumcheckFunction<F>,
    CS: CommmitmentScheme<F>,
{
    commitments: Vec<CS::Commitment>,
    _f: PhantomData<SF>,
}

impl<F, SF, CS> MultiCommit<F, SF, CS>
where
    F: Field,
    SF: SumcheckFunction<F>,
    CS: CommmitmentScheme<F>,
{
    pub fn new_empty() -> Self {
        Self {
            commitments: vec![],
            _f: PhantomData,
        }
    }
    pub fn commits(self) -> Vec<CS::Commitment> {
        self.commitments
    }
}

impl<F, SF, CS> CommittedStructure<F, SF, CS>
where
    F: Field,
    SF: SumcheckFunction<F>,
    CS: CommmitmentScheme<F>,
{
    pub fn new(mles: Rc<Vec<SF::Mles<F>>>, scheme: &CS) -> Self {
        let kinds = SF::KINDS;
        let kinds_flat: Vec<EvalKind> = kinds.flatten_vec();
        let mut structure_len = 0;
        let mut instance_len = 0;

        for kind in kinds_flat.clone().into_iter() {
            match kind {
                EvalKind::Committed(CommitType::Instance) => instance_len += 1,
                EvalKind::Committed(CommitType::Structure) => structure_len += 1,
                // other kinds are not a concern of commitments
                _ => {}
            }
        }

        let mut structure_mles: Vec<Vec<F>> = vec![Vec::with_capacity(mles.len()); structure_len];

        for eval in mles.iter() {
            let eval: SF::Mles<F> = eval.clone();
            let eval_flat: Vec<F> = eval.flatten_vec();
            let strucutre_evals = eval_flat
                .into_iter()
                .zip(&kinds_flat)
                .filter_map(|(eval, kind)| {
                    let is_structure = matches!(kind, EvalKind::Committed(CommitType::Structure));
                    is_structure.then_some(eval)
                })
                .enumerate();
            for (i, eval) in strucutre_evals {
                structure_mles[i].push(eval);
            }
        }
        let batch_commitment = StructuredBatchReduction::new(structure_mles, scheme);
        Self {
            mles,
            structure_len,
            instance_len,
            batch_commitment,
            _phantom: PhantomData,
        }
    }

    /// Number of variables forming the domain, log(mles.len()).
    pub fn vars(&self) -> usize {
        self.mles.len().ilog2() as usize
    }

    /// Provides the verifer for the batch commitment.
    pub fn verifier(&self) -> &StructuredBatchReduction<F, CS> {
        &self.batch_commitment
    }

    /// Commits to instance mles.
    pub fn commit(&self, scheme: &CS, mles: &[&[F]]) -> MultiCommit<F, SF, CS> {
        assert_eq!(
            self.instance_len,
            mles.len(),
            "unexpected number of mles to commit to"
        );
        let commitments = mles.iter().map(|mle| scheme.commit_mle(mle)).collect();
        MultiCommit {
            commitments,
            _f: PhantomData,
        }
    }

    /// Wraps commits into MultiCommit, panics on wrong length.
    /// To be used when commits are already available.
    pub fn instance_commit(&self, commitments: Vec<CS::Commitment>) -> MultiCommit<F, SF, CS> {
        assert_eq!(self.instance_len, commitments.len());
        MultiCommit {
            commitments,
            _f: PhantomData,
        }
    }

    /// Filter for instance mles, a zero is added just to match the types.
    fn instance_evals_filter() -> SF::Mles<(F, bool)> {
        let kinds = SF::KINDS;
        let evals = SF::map_evals(kinds, |kind| {
            matches!(kind, EvalKind::Committed(CommitType::Instance))
        });
        SF::map_evals(evals, |x| (F::zero(), x))
    }

    /// Merges 2 evals using a filter to select element between the two,
    /// true selects from the second one.
    fn merge_evals(evals: [&SF::Mles<F>; 2], filter: &SF::Mles<(F, bool)>) -> SF::Mles<F> {
        let [a, b]: [SF::Mles<(F, bool)>; 2] =
            evals.map(|evals| SF::map_evals(evals.clone(), |e| (e, false)));
        let a_with_filter = a.combine(filter, |a, filter| (a.0, filter.1));
        let merged = a_with_filter.combine(&b, |a, b| {
            let (a, filter) = a;
            let (b, _) = b;
            let eval = if filter { b } else { a };
            (eval, false)
        });
        SF::map_evals(merged, |(eval, _)| eval)
    }

    /// Creates batch eval instance, requires the instances mles, which will be merged with
    /// the inner structure, non-instance evals may be arbitary values.
    pub fn open_instance(
        &self,
        commit: MultiCommit<F, SF, CS>,
        committed_mles: Vec<SF::Mles<F>>,
        point: MultiPoint<F>,
    ) -> StructuredBatchEval<F, CS> {
        assert_eq!(commit.commitments.len(), self.instance_len);
        let mut mles = committed_mles;
        let filter = Self::instance_evals_filter();
        for evals in mles.iter_mut().zip(self.mles.iter()) {
            let (instance_evals, structure_evals) = evals;
            let evals: [&SF::Mles<F>; 2] = [structure_evals, instance_evals];
            let merged = Self::merge_evals(evals, &filter);
            // reusing this Vec
            *instance_evals = merged;
        }
        let point_evals = EvalsExt::eval(&mles, point.clone());

        let mut structure_evals = vec![];
        let mut instance_evals = vec![];

        let evals_flat = point_evals.flatten_vec();
        let kinds = SF::KINDS.flatten_vec();
        for (eval, kind) in evals_flat.into_iter().zip(kinds) {
            match kind {
                EvalKind::Committed(CommitType::Structure) => {
                    structure_evals.push(eval);
                }
                EvalKind::Committed(CommitType::Instance) => {
                    instance_evals.push(eval);
                }
                _ => {}
            }
        }
        //TODO:should be handled
        assert_eq!(self.structure_len, structure_evals.len());
        assert_eq!(self.instance_len, instance_evals.len());

        let commitments_and_evals: Vec<(CS::Commitment, F)> =
            commit.commitments.into_iter().zip(instance_evals).collect();
        let dynamic_batch = BatchEval::new(point, commitments_and_evals);
        StructuredBatchEval::new(dynamic_batch, structure_evals)
    }

    /// Combines committed mles into a single one using the challenge provided.
    fn combine_mles(mles: &[SF::Mles<F>], chall: F) -> Vec<F> {
        let strucutre_filter = SF::map_evals(SF::KINDS, |kind| {
            matches!(kind, EvalKind::Committed(CommitType::Structure))
        });
        let structure_filter: Vec<bool> = strucutre_filter.flatten_vec();
        let instance_filter = SF::map_evals(SF::KINDS, |kind| {
            matches!(kind, EvalKind::Committed(CommitType::Instance))
        });
        let instance_filter: Vec<bool> = instance_filter.flatten_vec();

        let mut buffer = Vec::with_capacity(structure_filter.len());
        let combined = mles
            .iter()
            .map(|evals| {
                buffer.clear();
                let evals: &SF::Mles<F> = evals;
                Evals::flatten(evals.clone(), &mut buffer);
                let instance_combined = Self::combine_eval(&buffer, &instance_filter, chall, None);
                Self::combine_eval(&buffer, &structure_filter, chall, Some(instance_combined))
            })
            .collect();
        combined
    }

    /// Combines a given eval, using a filter to ignore particular mles.
    /// Resulting into something like (a * chal + b) * chal + c
    fn combine_eval(evals_flat: &[F], filter: &[bool], chall: F, init: Option<F>) -> F {
        let mut iter = filter
            .iter()
            .zip(evals_flat)
            .filter_map(|(filter, eval)| filter.then_some(eval));
        let mut res = init.or_else(|| iter.next().cloned()).unwrap();
        for eval in iter {
            res *= chall;
            res += eval;
        }
        res
    }

    /// Combines the mles into a single one, witness side version of the
    /// reduction's verify().
    pub fn batch_mles<S: Duplex<F>>(
        &self,
        instance: StructuredBatchEval<F, CS>,
        mles: &[SF::Mles<F>],
        transcript: &mut Transcript<F, S>,
    ) -> Result<Vec<F>, transcript::Error>
    where
        CS: 'static,
    {
        let [chall] = transcript.send_message(&instance)?;
        Ok(Self::combine_mles(mles, chall))
    }

    /// Folds instance-witness pair.
    pub fn prove<S: Duplex<F>>(
        &self,
        instance: StructuredBatchEval<F, CS>,
        mles: &[SF::Mles<F>],
        transcript: &mut Transcript<F, S>,
    ) -> (OpenInstance<F, CS::Commitment>, Vec<F>)
    where
        CS: 'static,
    {
        let [challenge] = transcript.send_message(&instance).unwrap();
        let instance = self
            .batch_commitment
            .fold_with_challenge(instance, challenge);
        let witness = Self::combine_mles(mles, challenge);

        (instance, witness)
    }
}

impl<F, SF, CS> Reduction<F> for CommittedStructure<F, SF, CS>
where
    F: Field,
    SF: SumcheckFunction<F>,
    CS: CommmitmentScheme<F> + 'static,
{
    type A = StructuredBatchEval<F, CS>;

    type B = (OpenInstance<F, CS::Commitment>, SF::Mles<Option<F>>);

    type Key = Self;

    type Proof = ();

    type Error = batching::BatchingError<F, CS>;

    fn transcript_pattern(
        key: &Self,
        builder: transcript::TranscriptBuilder,
    ) -> transcript::TranscriptBuilder {
        let params = ParamResolver::new()
            .set::<StructureLength>(key.structure_len)
            .set::<CommitsNumber>(key.instance_len);
        builder.with_params(params, |builder| {
            StructuredBatchReduction::<F, CS>::transcript_pattern(&key.batch_commitment, builder)
        })
    }

    fn verify_reduction<S: Duplex<F>>(
        key: &Self::Key,
        instance: transcript::MessageGuard<Self::A>,
        transcript: transcript::TranscriptGuard<F, S, Self::Proof>,
    ) -> Result<Self::B, Self::Error> {
        let reduced = StructuredBatchReduction::verify_reduction(
            &key.batch_commitment,
            instance,
            transcript,
        )?;
        let (eval_instance, evaluations) = reduced;

        let PointEvals {
            instance,
            structure,
        } = evaluations;

        let mut instance_evals = instance.into_iter();
        let mut structure_evals = structure.into_iter();
        let evals: Vec<EvalKind> = SF::KINDS.flatten_vec();
        let evals = evals.into_iter().map(|kind| match kind {
            EvalKind::Committed(commit_type) => {
                let eval = match commit_type {
                    CommitType::Instance => instance_evals.next(),
                    CommitType::Structure => structure_evals.next(),
                };
                // shouldn't fail as previous reduction already checks
                assert!(eval.is_some());
                eval
            }
            _ => None,
        });
        let evals: SF::Mles<Option<F>> = SF::Mles::unflatten_vec(evals.collect());

        Ok((eval_instance, evals))
    }
}
