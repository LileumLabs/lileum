use crate::{
    commit2::{CommitmentScheme, CommitmentSchemeCore, OpenInstance, OpeningRelation},
    ipa::vector_utils::{challenge_combinations, compute_inner_product},
    ipa2::{IpaScheme, Proof, RoundMsg, Scalar},
};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use hash_to_curve::CurveMap;
use sponge::sponge::Duplex;
use std::ops::{Add, Mul};
use sumcheck::eq::eq;
use transcript::{
    reduction2::{
        message::{ForeignElement, SingleElement},
        Argument, GuardedProof, Message, NoError, ProverOutput, Reduction, Relation, Transcript,
        TranscriptBuilder, VerifierTranscript,
    },
    utils::cycle_cast,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IpaCommitmentScheme<F, G, M>
where
    F: PrimeField,
    G: VariableBaseMSM<ScalarField = F> + CurveGroup,
    M: CurveMap<G>,
{
    ipa: IpaScheme<F, G, M>,
    vars: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IpaCommitment<G>(pub(crate) G);

impl<G: CurveGroup> Message<Scalar<G>> for IpaCommitment<G> {
    type Params = ();

    type Error = NoError;

    fn len(_: &Self::Params) -> usize {
        ForeignElement::<G::BaseField, G::ScalarField>::len(&()) * 2
    }

    fn to_field_elements(&self, _: &Self::Params) -> Result<Vec<Scalar<G>>, Self::Error> {
        let affine = self.0.into_affine();
        // NOTE: maybe there should be an error for this instead.
        let (x, y) = affine.xy().unwrap();

        let elems = [*x, *y]
            .into_iter()
            .flat_map(|x| {
                let foreign = ForeignElement::from(x);
                let Ok(elems) = foreign.to_field_elements(&());
                elems
            })
            .collect();
        Ok(elems)
    }
}

impl<G: CurveGroup> Mul<Scalar<G>> for IpaCommitment<G> {
    type Output = Self;

    fn mul(self, rhs: Scalar<G>) -> Self::Output {
        Self(self.0 * rhs)
    }
}

impl<G: CurveGroup> Add<&Self> for IpaCommitment<G> {
    type Output = Self;

    fn add(self, rhs: &Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl<G: CurveGroup> Add for IpaCommitment<G> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl<F, G, M> CommitmentSchemeCore<F> for IpaCommitmentScheme<F, G, M>
where
    F: PrimeField,
    G: VariableBaseMSM<ScalarField = F> + CurveGroup,
    M: CurveMap<G> + Eq + 'static,
{
    type Commitment = IpaCommitment<G>;

    fn new(vars: usize) -> Self {
        let ipa = IpaScheme::init(vars, None);
        Self { ipa, vars }
    }

    fn commit_mle(&self, evals: &[F]) -> Self::Commitment {
        IpaCommitment(self.ipa.commit(evals))
    }

    fn commit_small_set(&self, evals: &[u8], set: [F; 256]) -> Self::Commitment {
        IpaCommitment(self.ipa.commit_small_set(evals, set))
    }

    fn commit_bytes(&self, evals: &[u8]) -> Self::Commitment {
        IpaCommitment(self.ipa.commit_bytes(evals))
    }
}

#[derive(Debug, Clone)]
pub enum IpaError {
    MissingMessage,
    /// The final folded commitment doesn't open to the expected value
    FinalOpenMismatch,
}

impl<F, G, M> Reduction<F, OpeningRelation<F, Self>, ()> for IpaCommitmentScheme<F, G, M>
where
    F: PrimeField,
    G: VariableBaseMSM<ScalarField = F> + CurveGroup,
    M: CurveMap<G> + Eq + 'static,
{
    type ProverKey = Self;

    type VerifierKey = Self;

    type Proof = Proof<F, G>;

    type Error = IpaError;

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        let builder = builder.round::<F, (), 1>(&());
        (0..key.vars)
            .fold(builder, |builder, _| {
                builder.round::<F, Option<RoundMsg<G>>, 1>(&())
            })
            .round::<F, SingleElement<F>, 0>(&())
    }

    fn verifier_key(pcs: &Self, _: &()) -> Self::VerifierKey {
        pcs.clone()
    }

    fn key_pair(pcs: &Self, _: &()) -> (Self::VerifierKey, Self::ProverKey) {
        (pcs.clone(), pcs.clone())
    }

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: OpenInstance<F, Self>,
        witness: Vec<F>,
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<(), Self::Proof> {
        let a = witness;
        let OpenInstance {
            commit,
            point,
            eval,
        } = instance;
        let b = eq(&point);
        let vectors = [a.to_vec(), b];

        let proof = key.ipa.prove(vectors, commit, eval, transcript);

        ProverOutput {
            instance: (),
            witness: (),
            proof,
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: OpenInstance<F, Self>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<<() as Relation>::Instance, Self::Error> {
        let Ok((_, [u])) = transcript.receive_message(|_| (), &GuardedProof::empty(), &());
        // casting challeng u into the base field, and then mapping to curve point
        let u: G::BaseField = cycle_cast(u);
        let u = key.ipa.map.map_to_curve(u);

        let OpenInstance {
            commit,
            point,
            eval,
        } = instance;

        let commitment: G = commit.0 + u * eval;
        let mut challenges = vec![];
        let commitment: Result<G, IpaError> = (0..key.vars).try_fold(commitment, |acc, i| {
            let (msg, [chall]) = transcript
                .receive_message(
                    |proof| proof.messages.get(i).cloned().map(Into::into),
                    &proof,
                    &(),
                )
                .map_err(|()| IpaError::MissingMessage)?;

            // NOTE: This shouldn't panic as the Option<T> implementation of
            // Message only returns Ok(_) when the value is Some(_).
            let RoundMsg { cl, cr } = msg.unwrap();
            challenges.push(chall);
            let commit = acc + cl * chall.square() + cr * chall.inverse().unwrap().square();
            Ok(commit)
        });
        let commitment: G = commitment?;

        let mut challs_inv = challenges.clone();
        ark_ff::fields::batch_inversion(&mut challs_inv);

        // Efficient way of folding vectors by a single msm/inner product
        // with the s vector.
        let s = challenge_combinations(&challenges, &challs_inv);

        // "a" the single value openened from the resulting folded commitment to
        // the length 1 vector.
        // Note: doesn't really need to be absorbed, but it probably isn't an
        // issue to do it anyway.
        let Ok((SingleElement(a), [])) =
            transcript.receive_message(|proof| SingleElement(proof.a), &proof, &());

        let b = eq(&point);
        let folded_b = compute_inner_product(&s, &b);
        let folded_g = G::msm_unchecked(&key.ipa.vector_basis, &s);

        // TODO: zk opening not revealing a
        // Checking that C = aG + abU
        let open = (u * folded_b + folded_g) * a;
        if commitment == open {
            Ok(())
        } else {
            Err(IpaError::FinalOpenMismatch)
        }
    }
}

impl<F, G, M> Argument<F, OpeningRelation<F, Self>> for IpaCommitmentScheme<F, G, M>
where
    F: PrimeField,
    G: VariableBaseMSM<ScalarField = F> + CurveGroup,
    M: CurveMap<G> + Eq + 'static,
{
}

impl<F, G, M> CommitmentScheme<F> for IpaCommitmentScheme<F, G, M>
where
    F: PrimeField,
    G: VariableBaseMSM<ScalarField = F> + CurveGroup,
    M: CurveMap<G> + Eq + 'static,
{
}
