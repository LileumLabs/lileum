use crate::{
    barycentric_eval::BarycentricWeights,
    sumcheck2::{
        evals::{EvalsCore, Mles},
        folding::{folding_degree, FieldFolder, Foldable},
        oracles::{Oracle, OracleData},
        ProverKey, SumcheckError, SumcheckInstance, SumcheckMessage, SumcheckRelation,
    },
};
use ark_ff::Field;
use sponge::sponge::Duplex;
use std::marker::PhantomData;
use transcript::reduction2::{
    FoldingRelation, FoldingScheme, GuardedProof, ProverOutput, Reduction, Transcript,
    TranscriptBuilder, VerifierTranscript,
};

#[derive(Clone, Copy, Debug)]
pub struct SumFold<F, O>(PhantomData<(F, O)>);

#[derive(Clone, Debug)]
pub struct SumFoldKey<F: Field, O: Oracle<F>> {
    // Weights for degree d.
    weights: BarycentricWeights<F>,
    // Weights for degree d + 1.
    extended_weights: BarycentricWeights<F>,
    degree: usize,
    data: OracleData<F, O>,
}

impl<F, O> Reduction<F, FoldingRelation<SumcheckRelation<F, O>>, SumcheckRelation<F, O>>
    for SumFold<F, O>
where
    F: Field,
    O: Oracle<F>,
    O::Instance: Foldable<F>,
{
    type ProverKey = SumFoldKey<F, O>;

    type VerifierKey = SumFoldKey<F, O>;

    type Proof = SumcheckMessage<F>;

    type Error = SumcheckError;

    type Params = ();

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        let degree = key.degree + 1;
        builder
            .round::<F, (), 1>(&())
            .round::<F, SumcheckMessage<F>, 1>(&degree)
    }

    fn verifier_key(oracle: &O) -> Self::VerifierKey {
        let degree = folding_degree(oracle);
        let weights = BarycentricWeights::compute(degree as u32);
        let extended_weights = BarycentricWeights::compute(degree as u32 + 1);
        let data = oracle.data().clone();

        SumFoldKey {
            weights,
            extended_weights,
            degree,
            data,
        }
    }

    fn key_pair(structure: &O) -> (Self::VerifierKey, Self::ProverKey) {
        let key = Self::verifier_key(structure);
        (key.clone(), key)
    }

    fn params(_: &Self::VerifierKey) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: [SumcheckInstance<F, O>; 2],
        witness: [Vec<Mles<O::Function, F>>; 2],
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<SumcheckRelation<F, O>, Self::Proof> {
        let [mut w1, w2] = witness;

        let mut acc = SumcheckMessage::zero(key.degree);
        // Compute message with original function first.
        let _ = w1.iter().zip(w2.iter()).fold(&mut acc.0, |acc, evals| {
            let (e1, e2) = evals;
            let evals = [e1, e2];
            ProverKey::<F, O>::eval_acc(&key.data, acc, evals);
            acc
        });
        let message = acc;

        // Check against sums if provided.
        {
            assert_eq!(instance[0].sum, message.eval_at_0());
            assert_eq!(instance[1].sum, message.eval_at_1());
        }

        // Lock instance and generate challenge.
        let [beta] = transcript.send_message(&(), &());

        let eq_beta = SumcheckMessage::new_degree_n(F::one() - beta, beta, key.degree + 1);
        // Compute final message eq(beta,x) * f(x).
        // By doing it at the end, having to compute d+2 points in the whole hypercube is
        // avoided, it is done instead over d+1 points.
        // For that same reason the original message has to be extended to d+2 points.
        let message = {
            let extended = message.clone().extend(&key.weights);
            extended * eq_beta
        };
        // Message is sent and sumcheck challenge received.
        let [r] = transcript.send_message(&message, &(key.degree + 1));
        let message_at_r = message.eval_at_x(r, &key.extended_weights);

        // Checking that message agrees with sum.
        {
            let sum = instance[0].sum * (F::ONE - beta) + instance[1].sum * beta;
            let eval_zero = message.eval_at_0();
            let eval_one = message.eval_at_1();
            assert_eq!(sum, eval_zero + eval_one);
        };

        let proof = message;

        let instance = {
            let folder = FieldFolder::new(r);
            let [a, b] = instance;
            let oracle_instance = Foldable::fold(&folder, a.oracle_instance, b.oracle_instance);
            let eqr = r * beta + (F::one() - r) * (F::one() - beta);
            let sum = message_at_r / eqr;
            SumcheckInstance {
                sum,
                oracle_instance,
            }
        };

        // Witness is folded as expected from the sumcheck reduction.
        for (e1, e2) in w1.iter_mut().zip(w2.iter()) {
            let folded = e1.combine(e2, |e1, e2| (F::ONE - r) * e1 + r * e2);
            *e1 = folded;
        }
        let witness = w1;

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: [SumcheckInstance<F, O>; 2],
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<SumcheckInstance<F, O>, Self::Error> {
        let Ok((_, [beta])) = transcript.receive_message(|_| (), &GuardedProof::empty(), &());
        // eq(x,beta) = x * beta + (1-x) * (1-beta)
        // eq(0,beta) = 1 - beta
        // eq(1,beta) = beta
        let sum = (F::one() - beta) * instance[0].sum + beta * instance[1].sum;

        // A single sumcheck round, we get message from prover, generate challenge
        // r, check message agrees with original sum.
        // And then the work is reduced to a new sumcheck instance over the same polynomial
        // with 1 variable fixed with r.
        let (msg, [r]) = transcript
            .receive_message(Clone::clone, &proof, &(key.degree + 1))
            .map_err(SumcheckError::Degree)?;

        if sum != msg.eval_at_0() + msg.eval_at_1() {
            return Err(SumcheckError::RoundSum);
        }

        let eqr = r * beta + (F::one() - r) * (F::one() - beta);

        // This would be the sum of eq(beta,r) * f(r,...)
        let new_sum = msg.eval_at_x(r, &key.extended_weights);
        // Thus, removing eq(beta,r) leaves just the sum of f(r,...)
        let sum = new_sum / eqr;
        let oracle_instance = {
            let folder = FieldFolder::new(r);
            let [a, b] = instance;
            Foldable::fold(&folder, a.oracle_instance, b.oracle_instance)
        };
        Ok(SumcheckInstance {
            sum,
            oracle_instance,
        })
    }
}

impl<F, O> FoldingScheme<F, SumcheckRelation<F, O>> for SumFold<F, O>
where
    F: Field,
    O: Oracle<F>,
    O::Instance: Foldable<F>,
{
}
