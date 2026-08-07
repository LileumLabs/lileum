use crate::{
    SumcheckError, SumcheckMessage,
    barycentric_eval::BarycentricWeights,
    evals::{EvalsCore, Mles},
    folding::{FieldFolder, Foldable, folding_degree},
    oracles::{Oracle, OracleData, SumcheckFunction, partial::OracleParams},
    powers::CompactPowers,
    zerocheck::{ZeroSumcheck, ZeroSumcheckInstance},
};
use ark_ff::Field;
use reduction::{
    FoldingRelation, FoldingScheme, GuardedProof, Message, ProverOutput, Reduction, Relation,
    Transcript, TranscriptBuilder, VerifierTranscript,
};
use sponge::sponge::Duplex;
use std::marker::PhantomData;

/// Folding scheme for zerocheck.
#[derive(Clone, Copy, Debug)]
pub struct ZeroFold<F, O>(PhantomData<(F, O)>);

#[derive(Clone, Debug)]
pub struct ZeroFoldKey<F: Field, O: Oracle<F>> {
    degree: usize,
    vars: usize,
    // Weights for degrees d to (d + vars + 1).
    weights: Vec<BarycentricWeights<F>>,
    data: OracleData<F, O>,
    params: <O::Instance as Message<F>>::Params,
}

impl<F, O> Reduction<F, FoldingRelation<ZeroSumcheck<F, O>>, ZeroSumcheck<F, O>> for ZeroFold<F, O>
where
    F: Field,
    O: Oracle<F>,
    O::Instance: Foldable<F>,
{
    type ProverKey = ZeroFoldKey<F, O>;

    type VerifierKey = ZeroFoldKey<F, O>;

    type Proof = SumcheckMessage<F>;

    type Error = SumcheckError;

    type Params = (OracleParams, <O::Instance as Message<F>>::Params);

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        let degree = key.degree + key.vars + 1;
        builder
            .round::<F, (), 1>(&())
            .round::<F, SumcheckMessage<F>, 1>(&degree)
    }

    fn verifier_key(oracle: &O) -> Self::VerifierKey {
        let degree = folding_degree(oracle);
        let vars = oracle.vars();
        let weights = (0..=(vars + 1))
            .map(|i| BarycentricWeights::compute((degree + i) as u32))
            .collect();
        let data = oracle.data().clone();
        let params = oracle.oracle_params();
        ZeroFoldKey {
            degree,
            vars,
            weights,
            data,
            params,
        }
    }

    fn key_pair(structure: &O) -> (Self::VerifierKey, Self::ProverKey) {
        let key = Self::verifier_key(structure);
        (key.clone(), key)
    }

    fn params(key: &Self::VerifierKey) -> Self::Params {
        let vars = key.vars;
        (OracleParams { vars }, key.params)
    }

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: [ZeroSumcheckInstance<F, O>; 2],
        witness: [Vec<Mles<O::Function, F>>; 2],
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<ZeroSumcheck<F, O>, Self::Proof> {
        let powers = instance
            .each_ref()
            .map(|instance| instance.zerocheck_powers.clone());

        let message = key.sum_messages(witness.each_ref().map(Vec::as_slice), powers);

        assert_eq!(instance[0].sum, message.eval_at_0());
        assert_eq!(instance[1].sum, message.eval_at_1());

        let [beta] = transcript.send_message(&(), &());

        let eq_beta =
            SumcheckMessage::new_degree_n(F::one() - beta, beta, key.degree + key.vars + 1);
        // Compute final message eq(beta,x) * f(x).
        // By doing it at the end, having to compute d+2 points in the whole hypercube is
        // avoided, it is done instead over d+1 points.
        // For that same reason the original message has to be extended to d+2 points.
        let message = {
            let extended = message.clone().extend(&key.weights[key.vars]);
            extended * eq_beta
        };
        // Message is sent and sumcheck challenge received.
        let [r] = transcript.send_message(&message, &(key.degree + key.vars + 1));

        // Checking that message agrees with sum.
        {
            let sum = instance[0].sum * (F::ONE - beta) + instance[1].sum * beta;
            let eval_zero = message.eval_at_0();
            let eval_one = message.eval_at_1();
            assert_eq!(sum, eval_zero + eval_one);
        };

        let sum = {
            let sum = message.eval_at_x(r, &key.weights[key.vars + 1]);
            let eqr = r * beta + (F::one() - r) * (F::one() - beta);
            sum / eqr
        };

        let proof = message;

        let [mut w1, w2] = witness;
        // Witness is folded as expected from the sumcheck reduction.
        for (e1, e2) in w1.iter_mut().zip(w2.iter()) {
            let folded = e1.combine(e2, |e1, e2| (F::ONE - r) * e1 + r * e2);
            *e1 = folded;
        }
        let witness = w1;

        let folder = FieldFolder::new(r);
        let [ins1, ins2] = instance;
        let oracle_instance =
            O::Instance::fold(&folder, ins1.oracle_instance, ins2.oracle_instance);
        let zerocheck_powers = folder.fold_powers(ins1.zerocheck_powers, ins2.zerocheck_powers);

        let instance = ZeroSumcheckInstance {
            sum,
            zerocheck_powers,
            oracle_instance,
        };

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: [ZeroSumcheckInstance<F, O>; 2],
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<<ZeroSumcheck<F, O> as Relation>::Instance, Self::Error> {
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
            .receive_message(Clone::clone, &proof, &(key.degree + key.vars + 1))
            .map_err(SumcheckError::Degree)?;

        if sum != msg.eval_at_0() + msg.eval_at_1() {
            return Err(SumcheckError::RoundSum);
        }

        let eqr = r * beta + (F::one() - r) * (F::one() - beta);

        // This would be the sum of eq(beta,r) * f(r,...)
        let new_sum = msg.eval_at_x(r, &key.weights[key.vars + 1]);
        // Thus, removing eq(beta,r) leaves just the sum of f(r,...)
        let sum = new_sum / eqr;
        let (oracle_instance, zerocheck_powers) = {
            let folder = FieldFolder::new(r);
            let [a, b] = instance;
            let oracle = Foldable::fold(&folder, a.oracle_instance, b.oracle_instance);
            let powers = folder.fold_powers(a.zerocheck_powers, b.zerocheck_powers);
            (oracle, powers)
        };

        Ok(ZeroSumcheckInstance {
            sum,
            zerocheck_powers,
            oracle_instance,
        })
    }
}

impl<F, O> FoldingScheme<F, ZeroSumcheck<F, O>> for ZeroFold<F, O>
where
    F: Field,
    O: Oracle<F>,
    O::Instance: Foldable<F>,
{
}

impl<F: Field, O: Oracle<F>> ZeroFoldKey<F, O> {
    fn sum_messages(
        &self,
        witness: [&[Mles<O::Function, F>]; 2],
        powers: [CompactPowers<F>; 2],
    ) -> SumcheckMessage<F> {
        let [w1, w2] = witness;
        assert_eq!(w1.len(), w2.len());

        let base_weights = &self.weights[0];
        let mut messages = Vec::with_capacity(w1.len() * base_weights.domain_size());

        let powers_left = powers[0].factors();
        let powers_right = powers[1].factors();

        let powers_even = SumcheckMessage::new_degree_n(
            powers_left[0].1,
            powers_right[0].1,
            base_weights.domain_size() - 1,
        );
        let powers_even_last = base_weights.extend(powers_even.inner());

        let powers_odd = SumcheckMessage::new_degree_n(
            powers_left[0].0,
            powers_right[0].0,
            base_weights.domain_size() - 1,
        );
        let powers_odd_last = base_weights.extend(powers_odd.inner());

        let [mut res0, mut res1] = [(); 2].map(|_| vec![F::ZERO; self.degree + 1]);
        // Multiply the first variable and fold into Vec<F>.
        for i in 0..(w1.len() / 2) {
            let evals = [&w1[i * 2], &w2[i * 2]];
            O::Function::eval_into(&self.data, &mut res0, evals);
            let evals = [&w1[i * 2 + 1], &w2[i * 2 + 1]];
            O::Function::eval_into(&self.data, &mut res1, evals);
            for i in 0..res0.len() {
                let even = res0[i] * powers_even.inner()[i];
                let odd = res1[i] * powers_odd.inner()[i];
                messages.push(even + odd);
            }
            let res0 = base_weights.extend(&res0);
            let res1 = base_weights.extend(&res1);
            messages.push(res0 * powers_even_last + res1 * powers_odd_last);
        }

        // Repeat with the rest of variables until a single message is left.
        let message = powers_left
            .iter()
            .zip(powers_right)
            .zip(&self.weights)
            .skip(1)
            .fold(messages, |messages, (powers, weights)| {
                let (powers_left, powers_right) = powers;
                let powers_even = [powers_left.1, powers_right.1];
                let powers_odd = [powers_left.0, powers_right.0];
                let powers = [powers_even, powers_odd];
                Self::fold_with_powers(powers, messages, weights)
            });

        assert_eq!(message.len(), self.weights[self.vars].domain_size());
        SumcheckMessage::new(message)
    }

    fn fold_with_powers(
        powers: [[F; 2]; 2],
        messages: Vec<F>,
        weights: &BarycentricWeights<F>,
    ) -> Vec<F> {
        let [powers_even, powers_odd] = powers;
        // As domain_size = degree + 1.
        let powers_degree = weights.domain_size();
        let powers_even =
            SumcheckMessage::new_degree_n(powers_even[0], powers_even[1], powers_degree - 1);
        let powers_even = powers_even.inner();
        let powers_even_last = weights.extend(powers_even);
        let powers_odd =
            SumcheckMessage::new_degree_n(powers_odd[0], powers_odd[1], powers_degree - 1);
        let powers_odd = powers_odd.inner();
        let powers_odd_last = weights.extend(powers_odd);
        assert_eq!(messages.len() % weights.domain_size(), 0);
        let n = messages.len() / weights.domain_size();

        let mut res = vec![];

        for i in 0..(n / 2) {
            let size = weights.domain_size();
            let offset = i * size * 2;
            let messages = &messages[offset..offset + size * 2];
            let (msg0, msg1) = messages.split_at(size);
            for i in 0..msg0.len() {
                let even = msg0[i] * powers_even[i];
                let odd = msg1[i] * powers_odd[i];
                res.push(even + odd);
            }
            let msg0 = weights.extend(msg0);
            let msg1 = weights.extend(msg1);
            res.push(msg0 * powers_even_last + msg1 * powers_odd_last);
        }
        assert_eq!(res.len(), (n / 2) * (weights.domain_size() + 1));
        res
    }

    pub fn params(&self) -> <<O as Oracle<F>>::Instance as Message<F>>::Params {
        self.params
    }
}
