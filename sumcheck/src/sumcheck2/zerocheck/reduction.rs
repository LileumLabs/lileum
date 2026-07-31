use crate::{
    polynomials::MultiPoint,
    sumcheck2::{
        evals::{Evals, Mles},
        oracles::{partial::OracleParams, Oracle, OracleData, QueryRelation, SumcheckFunction},
        prove,
        reduction::SumcheckVerifierKey,
        zerocheck::{ZeroSumcheck, ZeroSumcheckInstance, Zerocheck},
        OracleQueryInstance, SumcheckError, SumcheckInstance, SumcheckMessage, SumcheckReduction,
    },
    zerocheck::{CompactPowers, ShrinkingPowers},
};
use ark_ff::Field;
use sponge::sponge::Duplex;
use std::marker::PhantomData;
use transcript::reduction2::{
    GuardedProof, Message, NoError, ProverOutput, Reduction, Relation, Transcript,
    TranscriptBuilder, VerifierTranscript,
};

#[derive(Clone, Copy, Debug)]
pub struct ZerocheckReduction<F, O>(PhantomData<(F, O)>);

impl<F, O> Reduction<F, Zerocheck<F, O>, ZeroSumcheck<F, O>> for ZerocheckReduction<F, O>
where
    F: Field,
    O: Oracle<F>,
{
    type ProverKey = usize;

    type VerifierKey = usize;

    type Proof = ();

    type Error = NoError;

    type Params = ();

    fn transcript_pattern(_: &Self::VerifierKey, builder: TranscriptBuilder) -> TranscriptBuilder {
        builder.round::<F, (), 1>(&())
    }

    fn verifier_key(oracle: &O) -> Self::VerifierKey {
        oracle.vars()
    }

    fn key_pair(oracle: &O) -> (Self::VerifierKey, Self::ProverKey) {
        let vars = oracle.vars();
        (vars, vars)
    }

    fn params(_: &Self::VerifierKey) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        key: &usize,
        instance: O::Instance,
        witness: Vec<Mles<O::Function, F>>,
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<ZeroSumcheck<F, O>, Self::Proof> {
        let vars = *key;
        let [chall] = transcript.send_message(&(), &());
        let zerocheck_powers = CompactPowers::new(chall, vars);

        let instance = ZeroSumcheckInstance {
            sum: F::ZERO,
            zerocheck_powers,
            oracle_instance: instance,
        };

        ProverOutput {
            instance,
            witness,
            proof: (),
        }
    }

    fn verify<S: Duplex<F>>(
        key: &usize,
        instance: <Zerocheck<F, O> as Relation>::Instance,
        proof: GuardedProof<()>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<<ZeroSumcheck<F, O> as Relation>::Instance, Self::Error> {
        let vars = *key;

        let Ok(((), [chall])) = transcript.receive_message(|_| (), &proof, &());

        let zerocheck_powers = CompactPowers::new(chall, vars);

        Ok(ZeroSumcheckInstance {
            sum: F::ZERO,
            zerocheck_powers,
            oracle_instance: instance,
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ZerocheckSumcheckReduction<F, O>(PhantomData<(F, O)>);

impl<F: Field, O: Oracle<F>> Reduction<F, ZeroSumcheck<F, O>, QueryRelation<F, O>>
    for ZerocheckSumcheckReduction<F, O>
{
    type ProverKey = prove::ProverKey<F, O>;

    type VerifierKey = SumcheckVerifierKey<F, O>;

    type Proof = Vec<SumcheckMessage<F>>;

    type Error = SumcheckError;

    type Params = (OracleParams, <O::Instance as Message<F>>::Params);

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        SumcheckReduction::<F, O>::transcript_pattern(key, builder)
    }

    fn verifier_key(structure: &O) -> Self::VerifierKey {
        SumcheckReduction::verifier_key(structure).increase_degree()
    }

    fn key_pair(structure: &O) -> (Self::VerifierKey, Self::ProverKey) {
        let (verifier_key, prover_key) = SumcheckReduction::key_pair(structure);
        (verifier_key.increase_degree(), prover_key.increase_degree())
    }

    fn params(key: &Self::VerifierKey) -> Self::Params {
        let oracle_params = SumcheckReduction::<F, O>::params(key);
        let vars = key.vars();
        (OracleParams { vars }, oracle_params)
    }

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: ZeroSumcheckInstance<F, O>,
        witness: Vec<Mles<O::Function, F>>,
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<QueryRelation<F, O>, Self::Proof> {
        let ZeroSumcheckInstance {
            sum,
            zerocheck_powers,
            oracle_instance,
        } = instance;

        let instance_evals = O::instance_evals(&oracle_instance);
        let witness = key.prepare_witness(witness, instance_evals);
        let (messages, point, eval) =
            key.prove_zerocheck(witness.clone(), transcript, sum, zerocheck_powers);

        let instance = OracleQueryInstance {
            oracle_instance,
            point,
            eval,
        };

        let proof = messages;

        let witness = O::witness_from_evals(witness);

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: ZeroSumcheckInstance<F, O>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<<QueryRelation<F, O> as Relation>::Instance, Self::Error> {
        let ZeroSumcheckInstance {
            sum,
            zerocheck_powers,
            oracle_instance,
        } = instance;
        let instance = SumcheckInstance::new(sum, oracle_instance);
        let mut reduced = SumcheckReduction::<F, O>::verify(key, instance, proof, transcript)?;
        let powers_eval = zerocheck_powers.point_eval(&reduced.point);

        // As the check will be f(r) * z(r) = eval
        // We can take it off here and have the same output as normal sumcheck.
        // Checking instead f(r) = eval / z(r)
        reduced.eval /= powers_eval;
        Ok(reduced)
    }
}

impl<F: Field, O: Oracle<F>> prove::ProverKey<F, O> {
    fn prove_zerocheck<S: Duplex<F>>(
        &self,
        mut witness: Vec<Mles<O::Function, F>>,
        transcript: &mut Transcript<F, S>,
        mut sum: F,
        powers: CompactPowers<F>,
    ) -> (Vec<SumcheckMessage<F>>, MultiPoint<F>, F) {
        let mut powers_over_domain = powers.eval_over_domain();
        let mut shrinking_powers = ShrinkingPowers::new(powers);

        let mut vars = vec![];
        let mut messages = vec![];

        for _ in 0..self.vars() {
            let message = self.zerocheck_message(&witness, &powers_over_domain, sum);
            // To dissable the optimization after the first round.
            sum = F::ONE;
            let degree = self.degree();
            let [r] = transcript.send_message(&message, &degree);

            self.bind_variable(&mut witness, r);
            powers_over_domain = shrinking_powers.fix(r);
            vars.push(r);
            messages.push(message);
        }

        assert_eq!(witness.len(), 1);

        let data = self.data();
        let eval: F = O::Function::function(data, &witness[0]);

        vars.reverse();
        let point = MultiPoint::new(vars);

        (messages, point, eval)
    }

    /// Self::message specialized for zerocheck.
    fn zerocheck_message(
        &self,
        mles: &[Mles<O::Function, F>],
        powers: &[F],
        sum: F,
    ) -> SumcheckMessage<F> {
        assert!(mles.len().is_power_of_two());

        let degree = self.degree();

        let (left, right) = mles.split_at(mles.len() / 2);

        let data = self.data();

        let powers = {
            let (left, right) = powers.split_at(mles.len() / 2);
            left.iter().zip(right).map(|(left, right)| [*left, *right])
        };

        let mut message = vec![F::zero(); degree + 1];
        for ((left, right), powers) in left.iter().zip(right).zip(powers) {
            Self::zerocheck_eval_acc(data, &mut message, [left, right], powers, sum.is_zero());
        }

        SumcheckMessage(message)
    }

    fn zerocheck_eval_acc(
        data: &OracleData<F, O>,
        acc: &mut [F],
        evals: [&Mles<O::Function, F>; 2],
        powers: [F; 2],
        sums_to_zero: bool,
    ) {
        // NOTE: In zerocheck, if evaluations at 0 and 1 are zero,
        // we don't even need to compute them.
        let [left, right] = evals;
        // The last evaluations, and what is needed to compute the next.
        let mut e = <O::Function as Evals>::combine::<F, F, _, _>(left, right, |e0, e1| {
            let coeff = *e1 - e0;
            let mut last_eval = *e0;
            if sums_to_zero {
                last_eval += coeff.double();
            };
            (last_eval, coeff)
        });

        // Similarly to the powers use for zerocheck
        let [powl, powr] = powers;
        let power_coeff = powr - powl;
        let mut last_power = powl;
        if sums_to_zero {
            last_power += power_coeff.double();
        }

        let acc: &mut [F] = if sums_to_zero { &mut acc[2..] } else { acc };

        for m in acc.iter_mut() {
            let evals = <O::Function as Evals>::map_evals(&e, |(eval, _)| *eval);
            let eval = O::Function::function(data, &evals);

            *m += eval * last_power;
            <O::Function as Evals>::apply(&mut e, |(last, coeff)| {
                *last += coeff;
            });
            last_power += power_coeff;
        }
    }
}
