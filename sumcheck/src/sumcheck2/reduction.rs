use crate::{
    barycentric_eval::BarycentricWeights,
    polynomials::MultiPoint,
    sumcheck2::{
        degree,
        evals::Mles,
        oracles::{Oracle, QueryRelation},
        prove, OracleQueryInstance, SumcheckInstance, SumcheckMessage, SumcheckRelation,
    },
};
use ark_ff::Field;
use sponge::sponge::Duplex;
use std::{fmt::Debug, marker::PhantomData};
use transcript::reduction2::{
    GuardedProof, Message, ProverOutput, Reduction, Relation, Transcript, TranscriptBuilder,
    VerifierTranscript,
};

impl<F: Field> SumcheckMessage<F> {
    pub fn to_message(&self) -> crate::message::Message<F> {
        crate::message::Message::new(self.0.clone())
    }
}

/// A sumcheck message had an unexpected degree.
#[derive(Clone, Copy, Debug)]
pub struct UnexpectedDegree;

impl<F: Field> Message<F> for SumcheckMessage<F> {
    /// For the number of variables.
    type Params = usize;

    type Error = UnexpectedDegree;

    fn len(params: &Self::Params) -> usize {
        *params + 1
    }

    fn to_field_elements(&self, params: &Self::Params) -> Result<Vec<F>, Self::Error> {
        if self.0.len() == (params + 1) {
            Ok(self.0.clone())
        } else {
            Err(UnexpectedDegree)
        }
    }
}

/// The sumcheck reduction from the sumcheck relation to
/// the oracle query relation.
#[derive(Clone, Debug)]
pub struct SumcheckReduction<F, O>(PhantomData<(F, O)>);

#[derive(Clone, Copy, Debug)]
/// The error of the sumcheck reduction.
pub enum SumcheckError {
    /// Some message had the wrong degree.
    Degree(UnexpectedDegree),
    /// In some round, the 2 new sums didn't add up to the original sum.
    RoundSum,
}

/// The verifier key of the sumcheck reduction.
pub struct SumcheckVerifierKey<F: Field, O: Oracle<F>> {
    // oracle_instance_params: <SumcheckInstance<F, O> as Message<F>>::Params,
    degree: usize,
    vars: usize,
    weights: BarycentricWeights<F>,
    /// Message::Params of the oracle instance.
    params: <O::Instance as Message<F>>::Params,
}

impl<F: Field, O: Oracle<F>> SumcheckVerifierKey<F, O> {
    pub fn vars(&self) -> usize {
        self.vars
    }

    /// Increases the degree by 1, to be used by zerocheck
    /// which adds an extra multiplication at the end.
    pub(crate) fn increase_degree(mut self) -> Self {
        self.degree += 1;
        self.weights = BarycentricWeights::compute(self.degree as u32);
        self
    }
}

impl<F: Field, O: Oracle<F>> Reduction<F, SumcheckRelation<F, O>, QueryRelation<F, O>>
    for SumcheckReduction<F, O>
{
    type ProverKey = prove::ProverKey<F, O>;

    type VerifierKey = SumcheckVerifierKey<F, O>;

    type Proof = Vec<SumcheckMessage<F>>;

    type Error = SumcheckError;

    type Params = <O::Instance as Message<F>>::Params;

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        let degree = &key.degree;
        (0..key.vars).fold(builder, |builder, _| {
            builder.round::<F, SumcheckMessage<F>, 1>(degree)
        })
    }

    fn verifier_key(
        structure_1: &O,
        _structure_2: &<QueryRelation<F, O> as Relation>::Structure,
    ) -> Self::VerifierKey {
        let vars = structure_1.vars();
        let degree = degree::sumcheck_degree(structure_1);

        let weights = BarycentricWeights::compute(degree as u32);

        // let oracle_instance_params = structure_1.oracle_params();
        let params = structure_1.oracle_params();

        SumcheckVerifierKey {
            // oracle_instance_params,
            degree,
            vars,
            weights,
            params,
        }
    }

    fn key_pair(
        structure_1: &O,
        structure_2: &<QueryRelation<F, O> as Relation>::Structure,
    ) -> (Self::VerifierKey, Self::ProverKey) {
        let verifier_key = Self::verifier_key(structure_1, structure_2);
        let prover_key = prove::ProverKey::new(structure_1);
        (verifier_key, prover_key)
    }

    fn params(key: &Self::VerifierKey) -> Self::Params {
        key.params
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: SumcheckInstance<F, O>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<<QueryRelation<F, O> as Relation>::Instance, Self::Error> {
        let mut sum = instance.sum;

        let mut vars = vec![];
        for i in 0..key.vars {
            let (message, [r]) = transcript
                .receive_message(|proof| proof[i].clone(), &proof, &key.degree)
                .map_err(SumcheckError::Degree)?;

            let message = message.to_message();

            let e0 = message.eval_at_0();
            let e1 = message.eval_at_1();
            if e0 + e1 != sum {
                return Err(SumcheckError::RoundSum);
            }
            vars.push(r);
            sum = message.eval_at_x(r, &key.weights);
        }
        vars.reverse();
        let eval = sum;
        let point = MultiPoint::new(vars);
        let instance = OracleQueryInstance {
            oracle_instance: instance.oracle_instance,
            point,
            eval,
        };
        Ok(instance)
    }

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: SumcheckInstance<F, O>,
        witness: Vec<Mles<O::Function, F>>,
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<QueryRelation<F, O>, Self::Proof> {
        let instance_evals = O::instance_evals(&instance.oracle_instance);
        let witness = key.prepare_witness(witness, instance_evals);
        let (messages, point, eval) = key.prove(witness.clone(), transcript);

        let instance = OracleQueryInstance {
            oracle_instance: instance.oracle_instance,
            point,
            eval,
        };

        let witness = O::witness_from_evals(witness);

        let proof = messages;

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }
}
