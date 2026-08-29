use crate::{
    MultiPoint, OracleQueryInstance,
    oracles::{EvalLocation, Oracle, QueryRelation, SumcheckFunction},
};
use alloc::{fmt::Debug, rc::Rc, vec::Vec};
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use reduction::{
    Argument, GuardedProof, Message, ProverOutput, Reduction, Relation, Transcript,
    TranscriptBuilder, VerifierTranscript,
};
use sponge::sponge::Duplex;

#[derive(Clone, Debug)]
/// An oracle over MLEs which have a small representation and
/// can be cheaply evaluated over a point by the verifier.
pub struct SmallEvalOracle<F: Field, SF: SumcheckFunction<F>> {
    data: SF::Data,
    evals_over_domain: Rc<Vec<SF::Mles<F>>>,
    evals: SF::Mles<fn(&MultiPoint<F>) -> F>,
    vars: usize,
}

impl<F: Field, SF: SumcheckFunction<F>> CanonicalSerialize for SmallEvalOracle<F, SF> {
    fn serialize_with_mode<W: ark_serialize::Write>(
        &self,
        _writer: W,
        _compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        // Left unimplemented for now as this protocol is just for testing.
        todo!()
    }

    fn serialized_size(&self, _compress: ark_serialize::Compress) -> usize {
        todo!()
    }
}

impl<F: Field, SF: SumcheckFunction<F>> SmallEvalOracle<F, SF> {
    pub fn new(
        data: SF::Data,
        evals_over_domain: Option<Vec<SF::Mles<F>>>,
        evals: SF::Mles<fn(&MultiPoint<F>) -> F>,
        vars: usize,
    ) -> Self {
        let evals_over_domain = match evals_over_domain {
            Some(evals) => {
                assert_eq!(evals.len().ilog2() as usize, vars);
                evals
            }
            None => {
                // TODO: eval over domain
                todo!()
            }
        };
        let evals_over_domain = Rc::new(evals_over_domain);
        Self {
            data,
            evals_over_domain,
            evals,
            vars,
        }
    }
}

/// A polynomial with a small representation fixed in the
/// structure
#[derive(Clone, Copy, Debug)]
pub struct SmallNature;

impl From<SmallNature> for EvalLocation {
    fn from(_value: SmallNature) -> Self {
        EvalLocation::Structure
    }
}

impl<F: Field, SF: SumcheckFunction<F>> Oracle<F> for SmallEvalOracle<F, SF> {
    type Function = SF;

    type Instance = ();

    type Witness = ();

    type Nature = SmallNature;

    fn structure(&self) -> Rc<Vec<SF::Mles<F>>> {
        self.evals_over_domain.clone()
    }

    fn data(&self) -> &<Self::Function as SumcheckFunction<F>>::Data {
        &self.data
    }

    fn vars(&self) -> usize {
        self.vars
    }

    fn oracle_params(&self) -> <Self::Instance as Message<F>>::Params {}

    fn eval(&self, point: &MultiPoint<F>, _instance: &(), _witness: &()) -> SF::Mles<F> {
        SF::map_evals(&self.evals, |f| f(point))
    }

    fn witness_from_evals(_evals: Vec<SF::Mles<F>>) -> Self::Witness {}

    fn instance_evals(_instance: &()) -> SF::Mles<F> {
        SF::map_evals(&SF::natures(), |_| F::ZERO)
    }

    fn natures(&self) -> SF::Mles<Self::Nature> {
        // We just take some random available value of type Self::Evals.
        let evals = &self.evals_over_domain[0];
        SF::map_evals(evals, |_| SmallNature)
    }
}

/// An argument for the QueryRelation over the small oracle.
pub struct SmallOracleArgument;

type Rel<F, SF> = QueryRelation<F, SmallEvalOracle<F, SF>>;

impl<F, SF> Reduction<F, Rel<F, SF>, ()> for SmallOracleArgument
where
    F: Field,
    SF: SumcheckFunction<F>,
    <Rel<F, SF> as Relation>::Instance: Message<F, Params = ((), usize)>,
{
    type ProverKey = SmallEvalOracle<F, SF>;

    type VerifierKey = SmallEvalOracle<F, SF>;

    type Proof = ();

    type Error = ();

    type Params = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        // It is essentially a non-interactive protocol.
        builder
    }

    fn verifier_key(structure: &SmallEvalOracle<F, SF>) -> Self::VerifierKey {
        structure.clone()
    }

    fn key_pair(
        structure: &<Rel<F, SF> as Relation>::Structure,
    ) -> (Self::VerifierKey, Self::ProverKey) {
        (structure.clone(), structure.clone())
    }

    fn params(_: &Self::VerifierKey) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: <Rel<F, SF> as Relation>::Instance,
        _witness: <Rel<F, SF> as Relation>::Witness,
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<(), Self::Proof> {
        ProverOutput {
            instance: (),
            witness: (),
            proof: (),
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: OracleQueryInstance<F, ()>,
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<(), Self::Error> {
        match QueryRelation::check(key, &instance, &()) {
            true => Ok(()),
            false => Err(()),
        }
    }
}

impl<F, SF> Argument<F, Rel<F, SF>> for SmallOracleArgument
where
    F: Field,
    SF: SumcheckFunction<F>,
    <Rel<F, SF> as Relation>::Instance: Message<F, Params = ((), usize)>,
{
}
