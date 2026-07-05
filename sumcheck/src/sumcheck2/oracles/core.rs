use crate::{
    polynomials::MultiPoint,
    sumcheck2::{
        evals::EvalsCore,
        oracles::{
            composite::Either,
            partial::{Nature, OracleEval, OracleParams, PartialOracle, PartialQueryInstance},
            EvalLocation, SumcheckFunction,
        },
    },
};
use ark_ff::Field;
use sponge::sponge::Duplex;
use std::{convert::identity, marker::PhantomData, rc::Rc};
use transcript::reduction2::{
    Argument, GuardedProof, Message, ProverOutput, Reduction, Relation, Transcript,
    TranscriptBuilder, VerifierTranscript,
};

pub type Func<F> = fn(&[F], &MultiPoint<F>) -> F;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreOracle<F: Field, SF: SumcheckFunction<F>> {
    functions: SF::Mles<Func<F>>,
}

impl<F: Field, SF: SumcheckFunction<F>> CoreOracle<F, SF>
where
    SF::Natures: Nature,
{
    pub fn new(functions: SF::Mles<Option<Func<F>>>) -> Self {
        use CoreNature::*;
        let natures = SF::natures();
        let zero: Func<F> = |_, _| F::ZERO;
        let chall: Func<F> = |c, _| c[0];
        let functions: SF::Mles<Func<F>> = SF::combine(&natures, &functions, |nature, func| {
            let nature: Option<CoreNature> = nature.into_dynamic().into();
            match (nature, func) {
                (None, None) => zero,
                (None, Some(_)) => {
                    panic!("Small function provided when non was expected for this nature");
                }
                (Some(Challenge), None) => chall,
                (Some(SmallStructure | SmallInstance(_)), None) => {
                    panic!("Missing expected small function");
                }
                (Some(SmallStructure | SmallInstance(_)), Some(f)) => *f,
                (Some(Challenge), Some(_)) => {
                    panic!("Challenges are handled automatically, no function should be provided");
                }
            }
        });
        Self { functions }
    }

    /// TODO: doc
    pub fn set_witness(
        instance: &CoreOracleInstance<F, SF>,
        witness: &mut [SF::Mles<F>],
        filter: SF::Mles<bool>,
        generator: fn(&[F], &mut [SF::Mles<F>]),
    ) {
        assert!(witness.len().is_power_of_two());
        let vars = witness.len().ilog2() as usize;

        let coeffs = decode::<F, SF>(instance.elements.clone(), vars);
        let coeffs = SF::combine(&coeffs, &filter, |coeff, filter| match (filter, coeff) {
            (true, None) => {
                panic!("no coefficients available for MLE")
            }
            (true, coeff @ Some(_)) => coeff.clone(),
            (false, _) => None,
        });

        for coeff in coeffs.flatten_vec().into_iter().flatten() {
            generator(&coeff, witness);
        }
    }
}

#[derive(Clone, Debug)]
pub struct CoreOracleInstance<F, SF> {
    /// Elements which define small polynomials.
    elements: Vec<Vec<F>>,
    _f: PhantomData<SF>,
}

impl<F, SF> CoreOracleInstance<F, SF>
where
    F: Field,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
{
    /// For CoreNature::SmallInstance(Coeffs::Fixed(n)), vec![_,n] must be provided.
    /// For CoreNature::SmallInstance(Coeffs::PerVariable), vec![_,v] must be provided,
    /// with v the number of variables.
    /// For CoreNature::Challenge, vec![chall] must be provided.
    /// For every other nature, and empty vec should be used, any
    /// other cases will result in panic.
    pub fn new(coefficients: &SF::Mles<Vec<F>>, vars: usize) -> Self {
        use CoreNature::*;
        let natures = SF::natures();
        let coefficients = SF::combine(coefficients, &natures, |coeffs, nature| {
            let nature: Option<CoreNature> = nature.into_dynamic().into();
            match nature {
                Some(SmallInstance(Coeffs::Fixed(n))) => {
                    assert_eq!(coeffs.len(), n, "unexpected number of coefficients");
                    Some(coeffs.to_vec())
                }
                Some(SmallInstance(Coeffs::PerVariable)) => {
                    assert_eq!(coeffs.len(), vars, "unexpected number of coefficients");
                    Some(coeffs.to_vec())
                }
                Some(Challenge) => {
                    assert_eq!(
                        coeffs.len(),
                        1,
                        "other than 1 element provided for challenge"
                    );
                    Some(vec![coeffs[0]])
                }
                Some(SmallStructure) | None => {
                    assert!(
                        coeffs.is_empty(),
                        "no elements should be provided for this nature"
                    );
                    None
                }
            }
        });
        let elements = coefficients.flatten_vec().into_iter().flatten().collect();

        Self {
            elements,
            _f: PhantomData,
        }
    }
}

/// Unpacks the vector of coefficients into SF::Mles acording to SF::natures().
/// CoreNature::SmallStructure will get an empty vec![].
fn decode<F, SF>(coefficients: Vec<Vec<F>>, vars: usize) -> SF::Mles<Option<Vec<F>>>
where
    F: Field,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
{
    let natures = SF::natures();
    let mut coefficients = coefficients.into_iter();

    let evals = natures
        .flatten_vec()
        .into_iter()
        .map(|nature| {
            let nature: Option<CoreNature> = nature.into_dynamic().into();
            nature.map(|nature| match nature {
                CoreNature::SmallStructure => vec![],
                CoreNature::SmallInstance(Coeffs::Fixed(n)) => {
                    let coeff = coefficients.next().unwrap();
                    assert_eq!(n, coeff.len());
                    coeff
                }
                CoreNature::SmallInstance(Coeffs::PerVariable) => {
                    let coeff = coefficients.next().unwrap();
                    assert_eq!(vars, coeff.len());
                    coeff
                }
                CoreNature::Challenge => {
                    let coeff = coefficients.next().unwrap();
                    assert_eq!(1, coeff.len());
                    coeff
                }
            })
        })
        .collect();
    let evals = SF::Mles::unflatten_vec(evals);
    assert!(coefficients.next().is_none());
    evals
}

#[derive(Clone, Copy, Debug)]
pub enum CoreOracleError {
    MissingCoefficients,
    CoefficientsLength,
    UnexpectedCoefficients,
}

impl<F, SF> Message<F> for CoreOracleInstance<F, SF>
where
    F: Field,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
{
    type Params = OracleParams;

    type Error = CoreOracleError;

    fn len(params: &Self::Params) -> usize {
        let natures = SF::natures().flatten_vec();
        let mut len = 0;
        for nature in natures {
            let nature: Option<CoreNature> = nature.into_dynamic().into();
            let eval_len = match nature {
                Some(CoreNature::SmallStructure) => 0,
                Some(CoreNature::SmallInstance(Coeffs::Fixed(n))) => n,
                Some(CoreNature::SmallInstance(Coeffs::PerVariable)) => params.vars,
                Some(CoreNature::Challenge) => 1,
                None => 0,
            };
            len += eval_len;
        }
        len
    }

    fn to_field_elements(&self, params: &OracleParams) -> Result<Vec<F>, Self::Error> {
        use CoreOracleError::*;
        let natures = SF::natures().flatten_vec();

        let mut coefficients = self.elements.iter();

        for nature in natures {
            let nature: Option<CoreNature> = nature.into_dynamic().into();
            match nature {
                Some(CoreNature::SmallInstance(coeffs)) => {
                    let expected = match coeffs {
                        Coeffs::Fixed(n) => n,
                        Coeffs::PerVariable => params.vars,
                    };
                    if let Some(coeffs) = coefficients.next() {
                        if coeffs.len() != expected {
                            return Err(CoefficientsLength);
                        }
                    } else {
                        return Err(MissingCoefficients);
                    }
                }
                Some(CoreNature::Challenge) => {
                    if let Some(coeffs) = coefficients.next() {
                        if coeffs.len() != 1 {
                            return Err(CoefficientsLength);
                        }
                    } else {
                        return Err(MissingCoefficients);
                    }
                }
                _ => {}
            };
        }
        if coefficients.next().is_some() {
            return Err(UnexpectedCoefficients);
        }
        Ok(self.elements.iter().flatten().cloned().collect())
    }
}

/// The number of coefficients used to represent the small polynomial.
#[derive(Clone, Copy, Debug)]
pub enum Coeffs {
    Fixed(usize),
    PerVariable,
}

#[derive(Clone, Copy, Debug)]
pub enum CoreNature {
    SmallStructure,
    /// With n coefficients in the instance.
    SmallInstance(Coeffs),
    Challenge,
}

impl Nature for CoreNature {}

impl From<CoreNature> for EvalLocation {
    fn from(val: CoreNature) -> Self {
        use CoreNature::*;
        match val {
            SmallStructure => EvalLocation::Structure,
            SmallInstance(_) => EvalLocation::Witness,
            Challenge => EvalLocation::Instance,
        }
    }
}

impl<A> From<Either<CoreNature, A>> for Option<CoreNature> {
    fn from(value: Either<CoreNature, A>) -> Self {
        match value {
            Either::Left(x) => Some(x),
            Either::Right(_) => None,
        }
    }
}

impl<F: Field, SF: SumcheckFunction<F>> PartialOracle<F, SF> for CoreOracle<F, SF>
where
    SF::Natures: Nature,
{
    type Instance = CoreOracleInstance<F, SF>;

    type VerifierKey = Self;

    type Nature = CoreNature;

    type Builder = Self;

    type QueryRelation = CoreQueryRelation<F, SF>;

    fn build(builder: Self::Builder, _: &SF::Data, _: Rc<Vec<SF::Mles<F>>>) -> Self {
        //TODO: check that the structure is correct.
        builder
    }

    fn instance_evals(instance: &Self::Instance) -> SF::Mles<F> {
        let natures = SF::natures();
        let mut coefficients = instance.elements.iter();

        let evals = natures.flatten_vec().into_iter().map(|nature| {
            let nature: Option<CoreNature> = nature.into_dynamic().into();
            if let Some(nature) = nature {
                match nature {
                    CoreNature::SmallInstance(Coeffs::Fixed(n)) => {
                        let coeffs = coefficients.next().unwrap();
                        assert_eq!(coeffs.len(), n);
                        F::ZERO
                    }
                    CoreNature::Challenge => coefficients.next().unwrap()[0],
                    _ => F::ZERO,
                }
            } else {
                F::ZERO
            }
        });
        let evals = SF::Mles::unflatten_vec(evals.collect());
        assert!(coefficients.next().is_none());
        evals
    }

    fn evals(
        key: &Self::VerifierKey,
        instance: &Self::Instance,
        point: &MultiPoint<F>,
    ) -> SF::Mles<OracleEval<F>> {
        let coeffs = decode::<F, SF>(instance.elements.clone(), point.vars());
        let functions = &key.functions;
        SF::combine(functions, &coeffs, |function, coeff| {
            let eval = coeff.as_ref().map(|coeff| function(coeff, point));
            match eval {
                Some(e) => OracleEval::Computed(e),
                None => OracleEval::None,
            }
        })
    }
}

pub struct CoreQueryRelation<F, SF>(PhantomData<(F, SF)>);

impl<F, SF> Relation for CoreQueryRelation<F, SF>
where
    F: Field,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
{
    type Structure = CoreOracle<F, SF>;

    type Instance = PartialQueryInstance<F, SF, CoreOracleInstance<F, SF>>;

    type Witness = Vec<SF::Mles<F>>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        // While the PartialOracle trait fixes the type of the witness,
        // this relation has no witness.
        let _ = witness;
        let oracle_instance = instance.oracle_instance();
        let point = instance.point();
        let vars = point.vars();
        let expected_evals = instance.evals();

        let coefficients = decode::<F, SF>(oracle_instance.elements.clone(), vars);
        let functions = &structure.functions;

        let evals = SF::combine(functions, &coefficients, |func, coeff| {
            coeff.as_ref().map(|coeff| func(coeff, point))
        });
        let evals_valid = SF::combine(expected_evals, &evals, |expected, eval| {
            match (expected, eval) {
                (None, None) => true,
                (None, Some(_)) => panic!(),
                (Some(_), None) => false,
                (Some(expected), Some(eval)) => expected == eval,
            }
        });

        evals_valid.flatten_vec().into_iter().all(identity)
    }
}

impl<F, SF> Reduction<F, CoreQueryRelation<F, SF>, ()> for CoreOracle<F, SF>
where
    F: Field,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
{
    type ProverKey = Self;

    type VerifierKey = Self;

    type Proof = ();

    type Error = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        // It is a non-interactive protocol
        builder
    }

    fn verifier_key(oracle: &Self, _: &()) -> Self::VerifierKey {
        oracle.clone()
    }

    fn key_pair(oracle: &Self, _: &()) -> (Self::VerifierKey, Self::ProverKey) {
        (oracle.clone(), oracle.clone())
    }

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: PartialQueryInstance<F, SF, CoreOracleInstance<F, SF>>,
        witness: Vec<SF::Mles<F>>,
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<(), Self::Proof> {
        assert!(CoreQueryRelation::check(key, &instance, &witness));
        ProverOutput {
            instance: (),
            witness: (),
            proof: (),
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: PartialQueryInstance<F, SF, CoreOracleInstance<F, SF>>,
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<(), Self::Error> {
        // TODO: It would be better to implement it here with better errors
        // instead of relying on check().
        // As check doesn't make use of it.
        let witness = vec![];
        if CoreQueryRelation::check(key, &instance, &witness) {
            Ok(())
        } else {
            Err(())
        }
    }
}

impl<F, SF> Argument<F, CoreQueryRelation<F, SF>> for CoreOracle<F, SF>
where
    F: Field,
    SF: SumcheckFunction<F>,
    SF::Natures: Nature,
{
}
