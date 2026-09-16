use crate::{
    MultiPoint, OracleQueryInstance,
    evals::{EvalsCore, EvalsExt},
    folding::{FieldFolder, Foldable},
    oracles::{
        EvalLocation, Oracle, QueryRelation, SumcheckFunction,
        partial::{
            Nature, OracleEval, OracleParams, PartialOracle, PartialQueryInstance,
            PartialQueryRelation,
        },
    },
};
use alloc::{rc::Rc, vec::Vec};
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use core::{fmt::Debug, marker::PhantomData, panic};
use reduction::{
    GuardedProof, Message, ProverOutput, Reduction, Relation, Transcript, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A, B> CanonicalSerialize for Either<A, B>
where
    A: CanonicalSerialize,
    B: CanonicalSerialize,
{
    fn serialize_with_mode<W: ark_serialize::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        match self {
            Either::Left(x) => {
                false.serialize_with_mode(&mut writer, compress)?;
                x.serialize_with_mode(writer, compress)
            }
            Either::Right(x) => {
                true.serialize_with_mode(&mut writer, compress)?;
                x.serialize_with_mode(writer, compress)
            }
        }
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        match self {
            Either::Left(x) => false.serialized_size(compress) + x.serialized_size(compress),
            Either::Right(x) => true.serialized_size(compress) + x.serialized_size(compress),
        }
    }
}

impl<A, B> From<Either<A, B>> for EvalLocation
where
    A: Into<EvalLocation>,
    B: Into<EvalLocation>,
{
    fn from(value: Either<A, B>) -> Self {
        match value {
            Either::Left(a) => a.into(),
            Either::Right(b) => b.into(),
        }
    }
}

impl<A, B, C> From<Either<A, Either<B, C>>> for Option<Either<B, C>> {
    fn from(val: Either<A, Either<B, C>>) -> Self {
        match val {
            Either::Left(_) => None,
            Either::Right(x) => Some(x),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompositeOracle<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
{
    data: SF::Data,
    mles: Rc<Vec<SF::Mles<F>>>,
    vars: usize,
    evals_per_oracle: SF::Mles<Either<(), ()>>,
    partial_oracles: (P1, P2),
}

impl<F, SF, P1, P2> CompositeOracle<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
    SF::Natures: Into<Option<Either<P1::Nature, P2::Nature>>>,
{
    pub fn new(
        data: SF::Data,
        mles: Rc<Vec<SF::Mles<F>>>,
        builder1: P1::Builder,
        builder2: P2::Builder,
    ) -> Self {
        let vars = mles.len().next_power_of_two().ilog2() as usize;

        let evals_per_oracle = SF::map_evals(&SF::natures(), |nature| {
            let nature: Option<Either<P1::Nature, P2::Nature>> = (*nature).into();
            match nature {
                Some(Either::Left(_)) => Either::Left(()),
                // If it belongs to neither, it is assigned to right by default.
                // Something that could happen when nesting partial oracles, in
                // such case the incoming eval would always be None.
                Some(Either::Right(_)) | None => Either::Right(()),
            }
        });
        let partial_oracle1 = P1::build(builder1, &data, Rc::clone(&mles));
        let partial_oracle2 = P2::build(builder2, &data, Rc::clone(&mles));
        let partial_oracles = (partial_oracle1, partial_oracle2);
        Self {
            data,
            mles,
            vars,
            evals_per_oracle,
            partial_oracles,
        }
    }

    pub fn inner_oracles(&self) -> &(P1, P2) {
        &self.partial_oracles
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CompositeOracleInstance<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    pub oracle1_instance: P1::Instance,
    pub oracle2_instance: P2::Instance,
}

impl<F, SF, P1, P2> PartialEq for CompositeOracleInstance<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
    P1::Instance: PartialEq,
    P2::Instance: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.oracle1_instance == other.oracle1_instance
            && self.oracle2_instance == other.oracle2_instance
    }
}

impl<F, SF, P1, P2> Eq for CompositeOracleInstance<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
    P1::Instance: Eq,
    P2::Instance: Eq,
{
}

impl<F, SF, P1, P2> Foldable<F> for CompositeOracleInstance<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
    P1::Instance: Foldable<F>,
    P2::Instance: Foldable<F>,
{
    fn fold(folder: &FieldFolder<F>, a: Self, b: Self) -> Self {
        let oracle1_instance = P1::Instance::fold(folder, a.oracle1_instance, b.oracle1_instance);
        let oracle2_instance = P2::Instance::fold(folder, a.oracle2_instance, b.oracle2_instance);
        Self {
            oracle1_instance,
            oracle2_instance,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum CompositeError<F, P1: Message<F>, P2: Message<F>> {
    Oracle1(P1::Error),
    Oracle2(P2::Error),
    UnexpectedLenght,
}

impl<F, SF, P1, P2> Message<F> for CompositeOracleInstance<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    type Params = OracleParams;

    type Error = CompositeError<F, P1::Instance, P2::Instance>;

    fn len(params: &Self::Params) -> usize {
        P1::Instance::len(params) + P2::Instance::len(params)
    }

    fn to_field_elements(&self, params: &OracleParams) -> Result<Vec<F>, Self::Error> {
        use CompositeError::*;

        let mut elems = self
            .oracle1_instance
            .to_field_elements(params)
            .map_err(Oracle1)?;

        elems.extend(
            self.oracle2_instance
                .to_field_elements(params)
                .map_err(Oracle2)?,
        );

        Ok(elems)
    }
}

impl<F, SF, P1, P2> Oracle<F> for CompositeOracle<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F, Natures = Either<P1::Nature, P2::Nature>>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    type Function = SF;

    type Instance = CompositeOracleInstance<F, SF, P1, P2>;

    type Witness = Vec<SF::Mles<F>>;

    type Nature = Either<P1::Nature, P2::Nature>;

    fn instance_evals(instance: &Self::Instance) -> SF::Mles<F> {
        let natures = SF::natures().flatten_vec();
        let evals_oracle1 = P1::instance_evals(&instance.oracle1_instance).flatten_vec();
        assert_eq!(natures.len(), evals_oracle1.len());
        let evals_oracle2 = P2::instance_evals(&instance.oracle2_instance).flatten_vec();
        assert_eq!(natures.len(), evals_oracle2.len());

        let mut evals = Vec::new();

        for ((o1, o2), nature) in evals_oracle1.into_iter().zip(evals_oracle2).zip(natures) {
            let eval = match nature {
                Either::Left(_) => o1,
                Either::Right(_) => o2,
            };
            evals.push(eval);
        }

        SF::Mles::unflatten_vec(evals)
    }

    fn structure(&self) -> Rc<Vec<SF::Mles<F>>> {
        Rc::clone(&self.mles)
    }

    fn data(&self) -> &<Self::Function as SumcheckFunction<F>>::Data {
        &self.data
    }

    fn vars(&self) -> usize {
        self.vars
    }

    fn oracle_params(&self) -> <Self::Instance as Message<F>>::Params {
        OracleParams { vars: self.vars }
    }

    fn eval(
        &self,
        point: &MultiPoint<F>,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> SF::Mles<F> {
        let natures = SF::natures();
        let instance_evals = <Self as Oracle<F>>::instance_evals(instance);
        // TODO: Evaluate only what's needed of each.
        let witness_evals = EvalsExt::eval(witness, point);
        let structure_evals = EvalsExt::eval(&self.mles, point);

        let locations = SF::map_evals(&natures, |nature| match nature {
            Either::Left(n) => (*n).into(),
            Either::Right(n) => (*n).into(),
        });

        let evals = SF::combine(&instance_evals, &locations, |eval, location| {
            if let EvalLocation::Instance = location {
                *eval
            } else {
                F::ZERO
            }
        });

        let evals = SF::combine3(
            [&evals, &witness_evals],
            &locations,
            |eval, witness, location| match location {
                EvalLocation::Structure | EvalLocation::Instance => *eval,
                EvalLocation::Witness => *witness,
            },
        );

        SF::combine3(
            [&evals, &structure_evals],
            &locations,
            |eval, witness, location| match location {
                EvalLocation::Witness | EvalLocation::Instance => *eval,
                EvalLocation::Structure => *witness,
            },
        )
    }

    fn witness_from_evals(evals: Vec<SF::Mles<F>>) -> Self::Witness {
        evals.to_vec()
    }

    fn natures(&self) -> SF::Mles<Self::Nature> {
        SF::natures()
    }
}

#[derive(Clone, Debug)]
pub struct CompositeReductionKey<F: Field, SF: SumcheckFunction<F>, P1, P2>
where
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    // Number of evals provided to the oracle be the prover
    // and to be verified through some reduction.
    prover_evals: usize,
    evals_per_oracle: SF::Mles<Either<(), ()>>,
    data: SF::Data,
    oracle1_key: P1::VerifierKey,
    oracle2_key: P2::VerifierKey,
    vars: usize,
}

impl<F: Field, SF: SumcheckFunction<F>, P1, P2> CanonicalSerialize
    for CompositeReductionKey<F, SF, P1, P2>
where
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
    SF::Mles<Either<(), ()>>: CanonicalSerialize,
{
    fn serialize_with_mode<W: ark_serialize::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        let Self {
            prover_evals,
            evals_per_oracle,
            data,
            oracle1_key,
            oracle2_key,
            vars,
        } = self;
        prover_evals.serialize_with_mode(&mut writer, compress)?;
        evals_per_oracle.serialize_with_mode(&mut writer, compress)?;
        data.serialize_with_mode(&mut writer, compress)?;
        oracle1_key.serialize_with_mode(&mut writer, compress)?;
        oracle2_key.serialize_with_mode(&mut writer, compress)?;
        vars.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        let Self {
            prover_evals,
            evals_per_oracle,
            data,
            oracle1_key,
            oracle2_key,
            vars,
        } = self;
        prover_evals.serialized_size(compress)
            + evals_per_oracle.serialized_size(compress)
            + data.serialized_size(compress)
            + oracle1_key.serialized_size(compress)
            + oracle2_key.serialized_size(compress)
            + vars.serialized_size(compress)
    }
}

impl<F: Field, SF: SumcheckFunction<F>, P1, P2> CompositeReductionKey<F, SF, P1, P2>
where
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    pub fn p1_key(&self) -> &P1::VerifierKey {
        &self.oracle1_key
    }

    pub fn p2_key(&self) -> &P2::VerifierKey {
        &self.oracle2_key
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
/// All evaluations provided by the prover to the 2 oracles.
pub struct ProverEvals<F: Field>(Vec<F>);

impl<F: Field> Message<F> for ProverEvals<F> {
    type Params = usize;

    type Error = ();

    fn len(params: &Self::Params) -> usize {
        *params
    }

    fn to_field_elements(&self, params: &usize) -> Result<Vec<F>, Self::Error> {
        let expected_len = *params;
        if self.0.len() == expected_len {
            Ok(self.0.clone())
        } else {
            Err(())
        }
    }
}

impl<F, SF, P1, P2> Reduction<F, QueryRelation<F, Self>, PartialQueryRelation<F, SF, P1, P2>>
    for CompositeOracle<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F, Natures = Either<P1::Nature, P2::Nature>>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
    SF::Mles<Either<(), ()>>: CanonicalSerialize,
    <QueryRelation<F, Self> as Relation>::Instance: Message<F, Params = (OracleParams, usize)>,
{
    type ProverKey = CompositeReductionKey<F, SF, P1, P2>;

    type VerifierKey = CompositeReductionKey<F, SF, P1, P2>;

    type Proof = ProverEvals<F>;

    type Error = ();

    type Params = (OracleParams, usize);

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        builder.round::<F, ProverEvals<F>, 0>(&key.prover_evals)
    }

    fn verifier_key(oracle: &Self) -> Self::VerifierKey {
        let prover_evals = SF::natures()
            .flatten_vec()
            .into_iter()
            .map(|nature| if nature.prover_provided() { 1 } else { 0 })
            .sum();

        let data = oracle.data.clone();
        let oracle1_key = From::from(oracle.partial_oracles.0.clone());
        let oracle2_key = From::from(oracle.partial_oracles.1.clone());
        let evals_per_oracle = oracle.evals_per_oracle.clone();
        let vars = oracle.vars;
        CompositeReductionKey {
            prover_evals,
            evals_per_oracle,
            data,
            oracle1_key,
            oracle2_key,
            vars,
        }
    }

    fn key_pair(structure: &Self) -> (Self::VerifierKey, Self::ProverKey) {
        let key = Self::verifier_key(structure);
        (key.clone(), key)
    }

    fn params(key: &Self::VerifierKey) -> Self::Params {
        let vars = key.vars;
        (OracleParams { vars }, vars)
    }

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: OracleQueryInstance<F, CompositeOracleInstance<F, SF, P1, P2>>,
        witness: Vec<SF::Mles<F>>,
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<PartialQueryRelation<F, SF, P1, P2>, Self::Proof> {
        let OracleQueryInstance {
            oracle_instance,
            point,
            eval,
        } = instance;
        //PERF: This computation is a byproduct of sumcheck, it would be good
        //to reuse it instead of recomputing it here.
        let evals = EvalsExt::eval(&witness, &point);
        assert_eq!(eval, SF::function(&key.data, &evals));

        let evals1 = P1::evals(&key.oracle1_key, &oracle_instance.oracle1_instance, &point);
        let evals1 = SF::combine(&evals, &evals1, |eval, query| match query {
            OracleEval::Computed(e) => {
                assert_eq!(e, eval);
                Some(*e)
            }
            OracleEval::ProverProvided => Some(*eval),
            OracleEval::None => None,
        });

        let evals2 = P2::evals(&key.oracle2_key, &oracle_instance.oracle2_instance, &point);
        let evals2 = SF::combine(&evals, &evals2, |eval, query| match query {
            OracleEval::Computed(e) => {
                assert_eq!(e, eval);
                Some(*e)
            }
            OracleEval::ProverProvided => Some(*eval),
            OracleEval::None => None,
        });

        let check = SF::combine(
            &key.evals_per_oracle,
            &SF::natures(),
            |side, nature| match side {
                Either::Left(()) => Either::Left(nature.prover_provided()),
                Either::Right(()) => Either::Right(nature.prover_provided()),
            },
        );
        let prover_evals1 = SF::combine(&check, &evals1, |check, eval| match (check, eval) {
            (Either::Left(provided), Some(e)) => provided.then_some(*e),
            (Either::Right(_), None) => None,
            (Either::Left(_), None) | (Either::Right(_), Some(_)) => panic!(),
        });
        let prover_evals2 = SF::combine(&check, &evals2, |check, eval| match (check, eval) {
            (Either::Right(provided), Some(e)) => provided.then_some(*e),
            (Either::Left(_), None) => None,
            (Either::Right(_), None) | (Either::Left(_), Some(_)) => panic!(),
        });
        let prover_evals = SF::combine(&prover_evals1, &prover_evals2, |e1, e2| match (e1, e2) {
            (None, None) => None,
            (None, Some(e)) | (Some(e), None) => Some(*e),
            (Some(_), Some(_)) => panic!(),
        });

        let prover_evals = prover_evals.flatten_vec().into_iter().flatten().collect();
        let prover_evals = ProverEvals(prover_evals);
        let [] = transcript.send_message(&prover_evals, &key.prover_evals);
        let proof = prover_evals;

        let instance1 = PartialQueryInstance::new(evals1, oracle_instance.oracle1_instance, &point);
        let instance2 = PartialQueryInstance::new(evals2, oracle_instance.oracle2_instance, &point);
        let instance = (instance1, instance2);

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: OracleQueryInstance<F, CompositeOracleInstance<F, SF, P1, P2>>,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<<PartialQueryRelation<F, SF, P1, P2> as Relation>::Instance, Self::Error> {
        let OracleQueryInstance {
            oracle_instance,
            point,
            eval: expected_eval,
        } = instance;

        let params = key.prover_evals;
        let (prover_evals, []) = transcript.receive_message(Clone::clone, &proof, &params)?;
        let ProverEvals(prover_evals) = prover_evals;

        assert_eq!(prover_evals.len(), key.prover_evals);

        let (instance1, instance2) = {
            let mut prover_evals = prover_evals.into_iter();
            let evals = SF::natures().flatten_vec().into_iter().map(|nature| {
                if nature.prover_provided() {
                    Some(prover_evals.next().unwrap())
                } else {
                    None
                }
            });
            let evals = SF::Mles::unflatten_vec(evals.collect());
            assert!(prover_evals.next().is_none());
            let evals1 = SF::combine(&key.evals_per_oracle, &evals, |side, eval| match side {
                Either::Left(_) => *eval,
                Either::Right(_) => None,
            });
            let evals2 = SF::combine(&key.evals_per_oracle, &evals, |side, eval| match side {
                Either::Left(_) => None,
                Either::Right(_) => *eval,
            });
            (evals1, evals2)
        };

        let evals1 = P1::evals(&key.oracle1_key, &oracle_instance.oracle1_instance, &point);
        let evals1 = SF::combine(&evals1, &instance1, |eval, prover_eval| match eval {
            OracleEval::Computed(e) => Some(*e),
            OracleEval::ProverProvided => *prover_eval,
            OracleEval::None => None,
        });

        let evals2 = P2::evals(&key.oracle2_key, &oracle_instance.oracle2_instance, &point);
        let evals2 = SF::combine(&evals2, &instance2, |eval, prover_eval| match eval {
            OracleEval::Computed(e) => Some(*e),
            OracleEval::ProverProvided => *prover_eval,
            OracleEval::None => None,
        });

        let natures = SF::natures();
        let evals = SF::combine3([&evals1, &evals2], &natures, |eval1, eval2, nature| {
            match (eval1, eval2, nature) {
                // (None, None, Either::Left(_)) => todo!(),
                // (None, None, Either::Right(_)) => todo!(),
                // (None, Some(_), Either::Left(_)) => todo!(),
                (None, Some(e), Either::Right(_)) => *e,
                (Some(e), None, Either::Left(_)) => *e,
                // (Some(_), None, Either::Right(_)) => todo!(),
                // (Some(_), Some(_), Either::Left(_)) => todo!(),
                // (Some(_), Some(_), Either::Right(_)) => todo!(),
                _ => panic!("Incorrect oracle answered query, or correct oracle fail to answer"),
            }
        });

        let eval = SF::function(&key.data, &evals);

        if eval == expected_eval {
            let instance1 =
                PartialQueryInstance::new(evals1, oracle_instance.oracle1_instance, &point);
            let instance2 =
                PartialQueryInstance::new(evals2, oracle_instance.oracle2_instance, &point);
            Ok((instance1, instance2))
        } else {
            Err(())
        }
    }
}

pub struct CompositeQueryRelation<F, SF, P1, P2>(PhantomData<(F, SF, P1, P2)>);

impl<F, SF, P1, P2> Relation for CompositeQueryRelation<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    type Structure = CompositeOracle<F, SF, P1, P2>;

    type Instance = PartialQueryInstance<F, SF, CompositeOracleInstance<F, SF, P1, P2>>;

    type Witness = Vec<SF::Mles<F>>;

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let (instance1, instance2) = instance.clone().split(&structure.evals_per_oracle);

        let check1 = P1::QueryRelation::check(&structure.partial_oracles.0, &instance1, witness);
        let check2 = P2::QueryRelation::check(&structure.partial_oracles.1, &instance2, witness);

        check1 && check2
    }
}

#[derive(Clone, Debug)]
pub struct CompositeOracleKey<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    oracle1_key: P1::VerifierKey,
    oracle2_key: P2::VerifierKey,
    evals_per_oracle: SF::Mles<Either<(), ()>>,
}

impl<F, SF, P1, P2> CanonicalSerialize for CompositeOracleKey<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
    SF::Mles<Either<(), ()>>: CanonicalSerialize,
{
    fn serialize_with_mode<W: ark_serialize::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        let Self {
            oracle1_key,
            oracle2_key,
            evals_per_oracle,
        } = self;
        oracle1_key.serialize_with_mode(&mut writer, compress)?;
        oracle2_key.serialize_with_mode(&mut writer, compress)?;
        evals_per_oracle.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        let Self {
            oracle1_key,
            oracle2_key,
            evals_per_oracle,
        } = self;
        oracle1_key.serialized_size(compress)
            + oracle2_key.serialized_size(compress)
            + evals_per_oracle.serialized_size(compress)
    }
}

impl<F, SF, P1, P2> CompositeOracleKey<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    /// Splits a [PartialQueryInstance] over a composite instance into the 2
    /// instances that compose it.
    pub fn split(
        &self,
        instance: PartialQueryInstance<F, SF, CompositeOracleInstance<F, SF, P1, P2>>,
    ) -> <PartialQueryRelation<F, SF, P1, P2> as Relation>::Instance {
        instance.split(&self.evals_per_oracle)
    }

    pub fn p1_key(&self) -> &P1::VerifierKey {
        &self.oracle1_key
    }

    pub fn p2_key(&self) -> &P2::VerifierKey {
        &self.oracle2_key
    }
}

impl<F, SF, P1, P2> From<CompositeOracle<F, SF, P1, P2>> for CompositeOracleKey<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F>,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
{
    fn from(value: CompositeOracle<F, SF, P1, P2>) -> Self {
        let CompositeOracle {
            partial_oracles,
            evals_per_oracle,
            ..
        } = value;
        let (partial_oracle1, partial_oracle2) = partial_oracles;
        let oracle1_key = P1::VerifierKey::from(partial_oracle1);
        let oracle2_key = P2::VerifierKey::from(partial_oracle2);
        Self {
            oracle1_key,
            oracle2_key,
            evals_per_oracle,
        }
    }
}

impl<F, SF, P1, P2> PartialOracle<F, SF> for CompositeOracle<F, SF, P1, P2>
where
    F: Field,
    SF: SumcheckFunction<F> + Clone,
    P1: PartialOracle<F, SF>,
    P2: PartialOracle<F, SF>,
    SF::Natures: Into<Option<Either<P1::Nature, P2::Nature>>>,
    SF::Mles<Either<(), ()>>: CanonicalSerialize,
{
    type Instance = CompositeOracleInstance<F, SF, P1, P2>;

    type VerifierKey = CompositeOracleKey<F, SF, P1, P2>;

    type Nature = Either<P1::Nature, P2::Nature>;

    type QueryRelation = CompositeQueryRelation<F, SF, P1, P2>;

    type Builder = (P1::Builder, P2::Builder);

    fn build(builder: Self::Builder, data: &SF::Data, structure: Rc<Vec<<SF>::Mles<F>>>) -> Self {
        let (builder1, builder2) = builder;
        let mles = structure;
        Self::new(data.clone(), mles, builder1, builder2)
    }

    fn instance_evals(instance: &Self::Instance) -> SF::Mles<F> {
        let evals1 = P1::instance_evals(&instance.oracle1_instance);
        let evals2 = P2::instance_evals(&instance.oracle2_instance);
        evals1.combine(&evals2, |e1, e2| *e1 + e2)
    }

    fn evals(
        key: &Self::VerifierKey,
        instance: &Self::Instance,
        point: &MultiPoint<F>,
    ) -> SF::Mles<OracleEval<F>> {
        use OracleEval::*;
        let evals1 = P1::evals(&key.oracle1_key, &instance.oracle1_instance, point);
        let evals2 = P2::evals(&key.oracle2_key, &instance.oracle2_instance, point);
        evals1.combine(&evals2, |eval1, eval2| {
            match (eval1, eval2) {
                // (Computed(_), Computed(_)) => todo!(),
                // (Computed(_), ProverProvided) => todo!(),
                // (ProverProvided, Computed(_)) => todo!(),
                // (ProverProvided, ProverProvided) => todo!(),
                (Computed(e), None) | (None, Computed(e)) => Computed(*e),
                (ProverProvided, None) | (None, ProverProvided) => ProverProvided,
                (None, None) => None,
                _ => unreachable!(),
            }
        })
    }
}
