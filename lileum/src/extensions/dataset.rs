use crate::extensions::{
    Extension, ExtensionRelation, NoFolding,
    aggregation::SingleCommitAggregation,
    dataset::sumcheck::{DatasetOracle, committed_oracle_instance, core_oracle_instance},
};
use ::sumcheck::{
    MultiPoint, SumcheckInstance, SumcheckReduction,
    oracles::{
        composite::{CompositeOracle, CompositeOracleInstance, ProverEvals},
        core::CoreOracle,
    },
};
use alloc::{collections::BTreeMap, vec::Vec};
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use commit::{CommitmentScheme, OpenInstance, OpeningRelation, oracle::CommittedOracle};
use core::marker::PhantomData;
use lcs::{circuit::Var, extensions::LcsExtension, structure::WitnessIndex};
use reduction::{
    GuardedProof, NoError, ProverOutput, Reduction, Relation, Transcript, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;

/// An extension which allows to lookup values from an externally committed table.
#[derive(Clone, Debug)]
pub struct Dataset<F, C>(PhantomData<(F, C)>);

impl<F, C> Default for Dataset<F, C> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<F: Field, C: CommitmentScheme<F>> LcsExtension<F> for Dataset<F, C> {
    type Constraint = usize;

    type StructureBuilder = BTreeMap<usize, usize>;

    type WitnessBuilder = ();

    type Structure = BTreeMap<usize, usize>;

    type Witness = Vec<F>;

    type ExternalInstance = C::Commitment;

    type ExternalWitness = Vec<F>;

    fn process_structure<R: Fn(Var<WitnessIndex>) -> usize>(
        builder: Self::StructureBuilder,
        _var_reader: R,
    ) -> Self::Structure {
        builder
    }

    fn process_witness(_builder: Self::WitnessBuilder) -> Self::Witness {
        panic!("Shouldn't be called, this extension uses _ex");
    }

    fn process_witness_ex(
        _builder: Self::WitnessBuilder,
        _external_instance: Self::ExternalInstance,
        external_witness: Self::ExternalWitness,
    ) -> Self::Witness {
        external_witness
    }

    fn record_constraint<const N: usize, R: Fn(Var<WitnessIndex>) -> usize>(
        builder: &mut Self::StructureBuilder,
        var_reader: R,
        vars: [Var<WitnessIndex>; N],
        constraint: Self::Constraint,
    ) {
        assert_eq!(N, 1);
        let var = var_reader(vars[0]);

        assert!(
            !builder.contains_key(&var),
            "only one lookup is allowed per variable"
        );

        // TODO: maybe check out of bounds.
        builder.insert(var, constraint);
    }

    fn compute_constraint<const N: usize>(
        _witness: &mut Self::WitnessBuilder,
        _vars: [F; N],
        _constraint: Self::Constraint,
    ) {
        panic!("Shouldn't be called, this extension uses _ex");
    }

    fn compute_constraint_ex<const N: usize>(
        _witness: &mut Self::WitnessBuilder,
        vars: [F; N],
        constraint: Self::Constraint,
        _external_instance: &Self::ExternalInstance,
        external_witness: &Self::ExternalWitness,
    ) {
        assert_eq!(N, 1);
        let var = vars[0];

        assert_eq!(var, external_witness[constraint])
    }
}

#[derive(Clone, Debug)]
pub struct DatasetRel1<F, C>(PhantomData<(F, C)>);

impl<F, C> Relation for DatasetRel1<F, C>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Structure = BTreeMap<usize, usize>;

    type Instance = (C::Commitment, C::Commitment);

    type Witness = (Vec<F>, Vec<F>);

    fn check(
        structure: &Self::Structure,
        _instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let (trace, dataset) = witness;

        for (i, w) in trace.iter().enumerate() {
            let lookup = structure.get(&i).map(|i| dataset[*i]);
            if let Some(x) = lookup
                && *w != x
            {
                return false;
            }
        }

        true
    }
}

impl<F, C> ExtensionRelation<F, C, C::Commitment, Vec<F>, BTreeMap<usize, usize>>
    for DatasetRel1<F, C>
where
    F: Field,
    C: CommitmentScheme<F>,
{
}

#[derive(Clone, Debug)]
pub struct DatasetRel2<F, C>(PhantomData<(F, C)>);

pub struct Structure<C> {
    pcs: C,
    vars: usize,
    lookups: Vec<Option<usize>>,
}

impl<F, C> Relation for DatasetRel2<F, C>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type Structure = Structure<C>;

    type Instance = [C::Commitment; 2];

    type Witness = [Vec<F>; 2];

    fn check(
        structure: &Self::Structure,
        instance: &Self::Instance,
        witness: &Self::Witness,
    ) -> bool {
        let Structure { pcs, vars, lookups } = structure;
        let [trace_commit, data_commit] = instance;
        let [trace, data] = witness;
        assert_eq!(trace.len(), 1 << vars);
        assert_eq!(data.len(), 1 << vars);

        if &pcs.commit_mle(trace) != trace_commit {
            return false;
        }

        if &pcs.commit_mle(data) != data_commit {
            return false;
        }

        for (lookup, w) in lookups.iter().zip(trace) {
            if let Some(addr) = lookup
                && data[*addr] != *w
            {
                return false;
            }
        }

        true
    }
}

#[derive(Clone, Debug)]
pub struct DatasetReduction1;

#[derive(Clone, Debug)]
pub struct DatasetReduction2;

impl<F, C> Reduction<F, DatasetRel1<F, C>, DatasetRel2<F, C>> for DatasetReduction1
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = ();

    type Proof = ();

    type Error = NoError;

    type Params = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        builder
    }

    fn verifier_key(_structure: &BTreeMap<usize, usize>) -> Self::VerifierKey {}

    fn key_pair(_structure: &BTreeMap<usize, usize>) -> (Self::VerifierKey, Self::ProverKey) {
        ((), ())
    }

    fn params(_key: &Self::VerifierKey) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        instance: (C::Commitment, C::Commitment),
        witness: (Vec<F>, Vec<F>),
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<DatasetRel2<F, C>, Self::Proof> {
        let (w, d) = instance;
        let instance = [w, d];
        let (w, d) = witness;
        let witness = [w, d];
        ProverOutput {
            instance,
            witness,
            proof: (),
        }
    }

    fn verify<S: Duplex<F>>(
        _key: &Self::VerifierKey,
        instance: (C::Commitment, C::Commitment),
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<[C::Commitment; 2], Self::Error> {
        let (w, d) = instance;
        Ok([w, d])
    }
}

mod sumcheck {

    use alloc::vec;
    use alloc::vec::{IntoIter, Vec};
    use ark_ff::Field;
    use ark_serialize::CanonicalSerialize;
    use commit::{
        CommitmentScheme,
        oracle::{CommittedNature, CommittedOracle, CommittedOracleInstance},
    };
    use core::fmt::Debug;
    use sumcheck::{
        MultiPoint, SumcheckMessage, Var,
        evals::{Evals, EvalsCore},
        oracles::{
            SumcheckFunction,
            composite::{CompositeOracle, CompositeReductionKey, Either},
            core::{CoreNature, CoreOracle, CoreOracleInstance, SmallFunctions},
        },
    };
    use sumcheck_derive::EvalsCore;

    #[derive(Debug, Clone, Default, EvalsCore)]
    pub struct DatasetEvals<V: Debug + Clone> {
        selector: V,
        trace: V,
        data: V,
        counts: V,
        lookup_challenge: V,
        sumcheck_challenge: V,
        inverse_left: V,
        inverse_right: V,
        z_eq: V,
    }

    impl<V: Debug + Clone + CanonicalSerialize> CanonicalSerialize for DatasetEvals<V> {
        fn serialize_with_mode<W: ark_serialize::Write>(
            &self,
            mut writer: W,
            compress: ark_serialize::Compress,
        ) -> Result<(), ark_serialize::SerializationError> {
            let Self {
                selector,
                trace,
                data,
                counts,
                lookup_challenge,
                sumcheck_challenge,
                inverse_left,
                inverse_right,
                z_eq,
            } = self;
            selector.serialize_with_mode(&mut writer, compress)?;
            trace.serialize_with_mode(&mut writer, compress)?;
            data.serialize_with_mode(&mut writer, compress)?;
            counts.serialize_with_mode(&mut writer, compress)?;
            lookup_challenge.serialize_with_mode(&mut writer, compress)?;
            sumcheck_challenge.serialize_with_mode(&mut writer, compress)?;
            inverse_left.serialize_with_mode(&mut writer, compress)?;
            inverse_right.serialize_with_mode(&mut writer, compress)?;
            z_eq.serialize_with_mode(writer, compress)
        }

        fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
            let Self {
                selector,
                trace,
                data,
                counts,
                lookup_challenge,
                sumcheck_challenge,
                inverse_left,
                inverse_right,
                z_eq,
            } = self;
            selector.serialized_size(compress)
                + trace.serialized_size(compress)
                + data.serialized_size(compress)
                + counts.serialized_size(compress)
                + lookup_challenge.serialized_size(compress)
                + sumcheck_challenge.serialized_size(compress)
                + inverse_left.serialized_size(compress)
                + inverse_right.serialized_size(compress)
                + z_eq.serialized_size(compress)
        }
    }

    impl<F: Field> SmallFunctions<F> for DatasetEvals<()> {
        fn small_functions() -> Self::Mles<Option<sumcheck::oracles::core::Func<F>>> {
            DatasetEvals {
                z_eq: Some(|vars, point| MultiPoint::new(vars.to_vec()).eval_as_eq(point)),
                ..Default::default()
            }
        }
    }

    impl<F: Field> SumcheckFunction<F> for DatasetEvals<()> {
        type Natures = Either<CoreNature, CommittedNature>;

        type Data = ();

        fn natures() -> Self::Mles<Self::Natures> {
            todo!()
        }

        fn function<V: Var<F> + Debug>(_: &(), evals: &Self::Mles<V>) -> V {
            let DatasetEvals {
                selector,
                trace,
                data,
                counts,
                lookup_challenge,
                sumcheck_challenge,
                inverse_left,
                inverse_right,
                z_eq,
            } = evals.clone();

            let check1 = inverse_left.clone() * (trace + &lookup_challenge) - counts;
            let check2 = inverse_right.clone() * (data * selector + &lookup_challenge) - F::one();
            let check3 = inverse_left - inverse_right;

            let batched = check1 * &z_eq;
            let batched = batched * &sumcheck_challenge + check2 * z_eq;
            batched * sumcheck_challenge + check3
        }
    }

    pub type DatasetOracle<F, C, SF = DatasetEvals<()>> =
        CompositeOracle<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

    pub type VerifierKey<F, C> = sumcheck::SumcheckVerifierKey<F, DatasetOracle<F, C>>;
    pub type Proof<F> = Vec<SumcheckMessage<F>>;

    pub type CompositeVerifierKey<F, C, SF = DatasetEvals<()>> =
        CompositeReductionKey<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

    pub fn core_oracle_instance<F: Field>(
        vars: usize,
        chall1: F,
        chall2: F,
        chall3: MultiPoint<F>,
    ) -> CoreOracleInstance<F, DatasetEvals<()>> {
        assert_eq!(chall3.vars(), vars);
        let coefficients = DatasetEvals {
            lookup_challenge: vec![chall1],
            sumcheck_challenge: vec![chall2],
            z_eq: chall3.inner(),
            ..Default::default()
        };
        CoreOracleInstance::new(&coefficients, vars)
    }

    pub fn committed_oracle_instance<F, C>(
        trace: C::Commitment,
        data: C::Commitment,
        counts: C::Commitment,
        inverses: [C::Commitment; 2],
    ) -> CommittedOracleInstance<F, C, DatasetEvals<()>>
    where
        F: Field,
        C: CommitmentScheme<F>,
    {
        let [inverse_left, inverse_right] = inverses.map(Some);
        let commits = DatasetEvals {
            selector: None,
            trace: trace.into(),
            data: data.into(),
            counts: counts.into(),
            lookup_challenge: None,
            sumcheck_challenge: None,
            inverse_left,
            inverse_right,
            z_eq: None,
        };

        CommittedOracleInstance::new(commits)
    }
}

#[derive(Clone, Debug, CanonicalSerialize)]
pub struct VerifierKey<F: Field, C: CommitmentScheme<F>> {
    sumcheck: sumcheck::VerifierKey<F, C>,
    composite: sumcheck::CompositeVerifierKey<F, C>,
    vars: usize,
}

#[derive(Clone, Debug)]
pub struct Proof<F: Field, C: CommitmentScheme<F>> {
    counts_commit: C::Commitment,
    inverses: [C::Commitment; 2],
    sumcheck: sumcheck::Proof<F>,
    prover_evals: ProverEvals<F>,
}

impl<F, C> Reduction<F, DatasetRel2<F, C>, OpeningRelation<F, C>> for DatasetReduction2
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = VerifierKey<F, C>;

    type Proof = Proof<F, C>;

    type Error = ();

    type Params = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        _builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        todo!()
    }

    fn verifier_key(_structure: &Structure<C>) -> Self::VerifierKey {
        todo!()
    }

    fn key_pair(_structure: &Structure<C>) -> (Self::VerifierKey, Self::ProverKey) {
        todo!()
    }

    fn params(_key: &Self::VerifierKey) -> Self::Params {
        todo!()
    }

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: [C::Commitment; 2],
        _witness: [Vec<F>; 2],
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        todo!()
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: [C::Commitment; 2],
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        let [trace, data] = instance;

        let Ok((counts, [lookup_challenge])) =
            transcript.receive_message(|proof| proof.counts_commit.clone(), &proof, &());

        let Ok((inverses, [sumcheck_challenge])) =
            transcript.receive_message(|proof| proof.inverses.clone(), &proof, &());

        let sumcheck_instance: SumcheckInstance<F, DatasetOracle<F, C>> = {
            let vars = key.vars;
            let zerocheck_point = MultiPoint::new(transcript.point());
            let core_instance =
                core_oracle_instance(vars, lookup_challenge, sumcheck_challenge, zerocheck_point);
            let committed_instance =
                committed_oracle_instance::<F, C>(trace, data, counts, inverses);
            let oracle_instance = CompositeOracleInstance {
                oracle1_instance: core_instance,
                oracle2_instance: committed_instance,
            };
            SumcheckInstance::new(F::zero(), oracle_instance)
        };

        //TODO: handle
        let instance = SumcheckReduction::verify(
            &key.sumcheck,
            sumcheck_instance,
            proof.clone().map(|proof| proof.sumcheck),
            transcript,
        )
        .unwrap();

        let (core_instance, committed_instance) = CompositeOracle::verify(
            &key.composite,
            instance,
            proof.map(|proof| proof.prover_evals),
            transcript,
        )
        .unwrap();

        let () = CoreOracle::verify(
            key.composite.p1_key(),
            core_instance,
            GuardedProof::empty(),
            transcript,
        )
        .unwrap();

        let Ok(open_instance) = CommittedOracle::verify(
            key.composite.p2_key(),
            committed_instance,
            GuardedProof::empty(),
            transcript,
        );

        Ok(open_instance)
    }
}

impl<F: Field, C: CommitmentScheme<F>> Extension<F, C> for Dataset<F, C> {
    type Instance = C::Commitment;

    type R1 = DatasetRel1<F, C>;

    type R2 = DatasetRel2<F, C>;

    type R3 = OpeningRelation<F, C>;

    fn derive_structure(
        _vars: usize,
        _pcs: &C,
        _r1_structure: &Self::Structure,
    ) -> <Self::R2 as reduction::Relation>::Structure {
        todo!()
    }

    fn commit_witness(_pcs: &C, _witness: &Self::Witness) -> Self::Instance {
        todo!()
    }

    type Reduction1 = DatasetReduction1;

    type Reduction2 = DatasetReduction2;

    type AgregationScheme = SingleCommitAggregation;

    type FoldingScheme = NoFolding;
}
