use crate::extensions::{
    Extension, ExtensionRelation, NoFolding,
    aggregation::SingleCommitAggregation,
    dataset::sumcheck::{
        DatasetEvals, DatasetOracle, committed_oracle_instance, core_oracle_instance,
    },
};
use ::sumcheck::{
    MultiPoint, SumcheckInstance, SumcheckReduction,
    eq::eq,
    oracles::{
        Oracle,
        composite::{CompositeOracle, CompositeOracleInstance, ProverEvals},
        core::CoreOracle,
    },
};
use alloc::{collections::BTreeMap, vec::Vec};
use ark_ff::{Field, batch_inversion};
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
    use core::iter::repeat;
    use sumcheck::evals::eval_simple_mle;
    use sumcheck::{
        MultiPoint, SumcheckMessage, Var,
        evals::{Evals, EvalsCore},
        oracles::{
            SumcheckFunction,
            composite::{CompositeOracle, CompositeReductionKey, Either},
            core::{Coeffs, CoreNature, CoreOracle, CoreOracleInstance, SmallFunctions},
        },
    };
    use sumcheck_derive::EvalsCore;

    #[derive(Debug, Clone, Default, EvalsCore)]
    pub struct DatasetEvals<V: Debug + Clone> {
        pub selector: V,
        pub address: V,
        pub indices: V,
        pub trace: V,
        pub data: V,
        pub counts: V,
        pub lookup_challenge: V,
        pub compression_challenge: V,
        pub sumcheck_challenge: V,
        pub inverse_left: V,
        pub inverse_right: V,
        pub z_eq: V,
    }

    impl<V: Debug + Clone + CanonicalSerialize> CanonicalSerialize for DatasetEvals<V> {
        fn serialize_with_mode<W: ark_serialize::Write>(
            &self,
            mut writer: W,
            compress: ark_serialize::Compress,
        ) -> Result<(), ark_serialize::SerializationError> {
            let Self {
                selector,
                address,
                indices,
                trace,
                data,
                counts,
                lookup_challenge,
                compression_challenge,
                sumcheck_challenge,
                inverse_left,
                inverse_right,
                z_eq,
            } = self;
            selector.serialize_with_mode(&mut writer, compress)?;
            address.serialize_with_mode(&mut writer, compress)?;
            indices.serialize_with_mode(&mut writer, compress)?;
            trace.serialize_with_mode(&mut writer, compress)?;
            data.serialize_with_mode(&mut writer, compress)?;
            counts.serialize_with_mode(&mut writer, compress)?;
            lookup_challenge.serialize_with_mode(&mut writer, compress)?;
            compression_challenge.serialize_with_mode(&mut writer, compress)?;
            sumcheck_challenge.serialize_with_mode(&mut writer, compress)?;
            inverse_left.serialize_with_mode(&mut writer, compress)?;
            inverse_right.serialize_with_mode(&mut writer, compress)?;
            z_eq.serialize_with_mode(writer, compress)
        }

        fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
            let Self {
                selector,
                address,
                indices,
                trace,
                data,
                counts,
                lookup_challenge,
                compression_challenge,
                sumcheck_challenge,
                inverse_left,
                inverse_right,
                z_eq,
            } = self;
            selector.serialized_size(compress)
                + address.serialized_size(compress)
                + indices.serialized_size(compress)
                + trace.serialized_size(compress)
                + data.serialized_size(compress)
                + counts.serialized_size(compress)
                + lookup_challenge.serialized_size(compress)
                + compression_challenge.serialized_size(compress)
                + sumcheck_challenge.serialized_size(compress)
                + inverse_left.serialized_size(compress)
                + inverse_right.serialized_size(compress)
                + z_eq.serialized_size(compress)
        }
    }

    impl<F: Field> SmallFunctions<F> for DatasetEvals<()> {
        fn small_functions() -> Self::Mles<Option<sumcheck::oracles::core::Func<F>>> {
            let indices = |coeff: &[F], point: &MultiPoint<F>| {
                assert!(coeff.is_empty());
                let vars = point.vars();
                let mle: Vec<F> = (0..=u8::MAX)
                    .into_iter()
                    .chain(repeat(0))
                    .take(1 << vars)
                    .map(F::from)
                    .collect();
                //TODO: make O(log n)
                eval_simple_mle(&mle, point)
            };
            DatasetEvals {
                z_eq: Some(|vars, point| MultiPoint::new(vars.to_vec()).eval_as_eq(point)),
                indices: Some(indices),
                ..Default::default()
            }
        }
    }

    impl<F: Field> SumcheckFunction<F> for DatasetEvals<()> {
        type Natures = Either<CoreNature, CommittedNature>;

        type Data = ();

        fn natures() -> Self::Mles<Self::Natures> {
            let chall = Either::Left(CoreNature::Challenge);
            let committed = Either::Right(CommittedNature::Witness);
            let structure = Either::Right(CommittedNature::Structure);
            DatasetEvals {
                selector: structure,
                address: structure,
                indices: Either::Left(CoreNature::SmallStructure),
                trace: committed,
                data: committed,
                counts: structure,
                lookup_challenge: chall,
                compression_challenge: chall,
                sumcheck_challenge: chall,
                inverse_left: committed,
                inverse_right: committed,
                z_eq: Either::Left(CoreNature::SmallInstance(Coeffs::PerVariable)),
            }
        }

        fn function<V: Var<F> + Debug>(_: &(), evals: &Self::Mles<V>) -> V {
            let DatasetEvals {
                selector,
                address,
                indices,
                trace,
                data,
                counts,
                lookup_challenge,
                compression_challenge,
                sumcheck_challenge,
                inverse_left,
                inverse_right,
                z_eq,
            } = evals.clone();

            let lookup = address * &compression_challenge + trace * selector;
            let table = indices * &compression_challenge + data;

            let check1 = inverse_left.clone() * (lookup + &lookup_challenge) - counts;
            let check2 = inverse_right.clone() * (table + &lookup_challenge) - F::one();
            let check3 = inverse_left - inverse_right;

            let batched = check1 * &z_eq;
            let batched = batched * &sumcheck_challenge + check2 * z_eq;
            batched * sumcheck_challenge + check3
        }
    }

    pub type DatasetOracle<F, C, SF = DatasetEvals<()>> =
        CompositeOracle<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

    pub type VerifierKey<F, C> = sumcheck::SumcheckVerifierKey<F, DatasetOracle<F, C>>;
    pub type ProverKey<F, C> = sumcheck::ProverKey<F, DatasetOracle<F, C>>;
    pub type Proof<F> = Vec<SumcheckMessage<F>>;

    pub type CompositeVerifierKey<F, C, SF = DatasetEvals<()>> =
        CompositeReductionKey<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

    pub fn core_oracle_instance<F: Field>(
        vars: usize,
        challenges: [F; 3],
        zerocheck_point: MultiPoint<F>,
    ) -> CoreOracleInstance<F, DatasetEvals<()>> {
        assert_eq!(zerocheck_point.vars(), vars);

        let [lookup_challenge, compression_challenge, sumcheck_challenge] =
            challenges.map(|x| vec![x]);
        let coefficients = DatasetEvals {
            lookup_challenge,
            compression_challenge,
            sumcheck_challenge,
            z_eq: zerocheck_point.inner(),
            ..Default::default()
        };
        CoreOracleInstance::new(&coefficients, vars)
    }

    pub fn committed_oracle_instance<F, C>(
        trace: C::Commitment,
        data: C::Commitment,
        inverses: [C::Commitment; 2],
    ) -> CommittedOracleInstance<F, C, DatasetEvals<()>>
    where
        F: Field,
        C: CommitmentScheme<F>,
    {
        let [inverse_left, inverse_right] = inverses.map(Some);
        let commits = DatasetEvals {
            selector: None,
            address: None,
            indices: None,
            trace: trace.into(),
            data: data.into(),
            counts: None,
            lookup_challenge: None,
            compression_challenge: None,
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

pub struct ProverKey<F: Field, C: CommitmentScheme<F>> {
    pcs: C,
    oracle: sumcheck::DatasetOracle<F, C>,
    sumcheck: sumcheck::ProverKey<F, C>,
    composite: sumcheck::CompositeVerifierKey<F, C>,
    committed: commit::oracle::ProverKey<F, DatasetEvals<()>, C>,
    vars: usize,
}

#[derive(Clone, Debug)]
pub struct Proof<F: Field, C: CommitmentScheme<F>> {
    inverses: [C::Commitment; 2],
    sumcheck: sumcheck::Proof<F>,
    prover_evals: ProverEvals<F>,
}

impl<F: Field, C: CommitmentScheme<F>> ProverKey<F, C> {
    fn witness(
        &self,
        mut trace: Vec<F>,
        mut data: Vec<F>,
        lookup_challenge: F,
        compression_challenge: F,
    ) -> (Vec<DatasetEvals<F>>, [C::Commitment; 2]) {
        let mut witness = self.oracle.structure().to_vec();
        assert_eq!(trace.len(), data.len());
        assert_eq!(trace.len(), witness.len());

        for ((witness, trace), data) in witness.iter_mut().zip(&mut trace).zip(&mut data) {
            witness.trace = *trace;
            witness.data = *data;
            witness.lookup_challenge = lookup_challenge;

            let lookup = witness.address * compression_challenge + *trace * witness.selector;
            let table = witness.indices * compression_challenge + *data;

            *trace = lookup;
            *data = table;
        }

        let mut inverses = [trace, data].map(|mut vec| {
            batch_inversion(&mut vec);
            vec
        });

        for (right_inverse, structure) in inverses[1].iter_mut().zip(&witness) {
            *right_inverse *= structure.counts;
        }

        let inverse_commitments = inverses.map(|inverse| self.pcs.commit_mle(&inverse));

        (witness, inverse_commitments)
    }

    fn set_witness_challenges(
        &self,
        mut witness: Vec<DatasetEvals<F>>,
        sumcheck_challenge: F,
        zerocheck_challenge: &MultiPoint<F>,
    ) -> Vec<DatasetEvals<F>> {
        let z_eq = eq(zerocheck_challenge);

        for (witness, z_eq) in witness.iter_mut().zip(z_eq) {
            witness.sumcheck_challenge = sumcheck_challenge;
            witness.z_eq = z_eq;
        }
        witness
    }
}

impl<F, C> Reduction<F, DatasetRel2<F, C>, OpeningRelation<F, C>> for DatasetReduction2
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ProverKey<F, C>;

    type VerifierKey = VerifierKey<F, C>;

    type Proof = Proof<F, C>;

    type Error = ();

    type Params = ();

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        builder
            .round::<F, (), 2>(&())
            .round::<F, [C::Commitment; 2], 1>(&())
            .point::<F>(key.vars)
            .subprotocol::<SumcheckReduction<F, DatasetOracle<F, C>>, _, _, _>(&key.sumcheck)
            .subprotocol::<CompositeOracle<F, _, _, _>, _, _, _>(&key.composite)
            .subprotocol::<CoreOracle<F, DatasetEvals<()>>, _, _, _>(key.composite.p1_key())
            .subprotocol::<CommittedOracle<F, C, DatasetEvals<()>>, _, _, _>(key.composite.p2_key())
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
        key: &Self::ProverKey,
        instance: [C::Commitment; 2],
        witness: [Vec<F>; 2],
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        let vars = key.vars;
        let [trace_commit, data_commit] = instance;
        let [trace, data] = witness;

        let [lookup_challenge, compression_challenge] = transcript.send_message(&(), &());

        let (witness, inverses) = key.witness(trace, data, lookup_challenge, compression_challenge);

        let [sumcheck_challenge] = transcript.send_message(&inverses, &());

        let (instance, witness) = {
            let zerocheck_point = MultiPoint::new(transcript.point());

            let witness = key.set_witness_challenges(witness, sumcheck_challenge, &zerocheck_point);

            let challenges = [lookup_challenge, compression_challenge, sumcheck_challenge];
            let core_instance = core_oracle_instance(vars, challenges, zerocheck_point);

            let committed_instance =
                committed_oracle_instance::<F, C>(trace_commit, data_commit, inverses.clone());

            let oracle_instance = CompositeOracleInstance {
                oracle1_instance: core_instance,
                oracle2_instance: committed_instance,
            };

            (SumcheckInstance::new(F::zero(), oracle_instance), witness)
        };

        let ProverOutput {
            instance,
            witness,
            proof,
        } = SumcheckReduction::prove(&key.sumcheck, instance, witness, transcript);

        let ProverOutput {
            instance: (core_instance, committed_instance),
            witness,
            proof: prover_evals,
        } = CompositeOracle::prove(&key.composite, instance, witness, transcript);

        let ProverOutput {
            instance: (),
            witness: (),
            proof: (),
        } = CoreOracle::prove(&(), core_instance, witness.clone(), transcript);

        let ProverOutput {
            instance,
            witness,
            proof: (),
        } = CommittedOracle::prove(&key.committed, committed_instance, witness, transcript);

        let proof = Proof {
            inverses,
            sumcheck: proof,
            prover_evals,
        };

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: [C::Commitment; 2],
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        let [trace, data] = instance;

        let Ok(((), [lookup_challenge])) = transcript.receive_message(|_| (), &proof, &());

        let Ok((inverses, [compression_challenge, sumcheck_challenge])) =
            transcript.receive_message(|proof| proof.inverses.clone(), &proof, &());

        let sumcheck_instance: SumcheckInstance<F, DatasetOracle<F, C>> = {
            let vars = key.vars;
            let zerocheck_point = MultiPoint::new(transcript.point());
            let challenges = [lookup_challenge, compression_challenge, sumcheck_challenge];
            let core_instance = core_oracle_instance(vars, challenges, zerocheck_point);
            let committed_instance = committed_oracle_instance::<F, C>(trace, data, inverses);
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
