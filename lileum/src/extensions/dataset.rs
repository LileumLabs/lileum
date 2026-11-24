use crate::extensions::{
    Extension, ExtensionRelation, NoFolding, aggregation::SingleCommitAggregation,
};
use alloc::{collections::BTreeMap, vec::Vec};
use ark_ff::Field;
use commit::{CommitmentScheme, OpeningRelation};
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

impl<F, C> Reduction<F, DatasetRel2<F, C>, OpeningRelation<F, C>> for DatasetReduction2
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = ();

    type Proof = ();

    type Error = ();

    type Params = ();

    fn transcript_pattern(
        _key: &Self::VerifierKey,
        _builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        todo!()
    }

    fn verifier_key(_structure: &<DatasetRel2<F, C> as Relation>::Structure) -> Self::VerifierKey {
        todo!()
    }

    fn key_pair(
        _structure: &<DatasetRel2<F, C> as Relation>::Structure,
    ) -> (Self::VerifierKey, Self::ProverKey) {
        todo!()
    }

    fn params(_key: &Self::VerifierKey) -> Self::Params {
        todo!()
    }

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: <DatasetRel2<F, C> as Relation>::Instance,
        _witness: <DatasetRel2<F, C> as Relation>::Witness,
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        todo!()
    }

    fn verify<S: Duplex<F>>(
        _key: &Self::VerifierKey,
        _instance: <DatasetRel2<F, C> as Relation>::Instance,
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<<OpeningRelation<F, C> as Relation>::Instance, Self::Error> {
        todo!()
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
