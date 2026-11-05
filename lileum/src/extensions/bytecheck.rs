use crate::extensions::{
    Extension, ExtensionRelation, NoFolding,
    aggregation::SingleCommitAggregation,
    bytecheck::sumcheck::{
        BytecheckEvals, BytecheckOracle, committed_oracle_instance, core_oracle_instance,
    },
};
use ::sumcheck::{
    MultiPoint, SumcheckInstance, SumcheckReduction,
    oracles::{
        composite::{CompositeOracle, CompositeOracleInstance, ProverEvals},
        core::CoreOracle,
    },
};
use alloc::vec;
use alloc::vec::Vec;
use ark_ff::{BigInteger, Field, PrimeField, batch_inversion};
use ark_serialize::CanonicalSerialize;
use commit::{CommitmentScheme, OpenInstance, OpeningRelation, oracle::CommittedOracle};
use core::marker::PhantomData;
use lcs::{circuit::Var, extensions::LcsExtension, structure::WitnessIndex};
use reduction::{
    GuardedProof, NoError, ProverOutput, Reduction, Relation, Transcript, TranscriptBuilder,
    VerifierTranscript,
};
use sponge::sponge::Duplex;

/// An extension providing an 8 bits range check.
#[derive(Clone, Debug, Default)]
pub struct ByteCheck;

impl<F: Field> LcsExtension<F> for ByteCheck {
    type Constraint = ();

    type StructureBuilder = Vec<Var<WitnessIndex>>;

    type WitnessBuilder = (Self::StructureBuilder, Vec<u8>);

    type Structure = Vec<bool>;

    // too constrained to be this for now
    // type Witness = ();
    type Witness = Vec<F>;

    fn process_structure(_builder: Self::StructureBuilder) -> Self::Structure {
        todo!()
    }

    fn process_witness(_builder: Self::WitnessBuilder) -> Self::Witness {
        todo!()
    }

    fn record_constraint<const N: usize>(
        builder: &mut Self::StructureBuilder,
        vars: [Var<WitnessIndex>; N],
        _: (),
    ) {
        assert_eq!(N, 1);
        let var = vars[0];
        builder.push(var);
    }

    fn compute_constraint<const N: usize>(witness: &mut Self::WitnessBuilder, vars: [F; N], _: ()) {
        assert_eq!(N, 1);
        assert!(vars[0] >= F::from(u8::MIN));
        assert!(vars[0] <= F::from(u8::MAX));
        let v = vars[0].to_base_prime_field_elements().next().unwrap();
        let v = v.into_bigint().to_bytes_le()[0];
        witness.1.push(v);
    }
}

pub struct ByteCheckRel1<F, C>(PhantomData<(F, C)>);

impl<F: Field, C: CommitmentScheme<F>> Relation for ByteCheckRel1<F, C> {
    type Structure = Vec<bool>;

    type Instance = (C::Commitment, ());

    type Witness = (Vec<F>, Vec<F>);

    fn check(structure: &Self::Structure, _: &Self::Instance, witness: &Self::Witness) -> bool {
        assert_eq!(witness.0, witness.1);
        if structure.len() != witness.0.len() {
            return false;
        }
        for (w, constrained) in witness.0.iter().zip(structure) {
            if *constrained {
                let ge = *w >= F::from(u8::MIN);
                let le = *w <= F::from(u8::MAX);
                if !(ge && le) {
                    return false;
                }
            }
        }
        true
    }
}

//TODO: maybe better for the generics to be S, I, W
impl<F: Field, C: CommitmentScheme<F>> ExtensionRelation<F, C, (), Vec<F>, Vec<bool>>
    for ByteCheckRel1<F, C>
{
}

#[derive(Clone, Debug)]
pub struct ByteCheckRel2<F, C>(PhantomData<(F, C)>);

impl<F: Field, C: CommitmentScheme<F>> Relation for ByteCheckRel2<F, C> {
    type Structure = Vec<bool>;

    type Instance = C::Commitment;

    type Witness = Vec<F>;

    fn check(
        _structure: &Self::Structure,
        _instance: &Self::Instance,
        _witness: &Self::Witness,
    ) -> bool {
        todo!()
    }
}

pub struct BytecheckReduction1;

impl<F, C> Reduction<F, ByteCheckRel1<F, C>, ByteCheckRel2<F, C>> for BytecheckReduction1
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ();

    type VerifierKey = ();

    type Proof = ();

    type Error = NoError;

    type Params = ();

    fn transcript_pattern(_key: &(), builder: TranscriptBuilder) -> TranscriptBuilder {
        builder
    }

    fn verifier_key(_structure: &Vec<bool>) -> Self::VerifierKey {}

    fn key_pair(_structure: &Vec<bool>) -> (Self::VerifierKey, Self::ProverKey) {
        ((), ())
    }

    fn params(_key: &Self::VerifierKey) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        _key: &Self::ProverKey,
        _instance: (C::Commitment, ()),
        _witness: (Vec<F>, Vec<F>),
        _transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<ByteCheckRel2<F, C>, Self::Proof> {
        todo!()
    }

    fn verify<S: Duplex<F>>(
        _key: &Self::VerifierKey,
        _instance: (C::Commitment, ()),
        _proof: GuardedProof<Self::Proof>,
        _transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<C::Commitment, Self::Error> {
        todo!()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BytecheckReduction2;

mod sumcheck {
    use alloc::vec;
    use alloc::vec::{IntoIter, Vec};
    use ark_ff::Field;
    use ark_serialize::CanonicalSerialize;
    use commit::CommitmentScheme;
    use commit::oracle::{CommittedNature, CommittedOracle, CommittedOracleInstance};
    use core::fmt::Debug;
    use sumcheck::SumcheckMessage;
    use sumcheck::oracles::composite::CompositeReductionKey;
    use sumcheck::oracles::core::SmallFunctions;
    use sumcheck::{
        MultiPoint, Var,
        evals::{Evals, EvalsCore},
        oracles::{
            SumcheckFunction,
            composite::{CompositeOracle, Either},
            core::{Coeffs, CoreNature, CoreOracle, CoreOracleInstance},
        },
    };
    use sumcheck_derive::EvalsCore;

    #[derive(Debug, Clone, Default, EvalsCore)]
    pub struct BytecheckEvals<V: Debug + Clone> {
        lookup: V,
        table: V,
        counts: V,
        lookup_challenge: V,
        /// To combine the different sumcheck claims.
        sumcheck_challenge: V,
        inverse_left: V,
        inverse_right: V,
        z_eq: V,
    }

    impl<F: Field> BytecheckEvals<F> {
        pub fn witness(
            structure: &[Self],
            lookups: &[F],
            counts: &[F],
            challenges: [F; 2],
            inverses: [&[F]; 2],
            z_eq: MultiPoint<F>,
        ) -> Vec<BytecheckEvals<F>> {
            let _ = (structure, lookups, counts, challenges, inverses, z_eq);
            todo!()
        }
    }

    impl<V: Debug + Clone + CanonicalSerialize> CanonicalSerialize for BytecheckEvals<V> {
        fn serialize_with_mode<W: ark_serialize::Write>(
            &self,
            mut writer: W,
            compress: ark_serialize::Compress,
        ) -> Result<(), ark_serialize::SerializationError> {
            let Self {
                lookup,
                table,
                counts,
                lookup_challenge,
                sumcheck_challenge,
                inverse_left,
                inverse_right,
                z_eq,
            } = self;
            lookup.serialize_with_mode(&mut writer, compress)?;
            table.serialize_with_mode(&mut writer, compress)?;
            counts.serialize_with_mode(&mut writer, compress)?;
            lookup_challenge.serialize_with_mode(&mut writer, compress)?;
            sumcheck_challenge.serialize_with_mode(&mut writer, compress)?;
            inverse_left.serialize_with_mode(&mut writer, compress)?;
            inverse_right.serialize_with_mode(&mut writer, compress)?;
            z_eq.serialize_with_mode(writer, compress)
        }

        fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
            let Self {
                lookup,
                table,
                counts,
                lookup_challenge,
                sumcheck_challenge,
                inverse_left,
                inverse_right,
                z_eq,
            } = self;
            lookup.serialized_size(compress)
                + table.serialized_size(compress)
                + counts.serialized_size(compress)
                + lookup_challenge.serialized_size(compress)
                + sumcheck_challenge.serialized_size(compress)
                + inverse_left.serialized_size(compress)
                + inverse_right.serialized_size(compress)
                + z_eq.serialized_size(compress)
        }
    }

    impl<F: Field> SumcheckFunction<F> for BytecheckEvals<()> {
        type Natures = Either<CoreNature, CommittedNature>;

        type Data = ();

        fn natures() -> Self::Mles<Self::Natures> {
            let chall = Either::Left(CoreNature::Challenge);
            let committed = Either::Right(CommittedNature::Witness);
            BytecheckEvals {
                lookup: committed,
                table: Either::Left(CoreNature::SmallStructure),
                counts: committed,
                lookup_challenge: chall,
                sumcheck_challenge: chall,
                inverse_left: committed,
                inverse_right: committed,
                // eq(x,r) for r a random point for zerocheck.
                z_eq: Either::Left(CoreNature::SmallInstance(Coeffs::PerVariable)),
            }
        }

        fn function<V: Var<F> + Debug>(_: &(), evals: &Self::Mles<V>) -> V {
            // inv_l == m / (table + chall)  === inv_l * (table + chall) == m
            // inv_r == 1 / (lookup + chall) === inv_r * (lookup + chall) == 1
            // sum inv_l == sum inv_r
            let BytecheckEvals {
                lookup,
                table,
                counts,
                lookup_challenge,
                sumcheck_challenge,
                inverse_left,
                inverse_right,
                z_eq,
            } = evals.clone();
            // inv_l * (table + chall) - m = 0
            let check1 = inverse_left.clone() * (table + &lookup_challenge) - counts;
            // inv_r * (lookup + chall) - 1 == 0
            let check2 = inverse_right.clone() * (lookup + &lookup_challenge) - F::one();

            // sum inv_l == sum inv_r
            let check3 = inverse_left - inverse_right;

            // 1 and 2 are zerocheck, 3 is just a sum.

            let batched = check1 * &z_eq;
            let batched = batched * &sumcheck_challenge + check2 * z_eq;
            batched * sumcheck_challenge + check3
        }
    }

    impl<F: Field> SmallFunctions<F> for BytecheckEvals<()> {
        fn small_functions() -> Self::Mles<Option<sumcheck::oracles::core::Func<F>>> {
            todo!()
        }
    }

    pub type BytecheckOracle<F, C, SF = BytecheckEvals<()>> =
        CompositeOracle<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

    pub type VerifierKey<F, C> = sumcheck::SumcheckVerifierKey<F, BytecheckOracle<F, C>>;
    pub type ProverKey<F, C> = sumcheck::ProverKey<F, BytecheckOracle<F, C>>;
    pub type Proof<F> = Vec<SumcheckMessage<F>>;

    pub type CompositeVerifierKey<F, C, SF = BytecheckEvals<()>> =
        CompositeReductionKey<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

    pub fn core_oracle_instance<F: Field>(
        vars: usize,
        chall1: F,
        chall2: F,
        chall3: MultiPoint<F>,
    ) -> CoreOracleInstance<F, BytecheckEvals<()>> {
        assert_eq!(chall3.vars(), vars);
        let coefficients = BytecheckEvals {
            lookup_challenge: vec![chall1],
            sumcheck_challenge: vec![chall2],
            z_eq: chall3.inner(),
            ..Default::default()
        };
        CoreOracleInstance::new(&coefficients, vars)
    }

    pub fn committed_oracle_instance<F, C>(
        lookup: C::Commitment,
        counts: C::Commitment,
        inverses: [C::Commitment; 2],
    ) -> CommittedOracleInstance<F, C, BytecheckEvals<()>>
    where
        F: Field,
        C: CommitmentScheme<F>,
    {
        let [inverse_left, inverse_right] = inverses.map(Some);
        let commits = BytecheckEvals {
            lookup: lookup.into(),
            table: None,
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

#[derive(Clone, Debug)]
pub struct Proof<F: Field, C: CommitmentScheme<F>> {
    counts_commit: C::Commitment,
    left_inverse: C::Commitment,
    right_inverse: C::Commitment,
    sumcheck: sumcheck::Proof<F>,
    composite: ProverEvals<F>,
}

#[derive(Clone, Debug, CanonicalSerialize)]
pub struct VerifierKey<F: Field, C: CommitmentScheme<F>> {
    sumcheck: sumcheck::VerifierKey<F, C>,
    composite: sumcheck::CompositeVerifierKey<F, C>,
    vars: usize,
}

pub struct ProverKey<F: Field, C: CommitmentScheme<F>> {
    selector: Vec<bool>,
    pcs: C,
    vars: usize,
    structure: Vec<BytecheckEvals<F>>,
    sumcheck: sumcheck::ProverKey<F, C>,
    composite: sumcheck::CompositeVerifierKey<F, C>,
    committed: commit::oracle::ProverKey<F, BytecheckEvals<()>, C>,
}

impl<F, C> Reduction<F, ByteCheckRel2<F, C>, OpeningRelation<F, C>> for BytecheckReduction2
where
    F: Field,
    C: CommitmentScheme<F>,
{
    type ProverKey = ProverKey<F, C>;

    type VerifierKey = VerifierKey<F, C>;

    type Proof = Proof<F, C>;

    type Error = NoError;

    type Params = ();

    fn transcript_pattern(
        key: &Self::VerifierKey,
        builder: TranscriptBuilder,
    ) -> TranscriptBuilder {
        //TODO:
        builder
            .round::<F, C::Commitment, 1>(&())
            .round::<F, [C::Commitment; 2], 1>(&())
            .point::<F>(key.vars)
            .subprotocol::<SumcheckReduction<F, BytecheckOracle<F, C>>, F, _, _>(&key.sumcheck)
            .subprotocol::<CompositeOracle<F, _, _, _>, _, _, _>(&key.composite)
            .subprotocol::<CoreOracle<F, BytecheckEvals<()>>, _, _, _>(key.composite.p1_key())
            .subprotocol::<CommittedOracle<F, C, BytecheckEvals<()>>, _, _, _>(
                key.composite.p2_key(),
            )
    }

    fn verifier_key(_structure: &Vec<bool>) -> Self::VerifierKey {
        todo!()
    }

    fn key_pair(_structure: &Vec<bool>) -> (Self::VerifierKey, Self::ProverKey) {
        todo!()
    }

    fn params(_key: &Self::VerifierKey) -> Self::Params {}

    fn prove<S: Duplex<F>>(
        key: &Self::ProverKey,
        instance: C::Commitment,
        witness: Vec<F>,
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Self::Proof> {
        let domain_size = 1 << key.vars;
        let byte_witness: Vec<u8> = key
            .selector
            .iter()
            .zip(&witness)
            .map(|(s, w)| {
                if *s {
                    assert!(w >= &F::from(u8::MIN));
                    assert!(w <= &F::from(u8::MAX));
                    let v = w.to_base_prime_field_elements().next().unwrap();
                    v.into_bigint().to_bytes_le()[0]
                } else {
                    0
                }
            })
            .collect();

        let mut counts = vec![F::ZERO; 256];

        for byte in &byte_witness {
            counts[*byte as usize] += F::ONE;
        }

        counts.resize(domain_size, F::ZERO);
        //NOTE: suboptimal, make use of commit_small_set.
        let counts_commit = key.pcs.commit_mle(&counts);

        let [lookup_challenge] = transcript.send_message(&counts_commit, &());

        let mut inv_denoms: Vec<F> = (0..=255u8)
            .map(|table| lookup_challenge + F::from(table))
            .collect();
        batch_inversion(inv_denoms.as_mut_slice());

        let mut inv_l = inv_denoms.clone();
        for (inv, count) in inv_l.iter_mut().zip(&counts[0..256]) {
            *inv *= count;
        }
        inv_l.resize(domain_size, F::ZERO);
        let inv_l = inv_l;

        let inv_r: Vec<F> = byte_witness
            .iter()
            .map(|i| inv_denoms[*i as usize])
            .collect();

        //NOTE: suboptimal, make use of commit_smalle_set.
        let inv_l_commit = key.pcs.commit_mle(&inv_l);

        let set: [F; 256] = inv_r[0..256].try_into().unwrap();
        let inv_r_commit = key.pcs.commit_small_set(&byte_witness, set);

        let inv_commits = [inv_l_commit, inv_r_commit];
        let [sumcheck_challenge] = transcript.send_message(&inv_commits, &());

        let zerocheck_point = MultiPoint::new(transcript.point());

        let (instance, witness) = {
            let evals = BytecheckEvals::witness(
                &key.structure,
                &witness,
                &counts,
                [lookup_challenge, sumcheck_challenge],
                [&inv_l, &inv_r],
                zerocheck_point.clone(),
            );

            let core_instance = core_oracle_instance(
                key.vars,
                lookup_challenge,
                sumcheck_challenge,
                zerocheck_point,
            );
            let committed_instance = committed_oracle_instance::<F, C>(
                instance,
                counts_commit.clone(),
                inv_commits.clone(),
            );

            let oracle_instance = CompositeOracleInstance {
                oracle1_instance: core_instance,
                oracle2_instance: committed_instance,
            };

            let instance = SumcheckInstance::new(F::zero(), oracle_instance);
            (instance, evals)
        };

        let ProverOutput {
            instance,
            witness,
            proof: sumcheck_proof,
        } = SumcheckReduction::prove(&key.sumcheck, instance, witness, transcript);

        let ProverOutput {
            instance: (core_instance, committed_instance),
            witness,
            proof: composite,
        } = CompositeOracle::prove(&key.composite, instance, witness, transcript);

        let _ = CoreOracle::prove(&(), core_instance, witness.clone(), transcript);

        let ProverOutput {
            instance,
            witness,
            proof: (),
        } = CommittedOracle::prove(&key.committed, committed_instance, witness, transcript);

        let [left_inverse, right_inverse] = inv_commits;
        let proof = Proof {
            counts_commit,
            left_inverse,
            right_inverse,
            sumcheck: sumcheck_proof,
            composite,
        };

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }

    fn verify<S: Duplex<F>>(
        key: &Self::VerifierKey,
        instance: C::Commitment,
        proof: GuardedProof<Self::Proof>,
        transcript: &mut VerifierTranscript<F, S>,
    ) -> Result<OpenInstance<F, C>, Self::Error> {
        // inv_l == m / (table + chall)  === inv_l * (table + chall) == m
        // inv_r == 1 / (lookup + chall) === inv_r * (lookup + chall) == 1

        // let table be committed as structure, with values i for in 0..256,
        // and 0s anywhere else.
        // <- commit to counts
        // -> sample challenge chall
        // <- commit to inv_l = counts / (table + chall)
        // <- commit to inv_r = 1 / (lookup + chall)
        // -> sample sumcheck challenge chall2
        // -> sample point challenge chall3 for zerocheck
        // assert sum f' == sum count / (table + chall )
        // assert f' * (lookup + chall) == 1

        let vars = key.vars;
        //TODO:
        let (counts, [lookup_challenge]) = transcript
            .receive_message(|proof| proof.counts_commit.clone(), &proof, &())
            .unwrap();

        //TODO:
        let (inverses, [sumcheck_challenge]) = transcript
            .receive_message(
                |proof| [proof.left_inverse.clone(), proof.right_inverse.clone()],
                &proof,
                &(),
            )
            .unwrap();

        let sumcheck_instance: SumcheckInstance<F, BytecheckOracle<F, C>> = {
            let zerocheck_point = MultiPoint::new(transcript.point());
            let core_instance =
                core_oracle_instance(vars, lookup_challenge, sumcheck_challenge, zerocheck_point);
            let committed_instance = committed_oracle_instance::<F, C>(instance, counts, inverses);
            // let committed_instance
            // let coefficients = coreor
            // let core_oracle_isntance = CoreOracleInstance::new(coefficients, vars);
            let oracle_instance = CompositeOracleInstance {
                oracle1_instance: core_instance,
                oracle2_instance: committed_instance,
            };
            SumcheckInstance::new(F::zero(), oracle_instance)
        };

        //TODO:
        let instance = SumcheckReduction::verify(
            &key.sumcheck,
            sumcheck_instance,
            proof.clone().map(|proof| proof.sumcheck),
            transcript,
        )
        .unwrap();

        //TODO:
        let (core_instance, committed_instance) = CompositeOracle::verify(
            &key.composite,
            instance,
            proof.map(|proof| proof.composite),
            transcript,
        )
        .unwrap();

        //TODO:
        CoreOracle::verify(
            key.composite.p1_key(),
            core_instance,
            GuardedProof::empty(),
            transcript,
        )
        .unwrap();

        //TODO:
        let instance = CommittedOracle::verify(
            key.composite.p2_key(),
            committed_instance,
            GuardedProof::empty(),
            transcript,
        )
        .unwrap();

        Ok(instance)
    }
}

impl<F: Field, C: CommitmentScheme<F>> Extension<F, C> for ByteCheck {
    type Instance = ();

    type R1 = ByteCheckRel1<F, C>;

    type R2 = ByteCheckRel2<F, C>;

    type R3 = OpeningRelation<F, C>;

    fn derive_structure(_r1_structure: &Self::Structure) -> <Self::R2 as Relation>::Structure {
        todo!()
    }

    fn commit_witness(_pcs: &C, _witness: &Self::Witness) -> Self::Instance {
        todo!()
    }

    type Reduction1 = BytecheckReduction1;

    type Reduction2 = BytecheckReduction2;

    type AgregationScheme = SingleCommitAggregation;

    type FoldingScheme = NoFolding;
}
