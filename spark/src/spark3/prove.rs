use crate::spark3::{
    committed::{MinorStructure, SparkOracle},
    reduction::{self, sumcheck_instance, Proof},
    sumcheck_argument::{SparkChallenges, SparkEvals},
    SparseMle,
};
use ark_ff::{batch_inversion, Field};
use commit::commit2::{
    oracle::{self, CommittedOracle},
    CommitmentScheme, OpeningRelation,
};
use sponge::sponge::Duplex;
use std::rc::Rc;
use sumcheck::{
    self, eq,
    oracles::{
        composite::{CompositeOracle, CompositeReductionKey},
        core::CoreOracle,
    },
    MultiPoint, SumcheckReduction,
};
use transcript::reduction2::{ProverOutput, Reduction, Transcript};

type OracleKey<F, C, SF> =
    CompositeReductionKey<F, SF, CoreOracle<F, SF>, CommittedOracle<F, C, SF>>;

pub struct ProverKey<F: Field, C: CommitmentScheme<F>, const N: usize> {
    addresses: [Vec<u8>; N],
    minor_structure: Rc<MinorStructure<N>>,
    sumcheck_structure: Rc<Vec<SparkEvals<F, N>>>,
    pcs: C,
    sumcheck_key: sumcheck::ProverKey<F, SparkOracle<F, C, N>>,
    oracle_key: OracleKey<F, C, SparkEvals<(), N>>,
    core_oracle: CoreOracle<F, SparkEvals<(), N>>,
    committed_oracle_key: oracle::ProverKey<F, SparkEvals<(), N>, C>,
}

type VerifierKey<F, C, const N: usize> = reduction::Key<F, C, SparkEvals<(), N>, N>;

impl<F, C, const N: usize> ProverKey<F, C, N>
where
    F: Field,
    C: CommitmentScheme<F>,
{
    pub fn new(mle: &SparseMle<F, N>, pcs: C) -> (VerifierKey<F, C, N>, Self) {
        let minor_structure = MinorStructure::new(mle);
        let minor_structure = Rc::new(minor_structure);
        let mut addresses = [(); N].map(|_| Vec::new());

        let mut highest_address = 0u8;
        for address in &mle.addresses {
            highest_address = highest_address.max(address[N - 1]);
            for (i, address) in address.iter().enumerate() {
                addresses[i].push(*address);
            }
        }
        let vars = (N - 1) * 8 + (highest_address.highest_one().unwrap_or(0) + 1) as usize;

        let sumcheck_structure = SparkEvals::structure(mle);
        let sumcheck_structure = Rc::new(sumcheck_structure);

        let core_oracle = CoreOracle::new(SparkEvals::small_functions());

        let oracle = SparkOracle::new(
            (),
            Rc::clone(&sumcheck_structure),
            core_oracle.clone(),
            pcs.clone(),
        );

        let (sumcheck_verifier_key, sumcheck_key) = SumcheckReduction::key_pair(&oracle);

        let (_, oracle_key) = CompositeOracle::key_pair(&oracle);

        let (_, committed_oracle_key) = CommittedOracle::key_pair(&oracle.inner_oracles().1);

        let verifier_key = VerifierKey::new(
            (*minor_structure).clone(),
            sumcheck_verifier_key,
            oracle_key.clone(),
            vars,
        );

        let prover_key = Self {
            addresses,
            minor_structure,
            sumcheck_structure,
            pcs,
            sumcheck_key,
            oracle_key,
            core_oracle,
            committed_oracle_key,
        };
        (verifier_key, prover_key)
    }

    pub(crate) fn prove<S: Duplex<F>>(
        &self,
        points: [MultiPoint<F>; N],
        transcript: &mut Transcript<F, S>,
    ) -> ProverOutput<OpeningRelation<F, C>, Proof<F, C, N>> {
        let eqs: [Vec<F>; N] = points.clone().map(|point| eq::eq(&point));

        let mut witness = (*self.sumcheck_structure).clone();

        for (i, (addresses, table)) in self.addresses.iter().zip(&eqs).enumerate() {
            for (eval, addr) in witness.iter_mut().zip(addresses) {
                eval.dimensions[i].eq_lookup = table[(*addr) as usize];
            }
        }

        let lookup_commitments: [C::Commitment; N] = {
            let mut eqs = eqs.iter();
            self.addresses.each_ref().map(|addresses| {
                let eq: Vec<F> = eqs.next().unwrap().clone();
                let eq: [F; 256] = eq.try_into().unwrap();
                self.pcs.commit_small_set(addresses, eq)
            })
        };

        let [c1, c2] = transcript.send_message(&lookup_commitments, &());
        let lookup_chall = c1;
        let compression_chall = c2;

        let mut eqs = eqs.into_iter();
        let inverses_and_commits = self.addresses.each_ref().map(|addresses| {
            let eq: Vec<F> = eqs.next().unwrap().clone();
            let eq: [F; 256] = eq.try_into().unwrap();

            let mut inverses = eq;
            for (i, eq) in inverses.iter_mut().enumerate() {
                *eq = F::from(i as u8) * compression_chall + *eq + lookup_chall
            }
            batch_inversion(&mut inverses);

            let commit = self.pcs.commit_small_set(addresses, inverses);
            (inverses.to_vec(), commit)
        });

        let inverse_commitments = inverses_and_commits
            .each_ref()
            .map(|(_, commit)| commit.clone());

        let inverses = inverses_and_commits.map(|(inverses, _)| inverses);
        for (i, (addresses, table)) in self.addresses.iter().zip(inverses).enumerate() {
            for (eval, addr) in witness.iter_mut().zip(addresses) {
                eval.dimensions[i].inverse = table[(*addr) as usize];
            }
        }

        let [] = transcript.send_message(&inverse_commitments, &());

        let zerocheck_point = MultiPoint::new(transcript.point());

        let zerocheck_evals = eq::eq(&zerocheck_point);

        for (eval, z) in witness.iter_mut().zip(zerocheck_evals) {
            eval.zerocheck = z;
        }

        let [combination_chall] = transcript.send_message(&(), &());

        let expected_sums =
            self.minor_structure
                .expected_sums(&points, lookup_chall, compression_chall);

        let sum = expected_sums
            .into_iter()
            .fold(F::zero(), |acc, s| acc * combination_chall + s);

        let challenges = SparkChallenges::new(combination_chall, compression_chall, lookup_chall);

        let instance = sumcheck_instance(
            sum,
            lookup_commitments.clone(),
            inverse_commitments.clone(),
            zerocheck_point,
            &challenges,
        );

        let reduced = SumcheckReduction::prove(&self.sumcheck_key, instance, witness, transcript);

        let ProverOutput {
            instance,
            witness,
            proof: sumcheck_proof,
        } = reduced;

        let reduced = CompositeOracle::prove(&self.oracle_key, instance, witness, transcript);

        let ProverOutput {
            instance: (core_instance, committed_instance),
            witness,
            proof: oracle_query_proof,
        } = reduced;

        CoreOracle::prove(
            &self.core_oracle,
            core_instance,
            witness.clone(),
            transcript,
        );

        let reduced = CommittedOracle::prove(
            &self.committed_oracle_key,
            committed_instance,
            witness,
            transcript,
        );

        let ProverOutput {
            instance,
            witness,
            proof: _,
        } = reduced;

        let proof = Proof {
            lookup_commitments,
            inverse_commitments,
            sumcheck_proof,
            oracle_query_proof,
        };

        ProverOutput {
            instance,
            witness,
            proof,
        }
    }
}
