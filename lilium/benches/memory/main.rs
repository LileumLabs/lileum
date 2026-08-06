//! Memory benchmarks

mod allocator;

use allocator::{bench_memory, PeakMemory, PeakTrackingAllocator};
use ark_ff::{Field, UniformRand};
use ark_vesta::{Fr, Projective, VestaConfig};
use criterion::{
    criterion_group, criterion_main, BenchmarkGroup, BenchmarkId, Criterion, SamplingMode,
};
use rand::{rngs::StdRng, Rng, SeedableRng};
use std::time::Duration;

use ccs::circuit::BuildStructure;
use commit::commit2::CommitmentScheme;
use hash_to_curve::svdw::SvdwMap;
use lilium::{lilium2::circuit_key::CircuitKey, testing::utils::HashChain};
use sponge::{self, sponge::Duplex};

type Scheme = commit::ipa::IpaCommitmentScheme<Fr, Projective, SvdwMap<VestaConfig>>;
type Permutation = sponge::poseidon2::PoseidonDefault<Fr>;
type Sponge = sponge::sponge::Sponge<Fr, Permutation, 1, 2, 3>;

#[global_allocator]
static ALLOCATOR: PeakTrackingAllocator = PeakTrackingAllocator;

fn proving_memory(c: &mut Criterion<PeakMemory>) {
    let mut group = c.benchmark_group("Proving Memory");
    group.sampling_mode(SamplingMode::Flat);
    let mut rng = StdRng::seed_from_u64(0);
    prove::<11>(&mut group, &mut rng);
    prove::<89>(&mut group, &mut rng);
    prove::<178>(&mut group, &mut rng);
    group.finish()
}

fn prove<const N: usize>(group: &mut BenchmarkGroup<'_, PeakMemory>, rng: &mut impl Rng)
where
    Fr: Field,
    Scheme: CommitmentScheme<Fr>,
    Sponge: Duplex<Fr>,
{
    let profile = <HashChain<N> as BuildStructure<Fr, 1, 1, 1, 5>>::profile();

    group.bench_with_input(
        BenchmarkId::new("Proving", profile.witness_length),
        &(),
        |b, _| {
            let preimage = Fr::rand(rng);
            let key = CircuitKey::<Fr, Sponge, HashChain<N>, Scheme, 2, 4, 5>::new();

            bench_memory(b, || {
                let (_instance, _proof, _output) = key.prove_from_inputs([preimage]);
            });
        },
    );
}

fn verify<const N: usize>(group: &mut BenchmarkGroup<'_, PeakMemory>, rng: &mut impl Rng)
where
    Fr: Field,
    Scheme: CommitmentScheme<Fr>,
    Sponge: Duplex<Fr>,
{
    let profile = <HashChain<N> as BuildStructure<Fr, 1, 1, 1, 5>>::profile();

    group.bench_with_input(
        BenchmarkId::new("Verifying", profile.witness_length),
        &(),
        |b, _| {
            let preimage = Fr::rand(rng);
            let key = CircuitKey::<Fr, Sponge, HashChain<N>, Scheme, 2, 4, 5>::new();
            let (instance, proof, _) = key.prove_from_inputs([preimage]);

            bench_memory(b, || {
                let _ok = key.verify(instance.clone(), proof.clone());
            });
        },
    );
}

fn verification_memory(c: &mut Criterion<PeakMemory>) {
    let mut group = c.benchmark_group("Verification Memory");
    group.sampling_mode(SamplingMode::Flat);
    let mut rng = StdRng::seed_from_u64(0);
    verify::<11>(&mut group, &mut rng);
    verify::<89>(&mut group, &mut rng);
    verify::<178>(&mut group, &mut rng);
    group.finish()
}

fn fold<const N: usize>(group: &mut BenchmarkGroup<'_, PeakMemory>, rng: &mut impl Rng)
where
    Fr: Field,
    Scheme: CommitmentScheme<Fr>,
    Sponge: Duplex<Fr>,
{
    let profile = <HashChain<N> as BuildStructure<Fr, 1, 1, 1, 5>>::profile();

    group.bench_with_input(
        BenchmarkId::new("Folding", profile.witness_length),
        &(),
        |b, _| {
            let preimage = Fr::rand(rng);
            let key = CircuitKey::<Fr, Sponge, HashChain<N>, Scheme, 2, 4, 5>::new();

            let (instance, witness, _) = key.commit_witness([preimage]);

            bench_memory(b, || {
                let witnesses = [witness.clone(), witness.clone()];
                let _folded = key.fold_prove(instance.clone(), instance.clone(), witnesses);
            });
        },
    );
}

fn folding_memory(c: &mut Criterion<PeakMemory>) {
    let mut group = c.benchmark_group("Folding Memory");
    group.sampling_mode(SamplingMode::Flat);
    let mut rng = StdRng::seed_from_u64(0);
    fold::<11>(&mut group, &mut rng);
    fold::<712>(&mut group, &mut rng);
    fold::<5698>(&mut group, &mut rng);
    group.finish()
}

fn commit_and_fold<const N: usize>(group: &mut BenchmarkGroup<'_, PeakMemory>, rng: &mut impl Rng)
where
    Fr: Field,
    Scheme: CommitmentScheme<Fr>,
    Sponge: Duplex<Fr>,
{
    let profile = <HashChain<N> as BuildStructure<Fr, 1, 1, 1, 5>>::profile();

    group.bench_with_input(
        BenchmarkId::new("CommitFolding", profile.witness_length),
        &(),
        |b, _| {
            let preimage = Fr::rand(rng);
            let key = CircuitKey::<Fr, Sponge, HashChain<N>, Scheme, 2, 4, 5>::new();
            let (instance1, witness1, _) = key.commit_witness([preimage]);

            bench_memory(b, || {
                let preimage = Fr::rand(rng);
                let (instance2, witness2, _) = key.commit_witness([preimage]);
                let witnesses = [witness1.clone(), witness2];
                let _folded = key.fold_prove(instance1.clone(), instance2, witnesses);
            });
        },
    );
}

fn commit_folding_memory(c: &mut Criterion<PeakMemory>) {
    let mut group = c.benchmark_group("Commit and Fold Memory");
    group.sampling_mode(SamplingMode::Flat);
    let mut rng = StdRng::seed_from_u64(0);

    commit_and_fold::<11>(&mut group, &mut rng);
    commit_and_fold::<712>(&mut group, &mut rng);
    commit_and_fold::<5698>(&mut group, &mut rng);
    group.finish()
}

// Used to check SRS footprint
fn srs<CS, const N: usize>(group: &mut BenchmarkGroup<'_, PeakMemory>, name: &str)
where
    CS: CommitmentScheme<Fr>,
{
    let profile = <HashChain<N> as BuildStructure<Fr, 1, 1, 1, 5>>::profile();
    let vars = <HashChain<N> as BuildStructure<Fr, 1, 1, 1, 5>>::structure::<5>().vars();

    group.bench_with_input(
        BenchmarkId::new(name, profile.witness_length),
        &(),
        |b, _| {
            bench_memory(b, || {
                let _scheme = CS::new(vars);
            });
        },
    );
}

fn srs_memory(c: &mut Criterion<PeakMemory>) {
    let mut group = c.benchmark_group("SRS Memory");
    group.sampling_mode(SamplingMode::Flat);
    srs::<Scheme, 11>(&mut group, "IPA");
    srs::<Scheme, 712>(&mut group, "IPA");
    srs::<Scheme, 5698>(&mut group, "IPA");
    group.finish()
}

// Used to check whole CircuitKey footprint
fn setup<const N: usize>(group: &mut BenchmarkGroup<'_, PeakMemory>)
where
    Fr: Field,
    Scheme: CommitmentScheme<Fr>,
    Sponge: Duplex<Fr>,
{
    let profile = <HashChain<N> as BuildStructure<Fr, 1, 1, 1, 5>>::profile();

    group.bench_with_input(
        BenchmarkId::new("Setup", profile.witness_length),
        &(),
        |b, _| {
            bench_memory(b, || {
                let _key = CircuitKey::<Fr, Sponge, HashChain<N>, Scheme, 2, 4, 5>::new();
            });
        },
    );
}

fn setup_memory(c: &mut Criterion<PeakMemory>) {
    let mut group = c.benchmark_group("Setup Memory");
    group.sampling_mode(SamplingMode::Flat);
    setup::<11>(&mut group);
    setup::<712>(&mut group);
    setup::<5698>(&mut group);
    group.finish()
}

fn memory_benchmarks(c: &mut Criterion<PeakMemory>) {
    srs_memory(c);
    setup_memory(c);
    proving_memory(c);
    verification_memory(c);
    folding_memory(c);
    commit_folding_memory(c);
}

criterion_group! {
    name = hash_chain_memory;
    config = Criterion::default()
        .with_measurement(PeakMemory)
        .sample_size(10)
        .warm_up_time(Duration::from_millis(1))
        .measurement_time(Duration::from_millis(1));
    targets = memory_benchmarks
}
criterion_main!(hash_chain_memory);
