use ark_ff::{Field, UniformRand};
use ark_vesta::{Fr, Projective, VestaConfig};
use commit::CommitmentScheme;
use criterion::{
    BatchSize, BenchmarkGroup, BenchmarkId, Criterion, SamplingMode, criterion_group,
    criterion_main, measurement::WallTime,
};
use hash_to_curve::svdw::SvdwMap;
use lcs::circuit::BuildLcs;
use lileum::{CircuitKey, testing::utils::HashChain};
use rand::{Rng, SeedableRng, rngs::StdRng};
use sponge::{self, sponge::Duplex};

type Scheme = commit::ipa::IpaCommitmentScheme<Fr, Projective, SvdwMap<VestaConfig>>;
type Permutation = sponge::poseidon2::PoseidonDefault<Fr>;
type Sponge = sponge::sponge::Sponge<Fr, Permutation, 1, 2, 3>;

fn size<const N: usize>() -> u32 {
    let profile = <HashChain<N> as BuildLcs<Fr, 1, 1, 1, 5>>::profile();
    let witness_size = profile.witness_length.next_power_of_two().ilog2();
    println!("N: {}, len: 2^{}", N, witness_size);
    witness_size
}

#[allow(dead_code)]
/// A selection of circuits whose size sits just below a power of 2.
/// From 2^12 to 2^21.
fn sizes() {
    fn boundary<const N1: usize, const N2: usize>() {
        let s1 = size::<N1>();
        let s2 = size::<N2>();
        println!("---------");
        assert_eq!(s1 + 1, s2);
    }
    boundary::<11, 12>();
    boundary::<22, 23>();
    boundary::<44, 45>();
    boundary::<89, 90>();
    boundary::<178, 179>();
    boundary::<356, 357>();
    boundary::<712, 713>();
    boundary::<1424, 1425>();
    boundary::<2849, 2850>();
    boundary::<5698, 5699>();
}

fn proving(c: &mut Criterion) {
    let mut group = c.benchmark_group("Proving Time");
    group.sampling_mode(SamplingMode::Flat);
    let mut rng = StdRng::seed_from_u64(0);
    prove::<11>(&mut group, &mut rng);
    prove::<22>(&mut group, &mut rng);
    prove::<44>(&mut group, &mut rng);
    prove::<89>(&mut group, &mut rng);
    prove::<178>(&mut group, &mut rng);
    group.finish()
}

fn prove<const N: usize>(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut impl Rng)
where
    Fr: Field,
    Scheme: CommitmentScheme<Fr>,
    Sponge: Duplex<Fr>,
{
    let profile = <HashChain<N> as BuildLcs<Fr, 1, 1, 1, 5>>::profile();

    group.bench_with_input(
        BenchmarkId::new("Proving", profile.witness_length),
        &(),
        |b, _| {
            let preimage = Fr::rand(rng);
            let key = CircuitKey::<Fr, Sponge, HashChain<N>, Scheme, 2, 4, 5>::new();

            b.iter(|| {
                let (_instance, _proof, _output) = key.prove_from_inputs([preimage]);
            });
        },
    );
}

fn fold<const N: usize>(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut impl Rng)
where
    Fr: Field,
    Scheme: CommitmentScheme<Fr>,
    Sponge: Duplex<Fr>,
{
    let profile = <HashChain<N> as BuildLcs<Fr, 1, 1, 1, 5>>::profile();

    group.bench_with_input(
        BenchmarkId::new("Folding", profile.witness_length),
        &(),
        |b, _| {
            let preimage = Fr::rand(rng);
            let key = CircuitKey::<Fr, Sponge, HashChain<N>, Scheme, 2, 4, 5>::new();

            let (instance, witness, _) = key.commit_witness([preimage]);
            let instances = (instance.clone(), instance);
            let witnesses = [witness.clone(), witness];

            b.iter_batched(
                || (instances.clone(), witnesses.clone()),
                |((ins1, ins2), witnesses)| key.fold_prove(ins1, ins2, witnesses),
                BatchSize::PerIteration,
            );
        },
    );
}

fn folding(c: &mut Criterion) {
    let mut group = c.benchmark_group("Folding Time");
    group.sampling_mode(SamplingMode::Flat);
    let mut rng = StdRng::seed_from_u64(0);
    fold::<11>(&mut group, &mut rng);
    fold::<22>(&mut group, &mut rng);
    fold::<44>(&mut group, &mut rng);
    fold::<89>(&mut group, &mut rng);
    fold::<178>(&mut group, &mut rng);
    fold::<356>(&mut group, &mut rng);
    fold::<712>(&mut group, &mut rng);
    fold::<1424>(&mut group, &mut rng);
    fold::<2849>(&mut group, &mut rng);
    fold::<5698>(&mut group, &mut rng);
    group.finish()
}

fn commit_and_fold<const N: usize>(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut impl Rng)
where
    Fr: Field,
    Scheme: CommitmentScheme<Fr>,
    Sponge: Duplex<Fr>,
{
    let profile = <HashChain<N> as BuildLcs<Fr, 1, 1, 1, 5>>::profile();

    group.bench_with_input(
        BenchmarkId::new("CommitFolding", profile.witness_length),
        &(),
        |b, _| {
            let preimage = Fr::rand(rng);
            let key = CircuitKey::<Fr, Sponge, HashChain<N>, Scheme, 2, 4, 5>::new();
            let (instance1, witness1, _) = key.commit_witness([preimage]);

            b.iter(|| {
                let preimage = Fr::rand(rng);
                let (instance2, witness2, _) = key.commit_witness([preimage]);
                // let instances = (instance1.clone(), instance2);
                let witnesses = [witness1.clone(), witness2];
                let _folded = key.fold_prove(instance1.clone(), instance2, witnesses);
            });
        },
    );
}

fn commit_folding(c: &mut Criterion) {
    let mut group = c.benchmark_group("Commit and Fold Time");
    group.sampling_mode(SamplingMode::Flat);
    let mut rng = StdRng::seed_from_u64(0);

    commit_and_fold::<11>(&mut group, &mut rng);
    commit_and_fold::<22>(&mut group, &mut rng);
    commit_and_fold::<44>(&mut group, &mut rng);
    commit_and_fold::<89>(&mut group, &mut rng);
    commit_and_fold::<178>(&mut group, &mut rng);
    commit_and_fold::<356>(&mut group, &mut rng);
    commit_and_fold::<712>(&mut group, &mut rng);
    commit_and_fold::<1424>(&mut group, &mut rng);
    commit_and_fold::<2849>(&mut group, &mut rng);
    commit_and_fold::<5698>(&mut group, &mut rng);
    group.finish()
}

fn verify<const N: usize>(group: &mut BenchmarkGroup<'_, WallTime>, rng: &mut impl Rng)
where
    Fr: Field,
    Scheme: CommitmentScheme<Fr>,
    Sponge: Duplex<Fr>,
{
    let profile = <HashChain<N> as BuildLcs<Fr, 1, 1, 1, 5>>::profile();

    group.bench_with_input(
        BenchmarkId::new("Verifying", profile.witness_length),
        &(),
        |b, _| {
            let preimage = Fr::rand(rng);
            let key = CircuitKey::<Fr, Sponge, HashChain<N>, Scheme, 2, 4, 5>::new();
            let (instance, proof, _) = key.prove_from_inputs([preimage]);

            b.iter_batched(
                || (instance.clone(), proof.clone()),
                |(instance, proof)| key.verify(instance, proof),
                BatchSize::PerIteration,
            );
        },
    );
}

fn verifying(c: &mut Criterion) {
    let mut group = c.benchmark_group("Verification Time");
    group.sampling_mode(SamplingMode::Flat);
    let mut rng = StdRng::seed_from_u64(0);
    verify::<11>(&mut group, &mut rng);
    verify::<22>(&mut group, &mut rng);
    verify::<44>(&mut group, &mut rng);
    verify::<89>(&mut group, &mut rng);
    verify::<178>(&mut group, &mut rng);
    group.finish()
}

fn hash_chain_benchmarks(c: &mut Criterion) {
    proving(c);
    verifying(c);
    folding(c);
    commit_folding(c);
}

criterion_group! {
    name = hash_chain;
    config = Criterion::default().sample_size(10);
    targets = hash_chain_benchmarks
}
criterion_main!(hash_chain);
