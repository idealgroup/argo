use argo::{
    garble::groth16_verifier::{Input, InputBits, VerifierKey, evaluate, garble},
    mac::MacKey,
};
use ark_bn254::{Bn254, G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::UniformRand;
use ark_std::rand::{SeedableRng, rngs::StdRng};
use criterion::{Criterion, criterion_group, criterion_main};
use mimalloc::MiMalloc;
use rayon::{iter::ParallelIterator, slice::ParallelSlice};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn amortised_garble(c: &mut Criterion) {
    const N: u64 = 400;

    let mut rng = StdRng::seed_from_u64(0);

    let verifier_key = VerifierKey {
        G1: [G1Affine::rand(&mut rng)],
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Bn254::pairing(G1Affine::rand(&mut rng), G2Affine::generator()).0,
    };

    let mut garble_group = c.benchmark_group("amortised-garble");
    garble_group.sample_size(10);
    garble_group.bench_function("amortised_garble", |b| {
        b.iter(|| {
            let chunk_size = (N as usize).div_ceil(rayon::current_num_threads());

            (0..N)
                .collect::<Vec<_>>()
                .par_chunks(chunk_size)
                .for_each(|seeds| {
                    for &seed in seeds {
                        let mut seed_bytes = [0; 32];
                        seed_bytes[..8].copy_from_slice(&seed.to_le_bytes());
                        garble(&verifier_key, seed_bytes).unwrap();
                    }
                });
        })
    });
    garble_group.finish();

    let garbling = garble(&verifier_key, [0; 32]).unwrap();

    let mut eval_group = c.benchmark_group("amortised-eval");
    eval_group.sample_size(10);
    eval_group.bench_function("amortised_eval", |b| {
        b.iter(|| {
            let chunk_size = (N as usize).div_ceil(rayon::current_num_threads());
            let input = Input::random(&mut rng);
            let input_mac = garbling.input_mac_key.encode(&input);
            let bits = InputBits::from(&input);

            (0..N)
                .collect::<Vec<_>>()
                .par_chunks(chunk_size)
                .for_each(|seeds| {
                    for &_ in seeds {
                        evaluate(&verifier_key, &garbling.table, &bits, &input_mac).unwrap();
                    }
                });
        })
    });
    eval_group.finish();
}

criterion_group!(benches, amortised_garble);
criterion_main!(benches);
