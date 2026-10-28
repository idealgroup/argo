use argo::{
    garble::{
        Circuit, Nonce,
        groth16_verifier::{GID, Input, InputMacKey, VerifierKey, garble_groth16},
    },
    mac::{MacKey, Random},
};
use ark_bn254::{Bn254, Fq, G1Affine, G2Affine};
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
                        let mut rng = StdRng::seed_from_u64(seed);
                        let input_mac_key = InputMacKey::random_key(&mut rng);
                        let secret = Fq::rand(&mut rng);
                        let gid = GID::random(&mut rng);

                        garble_groth16(seed, secret, verifier_key, &input_mac_key, gid).unwrap();
                    }
                });
        })
    });
    garble_group.finish();

    let input_mac_key = InputMacKey::random_key(&mut rng);
    let table = {
        let mut rng = StdRng::seed_from_u64(0);
        let secret = Fq::rand(&mut rng);
        let gid = GID::random(&mut rng);

        garble_groth16(0, secret, verifier_key, &input_mac_key, gid).unwrap()
    };

    let mut eval_group = c.benchmark_group("amortised-eval");
    eval_group.sample_size(10);
    eval_group.bench_function("amortised_eval", |b| {
        b.iter(|| {
            let chunk_size = (N as usize).div_ceil(rayon::current_num_threads());
            let input = Input::random(&mut rng);
            let input_mac = input_mac_key.encode(&input);

            (0..N)
                .collect::<Vec<_>>()
                .par_chunks(chunk_size)
                .for_each(|seeds| {
                    for &_ in seeds {
                        table
                            .evaluate(&mut Nonce::new(), &input, &input_mac)
                            .unwrap();
                    }
                });
        })
    });
    eval_group.finish();
}

criterion_group!(benches, amortised_garble);
criterion_main!(benches);
