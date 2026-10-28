use argo::{
    garble::{
        Circuit, Nonce,
        groth16_verifier::{GID, Input, InputMac, InputMacKey, VerifierKey, garble_groth16},
    },
    mac::{MacKey, Random},
};
use ark_bn254::{Bn254, Fq, Fr, G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::UniformRand;
use ark_std::rand::{SeedableRng, rngs::StdRng};
use criterion::{Criterion, criterion_group, criterion_main};
use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn invalid_snark(c: &mut Criterion) {
    const SEED: u64 = 0;
    let mut rng = StdRng::seed_from_u64(SEED);

    let secret = Fq::rand(&mut rng);
    let gid = GID::random(&mut rng);

    let input = Input {
        A: G1Affine::rand(&mut rng).into(),
        B: G2Affine::rand(&mut rng).into(),
        C: G1Affine::rand(&mut rng).into(),
        x: [Fr::rand(&mut rng)],
    };

    let verifier_key = VerifierKey {
        G1: [G1Affine::rand(&mut rng)],
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Bn254::pairing(G1Affine::rand(&mut rng), G2Affine::generator()).0,
    };

    let input_mac_key = InputMacKey::random_key(&mut rng);

    let mut garble_group = c.benchmark_group("groth16-garble");
    garble_group.sample_size(100);
    garble_group.bench_function("garble", |b| {
        let mut res = None;
        b.iter(|| {
            res = Some(garble_groth16(SEED, secret, verifier_key, &input_mac_key, gid).unwrap());
        })
    });
    garble_group.finish();

    let table = garble_groth16(SEED, secret, verifier_key, &input_mac_key, gid).unwrap();

    let input_mac: InputMac = input_mac_key.encode(&input);

    let mut evaluate_group = c.benchmark_group("groth16-evaluate");
    evaluate_group.sample_size(100);
    evaluate_group.bench_function("evaluate", |b| {
        b.iter(|| {
            table
                .evaluate(&mut Nonce::new(), &input, &input_mac)
                .unwrap()
                .0
        })
    });

    let output = table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .0;

    assert_eq!(output, secret);
}

criterion_group!(benches, invalid_snark);
criterion_main!(benches);
