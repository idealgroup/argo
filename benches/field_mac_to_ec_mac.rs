use argo::{
    garble::{
        Circuit, Nonce,
        bivariate::InputMacKey,
        field_mac_to_ec_mac::{self, OutputMacKey},
        groth16_verifier::{KAPPA_A, KAPPA_B},
    },
    mac::{
        MacKey, Random, RandomFromPhi,
        endo::{EndoMac, EndoMacKey, PSqModR},
    },
    utils::{
        bits::{FromBits, NumBits, ToBits},
        group::FromLeBytesModOrder,
    },
};
use ark_bn254::{Fq, g1, g2};
use ark_ec::{scalar_mul::glv::GLVConfig, short_weierstrass::Affine};
use ark_ff::{Field, UniformRand};
use ark_std::rand::{SeedableRng, rngs::StdRng};
use criterion::{Criterion, criterion_group, criterion_main};

fn field_mac_to_ec_mac<Config, const KAPPA: usize>(is_full: bool, c: &mut Criterion)
where
    Config: GLVConfig + Clone + PSqModR,
    Config::BaseField: Field<BasePrimeField = Fq>
        + NumBits
        + ToBits
        + FromBits<bool, Config::BaseField>
        + FromBits<Config::BaseField, Config::BaseField>
        + Random,
    <Config::BaseField as Field>::BasePrimeField: FromLeBytesModOrder,
    EndoMacKey<Config, Affine<Config>>:
        RandomFromPhi<Affine<Config>, EndoMac<Config, Affine<Config>>>,
{
    const SEED: u64 = 0;
    let mut rng = StdRng::seed_from_u64(SEED);

    let input_point = Affine::<Config>::rand(&mut rng);
    let input = input_point.into();

    let input_mac_key = InputMacKey::random_key(&mut rng);
    let output_mac_key = OutputMacKey::<Config, KAPPA>::random_key(&mut rng);

    let mut garble_group = c.benchmark_group("field_mac_to_ec_mac_garble");
    garble_group.sample_size(100);
    garble_group.bench_function("garble", |b| {
        b.iter(|| {
            field_mac_to_ec_mac::Table::garble(
                &mut Nonce::new(),
                &mut rng,
                Some((is_full, output_mac_key.clone(), Fq::from(42u64))),
                &input_mac_key,
            )
            .unwrap();
        })
    });
    garble_group.finish();

    let table = field_mac_to_ec_mac::Table::garble(
        &mut Nonce::new(),
        &mut rng,
        Some((is_full, output_mac_key.clone(), Fq::from(42u64))),
        &input_mac_key,
    )
    .unwrap()
    .0;

    let input_mac = input_mac_key.encode(&input);

    let mut evaluate_group = c.benchmark_group("field_mac_to_ec_mac_evaluate");
    evaluate_group.sample_size(100);
    evaluate_group.bench_function("evaluate", |b| {
        b.iter(|| {
            table
                .evaluate(&mut Nonce::new(), &input, &input_mac)
                .unwrap()
                .0
        })
    });

    let evaluated_output_mac = table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .1;
    let expected_output_mac = output_mac_key.encode(&input_point);

    for (expected, evaluated) in expected_output_mac.iter().zip(evaluated_output_mac.iter()) {
        if **expected != **evaluated {
            if !is_full {
                assert_eq!(**expected, -**evaluated);
            } else {
                panic!()
            }
        }
    }
}

fn bench_groth16_curve_points(c: &mut Criterion) {
    // proof.A
    field_mac_to_ec_mac::<g1::Config, KAPPA_A>(true, c);

    // proof.B
    field_mac_to_ec_mac::<g2::Config, KAPPA_B>(false, c);

    // proof.C
    field_mac_to_ec_mac::<g1::Config, KAPPA_B>(false, c);
}

criterion_group!(benches, bench_groth16_curve_points);
criterion_main!(benches);
