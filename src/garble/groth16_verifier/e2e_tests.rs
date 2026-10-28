//! End-to-end runs of one garbled verifier on real ark-groth16 proofs: valid
//! proofs reveal nothing; invalid, malformed, and garbler-crafted exceptional
//! proofs reveal the secret.

use std::{
    panic::{AssertUnwindSafe, catch_unwind},
    sync::OnceLock,
};

use ark_bn254::{Bn254, Fq, Fq2, Fq12, Fr, G1Affine, G2Affine, g2};
use ark_ec::{
    AffineRepr, CurveGroup, scalar_mul::glv::GLVConfig, short_weierstrass::SWCurveConfig,
};
use ark_ff::{BigInt, BigInteger, Field, PrimeField, Zero};
use ark_groth16::{Groth16, Proof};
use ark_relations::{
    gr1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
    lc,
};
use ark_snark::SNARK;
use ark_std::{
    UniformRand,
    rand::{SeedableRng, rngs::StdRng},
};

use super::*;
use crate::{
    garble::bivariate::Monomial,
    garble::keys::{a_ec_mac_key, b_mac_key},
    mac::endo::{Endo, EndoMacKey, PSqModR},
    utils::error::InputError,
};

const SEED: u64 = 7;

/// Knowledge of a, b with a * b = x for the public input x.
#[derive(Clone)]
struct Multiply {
    a: Option<Fr>,
    b: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for Multiply {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let a = self.a.ok_or(SynthesisError::AssignmentMissing);
        let b = self.b.ok_or(SynthesisError::AssignmentMissing);
        let a_var = cs.new_witness_variable(|| a)?;
        let b_var = cs.new_witness_variable(|| b)?;
        let x_var = cs.new_input_variable(|| Ok(a? * b?))?;
        cs.enforce_r1cs_constraint(|| lc!() + a_var, || lc!() + b_var, || lc!() + x_var)
    }
}

/// The garbler's mask keys, recovered by replaying the garbling RNG.
struct GarblerKeys {
    a: Vec<EndoMacKey<g1::Config, G1Affine>>,
    b: Vec<EndoMacKey<g2::Config, G2Affine>>,
    c: Vec<EndoMacKeyG1>,
}

struct Fixture {
    verifier_key: VerifierKey,
    garbling: Garbling,
    keys: GarblerKeys,
    /// Valid proof of 3 * 11 = 33.
    proof: Input,
    /// Valid proof of 0 * 7 = 0, so that x = r is a non-canonical encoding.
    zero_proof: Input,
}

/// One setup, two proofs, and one garbling shared by all tests.
fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let mut rng = StdRng::seed_from_u64(SEED);
        let (pk, vk) =
            Groth16::<Bn254>::circuit_specific_setup(Multiply { a: None, b: None }, &mut rng)
                .unwrap();
        let mut prove = |a: u64, b: u64| {
            let (a, b) = (Fr::from(a), Fr::from(b));
            let circuit = Multiply {
                a: Some(a),
                b: Some(b),
            };
            let proof = Groth16::<Bn254>::prove(&pk, circuit, &mut rng).unwrap();
            assert!(Groth16::<Bn254>::verify(&vk, &[a * b], &proof).unwrap());
            proof_input(&proof, [a * b])
        };
        let proof = prove(3, 11);
        let zero_proof = prove(0, 7);

        let verifier_key = VerifierKey::from_groth16(&vk, &[PublicInput::Garbled]).unwrap();
        assert_eq!(verifier_key.pairing(&proof).unwrap(), Fq12::ONE);
        assert_eq!(verifier_key.pairing(&zero_proof).unwrap(), Fq12::ONE);

        let garbling = garble_with(SEED, &verifier_key);
        let keys = garbler_keys::<1>(SEED);
        assert_replayed_keys(&garbling, &keys, &proof);

        Fixture {
            verifier_key,
            garbling,
            keys,
            proof,
            zero_proof,
        }
    })
}

fn proof_input<const N: usize>(proof: &Proof<Bn254>, x: [Fr; N]) -> Input<N> {
    Input {
        A: proof.a.into(),
        B: proof.b.into(),
        C: proof.c.into(),
        x,
    }
}

fn seed_bytes(seed: u64) -> [u8; 32] {
    let mut bytes = [0; 32];
    bytes[..8].copy_from_slice(&seed.to_le_bytes());
    bytes
}

fn garble_with<const N: usize>(seed: u64, verifier_key: &VerifierKey<N>) -> Garbling<N> {
    let garbling = garble(verifier_key, seed_bytes(seed)).unwrap();
    assert!(garbling.table.has_garbled_shape());
    garbling
}

/// Replays `garble`'s RNG draws up to and including the C mask keys.
fn garbler_keys<const N: usize>(seed: u64) -> GarblerKeys {
    let mut rng = ChaCha20Rng::from_seed(seed_bytes(seed));
    while Fq::rand(&mut rng).is_zero() {}
    InputMacKey::<N>::random_key(&mut rng);
    GID::random(&mut rng);
    let rs: [Fr; KAPPA_B] = std::array::from_fn(|_| Fr::rand(&mut rng));
    let x = Fr::rand(&mut rng);
    let a = a_ec_mac_key(&mut rng, x).to_vec();
    let (ddh, b) = b_mac_key(&mut rng, x, rs);
    let c = ddh
        .phis
        .iter()
        .map(|phi| EndoMacKeyG1::random_from_phi(&mut rng, &phi.clone().into()))
        .collect();
    GarblerKeys {
        a,
        b: b.to_vec(),
        c,
    }
}

/// The replayed keys must be the ones inside the garbled converters, otherwise
/// the crafted inputs below would only be random invalid proofs.
fn assert_replayed_keys<const N: usize>(
    garbling: &Garbling<N>,
    keys: &GarblerKeys,
    input: &Input<N>,
) {
    let Garbling {
        table,
        input_mac_key,
        ..
    } = garbling;
    let input_mac = input_mac_key.encode(input);
    let mut nonce = Nonce::new();
    assert!(
        table
            .input_validity
            .evaluate_coordinates(&mut nonce, &InputBits::from(input), &input_mac)
            .unwrap()
            .is_ok()
    );
    let a_mac = table
        .a_ec_mac
        .evaluate(&mut nonce, &input.A, &input_mac.A)
        .unwrap()
        .1;
    let b_mac = table
        .b_ec_mac
        .evaluate(&mut nonce, &input.B, &input_mac.B)
        .unwrap()
        .1;
    let c_mac = table
        .c_ec_mac
        .evaluate(&mut nonce, &input.C, &input_mac.C)
        .unwrap()
        .1;
    aes_ctr_clear_set();
    aes_mitccr_clear_set();

    let (A, B, C): (G1Affine, G2Affine, G1Affine) =
        (input.A.into(), input.B.into(), input.C.into());
    for (mac, key) in a_mac.iter().zip(&keys.a) {
        assert!(**mac == *key.encode(&A));
    }
    // Compact conversions recover y by a square root, so only up to sign.
    for (mac, key) in b_mac.iter().zip(&keys.b) {
        let expected = *key.encode(&B);
        assert!(**mac == expected || **mac == -expected);
    }
    for (mac, key) in c_mac.iter().zip(&keys.c) {
        let expected = *key.encode(&C);
        assert!(**mac == expected || **mac == -expected);
    }
}

/// The point P with phi(P) = K for the first replica with a nonzero phi.
fn doubling_input<G: GLVConfig + PSqModR>(keys: &[EndoMacKey<G, Affine<G>>]) -> Affine<G> {
    keys.iter()
        .find_map(|key| {
            EndoScalar::<G>::iter()
                .into_iter()
                .take(6)
                .map(|inverse| inverse.endo(key.k))
                .find(|point| key.phi.endo(*point) == key.k)
        })
        .unwrap()
}

fn evaluate_table<const N: usize>(
    verifier_key: &VerifierKey<N>,
    table: &Table<N>,
    input_mac_key: &InputMacKey<N>,
    input: &Input<N>,
) -> Result<Option<Fq>, EvalError> {
    evaluate_raw(verifier_key, table, input_mac_key, &input.into())
}

fn evaluate_garbling<const N: usize>(
    verifier_key: &VerifierKey<N>,
    garbling: &Garbling<N>,
    input: &Input<N>,
) -> Result<Option<Fq>, EvalError> {
    evaluate_table(
        verifier_key,
        &garbling.table,
        &garbling.input_mac_key,
        input,
    )
}

fn evaluate(input: &Input) -> Result<Option<Fq>, EvalError> {
    let f = fixture();
    evaluate_garbling(&f.verifier_key, &f.garbling, input)
}

/// Asserts every case reveals the secret, reporting all failing cases at once.
fn assert_reveal(cases: Vec<(&str, Input)>) {
    let f = fixture();
    assert_reveals(&f.verifier_key, &f.garbling, cases);
}

fn assert_reveals<const N: usize>(
    verifier_key: &VerifierKey<N>,
    garbling: &Garbling<N>,
    cases: Vec<(&str, Input<N>)>,
) {
    let failures: Vec<_> = cases
        .into_iter()
        .filter_map(|(name, input)| {
            let evaluate = || evaluate_garbling(verifier_key, garbling, &input);
            let outcome = match catch_unwind(AssertUnwindSafe(evaluate)) {
                Ok(Ok(Some(output))) if output == garbling.secret => return None,
                Ok(Ok(None)) => "accepted".to_owned(),
                Ok(Ok(Some(_))) => "wrong output".to_owned(),
                Ok(Err(error)) => format!("{error:?}"),
                Err(_) => "panicked".to_owned(),
            };
            Some(format!("{name}: {outcome}"))
        })
        .collect();
    assert!(failures.is_empty(), "secret not revealed: {failures:#?}");
}

fn with_a<const N: usize>(input: &Input<N>, A: G1Affine) -> Input<N> {
    Input {
        A: A.into(),
        ..*input
    }
}

fn with_b<const N: usize>(input: &Input<N>, B: G2Affine) -> Input<N> {
    Input {
        B: B.into(),
        ..*input
    }
}

fn with_c<const N: usize>(input: &Input<N>, C: G1Affine) -> Input<N> {
    Input {
        C: C.into(),
        ..*input
    }
}

fn off_subgroup_twist_point(rng: &mut StdRng) -> G2Affine {
    loop {
        let x = Fq2::rand(rng);
        if let Some(y) = (x.square() * x + g2::Config::COEFF_B).sqrt() {
            let point = G2Affine::new_unchecked(x, y);
            if !point.mul_bigint(Fr::MODULUS).is_zero() {
                return point;
            }
        }
    }
}

#[test]
fn valid_proofs_reveal_nothing() {
    let f = fixture();
    assert_eq!(evaluate(&f.proof).unwrap(), None);
    assert_eq!(evaluate(&f.zero_proof).unwrap(), None);
}

#[test]
fn invalid_proofs_reveal_secret() {
    let f = fixture();
    let (A, B, C): (G1Affine, G2Affine, G1Affine) =
        (f.proof.A.into(), f.proof.B.into(), f.proof.C.into());
    let g1 = G1Affine::generator();
    assert_reveal(vec![
        ("A + G", with_a(&f.proof, (A + g1).into_affine())),
        (
            "B + H",
            with_b(&f.proof, (B + G2Affine::generator()).into_affine()),
        ),
        ("C + G", with_c(&f.proof, (C + g1).into_affine())),
        (
            "x + 1",
            Input {
                x: [f.proof.x[0] + Fr::ONE],
                ..f.proof
            },
        ),
        (
            "A of another proof",
            with_a(&f.proof, f.zero_proof.A.into()),
        ),
    ]);
}

#[test]
fn malformed_proofs_reveal_secret() {
    let f = fixture();
    let p = Fq::new_unchecked(Fq::MODULUS);
    let zero = bivariate::Input {
        x: Fq::ZERO,
        y: Fq::ZERO,
    };
    let mut rng = StdRng::seed_from_u64(99);

    // x = r is the zero proof's own public input, so the pairing accepts it.
    let non_canonical_x = Input {
        x: [Fr::new_unchecked(Fr::MODULUS)],
        ..f.zero_proof
    };
    assert_eq!(f.verifier_key.pairing(&non_canonical_x).unwrap(), Fq12::ONE);

    let mut cases = vec![("x = r", non_canonical_x)];
    for (name, input) in [
        (
            "A.x = p",
            Input {
                A: bivariate::Input { x: p, ..f.proof.A },
                ..f.proof
            },
        ),
        ("B.y.c1 = p", {
            let mut input = f.proof;
            input.B.y.c1 = p;
            input
        }),
        (
            "C.y = p",
            Input {
                C: bivariate::Input { y: p, ..f.proof.C },
                ..f.proof
            },
        ),
        (
            "A off curve",
            Input {
                A: bivariate::Input {
                    y: f.proof.A.y + Fq::ONE,
                    ..f.proof.A
                },
                ..f.proof
            },
        ),
        (
            "B off curve",
            Input {
                B: bivariate::Input {
                    x: f.proof.B.x + Fq2::ONE,
                    ..f.proof.B
                },
                ..f.proof
            },
        ),
        (
            "C off curve",
            Input {
                C: bivariate::Input {
                    x: f.proof.C.x.double(),
                    ..f.proof.C
                },
                ..f.proof
            },
        ),
        ("A = (0, 0)", Input { A: zero, ..f.proof }),
        (
            "B = (0, 0)",
            Input {
                B: bivariate::Input {
                    x: Fq2::ZERO,
                    y: Fq2::ZERO,
                },
                ..f.proof
            },
        ),
        ("C = (0, 0)", Input { C: zero, ..f.proof }),
        (
            "B outside G2",
            with_b(&f.proof, off_subgroup_twist_point(&mut rng)),
        ),
    ] {
        cases.push((name, input));
    }
    assert_reveal(cases);
}

/// A garbler who knows a mask K can submit P with phi(P) = +-K, which hits
/// the doubling and cancellation cases of the chord formula in one replica.
/// These proofs are invalid, so they must reveal the secret like any other.
#[test]
fn exceptional_proofs_reveal_secret() {
    let f = fixture();
    let a = doubling_input(&f.keys.a);
    let b = doubling_input(&f.keys.b);
    let c = doubling_input(&f.keys.c);
    assert!(!b.is_in_correct_subgroup_assuming_on_curve());

    assert_reveal(vec![
        ("A doubling", with_a(&f.proof, a)),
        ("A cancellation", with_a(&f.proof, -a)),
        ("B doubling", with_b(&f.proof, b)),
        ("B cancellation", with_b(&f.proof, -b)),
        ("C doubling", with_c(&f.proof, c)),
        ("C cancellation", with_c(&f.proof, -c)),
    ]);
}

/// Knowledge of a, b with a * b = x1 and a + b = x2.
#[derive(Clone)]
struct MulAdd {
    a: Option<Fr>,
    b: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for MulAdd {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let a = self.a.ok_or(SynthesisError::AssignmentMissing);
        let b = self.b.ok_or(SynthesisError::AssignmentMissing);
        let a_var = cs.new_witness_variable(|| a)?;
        let b_var = cs.new_witness_variable(|| b)?;
        let x1 = cs.new_input_variable(|| Ok(a? * b?))?;
        let x2 = cs.new_input_variable(|| Ok(a? + b?))?;
        cs.enforce_r1cs_constraint(|| lc!() + a_var, || lc!() + b_var, || lc!() + x1)?;
        cs.enforce_r1cs_constraint(
            || lc!() + a_var + b_var,
            || lc!() + Variable::One,
            || lc!() + x2,
        )
    }
}

/// Knowledge of a with a * a = a, so no public inputs at all.
#[derive(Clone)]
struct Idempotent {
    a: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for Idempotent {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        cs.enforce_r1cs_constraint(|| lc!() + a, || lc!() + a, || lc!() + a)
    }
}

fn mul_add_setup(
    rng: &mut StdRng,
) -> (
    ark_groth16::ProvingKey<Bn254>,
    ark_groth16::VerifyingKey<Bn254>,
) {
    Groth16::<Bn254>::circuit_specific_setup(MulAdd { a: None, b: None }, rng).unwrap()
}

/// A proof of a * b = x1, a + b = x2, and its public inputs.
fn mul_add_proof(
    pk: &ark_groth16::ProvingKey<Bn254>,
    rng: &mut StdRng,
    a: u64,
    b: u64,
) -> (Proof<Bn254>, [Fr; 2]) {
    let (a, b) = (Fr::from(a), Fr::from(b));
    let proof = Groth16::<Bn254>::prove(
        pk,
        MulAdd {
            a: Some(a),
            b: Some(b),
        },
        rng,
    )
    .unwrap();
    (proof, [a * b, a + b])
}

/// Constant public inputs are folded into `c`, so each statement gets its own
/// garbling and the evaluator holds no labels for them.
#[test]
fn constant_inputs_change_per_garbling() {
    let mut rng = StdRng::seed_from_u64(SEED);
    let (pk, vk) = mul_add_setup(&mut rng);
    let (proof1, inputs1) = mul_add_proof(&pk, &mut rng, 3, 11);
    let (proof2, inputs2) = mul_add_proof(&pk, &mut rng, 5, 7);
    let constant = |inputs: [Fr; 2]| inputs.map(PublicInput::Constant);
    let vk1 = VerifierKey::<0>::from_groth16(&vk, &constant(inputs1)).unwrap();
    let vk2 = VerifierKey::<0>::from_groth16(&vk, &constant(inputs2)).unwrap();
    let (proof1, proof2) = (proof_input(&proof1, []), proof_input(&proof2, []));
    assert_eq!(vk1.pairing(&proof1).unwrap(), Fq12::ONE);
    assert_eq!(vk2.pairing(&proof2).unwrap(), Fq12::ONE);

    let garbling1 = garble_with(SEED, &vk1);
    let garbling2 = garble_with(SEED + 1, &vk2);
    assert_replayed_keys(&garbling1, &garbler_keys::<0>(SEED), &proof1);

    assert_eq!(evaluate_garbling(&vk1, &garbling1, &proof1).unwrap(), None);
    assert_eq!(evaluate_garbling(&vk2, &garbling2, &proof2).unwrap(), None);
    // A valid proof for other constants is an invalid proof for this garbling.
    assert_eq!(
        evaluate_garbling(&vk1, &garbling1, &proof2).unwrap(),
        Some(garbling1.secret)
    );
    assert_eq!(
        evaluate_garbling(&vk2, &garbling2, &proof1).unwrap(),
        Some(garbling2.secret)
    );
}

#[test]
fn zero_garbled_inputs_reveal_on_bad_proofs() {
    let mut rng = StdRng::seed_from_u64(SEED);
    let (pk, vk) = mul_add_setup(&mut rng);
    let (proof, inputs) = mul_add_proof(&pk, &mut rng, 3, 11);
    let verifier_key =
        VerifierKey::<0>::from_groth16(&vk, &inputs.map(PublicInput::Constant)).unwrap();
    let proof = proof_input(&proof, []);
    let garbling = garble_with(SEED, &verifier_key);
    let keys = garbler_keys::<0>(SEED);

    let (A, B, C): (G1Affine, G2Affine, G1Affine) =
        (proof.A.into(), proof.B.into(), proof.C.into());
    let p = Fq::new_unchecked(Fq::MODULUS);
    let a = doubling_input(&keys.a);
    let b = doubling_input(&keys.b);
    let c = doubling_input(&keys.c);
    assert_reveals(
        &verifier_key,
        &garbling,
        vec![
            (
                "A + G",
                with_a(&proof, (A + G1Affine::generator()).into_affine()),
            ),
            (
                "B + H",
                with_b(&proof, (B + G2Affine::generator()).into_affine()),
            ),
            (
                "C + G",
                with_c(&proof, (C + G1Affine::generator()).into_affine()),
            ),
            (
                "A.x = p",
                Input {
                    A: bivariate::Input { x: p, ..proof.A },
                    ..proof
                },
            ),
            (
                "B outside G2",
                with_b(&proof, off_subgroup_twist_point(&mut rng)),
            ),
            ("A doubling", with_a(&proof, a)),
            ("B cancellation", with_b(&proof, -b)),
            ("C doubling", with_c(&proof, c)),
        ],
    );
}

#[test]
fn circuit_without_public_inputs() {
    let mut rng = StdRng::seed_from_u64(SEED);
    let (pk, vk) =
        Groth16::<Bn254>::circuit_specific_setup(Idempotent { a: None }, &mut rng).unwrap();
    assert_eq!(vk.gamma_abc_g1.len(), 1);
    let proof = Groth16::<Bn254>::prove(&pk, Idempotent { a: Some(Fr::ONE) }, &mut rng).unwrap();
    let proof = proof_input(&proof, []);
    let verifier_key = VerifierKey::<0>::from_groth16(&vk, &[]).unwrap();
    let garbling = garble_with(SEED, &verifier_key);

    let evaluate = |input| evaluate_garbling(&verifier_key, &garbling, input).unwrap();
    assert_eq!(evaluate(&proof), None);
    let C: G1Affine = proof.C.into();
    let invalid = with_c(&proof, (C + G1Affine::generator()).into_affine());
    assert_eq!(evaluate(&invalid), Some(garbling.secret));
}

/// One input fixed at garbling time and one garbled.
#[test]
fn constant_and_garbled_inputs() {
    let mut rng = StdRng::seed_from_u64(SEED);
    let (pk, vk) = mul_add_setup(&mut rng);
    let (proof, [x1, x2]) = mul_add_proof(&pk, &mut rng, 3, 11);
    let verifier_key =
        VerifierKey::<1>::from_groth16(&vk, &[PublicInput::Constant(x1), PublicInput::Garbled])
            .unwrap();
    let proof = proof_input(&proof, [x2]);
    let garbling = garble_with(SEED, &verifier_key);

    let evaluate = |input| evaluate_garbling(&verifier_key, &garbling, input).unwrap();
    assert_eq!(evaluate(&proof), None);
    let wrong_x2 = Input {
        x: [x2 + Fr::ONE],
        ..proof
    };
    assert_eq!(evaluate(&wrong_x2), Some(garbling.secret));
}

#[test]
fn from_groth16_rejects_mismatched_inputs() {
    let mut rng = StdRng::seed_from_u64(SEED);
    let (_, mut vk) = mul_add_setup(&mut rng);
    let x = PublicInput::Constant(Fr::ONE);

    assert_eq!(
        VerifierKey::<0>::from_groth16(&vk, &[x]),
        Err(VerifierKeyError::PublicInputLength {
            expected: 2,
            actual: 1
        })
    );
    assert_eq!(
        VerifierKey::<1>::from_groth16(&vk, &[x, x]),
        Err(VerifierKeyError::GarbledInputCount {
            expected: 1,
            actual: 0
        })
    );
    assert_eq!(
        VerifierKey::<0>::from_groth16(&vk, &[x, PublicInput::Garbled]),
        Err(VerifierKeyError::GarbledInputCount {
            expected: 0,
            actual: 1
        })
    );
    vk.gamma_abc_g1.clear();
    assert_eq!(
        VerifierKey::<0>::from_groth16(&vk, &[]),
        Err(VerifierKeyError::MissingConstantTerm)
    );
}

fn with_component<const N: usize>(
    bits: &InputBits<N>,
    index: usize,
    value: BigInt<4>,
) -> InputBits<N> {
    let mut raw = bits.bits().to_vec();
    raw[index * COMPONENT_BITS..(index + 1) * COMPONENT_BITS]
        .copy_from_slice(&value.to_bits_le()[..COMPONENT_BITS]);
    InputBits::new(raw).unwrap()
}

fn evaluate_raw<const N: usize>(
    verifier_key: &VerifierKey<N>,
    table: &Table<N>,
    input_mac_key: &InputMacKey<N>,
    bits: &InputBits<N>,
) -> Result<Option<Fq>, EvalError> {
    let input_mac = input_mac_key.encode_bits(bits);
    aes_ctr_clear_set();
    aes_mitccr_clear_set();
    let output = table.evaluate_bits(verifier_key, bits, &input_mac);
    aes_ctr_clear_set();
    aes_mitccr_clear_set();
    output
}

/// Assert can sign any bits, including a component at or above its modulus.
/// Every such component must reveal the secret, even when it reduces to the
/// valid proof's value.
#[test]
fn non_canonical_bits_reveal_secret() {
    let f = fixture();
    let valid = InputBits::from(&f.proof);
    let names = [
        "A.x", "A.y", "B.x.c0", "B.x.c1", "B.y.c0", "B.y.c1", "C.x", "C.y", "x",
    ];
    let mut failures = Vec::new();
    let mut shifted_cases = 0;
    for (index, name) in names.into_iter().enumerate() {
        let modulus = if index < 8 { Fq::MODULUS } else { Fr::MODULUS };
        let mut plus_one = modulus;
        plus_one.add_with_carry(&BigInt::one());
        let mut values = vec![
            ("modulus", modulus),
            ("modulus + 1", plus_one),
            ("2^254 - 1", BigInt::from_bits_le(&[true; COMPONENT_BITS])),
        ];
        let component = &valid.bits()[index * COMPONENT_BITS..(index + 1) * COMPONENT_BITS];
        let mut shifted = BigInt::<4>::from_bits_le(component);
        shifted.add_with_carry(&modulus);
        if shifted.num_bits() as usize <= COMPONENT_BITS {
            values.push(("valid value + modulus", shifted));
            shifted_cases += 1;
        }

        for (value_name, value) in values {
            let bits = with_component(&valid, index, value);
            let g = &f.garbling;
            match evaluate_raw(&f.verifier_key, &g.table, &g.input_mac_key, &bits) {
                Ok(Some(output)) if output == g.secret => {}
                output => failures.push(format!("{name} = {value_name}: {output:?}")),
            }
        }
    }
    assert!(failures.is_empty(), "secret not revealed: {failures:#?}");
    assert!(shifted_cases > 0);
}

#[test]
fn labels_from_pairs_match_encoding() {
    let f = fixture();
    let g = &f.garbling;
    let bits = InputBits::from(&f.proof);
    let pairs = g.input_mac_key.label_pairs();
    assert_eq!(pairs.len(), InputBits::<1>::LEN);
    let labels: Vec<_> = pairs
        .iter()
        .zip(bits.bits())
        .map(|(pair, bit)| pair[*bit as usize])
        .collect();
    let input_mac = InputMac::from_labels(&labels).unwrap();
    assert_eq!(input_mac, g.input_mac_key.encode(&f.proof));
    assert_eq!(input_mac, g.input_mac_key.encode_bits(&bits));
    assert_eq!(
        super::evaluate(&f.verifier_key, &g.table, &bits, &input_mac),
        None
    );

    assert_eq!(InputBits::<0>::LEN, 2032);
    assert_eq!(
        InputBits::<1>::new(vec![false; 3]),
        Err(InputError::BitCount {
            expected: 2286,
            actual: 3
        })
    );
    assert_eq!(
        InputMac::<1>::from_labels(&labels[1..]),
        Err(InputError::LabelCount {
            expected: 2286,
            actual: 2285
        })
    );
}

#[test]
fn non_canonical_bits_without_garbled_inputs() {
    let mut rng = StdRng::seed_from_u64(SEED);
    let (pk, vk) = mul_add_setup(&mut rng);
    let (proof, inputs) = mul_add_proof(&pk, &mut rng, 3, 11);
    let verifier_key =
        VerifierKey::<0>::from_groth16(&vk, &inputs.map(PublicInput::Constant)).unwrap();
    let Garbling {
        table,
        secret,
        input_mac_key,
    } = garble_with(SEED, &verifier_key);
    let evaluate =
        |bits: &InputBits<0>| evaluate_raw(&verifier_key, &table, &input_mac_key, bits).unwrap();
    let valid = InputBits::from(&proof_input(&proof, []));
    assert_eq!(evaluate(&valid), None);

    for index in 0..8 {
        let mut plus_one = Fq::MODULUS;
        plus_one.add_with_carry(&BigInt::one());
        let bits = with_component(&valid, index, plus_one);
        assert_eq!(evaluate(&bits), Some(secret));
    }
}

fn serialize<const N: usize>(table: &Table<N>) -> Vec<u8> {
    let mut bytes = Vec::new();
    table.serialize_compressed(&mut bytes).unwrap();
    bytes
}

fn deserialize(bytes: &[u8]) -> Table {
    Table::deserialize_compressed(bytes).unwrap()
}

/// Hidden tables come from the garbler unopened, so one that deserializes
/// but has the wrong shape must be rejected rather than evaluated.
#[test]
fn malformed_tables_are_rejected() {
    let f = fixture();
    let bytes = serialize(&f.garbling.table);
    for len in [0, 1, bytes.len() / 2, bytes.len() - 1] {
        assert!(Table::<1>::deserialize_compressed(&bytes[..len]).is_err());
    }

    type Mutation = (&'static str, fn(&mut Table));
    let mutations: [Mutation; 8] = [
        ("C converter replica dropped", |t| {
            t.c_ec_mac.x.pop();
        }),
        ("Y tables on a compact converter", |t| {
            t.b_ec_mac.y = Some(Vec::new())
        }),
        ("doubling ciphertext dropped", |t| {
            t.a_ec_mac.doubling.pop();
        }),
        ("polynomial term dropped", |t| {
            t.c_ec_mac.z[0].tables.pop();
        }),
        ("monomial changed", |t| {
            t.a_ec_mac.x[0].tables[0].1 = Monomial::new(200, 200)
        }),
        ("scalar bit adaptor dropped", |t| {
            t.x_G[0].adaptors.pop();
        }),
        ("bit adaptor ciphertext truncated", |t| {
            t.x_G[0].adaptors[0].ciphertext.pop();
        }),
        ("gid changed", |t| t.gid[0] ^= 1),
    ];
    for (name, mutate) in mutations {
        let mut table = deserialize(&bytes);
        mutate(&mut table);
        let table = deserialize(&serialize(&table));
        assert!(!table.has_garbled_shape(), "{name}");
        let output = evaluate_table(&f.verifier_key, &table, &f.garbling.input_mac_key, &f.proof);
        assert!(
            matches!(output, Err(EvalError::MalformedTable)),
            "{name}: {output:?}"
        );
    }
}

/// Tables of the right shape can still disagree with each other. The compact
/// converters then decode an x with no curve point, which used to panic.
#[test]
fn inconsistent_converters_do_not_panic() {
    let f = fixture();
    let bytes = serialize(&f.garbling.table);
    let evaluate =
        |table| evaluate_table(&f.verifier_key, table, &f.garbling.input_mac_key, &f.proof);

    let mut table = deserialize(&bytes);
    for x in &mut table.b_ec_mac.x {
        x.constant += Fq2::ONE;
    }
    assert!(table.has_garbled_shape());
    let output = evaluate(&table);
    assert!(
        matches!(output, Err(EvalError::InvalidMacPoint)),
        "{output:?}"
    );

    let mut table = deserialize(&bytes);
    for x in &mut table.c_ec_mac.x {
        x.constant += Fq::ONE;
    }
    let output = evaluate(&table);
    assert!(
        matches!(output, Err(EvalError::InvalidMacPoint)),
        "{output:?}"
    );
}

/// Garbling keeps no key state between calls, so circuits with different
/// delta and gamma can be garbled one after another in one process.
#[test]
fn two_circuits_in_one_process() {
    let mut rng = StdRng::seed_from_u64(SEED);
    let mut garble_circuit = |seed| {
        let (pk, vk) = mul_add_setup(&mut rng);
        let (proof, inputs) = mul_add_proof(&pk, &mut rng, 3, 11);
        let verifier_key =
            VerifierKey::<0>::from_groth16(&vk, &inputs.map(PublicInput::Constant)).unwrap();
        let garbling = garble_with(seed, &verifier_key);
        (verifier_key, garbling, proof_input(&proof, []))
    };
    let (vk1, garbling1, proof1) = garble_circuit(SEED);
    let (vk2, garbling2, proof2) = garble_circuit(SEED + 1);

    assert_eq!(evaluate_garbling(&vk1, &garbling1, &proof1).unwrap(), None);
    assert_eq!(evaluate_garbling(&vk2, &garbling2, &proof2).unwrap(), None);
    assert_eq!(
        evaluate_garbling(&vk1, &garbling1, &proof2).unwrap(),
        Some(garbling1.secret)
    );
    assert_eq!(
        evaluate_garbling(&vk2, &garbling2, &proof1).unwrap(),
        Some(garbling2.secret)
    );
}

/// The AES key schedules cached during a call are labels of that garbling
/// only, so none may outlive the call.
#[test]
fn aes_key_cache_is_cleared_after_each_call() {
    use crate::utils::aes_hash::aes_ctr::cached_instances;

    let f = fixture();
    let mut rng = StdRng::seed_from_u64(SEED);
    let (pk, vk) = mul_add_setup(&mut rng);
    let (_, inputs) = mul_add_proof(&pk, &mut rng, 3, 11);
    let verifier_key =
        VerifierKey::<0>::from_groth16(&vk, &inputs.map(PublicInput::Constant)).unwrap();
    garble_with(SEED, &verifier_key);
    assert_eq!(cached_instances(), 0);

    evaluate(&f.proof).unwrap();
    assert_eq!(cached_instances(), 0);
}

/// Cut-and-choose opens an instance by its seed, so regarbling the seed must
/// give the same table, secret and labels.
#[test]
fn same_seed_rebuilds_the_instance() {
    let f = fixture();
    let again = garble_with(SEED, &f.verifier_key);
    assert_eq!(serialize(&again.table), serialize(&f.garbling.table));
    assert_eq!(again.secret, f.garbling.secret);
    assert_eq!(
        again.input_mac_key.label_pairs(),
        f.garbling.input_mac_key.label_pairs()
    );

    let other = garble_with(SEED + 1, &f.verifier_key);
    assert_ne!(serialize(&other.table), serialize(&f.garbling.table));
    assert_ne!(other.secret, f.garbling.secret);
    assert_eq!(again.table.gid(), f.garbling.table.gid());
    assert_ne!(other.table.gid(), f.garbling.table.gid());
}

#[test]
fn garble_rejects_a_zero_pairing_constant() {
    let verifier_key = VerifierKey::<0> {
        c: Fq12::ZERO,
        ..fixture_without_garbled_inputs()
    };
    assert!(matches!(
        garble(&verifier_key, seed_bytes(SEED)),
        Err(GarbleError::DegenerateVerifierKey)
    ));
}

fn fixture_without_garbled_inputs() -> VerifierKey<0> {
    let mut rng = StdRng::seed_from_u64(SEED);
    let (pk, vk) = mul_add_setup(&mut rng);
    let (_, inputs) = mul_add_proof(&pk, &mut rng, 3, 11);
    VerifierKey::<0>::from_groth16(&vk, &inputs.map(PublicInput::Constant)).unwrap()
}

/// A flipped bit anywhere in a hidden table either fails to deserialize or
/// gives a table that evaluates without panicking.
#[test]
fn flipped_bits_do_not_panic() {
    use ark_std::rand::Rng;

    let f = fixture();
    let bytes = serialize(&f.garbling.table);
    let mut rng = StdRng::seed_from_u64(SEED);
    for _ in 0..16 {
        let mut flipped = bytes.clone();
        flipped[rng.gen_range(0..bytes.len())] ^= 1 << rng.gen_range(0..8);
        if let Ok(table) = Table::<1>::deserialize_compressed(&flipped[..]) {
            let _ = evaluate_table(&f.verifier_key, &table, &f.garbling.input_mac_key, &f.proof);
        }
    }
}

/// A length prefix comes before the elements it counts, so a huge one must
/// fail on the missing elements rather than allocate for them up front.
#[test]
fn huge_length_prefixes_are_rejected() {
    let f = fixture();
    let bytes = serialize(&f.garbling.table);
    let lengths = [KAPPA_A, KAPPA_B, COMPONENT_BITS].map(|len| (len as u64).to_le_bytes());
    let prefixes: Vec<_> = (0..bytes.len() - 8)
        .filter(|&i| lengths.iter().any(|len| bytes[i..i + 8] == *len))
        .collect();
    assert!(prefixes.len() > 8);

    for &i in prefixes.iter().step_by(prefixes.len() / 8) {
        for huge in [u64::MAX, 1 << 40] {
            let mut mutated = bytes.clone();
            mutated[i..i + 8].copy_from_slice(&huge.to_le_bytes());
            assert!(
                Table::<1>::deserialize_compressed(&mutated[..]).is_err(),
                "length {huge} at byte {i}"
            );
        }
    }
}
