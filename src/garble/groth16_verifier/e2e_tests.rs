//! End-to-end runs of one garbled verifier on real ark-groth16 proofs: valid
//! proofs reveal nothing; invalid, malformed, and garbler-crafted exceptional
//! proofs reveal the secret.

use std::{
    panic::{AssertUnwindSafe, catch_unwind},
    sync::OnceLock,
};

use ark_bn254::{Bn254, Fq, Fq2, Fq12, Fr, G1Affine, G2Affine, g2};
use ark_ec::{
    AffineRepr, CurveGroup, pairing::Pairing, scalar_mul::glv::GLVConfig,
    short_weierstrass::SWCurveConfig,
};
use ark_ff::{Field, PrimeField, Zero};
use ark_groth16::{Groth16, Proof};
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_snark::SNARK;
use ark_std::{
    UniformRand,
    rand::{SeedableRng, rngs::StdRng},
};

use super::*;
use crate::{
    garble::keys::{a_ec_mac_key, b_mac_key},
    mac::endo::{Endo, EndoMacKey, PSqModR},
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
        cs.enforce_constraint(lc!() + a_var, lc!() + b_var, lc!() + x_var)
    }
}

/// The garbler's mask keys, recovered by replaying the garbling RNG.
struct GarblerKeys {
    a: Vec<EndoMacKey<g1::Config, G1Affine>>,
    b: Vec<EndoMacKey<g2::Config, G2Affine>>,
    c: Vec<EndoMacKeyG1>,
}

struct Fixture {
    secret: Fq,
    input_mac_key: InputMacKey,
    table: Table,
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
            proof_input(&proof, a * b)
        };
        let proof = prove(3, 11);
        let zero_proof = prove(0, 7);

        // e(A, B) = e(alpha, beta) e(L, gamma) e(C, delta) with
        // L = gamma_abc[0] + x gamma_abc[1].
        let c = Bn254::multi_pairing([vk.alpha_g1, vk.gamma_abc_g1[0]], [vk.beta_g2, vk.gamma_g2])
            .0
            .inverse()
            .unwrap();
        let verifier_key = VerifierKey {
            G1: vk.gamma_abc_g1[1],
            H1: -vk.delta_g2,
            H2: -vk.gamma_g2,
            c,
        };
        assert_eq!(verifier_key.pairing(&proof), Fq12::ONE);
        assert_eq!(verifier_key.pairing(&zero_proof), Fq12::ONE);

        let secret = Fq::rand(&mut rng);
        let input_mac_key = InputMacKey::random_key(&mut rng);
        let gid = GID::random(&mut rng);
        let table = garble_groth16(SEED, secret, verifier_key, &input_mac_key, gid).unwrap();

        let keys = garbler_keys();
        assert_replayed_keys(&table, &input_mac_key, &keys, &proof);

        Fixture {
            secret,
            input_mac_key,
            table,
            keys,
            proof,
            zero_proof,
        }
    })
}

fn proof_input(proof: &Proof<Bn254>, x: Fr) -> Input {
    Input {
        A: proof.a.into(),
        B: proof.b.into(),
        C: proof.c.into(),
        x,
    }
}

/// Replays `Table::garble`'s RNG draws up to and including the C mask keys.
fn garbler_keys() -> GarblerKeys {
    let mut rng = StdRng::seed_from_u64(SEED);
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
fn assert_replayed_keys(
    table: &Table,
    input_mac_key: &InputMacKey,
    keys: &GarblerKeys,
    input: &Input,
) {
    let input_mac = input_mac_key.encode(input);
    let mut nonce = Nonce::new();
    assert!(
        table
            .input_validity
            .evaluate_coordinates(&mut nonce, input, &input_mac)
            .unwrap()
            .is_none()
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

fn evaluate(input: &Input) -> Result<Fq, EvalError> {
    let f = fixture();
    let input_mac = f.input_mac_key.encode(input);
    aes_ctr_clear_set();
    aes_mitccr_clear_set();
    let output = f.table.evaluate(&mut Nonce::new(), input, &input_mac);
    aes_ctr_clear_set();
    aes_mitccr_clear_set();
    output.map(|(output, _)| output)
}

/// Asserts every case reveals the secret, reporting all failing cases at once.
fn assert_reveal(cases: Vec<(&str, Input)>) {
    let secret = fixture().secret;
    let failures: Vec<_> = cases
        .into_iter()
        .filter_map(|(name, input)| {
            let outcome = match catch_unwind(AssertUnwindSafe(|| evaluate(&input))) {
                Ok(Ok(output)) if output == secret => return None,
                Ok(Ok(output)) if output.is_zero() => "accepted".to_owned(),
                Ok(Ok(_)) => "wrong output".to_owned(),
                Ok(Err(error)) => format!("{error:?}"),
                Err(_) => "panicked".to_owned(),
            };
            Some(format!("{name}: {outcome}"))
        })
        .collect();
    assert!(failures.is_empty(), "secret not revealed: {failures:#?}");
}

fn with_a(input: &Input, A: G1Affine) -> Input {
    Input {
        A: A.into(),
        ..*input
    }
}

fn with_b(input: &Input, B: G2Affine) -> Input {
    Input {
        B: B.into(),
        ..*input
    }
}

fn with_c(input: &Input, C: G1Affine) -> Input {
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
    assert_eq!(evaluate(&f.proof).unwrap(), Fq::ZERO);
    assert_eq!(evaluate(&f.zero_proof).unwrap(), Fq::ZERO);
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
                x: f.proof.x + Fr::ONE,
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
        x: Fr::new_unchecked(Fr::MODULUS),
        ..f.zero_proof
    };
    assert_eq!(f.table.verifier_key.pairing(&non_canonical_x), Fq12::ONE);

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
