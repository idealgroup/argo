//! Garbling table for a Groth16 verifier that commits to a secret `s`.
//! This table reveals `s` if it is evaluated on:
//! - (A, B, C) that does not satisfy e(A, B) e(C, H_1) e([x], H_2) = c^{-1},
//! where H_1, c are from the verifier key;
//! - (A, B, C) where any of the points is an invalid curve point;
//! - (A, B, C) where any of the (x, y) coordinates is larger than |Fq|;
//! - `x`` where `x` is larger than |Fr|.

pub(crate) mod input_validity;

use core::panic;
use std::{any::type_name, marker::PhantomData};

use ark_bn254::{Bn254, Fq, Fq2, Fq12, Fr, G1Affine, G2Affine, g1, g2};
use ark_ec::{
    AffineRepr, CurveGroup,
    pairing::Pairing,
    short_weierstrass::{Affine, Projective},
};
use ark_ff::{AdditiveGroup, Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    UniformRand,
    rand::{SeedableRng, rngs::StdRng},
};
use num_bigint::BigInt;
use parking_lot::RwLock;

use crate::{
    garble::{
        Circuit, Nonce,
        bilinear::{
            pairing::{self, GENERATOR_EXPONENT},
            scalar_mul,
        },
        bivariate, conditional_reveal, field_mac_to_ec_mac,
        keys::{a_ec_mac_key, b_mac_key},
    },
    mac::{
        IdentityMac, IdentityMacKey, IteratedMac, Mac, MacKey, RandomFromPhi,
        ddh::DDHMac,
        digit,
        endo::{EndoMacFq12, EndoMacG2, EndoMacKeyG1, EndoScalar},
    },
    utils::{
        constants::R_MUL_COFACTOR_GENERATOR,
        error::{EvalError, GarbleError},
    },
};

#[cfg(test)]
use crate::mac::Random;
#[cfg(test)]
use crate::utils::aes_hash::{
    aes_ctr::clear_set as aes_ctr_clear_set, aes_mitccr::clear_set as aes_mitccr_clear_set,
};

static PREPROCESSED_VK: RwLock<Option<GarblePreprocessedVk>> = RwLock::new(None);

#[cfg(test)]
pub(crate) fn reset_preprocessed_vk() {
    let mut w = PREPROCESSED_VK.write();
    *w = None;
}

// KAPPA_B is 1 + log_7(2^128)
pub const KAPPA_B: usize = 46 + 1;
// KAPPA_A is ceil(log_7(r))
pub const KAPPA_A: usize = 92;

pub type GID = [u8; 16];

/// Groth16 verifier key
#[derive(Debug, Clone, Copy, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey {
    pub G1: G1Affine,
    pub H1: G2Affine,
    pub H2: G2Affine,
    pub c: Fq12,
}

#[derive(Copy, Clone)]
pub struct GarblePreprocessedVk {
    /// e(G, H1)^{2^i}
    pub h1_target_pow_2: [Fq12; Fr::MODULUS_BIT_SIZE as usize],
    /// e(G, H2)^{2^i}
    pub h2_target_pow_2: [Fq12; Fr::MODULUS_BIT_SIZE as usize],
}

impl VerifierKey {
    /// Given the input (A, B, C), returns e(A, B) e(C, H_1) e([x], H_2) * c.
    /// Recall that if (A, B, C) is a valid Groth16 proof, it should satisfy
    ///                 e(A, B) e(C, H_1) e([x], H_2) = c^{-1}.
    /// In other words, this method should return Fq12::ONE on a valid proof.
    fn pairing(&self, input: &Input) -> Fq12 {
        Bn254::multi_pairing(
            vec![
                input.A.into(),
                input.C.into(),
                (self.G1 * input.x).into_affine(),
            ],
            vec![input.B.into(), self.H1, self.H2],
        )
        .0 * self.c
    }

    pub(crate) fn garble_preprocess(&self) -> GarblePreprocessedVk {
        if let Some(vk) = PREPROCESSED_VK.read().as_ref() {
            return *vk;
        }

        let preprocessed_vk = {
            let compute_pow_2 = |value: Fq12| {
                let mut powers = [Fq12::ZERO; Fr::MODULUS_BIT_SIZE as usize];
                powers[0] = value;
                for i in 1..Fr::MODULUS_BIT_SIZE as usize {
                    powers[i] = powers[i - 1].square();
                }
                powers
            };

            // h1_target := e(G, H1)
            let h1_target = Bn254::pairing(G1Affine::generator(), self.H1).0;

            // h2_target := e(G, H2)
            let h2_target = Bn254::pairing(G1Affine::generator(), self.H2).0;

            // [h1_target^{2^i}]
            let h1_target_pow_2 = compute_pow_2(h1_target);

            // [h2_target^{2^i}]
            let h2_target_pow_2 = compute_pow_2(h2_target);

            GarblePreprocessedVk {
                h1_target_pow_2,
                h2_target_pow_2,
            }
        };

        PREPROCESSED_VK.write().get_or_insert(preprocessed_vk);

        preprocessed_vk
    }
}

/// Groth16 proof.
#[derive(Debug, Clone, Copy)]
pub struct Input {
    pub A: bivariate::Input<Fq>,
    pub B: bivariate::Input<Fq2>,
    pub C: bivariate::Input<Fq>,
    pub x: Fr,
}

impl Input {
    pub fn random(rng: &mut StdRng) -> Self {
        use ark_ff::UniformRand;

        Input {
            A: G1Affine::rand(rng).into(),
            B: G2Affine::rand(rng).into(),
            C: G1Affine::rand(rng).into(),
            x: Fr::rand(rng),
        }
    }
}

/// Input MAC key from the Groth16 proof.
#[derive(Clone)]
pub struct InputMacKey {
    A: bivariate::InputMacKey<Fq>,
    B: bivariate::InputMacKey<Fq2>,
    C: bivariate::InputMacKey<Fq>,
    x: digit::bytes::DigitMacKey<Fr>,
}

/// Input MAC of the Groth16 proof.
#[derive(Debug, Clone)]
pub struct InputMac {
    A: bivariate::InputMac<Fq>,
    B: bivariate::InputMac<Fq2>,
    C: bivariate::InputMac<Fq>,
    x: digit::bytes::DigitMac<Fr>,
}

type Output = conditional_reveal::Output;

impl MacKey<Input, InputMac> for InputMacKey {
    fn encode(&self, value: &Input) -> InputMac {
        InputMac {
            A: self.A.encode(&value.A),
            B: self.B.encode(&value.B),
            C: self.C.encode(&value.C),
            x: self.x.encode(&value.x),
        }
    }
    #[cfg(test)]
    fn decode(&self, mac: &InputMac) -> Input {
        Input {
            A: self.A.decode(&mac.A),
            B: self.B.decode(&mac.B),
            C: self.C.decode(&mac.C),
            x: self.x.decode(&mac.x),
        }
    }
    fn random_key(rng: &mut StdRng) -> Self {
        Self {
            A: bivariate::InputMacKey::random_key(rng),
            B: bivariate::InputMacKey::random_key(rng),
            C: bivariate::InputMacKey::random_key(rng),
            x: digit::bytes::DigitMacKey::random_key(rng),
        }
    }
}

impl Mac<Input> for InputMac {
    type Key = InputMacKey;

    #[cfg(test)]
    fn random_input(rng: &mut StdRng) -> Input {
        Input::random(rng)
    }
}

/// Given an RNG seed, a domain separation tag for the fixed-key AES hash, and
/// the verifier key, returns a garbling table and the input MAC key used
pub fn garble_groth16(
    rng_seed: u64,
    secret: Fq,
    verifier_key: VerifierKey,
    input_mac_key: &InputMacKey,
    gid: GID,
) -> Result<Table, GarbleError> {
    let mut rng = StdRng::seed_from_u64(rng_seed);
    let mut nonce = Nonce::new();

    let table = Table::garble(
        &mut nonce,
        &mut rng,
        Some((secret, gid, verifier_key)),
        input_mac_key,
    )?
    .0;

    #[cfg(test)]
    aes_ctr_clear_set();
    #[cfg(test)]
    aes_mitccr_clear_set();

    Ok(table)
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
/// This table is structured as a collection of smaller modular tables.
pub struct Table {
    // Check that the input is well-formed
    input_validity: input_validity::Table,
    // [x]G
    x_G: scalar_mul::fixed::Table<g1::Config, KAPPA_B>,
    // Maps input MAC of (A.x, A.y) to iterated MAC of A projective coordinates
    a_ec_mac: field_mac_to_ec_mac::Table<g1::Config, KAPPA_A>,
    // Maps input MAC of (B.x, B.y) to iterated MAC of B projective coordinates
    b_ec_mac: field_mac_to_ec_mac::Table<g2::Config, KAPPA_B>,
    // Maps input MAC of (C.x, C.y) to iterated MAC of C projective coordinates
    c_ec_mac: field_mac_to_ec_mac::Table<g1::Config, KAPPA_B>,
    // e(A,B)
    pairing: pairing::Table,
    // Leaks secret if evaluated on an input != 1 and its MAC
    pub conditional_reveal: conditional_reveal::Table<KAPPA_B>,
    // Groth16 verifier key
    verifier_key: VerifierKey,
    // Global ID of this instance
    gid: GID,
}

impl Circuit<Input, InputMac, Output, IdentityMac<Output>> for Table {
    type Aux = (Fq, GID, VerifierKey);

    fn garble(
        parent_nonce: &mut Nonce,
        rng: &mut StdRng,
        aux: Option<Self::Aux>,
        input_mac_key: &InputMacKey,
    ) -> Result<(Self, <IdentityMac<Output> as Mac<Output>>::Key), GarbleError> {
        // The secret that will be conditionally revealed, and the Groth16 verifier key
        let (secret, gid, verifier_key) = aux
            .ok_or_else(|| GarbleError::AuxError(type_name::<Self::Aux>(), type_name::<Self>()))?;

        // Sample `KAPPA_B` random `r`s
        let mut rs = Box::new([Fr::ZERO; KAPPA_B]);
        for r in rs.iter_mut() {
            *r = Fr::rand(rng);
        }

        // Sample x uniformly at random
        let x = Fr::rand(rng);
        let a_ec_mac_key = a_ec_mac_key(rng, x);
        let (b_ddh_mac_key, b_ec_mac_key) = b_mac_key(rng, x, *rs);

        // Garbling table for the pairing e(A, B). It uses a_ec_mac_key,
        // b_ec_mac_key as input MAC keys, and pairing_output_mac_key as the output
        // MAC key.
        let (pairing, pairing_output_mac_key) =
            pairing::Table::garble(*rs, &(a_ec_mac_key.clone(), b_ddh_mac_key))?;

        let enc_s = {
            let hash_packed_phis = conditional_reveal::Table::<KAPPA_B>::hash_packed_phis(
                pairing_output_mac_key.iter().map(|key| key.phi.clone()),
            );
            hash_packed_phis + secret
        };

        // Construct c_ec_mac_key to use the same `phi`s as pairing_output_mac_key.
        // c_ec_mac_key is used as the output key for field_to_ec_mac of `C`
        let mut c_ec_mac_key = Vec::with_capacity(KAPPA_B);
        pairing_output_mac_key.iter().for_each(|key| {
            c_ec_mac_key.push(EndoMacKeyG1::random_from_phi(rng, &key.phi.clone().into()))
        });
        // This unwrap cannot fail because `pairing_output_mac_key` is a fixed
        // array of `[EndoMacFq12Key; KAPPA_B]`.
        let c_ec_mac_key: [EndoMacKeyG1; KAPPA_B] =
            c_ec_mac_key.try_into().unwrap_or_else(|_| panic!());

        // Raw range and curve checks must use the first nonces so evaluation
        // can reject malformed inputs before point conversion or scalar mul.
        let input_validity = {
            let aux = input_validity::Aux {
                secret,
                gid,
                b_ec_mac_key: Box::new(b_ec_mac_key.clone()),
            };
            input_validity::Table::garble(parent_nonce, rng, &aux, input_mac_key)?
        };

        // Garbling table for field_to_ec_mac of `A`
        let a_ec_mac = field_mac_to_ec_mac::Table::garble(
            parent_nonce,
            rng,
            // The a_ec_mac_key that we sampled earlier
            Some((true, a_ec_mac_key.clone())),
            // Input MAC key for the (x, y) coordinates of `A`
            &input_mac_key.A,
        )?
        .0;

        // Garbling table for field_to_ec_mac of `B`
        let b_ec_mac = field_mac_to_ec_mac::Table::garble(
            parent_nonce,
            rng,
            // The b_ec_mac_key that we sampled earlier
            Some((false, b_ec_mac_key.clone())),
            // Input MAC key for the (x, y) coordinates of `B`
            &input_mac_key.B,
        )?
        .0;

        // Garbling table for field_to_ec_mac of `C`
        let c_ec_mac = field_mac_to_ec_mac::Table::garble(
            parent_nonce,
            rng,
            // The c_ec_mac_key that we sampled earlier
            Some((false, c_ec_mac_key.clone())),
            // Input MAC key for the (x, y) coordinates of `C`
            &input_mac_key.C,
        )?
        .0;

        let (x_G, x_G_output_mac_key) = {
            let input_mac_key = &input_mac_key.x;

            let mut c_phis = vec![EndoScalar::default(); KAPPA_B];
            c_phis
                .iter_mut()
                .zip(pairing_output_mac_key.iter())
                .for_each(|(endoscalar, key)| {
                    *endoscalar = key.phi.clone().into();
                });
            // This unwrap cannot fail because `pairing_output_mac_key` is a
            // fixed array of length `KAPPA_B`.
            let c_phis = c_phis.try_into().unwrap_or_else(|_| panic!());

            scalar_mul::fixed::Table::garble(
                parent_nonce,
                rng,
                Some((verifier_key.G1, c_phis)),
                input_mac_key,
            )?
        };

        // Garbling table for the conditional revelation of `secret`.
        let conditional_reveal = {
            let input_mac_key = conditional_reveal::Table::groth16_input_mac_key(
                &verifier_key,
                &pairing_output_mac_key,
                &c_ec_mac_key,
                &x_G_output_mac_key,
            )?;

            conditional_reveal::Table::garble(enc_s, &input_mac_key)
        };

        Ok((
            Self {
                input_validity,
                x_G,
                a_ec_mac,
                b_ec_mac,
                c_ec_mac,
                pairing,
                conditional_reveal,
                verifier_key,
                gid,
            },
            IdentityMacKey,
        ))
    }

    fn evaluate(
        &self,
        parent_nonce: &mut Nonce,
        input: &Input,
        input_mac: &InputMac,
    ) -> Result<(Output, IdentityMac<Output>), EvalError> {
        // The Groth16 input (A, B, C).
        let Input { A, B, C, x } = *input;
        let VerifierKey { H1, H2, .. } = self.verifier_key;

        if let Some(secret) =
            self.input_validity
                .evaluate_coordinates(parent_nonce, input, input_mac)?
        {
            return Ok((secret, IdentityMac(PhantomData)));
        }

        // Evaluate the field_to_ec_mac table for `A`.
        let a_ec_mac = self.a_ec_mac.evaluate(parent_nonce, &A, &input_mac.A)?.1;

        // Evaluate the field_to_ec_mac table for `B`.
        let b_ec_mac = self.b_ec_mac.evaluate(parent_nonce, &B, &input_mac.B)?.1;

        if let Some(secret) =
            self.input_validity
                .evaluate_subgroup(parent_nonce, &B.into(), &b_ec_mac)?
        {
            return Ok((secret, IdentityMac(PhantomData)));
        }

        // Evaluate the field_to_ec_mac table for `C`.
        let c_ec_mac = self.c_ec_mac.evaluate(parent_nonce, &C, &input_mac.C)?.1;

        let x_G_mac = self.x_G.evaluate(parent_nonce, &x, &input_mac.x)?.1;

        // Compute the pairing e(A,B) e(C, H_1) on the input A, B, C
        let conditional_reveal_input = self.verifier_key.pairing(input);

        // Compute the pairing e(A,B) e(C, H_1) on the MACs of A, B, C
        let conditional_reveal_macs: Result<Vec<_>, EvalError> = {
            let to_ddh_mac = |ec_mac: &IteratedMac<Affine<g2::Config>, EndoMacG2, KAPPA_B>| {
                let mut macs = Vec::with_capacity(KAPPA_B);
                for (i, mac) in ec_mac.iter().enumerate() {
                    let mac = **mac
                        - R_MUL_COFACTOR_GENERATOR.mul_bigint(
                            BigInt::from(GENERATOR_EXPONENT)
                                .pow(i as u32)
                                .to_u64_digits()
                                .1,
                        );
                    macs.push(mac);
                }
                let macs = Projective::<g2::Config>::normalize_batch(&macs);
                DDHMac(macs.try_into().unwrap())
            };

            let b_ddh_macs = [to_ddh_mac(&b_ec_mac), to_ddh_mac(&-b_ec_mac)];
            let prepared_c_ec_macs = [c_ec_mac.clone(), -c_ec_mac.clone()];

            let mut results = Vec::with_capacity(4); // 2 * 2 = 4 combinations

            for b_ddh_mac in &b_ddh_macs {
                for c_ec_mac in &prepared_c_ec_macs {
                    let (_, AB_mac) = self.pairing.evaluate(
                        &(A.into(), B.into()),
                        &(a_ec_mac.clone(), b_ddh_mac.clone()),
                    )?;

                    let conditional_reveal_mac: [EndoMacFq12; KAPPA_B] =
                        std::array::from_fn(|idx| {
                            let AB = &AB_mac[idx];
                            let C = &c_ec_mac[idx];
                            let x_G = &x_G_mac[idx];
                            let pairing = Bn254::multi_pairing([**C, **x_G], [H1, H2]);
                            (pairing.0 * **AB).into()
                        });

                    results.push(conditional_reveal_mac.into());
                }
            }

            Ok(results)
        };

        // Evaluate the conditional reveal circuit.
        self.conditional_reveal
            .evaluate(&conditional_reveal_input, &conditional_reveal_macs?)
            .map(|result| (result, IdentityMac(PhantomData)))
    }
}

#[cfg(test)]
fn test_groth16(mut rng: &mut StdRng, input: &Input, vk: &VerifierKey, secret: Fq) -> Fq {
    let gid = GID::random(rng);

    let input_mac_key = InputMacKey::random_key(&mut rng);
    let table = Table::garble(
        &mut Nonce::new(),
        rng,
        Some((secret, gid, *vk)),
        &input_mac_key,
    )
    .unwrap()
    .0;
    aes_ctr_clear_set();
    aes_mitccr_clear_set();

    let input_mac = input_mac_key.encode(input);
    let output = table
        .evaluate(&mut Nonce::new(), input, &input_mac)
        .unwrap()
        .0;
    aes_ctr_clear_set();
    aes_mitccr_clear_set();

    output
}

#[test]
/// Evaluating the circuit on a valid SNARK and its MAC should return Fq::ZERO,
/// i.e. it should not reveal the `secret`.
fn test_valid_groth16() {
    use ark_ff::AdditiveGroup;
    use ark_ff::Field;

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    let secret = Fq::rand(&mut rng);

    let input = InputMac::random_input(&mut rng);
    let G1 = G1Affine::rand(&mut rng);
    let H1 = G2Affine::rand(&mut rng);
    let H2 = G2Affine::rand(&mut rng);

    // Construct `c` for the verifier key s.t. our chosen inputs are valid,
    // i.e. e(A,B) e(C, H_1) = c^{-1}
    let c = Bn254::multi_pairing(
        vec![input.A.into(), input.C.into(), (G1 * input.x).into_affine()],
        vec![input.B.into(), H1, H2],
    )
    .0
    .inverse()
    .unwrap();

    let verifier_key = VerifierKey { G1, H1, H2, c };
    let output = test_groth16(&mut rng, &input, &verifier_key, secret);

    // Assert that the circuit returns Fq::ZERO when evaluated on a valid input
    assert_eq!(output, Fq::ZERO);
}

#[test]
/// Evaluating the circuit on an invalid SNARK and its MAC should reveal the
/// `secret`.
fn test_invalid_groth16() {
    const SEED: u64 = 0;
    let mut rng = StdRng::seed_from_u64(SEED);

    let secret = Fq::rand(&mut rng);

    let input = InputMac::random_input(&mut rng);
    let verifier_key = VerifierKey {
        G1: G1Affine::rand(&mut rng),
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Bn254::pairing(G1Affine::rand(&mut rng), G2Affine::generator()).0,
    };

    let output = test_groth16(&mut rng, &input, &verifier_key, secret);

    assert_eq!(output, secret);
}

#[test]
/// Roundtrip serialisation and deserialisation of the table.
fn test_groth16_serde_roundtrip() {
    use crate::garble::Circuit;
    use crate::garble::Nonce;
    use crate::mac::MacKey;
    use ark_bn254::{G1Projective, G2Projective};
    use ark_ec::PrimeGroup;
    use ark_ff::UniformRand;
    use ark_std::rand::rngs::StdRng;
    use std::fs::File;
    use std::io::{BufReader, BufWriter, Write};

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);
    let secret = Fq::rand(&mut rng);

    let input = InputMac::random_input(&mut rng);
    let input_mac_key = InputMacKey::random_key(&mut rng);
    let gid = GID::random(&mut rng);

    let verifier_key = VerifierKey {
        G1: G1Affine::rand(&mut rng),
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Bn254::pairing(G1Projective::rand(&mut rng), G2Projective::generator()).0,
    };

    let original_table = garble_groth16(SEED, secret, verifier_key, &input_mac_key, gid).unwrap();

    let input_mac: InputMac = input_mac_key.encode(&input);

    let original_output = original_table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .0;
    aes_ctr_clear_set();
    aes_mitccr_clear_set();

    std::fs::create_dir_all("bin").expect("Could not create directory /bin");
    let file_name = "bin/groth16_table.bin";
    let file = File::create(file_name).expect("Could not create file");
    let mut writer = BufWriter::new(file);
    original_table.serialize_compressed(&mut writer).unwrap();
    writer.flush().unwrap();

    drop(original_table);

    let file = File::open(file_name).expect("Could not open file");
    let mut reader = BufReader::new(file);
    let deserialised_table = Table::deserialize_compressed(&mut reader).unwrap();
    let deserialised_output = deserialised_table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .0;
    aes_ctr_clear_set();
    aes_mitccr_clear_set();

    assert_eq!(original_output, deserialised_output);
}

#[test]
/// Malformed inputs must reveal the secret, and must be rejected before point
/// conversion or scalar multiplication.
fn test_malformed_groth16() {
    use crate::utils::group::get_curve_point_not_in_g2;

    let mut rng = StdRng::seed_from_u64(0);
    let secret = Fq::rand(&mut rng);

    let mut valid = Input::random(&mut rng);
    valid.x = Fr::ZERO;
    let mut verifier_key = VerifierKey {
        G1: G1Affine::rand(&mut rng),
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Fq12::ONE,
    };
    verifier_key.c = verifier_key.pairing(&valid).inverse().unwrap();

    let input_mac_key = InputMacKey::random_key(&mut rng);
    let gid = GID::random(&mut rng);
    let table = garble_groth16(0, secret, verifier_key, &input_mac_key, gid).unwrap();

    let mut inputs = [valid; 4];
    // x = r passes the pairing check, so only the range check reveals `secret`.
    inputs[0].x = Fr::new_unchecked(Fr::MODULUS);
    assert_eq!(verifier_key.pairing(&inputs[0]), Fq12::ONE);
    inputs[1].B.y.c1 = Fq::new_unchecked(Fq::MODULUS);
    inputs[2].C = bivariate::Input {
        x: Fq::ZERO,
        y: Fq::ZERO,
    };
    inputs[3].B = get_curve_point_not_in_g2(&mut rng).into();

    for input in inputs {
        let input_mac = input_mac_key.encode(&input);
        let output = table.evaluate(&mut Nonce::new(), &input, &input_mac);
        aes_ctr_clear_set();
        aes_mitccr_clear_set();
        assert_eq!(output.unwrap().0, secret);
    }
}
