//! Garbling table for a Groth16 verifier that commits to a secret `s`.
//! This table reveals `s` if it is evaluated on:
//! - (A, B, C, x) that does not satisfy e(A, B) e(C, H_1) e([x], H_2) = c^{-1},
//!   where [x] = Σ x_l G1_l over the `N` garbled public inputs, and H_1, c are
//!   from the verifier key;
//! - (A, B, C) where any of the points is an invalid curve point;
//! - (A, B, C) where any of the (x, y) coordinates is larger than |Fq|;
//! - `x_l` where `x_l` is larger than |Fr|.
//!
//! Public inputs known at garbling time are folded into `c` instead, so with
//! `N = 0` the proof is (A, B, C) alone.

pub(crate) mod input_validity;

#[cfg(test)]
mod e2e_tests;
#[cfg(test)]
mod golden_tests;

use core::panic;

use ark_bn254::{Fq, Fq2, Fq12, Fr, G1Affine, G1Projective, G2Affine, g1, g2};
use ark_ec::{
    AffineRepr, CurveGroup,
    short_weierstrass::{Affine, Projective},
};
use ark_ff::{AdditiveGroup, CyclotomicMultSubgroup, Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use num_bigint::BigInt;
use rand_chacha::ChaCha20Rng;
use rand_core::{CryptoRngCore, SeedableRng};

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
        IteratedMac, Mac, MacKey, Random, RandomFromPhi,
        bit::bytes::{Bit16ByteMac, Bit16ByteMacKey},
        ddh::DDHMac,
        digit,
        endo::{EndoMacFq12, EndoMacG2, EndoMacKeyG1, EndoScalar},
    },
    utils::{
        aes_hash::aes_ctr::AesCacheScope,
        bits::ToBits,
        constants::R_MUL_COFACTOR_GENERATOR,
        error::{EvalError, GarbleError, InputError},
        group::checked_multi_pairing,
    },
};

#[cfg(feature = "groth16")]
use crate::utils::error::VerifierKeyError;
#[cfg(test)]
use crate::{
    garble::bit_adaptor::clear_set as bit_adaptor_clear_set,
    utils::aes_hash::{
        aes_ctr::clear_set as aes_ctr_clear_set, aes_mitccr::clear_set as aes_mitccr_clear_set,
    },
};
#[cfg(test)]
use ark_std::rand::rngs::StdRng;
#[cfg(any(test, feature = "groth16"))]
use {ark_bn254::Bn254, ark_ec::pairing::Pairing};

// KAPPA_B is 1 + log_7(2^128)
pub const KAPPA_B: usize = 46 + 1;
// KAPPA_A is ceil(log_7(r))
pub const KAPPA_A: usize = 92;

pub type GID = [u8; 16];

/// Groth16 verifier key with `N` garbled public inputs. Public inputs that are
/// fixed at garbling time are folded into `c` and need no labels.
#[derive(Debug, Clone, Copy, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey<const N: usize = 1> {
    pub G1: [G1Affine; N],
    pub H1: G2Affine,
    pub H2: G2Affine,
    pub c: Fq12,
}

/// How a Groth16 public input enters the garbled verifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PublicInput {
    /// Known at garbling time and folded into `c`.
    Constant(Fr),
    /// Part of the proof, with its own labels.
    Garbled,
}

impl<const N: usize> VerifierKey<N> {
    /// Builds the key from a Groth16 verifying key. `inputs` gives every public
    /// input in order; exactly `N` of them must be [`PublicInput::Garbled`].
    #[cfg(feature = "groth16")]
    pub fn from_groth16(
        vk: &ark_groth16::VerifyingKey<Bn254>,
        inputs: &[PublicInput],
    ) -> Result<Self, VerifierKeyError> {
        let (ic0, ics) = vk
            .gamma_abc_g1
            .split_first()
            .ok_or(VerifierKeyError::MissingConstantTerm)?;
        if inputs.len() != ics.len() {
            return Err(VerifierKeyError::PublicInputLength {
                expected: ics.len(),
                actual: inputs.len(),
            });
        }

        let mut l = ic0.into_group();
        let mut garbled = Vec::with_capacity(N);
        for (input, ic) in inputs.iter().zip(ics) {
            match input {
                PublicInput::Constant(x) => l += *ic * x,
                PublicInput::Garbled => garbled.push(*ic),
            }
        }
        let G1 =
            garbled
                .try_into()
                .map_err(|garbled: Vec<_>| VerifierKeyError::GarbledInputCount {
                    expected: N,
                    actual: garbled.len(),
                })?;

        // e(A, B) = e(alpha, beta) e(L, gamma) e(C, delta)
        let c = Bn254::multi_pairing([vk.alpha_g1, l.into_affine()], [vk.beta_g2, vk.gamma_g2])
            .0
            .inverse()
            .ok_or(VerifierKeyError::DegenerateKey)?;

        Ok(Self {
            G1,
            H1: -vk.delta_g2,
            H2: -vk.gamma_g2,
            c,
        })
    }

    /// Given the input (A, B, C, x), returns e(A, B) e(C, H_1) e([x], H_2) * c,
    /// where [x] = Σ x_l G1_l. Recall that if (A, B, C, x) is a valid Groth16
    /// proof, it should satisfy
    ///                 e(A, B) e(C, H_1) e([x], H_2) = c^{-1}.
    /// In other words, this method should return Fq12::ONE on a valid proof.
    fn pairing(&self, input: &Input<N>) -> Result<Fq12, EvalError> {
        let x_G1: G1Projective = self.G1.iter().zip(&input.x).map(|(G1, x)| *G1 * x).sum();
        let pairing = checked_multi_pairing(
            [input.A.into(), input.C.into(), x_G1.into_affine()],
            [input.B.into(), self.H1, self.H2],
        )?;
        Ok(pairing * self.c)
    }
}

/// Groth16 proof with `N` garbled public inputs.
#[derive(Debug, Clone, Copy)]
pub struct Input<const N: usize = 1> {
    pub A: bivariate::Input<Fq>,
    pub B: bivariate::Input<Fq2>,
    pub C: bivariate::Input<Fq>,
    pub x: [Fr; N],
}

impl<const N: usize> Input<N> {
    pub fn random(rng: &mut impl CryptoRngCore) -> Self {
        use ark_ff::UniformRand;

        Input {
            A: G1Affine::rand(rng).into(),
            B: G2Affine::rand(rng).into(),
            C: G1Affine::rand(rng).into(),
            x: std::array::from_fn(|_| Fr::rand(rng)),
        }
    }
}

/// Bits in each proof component: a coordinate in Fq or a public input in Fr.
pub const COMPONENT_BITS: usize = Fq::MODULUS_BIT_SIZE as usize;
const _: () = assert!(Fr::MODULUS_BIT_SIZE as usize == COMPONENT_BITS);

/// A, B and C have 8 base-field coordinates.
const POINT_COMPONENTS: usize = 8;

/// The clear proof as raw bits, in label order: A.x, A.y, B.x.c0, B.x.c1,
/// B.y.c0, B.y.c1, C.x, C.y, then each garbled public input, every component
/// least significant bit first. A component need not be below its modulus; one
/// that isn't reveals the secret.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputBits<const N: usize = 1>(Vec<bool>);

impl<const N: usize> InputBits<N> {
    pub const LEN: usize = (POINT_COMPONENTS + N) * COMPONENT_BITS;

    pub fn new(bits: Vec<bool>) -> Result<Self, InputError> {
        if bits.len() != Self::LEN {
            return Err(InputError::BitCount {
                expected: Self::LEN,
                actual: bits.len(),
            });
        }
        Ok(Self(bits))
    }

    pub fn bits(&self) -> &[bool] {
        &self.0
    }

    fn component(&self, index: usize) -> &[bool] {
        &self.0[index * COMPONENT_BITS..(index + 1) * COMPONENT_BITS]
    }
}

impl<const N: usize> From<&Input<N>> for InputBits<N> {
    fn from(input: &Input<N>) -> Self {
        let Input { A, B, C, x } = input;
        let mut bits = Vec::with_capacity(Self::LEN);
        for component in [A.x, A.y, B.x.c0, B.x.c1, B.y.c0, B.y.c1, C.x, C.y] {
            bits.extend(component.to_bits());
        }
        for x in x {
            bits.extend(x.to_bits());
        }
        Self(bits)
    }
}

/// Input MAC key from the Groth16 proof.
#[derive(Clone)]
pub struct InputMacKey<const N: usize = 1> {
    A: bivariate::InputMacKey<Fq>,
    B: bivariate::InputMacKey<Fq2>,
    C: bivariate::InputMacKey<Fq>,
    x: [digit::bytes::DigitMacKey<Fr>; N],
}

/// Input MAC of the Groth16 proof.
#[derive(Debug, Clone, PartialEq)]
pub struct InputMac<const N: usize = 1> {
    A: bivariate::InputMac<Fq>,
    B: bivariate::InputMac<Fq2>,
    C: bivariate::InputMac<Fq>,
    x: [digit::bytes::DigitMac<Fr>; N],
}

/// A 16-byte label of one input bit.
pub type Label = [u8; 16];

impl<const N: usize> InputMacKey<N> {
    fn bit_keys(&self) -> impl Iterator<Item = &Bit16ByteMacKey> {
        let Self { A, B, C, x } = self;
        let keys: [&[Bit16ByteMacKey]; 6] = [&A.x, &A.y, &B.x, &B.y, &C.x, &C.y];
        keys.into_iter()
            .chain(x.iter().map(|key| &key[..]))
            .flatten()
    }

    /// The labels of 0 and of 1 for every input bit, in [`InputBits`] order.
    pub fn label_pairs(&self) -> Vec<[Label; 2]> {
        self.bit_keys()
            .map(|key| [*key.encode(&false), *key.encode(&true)])
            .collect()
    }

    /// The labels of `bits`, which need not spell canonical field elements.
    pub fn encode_bits(&self, bits: &InputBits<N>) -> InputMac<N> {
        InputMac::collect(
            self.bit_keys()
                .zip(bits.bits())
                .map(|(key, bit)| key.encode(bit)),
        )
    }
}

impl<const N: usize> InputMac<N> {
    /// Builds the input MAC from one label per bit, in [`InputBits`] order.
    pub fn from_labels(labels: &[Label]) -> Result<Self, InputError> {
        let expected = InputBits::<N>::LEN;
        if labels.len() != expected {
            return Err(InputError::LabelCount {
                expected,
                actual: labels.len(),
            });
        }

        Ok(Self::collect(
            labels.iter().map(|label| Bit16ByteMac::from(*label)),
        ))
    }

    /// Splits one MAC per bit, in [`InputBits`] order, into components.
    fn collect(mut labels: impl Iterator<Item = Bit16ByteMac>) -> Self {
        let mut take = |bits: usize| labels.by_ref().take(bits).collect::<Vec<_>>();
        let A = bivariate::InputMac {
            x: take(COMPONENT_BITS).into(),
            y: take(COMPONENT_BITS).into(),
        };
        let B = bivariate::InputMac {
            x: take(2 * COMPONENT_BITS).into(),
            y: take(2 * COMPONENT_BITS).into(),
        };
        let C = bivariate::InputMac {
            x: take(COMPONENT_BITS).into(),
            y: take(COMPONENT_BITS).into(),
        };
        let x = std::array::from_fn(|_| take(COMPONENT_BITS).into());
        Self { A, B, C, x }
    }
}

impl<const N: usize> MacKey<Input<N>, InputMac<N>> for InputMacKey<N> {
    fn encode(&self, value: &Input<N>) -> InputMac<N> {
        InputMac {
            A: self.A.encode(&value.A),
            B: self.B.encode(&value.B),
            C: self.C.encode(&value.C),
            x: std::array::from_fn(|l| self.x[l].encode(&value.x[l])),
        }
    }
    #[cfg(test)]
    fn decode(&self, mac: &InputMac<N>) -> Input<N> {
        Input {
            A: self.A.decode(&mac.A),
            B: self.B.decode(&mac.B),
            C: self.C.decode(&mac.C),
            x: std::array::from_fn(|l| self.x[l].decode(&mac.x[l])),
        }
    }
    fn random_key(rng: &mut impl CryptoRngCore) -> Self {
        Self {
            A: bivariate::InputMacKey::random_key(rng),
            B: bivariate::InputMacKey::random_key(rng),
            C: bivariate::InputMacKey::random_key(rng),
            x: std::array::from_fn(|_| digit::bytes::DigitMacKey::random_key(rng)),
        }
    }
}

impl<const N: usize> Mac<Input<N>> for InputMac<N> {
    type Key = InputMacKey<N>;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> Input<N> {
        Input::random(rng)
    }
}

/// The value that evaluating a table on an invalid proof reveals.
pub type Secret = Fq;

/// A garbled verifier with the garbler's secrets.
pub struct Garbling<const N: usize = 1> {
    pub table: Table<N>,
    /// Revealed by an invalid proof. Never zero.
    pub secret: Secret,
    /// The labels of every input bit, see [`InputMacKey::label_pairs`].
    pub input_mac_key: InputMacKey<N>,
}

/// Garbles a verifier for `verifier_key`. ChaCha20 seeded with `seed` derives,
/// in this order, the secret, the label keys, the gid and the table, so anyone
/// holding the seed and the key can rebuild the same bytes on any platform.
pub fn garble<const N: usize>(
    verifier_key: &VerifierKey<N>,
    seed: [u8; 32],
) -> Result<Garbling<N>, GarbleError> {
    let mut rng = ChaCha20Rng::from_seed(seed);
    let secret = loop {
        let secret = Fq::rand(&mut rng);
        if secret != Fq::ZERO {
            break secret;
        }
    };
    let input_mac_key = InputMacKey::random_key(&mut rng);
    let gid = GID::random(&mut rng);
    let table = Table::garble(&mut rng, secret, gid, verifier_key, &input_mac_key)?;

    #[cfg(test)]
    {
        aes_ctr_clear_set();
        aes_mitccr_clear_set();
        bit_adaptor_clear_set();
    }

    Ok(Garbling {
        table,
        secret,
        input_mac_key,
    })
}

/// Evaluates `table` against the evaluator's own `verifier_key` on the proof
/// bits and their labels. Returns the secret for an invalid proof, and `None`
/// for a valid proof or a table that fails to evaluate.
pub fn evaluate<const N: usize>(
    verifier_key: &VerifierKey<N>,
    table: &Table<N>,
    bits: &InputBits<N>,
    input_mac: &InputMac<N>,
) -> Option<Secret> {
    table
        .evaluate_bits(verifier_key, bits, input_mac)
        .ok()
        .flatten()
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
/// This table is structured as a collection of smaller modular tables.
pub struct Table<const N: usize = 1> {
    // Check that the input is well-formed
    input_validity: input_validity::Table<N>,
    // [x_l]G1_l for each garbled public input
    x_G: [scalar_mul::fixed::Table<g1::Config, KAPPA_B>; N],
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
    // Global ID of this instance
    gid: GID,
}

impl<const N: usize> Table<N> {
    fn garble(
        rng: &mut impl CryptoRngCore,
        secret: Secret,
        gid: GID,
        verifier_key: &VerifierKey<N>,
        input_mac_key: &InputMacKey<N>,
    ) -> Result<Self, GarbleError> {
        let _aes_cache = AesCacheScope::new();
        let parent_nonce = &mut Nonce::new();

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
            Some((true, a_ec_mac_key.clone(), secret)),
            // Input MAC key for the (x, y) coordinates of `A`
            &input_mac_key.A,
        )?
        .0;

        // Garbling table for field_to_ec_mac of `B`
        let b_ec_mac = field_mac_to_ec_mac::Table::garble(
            parent_nonce,
            rng,
            // The b_ec_mac_key that we sampled earlier
            Some((false, b_ec_mac_key.clone(), secret)),
            // Input MAC key for the (x, y) coordinates of `B`
            &input_mac_key.B,
        )?
        .0;

        // Garbling table for field_to_ec_mac of `C`
        let c_ec_mac = field_mac_to_ec_mac::Table::garble(
            parent_nonce,
            rng,
            // The c_ec_mac_key that we sampled earlier
            Some((false, c_ec_mac_key.clone(), secret)),
            // Input MAC key for the (x, y) coordinates of `C`
            &input_mac_key.C,
        )?
        .0;

        let (x_G, x_G_output_mac_keys) = {
            let mut c_phis = vec![EndoScalar::default(); KAPPA_B];
            c_phis
                .iter_mut()
                .zip(pairing_output_mac_key.iter())
                .for_each(|(endoscalar, key)| {
                    *endoscalar = key.phi.clone().into();
                });
            // This unwrap cannot fail because `pairing_output_mac_key` is a
            // fixed array of length `KAPPA_B`.
            let c_phis: [EndoScalar<g1::Config>; KAPPA_B] =
                c_phis.try_into().unwrap_or_else(|_| panic!());

            let mut tables = Vec::with_capacity(N);
            let mut keys = Vec::with_capacity(N);
            for (G1, input_mac_key) in verifier_key.G1.iter().zip(&input_mac_key.x) {
                let (table, key) = scalar_mul::fixed::Table::garble(
                    parent_nonce,
                    rng,
                    Some((*G1, c_phis.clone())),
                    input_mac_key,
                )?;
                tables.push(table);
                keys.push(key);
            }
            // These unwraps cannot fail because both vectors hold one entry
            // per garbled input.
            let tables: [_; N] = tables.try_into().unwrap_or_else(|_| panic!());
            let keys: [_; N] = keys.try_into().unwrap_or_else(|_| panic!());
            (tables, keys)
        };

        // Garbling table for the conditional revelation of `secret`.
        let conditional_reveal = {
            let input_mac_key = conditional_reveal::Table::groth16_input_mac_key(
                verifier_key,
                &pairing_output_mac_key,
                &c_ec_mac_key,
                &x_G_output_mac_keys,
            )?;

            conditional_reveal::Table::garble(enc_s, &input_mac_key)
        };

        Ok(Self {
            input_validity,
            x_G,
            a_ec_mac,
            b_ec_mac,
            c_ec_mac,
            pairing,
            conditional_reveal,
            gid,
        })
    }

    /// The global ID that domain-separates this table's hashes.
    pub fn gid(&self) -> GID {
        self.gid
    }

    /// Whether every part has the shape `garble` produces: the replica and bit
    /// counts, the Y tables, the polynomial monomials and the gids. Check this
    /// before accepting a table from a garbler; `evaluate_bits` checks it too.
    pub fn has_garbled_shape(&self) -> bool {
        self.input_validity.has_garbled_shape(&self.gid)
            && self.x_G.iter().all(|table| table.has_garbled_shape())
            && self.a_ec_mac.has_garbled_shape(true)
            && self.b_ec_mac.has_garbled_shape(false)
            && self.c_ec_mac.has_garbled_shape(false)
    }

    /// Evaluates against `verifier_key` on the raw proof bits and their
    /// labels. Returns the secret for an invalid proof and `None` for a valid
    /// one.
    pub fn evaluate_bits(
        &self,
        verifier_key: &VerifierKey<N>,
        bits: &InputBits<N>,
        input_mac: &InputMac<N>,
    ) -> Result<Option<Secret>, EvalError> {
        if !self.has_garbled_shape() {
            return Err(EvalError::MalformedTable);
        }
        let _aes_cache = AesCacheScope::new();
        let parent_nonce = &mut Nonce::new();

        let input = match self
            .input_validity
            .evaluate_coordinates(parent_nonce, bits, input_mac)?
        {
            Ok(input) => input,
            Err(secret) => return Ok(Some(secret)),
        };
        // The Groth16 input (A, B, C).
        let Input { A, B, C, x } = input;
        let VerifierKey { H1, H2, .. } = *verifier_key;

        // A point that hits a conversion's doubling case releases the secret.
        if let Some(secret) = self
            .a_ec_mac
            .reveal(&input_mac.A)
            .or_else(|| self.b_ec_mac.reveal(&input_mac.B))
            .or_else(|| self.c_ec_mac.reveal(&input_mac.C))
        {
            return Ok(Some(secret));
        }

        // Evaluate the field_to_ec_mac table for `A`.
        let a_ec_mac = self.a_ec_mac.evaluate(parent_nonce, &A, &input_mac.A)?.1;

        // Evaluate the field_to_ec_mac table for `B`.
        let b_ec_mac = self.b_ec_mac.evaluate(parent_nonce, &B, &input_mac.B)?.1;

        if let Some(secret) =
            self.input_validity
                .evaluate_subgroup(parent_nonce, &B.into(), &b_ec_mac)?
        {
            return Ok(Some(secret));
        }

        // Evaluate the field_to_ec_mac table for `C`.
        let c_ec_mac = self.c_ec_mac.evaluate(parent_nonce, &C, &input_mac.C)?.1;

        // Σ_l MAC([x_l]G1_l) for each replica. All x_G tables share the
        // pairing output's phis, so the sum is a MAC of [x] = Σ_l x_l G1_l.
        let x_G_mac = {
            let mut sums = vec![G1Projective::ZERO; KAPPA_B];
            for ((table, x), input_mac) in self.x_G.iter().zip(&x).zip(&input_mac.x) {
                let mac = table.evaluate(parent_nonce, x, input_mac)?.1;
                sums.iter_mut()
                    .zip(mac.iter())
                    .for_each(|(sum, mac)| *sum += **mac);
            }
            G1Projective::normalize_batch(&sums)
        };

        // Compute the pairing e(A,B) e(C, H_1) on the input A, B, C
        let conditional_reveal_input = verifier_key.pairing(&input)?;

        // Compute the pairing e(A,B) e(C, H_1) on the MACs of A, B, C
        let conditional_reveal_macs = {
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
                macs.try_into()
                    .map(DDHMac)
                    .map_err(|_| EvalError::MalformedTable)
            };

            let mut AB_macs = Vec::with_capacity(2);
            for b_ddh_mac in [to_ddh_mac(&b_ec_mac)?, to_ddh_mac(&-b_ec_mac)?] {
                AB_macs.push(
                    self.pairing
                        .evaluate(&(A.into(), B.into()), &(a_ec_mac.clone(), b_ddh_mac))?,
                );
            }

            // e(C, H1) e(x_G, H2) for +C and -C, using e(-C, H1) = e(C, H1)^-1.
            let mut c_terms = [Vec::with_capacity(KAPPA_B), Vec::with_capacity(KAPPA_B)];
            for (C, x_G) in c_ec_mac.iter().zip(&x_G_mac) {
                let C_term = checked_multi_pairing([**C], [H1])?;
                let x_G_term = if x_G.is_zero() {
                    Fq12::ONE
                } else {
                    checked_multi_pairing([*x_G], [H2])?
                };
                let C_term_inverse = C_term
                    .cyclotomic_inverse()
                    .ok_or(EvalError::DegeneratePairing)?;
                c_terms[0].push(C_term * x_G_term);
                c_terms[1].push(C_term_inverse * x_G_term);
            }

            let mut results = Vec::with_capacity(4); // 2 * 2 = 4 combinations
            for AB_mac in &AB_macs {
                for c_term in &c_terms {
                    let conditional_reveal_mac: [EndoMacFq12; KAPPA_B] =
                        std::array::from_fn(|i| EndoMacFq12::from(c_term[i] * *AB_mac[i]));
                    results.push(conditional_reveal_mac.into());
                }
            }

            results
        };

        // Evaluate the conditional reveal circuit.
        self.conditional_reveal
            .evaluate(&conditional_reveal_input, &conditional_reveal_macs)
    }
}

#[cfg(test)]
fn test_groth16(
    rng: &mut impl CryptoRngCore,
    input: &Input,
    vk: &VerifierKey,
    secret: Fq,
) -> Option<Secret> {
    let gid = GID::random(rng);

    let input_mac_key = InputMacKey::random_key(rng);
    let table = Table::garble(rng, secret, gid, vk, &input_mac_key).unwrap();
    aes_ctr_clear_set();
    aes_mitccr_clear_set();

    let input_mac = input_mac_key.encode(input);
    let output = table.evaluate_bits(vk, &input.into(), &input_mac).unwrap();
    aes_ctr_clear_set();
    aes_mitccr_clear_set();

    output
}

#[test]
/// Evaluating the circuit on a valid SNARK and its MAC should not reveal the
/// `secret`.
fn test_valid_groth16() {
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
        vec![
            input.A.into(),
            input.C.into(),
            (G1 * input.x[0]).into_affine(),
        ],
        vec![input.B.into(), H1, H2],
    )
    .0
    .inverse()
    .unwrap();

    let verifier_key = VerifierKey {
        G1: [G1],
        H1,
        H2,
        c,
    };
    let output = test_groth16(&mut rng, &input, &verifier_key, secret);

    assert_eq!(output, None);
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
        G1: [G1Affine::rand(&mut rng)],
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Bn254::pairing(G1Affine::rand(&mut rng), G2Affine::generator()).0,
    };

    let output = test_groth16(&mut rng, &input, &verifier_key, secret);

    assert_eq!(output, Some(secret));
}

#[test]
/// Roundtrip serialisation and deserialisation of the table.
fn test_groth16_serde_roundtrip() {
    use crate::mac::MacKey;
    use ark_bn254::{G1Projective, G2Projective};
    use ark_ec::PrimeGroup;
    use ark_ff::UniformRand;
    use ark_std::rand::rngs::StdRng;
    use std::fs::File;
    use std::io::{BufReader, BufWriter, Write};

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    let input = InputMac::random_input(&mut rng);
    let verifier_key = VerifierKey {
        G1: [G1Affine::rand(&mut rng)],
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Bn254::pairing(G1Projective::rand(&mut rng), G2Projective::generator()).0,
    };

    let Garbling {
        table: original_table,
        input_mac_key,
        ..
    } = garble(&verifier_key, [0; 32]).unwrap();

    let input_mac: InputMac = input_mac_key.encode(&input);
    let bits = InputBits::from(&input);

    let original_output = original_table
        .evaluate_bits(&verifier_key, &bits, &input_mac)
        .unwrap();
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
        .evaluate_bits(&verifier_key, &bits, &input_mac)
        .unwrap();
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

    let mut valid = Input::random(&mut rng);
    valid.x = [Fr::ZERO];
    let mut verifier_key = VerifierKey {
        G1: [G1Affine::rand(&mut rng)],
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Fq12::ONE,
    };
    verifier_key.c = verifier_key.pairing(&valid).unwrap().inverse().unwrap();

    let Garbling {
        table,
        secret,
        input_mac_key,
    } = garble(&verifier_key, [0; 32]).unwrap();

    let mut inputs = [valid; 4];
    // x = r passes the pairing check, so only the range check reveals `secret`.
    inputs[0].x = [Fr::new_unchecked(Fr::MODULUS)];
    assert_eq!(verifier_key.pairing(&inputs[0]).unwrap(), Fq12::ONE);
    inputs[1].B.y.c1 = Fq::new_unchecked(Fq::MODULUS);
    inputs[2].C = bivariate::Input {
        x: Fq::ZERO,
        y: Fq::ZERO,
    };
    inputs[3].B = get_curve_point_not_in_g2(&mut rng).into();

    for input in inputs {
        let input_mac = input_mac_key.encode(&input);
        let output = table.evaluate_bits(&verifier_key, &(&input).into(), &input_mac);
        aes_ctr_clear_set();
        aes_mitccr_clear_set();
        assert_eq!(output.unwrap(), Some(secret));
    }
}
