//! The `field_to_ec_mac` on a G2 point produces `KAPPA_B` iterated MACs of the
//! form `m = phi * P + k`, where `k` is always in G2.
//!
//! This gadget leaks a secret if `P` is not in G2.
//!
//! If x is not in subgroup then r * m = y != 0, where `r` is group order
//! Solve dlog of y wrt z = r * P will return phi as long as gcd(h, 6) = 1,
//! where h is the cofactor

use std::any::type_name;
use std::marker::PhantomData;

use ark_bn254::{Fq, Fr, g2};
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::Projective;
use ark_ec::{CurveGroup, short_weierstrass::Affine};
use ark_ff::{AdditiveGroup, PrimeField};
use rand_core::CryptoRngCore;

use crate::garble::groth16_verifier::KAPPA_B;
use crate::garble::{Circuit, conditional_reveal};
use crate::mac::endo::{Endo, EndoScalar, IteratedEndoMacG2};
use crate::mac::{IdentityMac, IdentityMacKey};
use crate::utils::error::{EvalError, GarbleError};
use crate::utils::try_unwrap_single;

#[cfg(test)]
use crate::mac::endo::EndoMacKeyG2;

type Input = Affine<g2::Config>;
type InputMac = IteratedEndoMacG2<KAPPA_B>;

type Output = Fq;

pub(crate) struct Table {
    pub(crate) enc_s: Fq,
    pub(crate) r_ks: Box<[Affine<g2::Config>; KAPPA_B]>,
}

impl Circuit<Input, InputMac, Output, IdentityMac<Output>> for Table {
    type Aux = Fq;

    fn garble(
        _parent_nonce: &mut super::Nonce,
        _rng: &mut impl CryptoRngCore,
        aux: Option<Self::Aux>,
        input_mac_key: &<InputMac as crate::mac::Mac<Input>>::Key,
    ) -> Result<(Self, <IdentityMac<Output> as crate::mac::Mac<Output>>::Key), GarbleError> {
        let secret = aux
            .ok_or_else(|| GarbleError::AuxError(type_name::<Self::Aux>(), type_name::<Self>()))?;
        let enc_s = secret
            + conditional_reveal::Table::<KAPPA_B>::hash_packed_phis(
                input_mac_key.iter().map(|key| key.phi.clone()),
            );

        let mut r_ks = Vec::with_capacity(KAPPA_B);
        input_mac_key
            .iter()
            .for_each(|key| r_ks.push(key.k.mul_bigint(Fr::MODULUS)));
        let r_ks = Projective::<g2::Config>::normalize_batch(&r_ks);

        let table = Self {
            enc_s,
            // This unwrap cannot fail since `input_mac_key` is a fixed array
            // of size `KAPPA_B`.
            r_ks: r_ks.try_into().unwrap(),
        };

        Ok((table, IdentityMacKey))
    }

    fn evaluate(
        &self,
        _parent_nonce: &mut super::Nonce,
        input: &Input,
        input_mac: &InputMac,
    ) -> Result<(Output, IdentityMac<Output>), EvalError> {
        // For each possible value of `phi`, compute [r * phi] P
        let phis = EndoScalar::<g2::Config>::iter();
        let r_phi_P: Vec<_> = phis
            .iter()
            .map(|phi| phi.endo(input.mul_bigint(Fr::MODULUS).into_affine()))
            .collect();

        if r_phi_P.iter().all(|point| point.is_zero()) {
            return Ok((Fq::ZERO, IdentityMac(PhantomData)));
        }

        let mut recovered_phis = Vec::with_capacity(KAPPA_B);
        input_mac
            .iter()
            .zip(self.r_ks.iter())
            .for_each(|(mac, r_k)| {
                // m     =     phi * P +     k, where k is a curve point not necessarily in G2
                // r * m = r * phi * P + r * k
                let r_mac = mac.mul_bigint(Fr::MODULUS).into_affine();
                // r * phi * P
                let mac_minus_r_k = (r_mac - r_k).into_affine();
                let neg_mac_minus_r_k = (-r_mac - r_k).into_affine();

                let find_position =
                    |mac: Affine<g2::Config>| r_phi_P.iter().position(|&x| x == mac);

                // This could fail to decode in at most one position
                let phi = try_unwrap_single(
                    [mac_minus_r_k, neg_mac_minus_r_k]
                        .iter()
                        .map(|&mac| find_position(mac)),
                );
                recovered_phis.push(phi);
            });

        let phis = if recovered_phis.iter().all(Option::is_some) {
            recovered_phis
                .iter()
                // This unwrap cannot fail because each idx is Some(usize)
                .map(|&idx| phis[idx.unwrap()].clone())
                .collect()
        } else {
            EndoScalar::<g2::Config>::decode(&recovered_phis)?
        };

        // Recover the secret as the pow_6_lincomb of the phis.
        let s = self.enc_s - conditional_reveal::Table::<KAPPA_B>::hash_packed_phis(phis);

        Ok((s, IdentityMac(PhantomData)))
    }
}

#[test]
fn test_g2_subgroup_check() {
    use crate::{garble::Nonce, mac::MacKey, utils::group::get_curve_point_not_in_g2};
    use ark_std::{
        UniformRand,
        rand::{SeedableRng, rngs::StdRng},
    };

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);
    let secret = Fq::rand(&mut rng);

    let input = get_curve_point_not_in_g2(&mut rng);
    let input_mac_key = <[EndoMacKeyG2; KAPPA_B]>::random_key(&mut rng);
    let input_mac = input_mac_key.encode(&input);

    let table = Table::garble(&mut Nonce::new(), &mut rng, Some(secret), &input_mac_key)
        .unwrap()
        .0;

    let output = table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .0;

    assert_eq!(output, secret);
}

/// Our B_mac's are constructed as
///                           M = phi_i * B + K_i,
/// where K_i = G2::Affine::rand() + GENERATOR_EXPONENT^i * R_MUL_COFACTOR_GENERATOR
///          := G2::Affine::rand() + r_K
///
/// r K_i = r r_(K,i)
///
/// We want to pick a malicious B s.t.
///            r M  = phi (r B) + r r_K
///            -r M = psi (r B) + r r_K
/// for phi != psi.
///
/// phi (r B) + r r_K = -psi (r B) - r r_K
/// 2 r r_K = -(phi + psi) (r B)
/// (-2 / (phi + psi)) r_K = B
///
/// Let      B = -2 / (phi + psi) r_K,
///
/// r M  = phi r (-2 / (phi + psi)) r_K + r r_K
/// r M  = r (1 - 2 phi / (phi + psi)) r_K
///      = r (phi + psi - 2 phi) / (phi + psi) r_K
///      = r (psi - phi) / (phi + psi) r_K
#[test]
fn test_g2_subgroup_check_decoding_error() {
    use crate::garble::bilinear::pairing::GENERATOR_EXPONENT;
    use crate::utils::constants::R_MUL_COFACTOR_GENERATOR;
    use num_bigint::BigInt;

    use crate::{
        garble::Nonce,
        mac::{MacKey, endo::EndoMacKey},
    };
    use ark_ec::CurveConfig;
    use ark_std::{
        UniformRand,
        rand::{SeedableRng, rngs::StdRng},
    };

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);
    let secret = Fq::rand(&mut rng);

    let phis = EndoScalar::<g2::Config>::sample_endoscalars_with_checksum::<KAPPA_B>(&mut rng);

    let r_Ks: Vec<_> = (0..KAPPA_B)
        .map(|i| {
            R_MUL_COFACTOR_GENERATOR.mul_bigint(
                BigInt::from(GENERATOR_EXPONENT)
                    .pow(i as u32)
                    .to_u64_digits()
                    .1,
            )
        })
        .collect();

    let input = {
        // For a phi = 1, pick psi = omega^2
        let phi = EndoScalar::<g2::Config>::Zero(PhantomData);
        let psi = EndoScalar::<g2::Config>::Two(PhantomData); // omega^2

        let pos = phis
            .iter()
            .position(|x| matches!(x, EndoScalar::Zero(_)))
            .unwrap();

        let r_K = r_Ks[pos].into_affine();

        // Multiplicative inverse of `r` in the cofactor group
        let r_inv = BigInt::new(
            num_bigint::Sign::Plus,
            vec![
                4253048345, 1882119487, 4128629490, 1713099679, 2683052162, 2185606924, 1889062932,
                405940025,
            ],
        );

        {
            let g2_cofactor = ark_ff::BigInt::<4>::new(g2::Config::COFACTOR.try_into().unwrap());
            assert_eq!(
                (r_inv.clone() * BigInt::from(Fr::MODULUS)) % BigInt::from(g2_cofactor),
                BigInt::from(1)
            );
        }

        // Pick a psi != phi, and let
        // Let phi = 1, psi = omega^2 => phi + psi = -omega
        // -2 / -omega = 2 omega^2

        // Let B = -2 / (phi + psi) r_K
        //       = (-2 / -omega) r_K
        //       = (2 omega^2) r_K
        //       = 2 psi(r_K)
        let B = psi
            .endo(r_K)
            .mul_bigint(ark_ff::BigInt::<1>::from(2u8))
            .into_affine();

        {
            // B = 2 omega^2 r_K
            // B = (-2 / -omega) r_K
            // Check that phi(B) + psi(B) == -2 r_K
            assert_eq!(
                phi.endo(B) + psi.endo(B),
                -r_K.mul_bigint(ark_ff::BigInt::<1>::from(2u8))
            );

            // phi(P) + psi(P) = chi(P) as curve points
            let chi = EndoScalar::<g2::Config>::One(PhantomData); // -omega
            assert_eq!(phi.endo(B) + psi.endo(B), chi.endo(B));
        }

        B
    };

    let input_mac_key: [EndoMacKeyG2; KAPPA_B] = phis
        .into_iter()
        .zip(r_Ks.iter())
        .map(|(phi, r_K)| {
            let k = Affine::<g2::Config>::rand(&mut rng) + r_K;
            EndoMacKey {
                phi,
                k: k.into_affine(),
                k_scalar: None,
            }
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap_or_else(|_| panic!());

    let input_mac = input_mac_key.encode(&input);

    let table = Table::garble(&mut Nonce::new(), &mut rng, Some(secret), &input_mac_key)
        .unwrap()
        .0;

    let output = table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .0;

    assert_eq!(output, secret);
}
