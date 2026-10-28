//! Since the endoscalar assumes existence of sixth roots of unity, this works
//! only for curves with j-invariant = 0.
//!
//! Here, we fix the implementation to be for Bn254.

use std::{marker::PhantomData, ops::Neg};

use ark_bn254::{Bn254, Fq, Fq12, Fr, g1, g2};
use ark_ec::{
    AdditiveGroup, AffineRepr, CurveGroup, PrimeGroup,
    pairing::Pairing,
    scalar_mul::glv::GLVConfig,
    short_weierstrass::{Affine, Projective},
};
use ark_ff::{BigInt, Field, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;
use derive_more::Deref;
use rand_core::CryptoRngCore;

use crate::{
    garble::{bivariate::Poly, groth16_verifier::KAPPA_B},
    mac::{IteratedMac, Mac, MacKey, Random, RandomFromPhi},
    utils::{
        bits::pow_n_lincomb,
        constants::{G1_P_SQ_MOD_R, G2_P_SQ_MOD_R},
        error::EvalError,
        group::get_curve_point_not_in_g2,
    },
};

pub(crate) const ENDO_SIZE: usize = 7;

#[derive(Clone, Copy)]
pub enum EndoScalar<G> {
    Zero(PhantomData<G>),
    One(PhantomData<G>),
    Two(PhantomData<G>),
    Three(PhantomData<G>),
    Four(PhantomData<G>),
    Five(PhantomData<G>),
    NegInf(PhantomData<G>),
}

impl<G> Default for EndoScalar<G> {
    fn default() -> Self {
        Self::Zero(PhantomData)
    }
}

impl<G: GLVConfig> Random for EndoScalar<G> {
    fn random(rng: &mut impl CryptoRngCore) -> EndoScalar<G> {
        let exp = rng.gen_range(0..ENDO_SIZE);
        Self::from_u8(exp as u8)
    }
}

impl<G> PartialEq for EndoScalar<G> {
    fn eq(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (Self::Zero(_), Self::Zero(_))
                | (Self::One(_), Self::One(_))
                | (Self::Two(_), Self::Two(_))
                | (Self::Three(_), Self::Three(_))
                | (Self::Four(_), Self::Four(_))
                | (Self::Five(_), Self::Five(_))
                | (Self::NegInf(_), Self::NegInf(_))
        )
    }
}

impl<G> Eq for EndoScalar<G> {}

impl From<EndoScalar<g2::Config>> for EndoScalar<g1::Config> {
    fn from(value: EndoScalar<g2::Config>) -> Self {
        match value {
            EndoScalar::Zero(_) => EndoScalar::Zero(PhantomData),
            EndoScalar::One(_) => EndoScalar::One(PhantomData),
            EndoScalar::Two(_) => EndoScalar::Two(PhantomData),
            EndoScalar::Three(_) => EndoScalar::Three(PhantomData),
            EndoScalar::Four(_) => EndoScalar::Four(PhantomData),
            EndoScalar::Five(_) => EndoScalar::Five(PhantomData),
            EndoScalar::NegInf(_) => EndoScalar::NegInf(PhantomData),
        }
    }
}

impl From<EndoScalar<g1::Config>> for EndoScalar<g2::Config> {
    fn from(value: EndoScalar<g1::Config>) -> Self {
        match value {
            EndoScalar::Zero(_) => EndoScalar::Zero(PhantomData),
            EndoScalar::One(_) => EndoScalar::One(PhantomData),
            EndoScalar::Two(_) => EndoScalar::Two(PhantomData),
            EndoScalar::Three(_) => EndoScalar::Three(PhantomData),
            EndoScalar::Four(_) => EndoScalar::Four(PhantomData),
            EndoScalar::Five(_) => EndoScalar::Five(PhantomData),
            EndoScalar::NegInf(_) => EndoScalar::NegInf(PhantomData),
        }
    }
}

pub trait PSqModR: GLVConfig {
    fn p_sq_mod_r() -> Self::ScalarField;
}

impl PSqModR for g1::Config {
    fn p_sq_mod_r() -> Self::ScalarField {
        *G1_P_SQ_MOD_R
    }
}

impl PSqModR for g2::Config {
    fn p_sq_mod_r() -> Self::ScalarField {
        *G2_P_SQ_MOD_R
    }
}

pub(crate) trait Endo<G, Gt> {
    fn endo(&self, value: Gt) -> Gt;
}

impl<G> Endo<Affine<G>, Affine<G>> for EndoScalar<G>
where
    G: GLVConfig + PSqModR,
{
    fn endo(&self, point: Affine<G>) -> Affine<G> {
        match self {
            Self::NegInf(_) => Affine::identity(),
            _ if point.is_zero() => point,
            _ => {
                let phi = Self::omega_base().pow([self.as_u8() as u64]);
                let (a, b) = {
                    let phi_sq = phi.square();
                    // (phi^4, phi^3)
                    (phi_sq.square(), phi_sq * phi)
                };

                Affine::new_unchecked(a * point.x, b * point.y)
            }
        }
    }
}

impl Endo<Affine<g2::Config>, Fq12> for EndoScalar<g2::Config> {
    fn endo(&self, value: Fq12) -> Fq12 {
        match self {
            EndoScalar::NegInf(_) => Fq12::ONE,
            _ => value.frobenius_map(2 * self.as_u8() as usize),
        }
    }
}

impl<G: GLVConfig> EndoScalar<G>
where
    G: PSqModR,
{
    #[inline]
    pub(crate) fn two_minus_omega() -> G::ScalarField {
        let two = G::ScalarField::ONE + G::ScalarField::ONE;
        let neg_omega = EndoScalar::One(PhantomData::<G>).as_scalar();
        two + neg_omega
    }

    #[inline]
    fn omega_scalar() -> G::ScalarField {
        // We need multiplication by this scalar to equal Frobenius squared
        // The same LAMBDA does not correspond to the same ENDO_COEFFS in G1
        // and G2
        // So, if you fix ENDO_COEFFS you get different LAMBDA (as BN254 does)
        // This reverses that and has the effect of fixing the endomorphism to
        // be multiplication by p^2.
        if -G::LAMBDA == G::p_sq_mod_r() {
            -G::LAMBDA
        } else {
            -(G::LAMBDA.square())
        }
    }

    #[inline]
    pub(crate) fn omega_base() -> G::BaseField {
        if -G::LAMBDA == G::p_sq_mod_r() {
            -G::ENDO_COEFFS[0]
        } else {
            -(G::ENDO_COEFFS[0].square())
        }
    }

    pub(crate) fn as_scalar(&self) -> G::ScalarField {
        match self {
            // When self = NEGINF, return ZERO
            EndoScalar::NegInf(_) => G::ScalarField::ZERO,
            _ => {
                let exp = self.as_u8() as u64;
                Self::omega_scalar().pow([exp])
            }
        }
    }

    /// Takes a quadratic polynomial from the function field of an elliptic
    /// curve:
    ///                        f : E/F -> F, f(X, Y)
    /// in coefficient form in the following monomial order
    ///                        [1, X, Y, X^2, XY, Y^2]
    /// and composes an endomorphism with it
    pub(crate) fn endo_biquadratic_poly(&self, poly: Poly<G::BaseField>) -> Poly<G::BaseField> {
        match self {
            Self::NegInf(_) => {
                let mut coeffs: [Option<G::BaseField>; 6] = poly.to_biquadratic_coeffs();
                coeffs.iter_mut().for_each(|coeff| {
                    if coeff.is_some() {
                        *coeff = Some(G::BaseField::ZERO);
                    }
                });

                coeffs[0] = Some(poly.leading_coeff());
                Poly::biquadratic(coeffs)
            }
            _ => {
                let (a, b) = {
                    let phi = Self::omega_base().pow([self.as_u8() as u64]);

                    let phi_sq = phi.square();
                    (phi_sq.square(), phi_sq * phi)
                };

                // [1, a, b, a^2, a b, b^2]
                let mut coeffs = [None; 6];
                let scalars = [G::BaseField::ONE, a, b, a.square(), a * b, b.square()];
                coeffs
                    .iter_mut()
                    .zip(scalars.iter())
                    .zip(poly.iter())
                    .for_each(|((coeff, scalar), poly)| *coeff = Some(*scalar * poly.1));

                Poly::biquadratic(coeffs)
            }
        }
    }
}

impl<G: GLVConfig> EndoScalar<G> {
    pub(crate) fn iter() -> Vec<Self> {
        vec![
            EndoScalar::Zero(PhantomData),
            EndoScalar::One(PhantomData),
            EndoScalar::Two(PhantomData),
            EndoScalar::Three(PhantomData),
            EndoScalar::Four(PhantomData),
            EndoScalar::Five(PhantomData),
            EndoScalar::NegInf(PhantomData),
        ]
    }

    fn from_u8(value: u8) -> Self {
        match value {
            0 => Self::Zero(PhantomData),
            1 => Self::One(PhantomData),
            2 => Self::Two(PhantomData),
            3 => Self::Three(PhantomData),
            4 => Self::Four(PhantomData),
            5 => Self::Five(PhantomData),
            6 => Self::NegInf(PhantomData),
            _ => panic!(),
        }
    }

    fn as_u8(&self) -> u8 {
        match self {
            EndoScalar::Zero(_) => 0,
            EndoScalar::One(_) => 1,
            EndoScalar::Two(_) => 2,
            EndoScalar::Three(_) => 3,
            EndoScalar::Four(_) => 4,
            EndoScalar::Five(_) => 5,
            EndoScalar::NegInf(_) => 6,
        }
    }

    pub(crate) fn pack<I>(endoscalars: I) -> Fq
    where
        I: IntoIterator<Item = Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        pow_n_lincomb::<_, Fq, Fq>(
            endoscalars.into_iter().map(|phi| Fq::from(phi.as_u8())),
            Fq::from(BigInt::from(ENDO_SIZE as u8)),
        )
    }

    fn mod_sum(endoscalars: &[Self]) -> Self {
        let sum = endoscalars
            .iter()
            .map(|phi| phi.as_u8() as usize)
            .sum::<usize>();
        Self::from_u8((sum % ENDO_SIZE) as u8)
    }
}

impl<G> EndoScalar<G>
where
    G: GLVConfig + Clone,
{
    fn neg(&self) -> Self {
        let modulus = ENDO_SIZE as u8;
        Self::from_u8((modulus - self.as_u8()) % modulus)
    }

    fn checksum(endoscalars: &[Self]) -> Self {
        Self::neg(&Self::mod_sum(endoscalars))
    }

    pub(crate) fn sample_endoscalars_with_checksum<const N: usize>(
        rng: &mut impl CryptoRngCore,
    ) -> Vec<Self> {
        let mut res = vec![Self::Zero(PhantomData); N];
        res.iter_mut()
            .take(N - 1)
            .for_each(|res| *res = Self::random(rng));
        res[N - 1] = Self::checksum(&res);

        res
    }

    /// Recover a single missing endoscalar from a checksummed array.
    pub(crate) fn decode(endoscalars: &[Option<usize>]) -> Result<Vec<Self>, EvalError> {
        let mut result = vec![Self::Zero(PhantomData); KAPPA_B];

        let mut missing_idx = vec![];
        endoscalars.iter().enumerate().for_each(|(idx, phi)| {
            if let Some(phi) = phi {
                let phi = Self::from_u8(*phi as u8);
                result[idx] = phi;
            } else {
                missing_idx.push(idx);
            }
        });

        // The decoding can only fail in one idx
        if missing_idx.len() > 1 {
            return Err(EvalError::DecodingError);
        }

        result[missing_idx[0]] = Self::checksum(&result);

        Ok(result)
    }
}

#[derive(Clone, Copy, PartialEq, CanonicalSerialize, CanonicalDeserialize, Deref)]
pub struct EndoMac<G, Gt>
where
    G: GLVConfig,
    Gt: Sync + CanonicalSerialize + CanonicalDeserialize + Neg,
{
    #[deref]
    mac: Gt,
    _marker: PhantomData<G>,
}

impl<G, Gt> Neg for EndoMac<G, Gt>
where
    G: GLVConfig,
    Gt: Sync + CanonicalSerialize + CanonicalDeserialize + Neg<Output = Gt>,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            mac: -self.mac,
            _marker: PhantomData,
        }
    }
}

impl<G, Gt> From<Gt> for EndoMac<G, Gt>
where
    G: GLVConfig,
    Gt: Sync + CanonicalSerialize + CanonicalDeserialize + Neg,
{
    fn from(mac: Gt) -> Self {
        Self {
            mac,
            _marker: PhantomData,
        }
    }
}

pub(crate) type IteratedEndoMac<G, Gt, const N: usize> = IteratedMac<Gt, EndoMac<G, Gt>, N>;

#[derive(Clone, Copy)]
pub struct EndoMacKey<G: GLVConfig, Gt> {
    pub(crate) phi: EndoScalar<G>,
    pub(crate) k_scalar: Option<G::ScalarField>,
    pub(crate) k: Gt,
}

pub(crate) type EndoMacG1 = EndoMac<g1::Config, Affine<g1::Config>>;
pub(crate) type EndoMacKeyG1 = EndoMacKey<g1::Config, Affine<g1::Config>>;
pub(crate) type IteratedEndoMacG1<const N: usize> =
    IteratedEndoMac<g1::Config, Affine<g1::Config>, N>;

pub(crate) type EndoMacG2 = EndoMac<g2::Config, Affine<g2::Config>>;
pub(crate) type EndoMacKeyG2 = EndoMacKey<g2::Config, Affine<g2::Config>>;
pub(crate) type IteratedEndoMacG2<const N: usize> =
    IteratedEndoMac<g2::Config, Affine<g2::Config>, N>;

pub(crate) type EndoMacFq12 = EndoMac<g2::Config, Fq12>;
pub(crate) type EndoMacKeyFq12 = EndoMacKey<g2::Config, Fq12>;
pub(crate) type IteratedEndoMacFq12<const N: usize> = IteratedEndoMac<g2::Config, Fq12, N>;

impl<G> Mac<Affine<G>> for EndoMac<G, Affine<G>>
where
    G: GLVConfig + Clone,
    EndoMacKey<G, Affine<G>>: RandomFromPhi<Affine<G>, Self>,
{
    type Key = EndoMacKey<G, Affine<G>>;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> Affine<G> {
        use ark_std::rand::{distributions::Standard, prelude::Distribution as _};

        Standard.sample(rng)
    }
}

impl RandomFromPhi<Affine<g1::Config>, EndoMacG1> for EndoMacKeyG1 {
    type Phi = EndoScalar<g1::Config>;

    fn random_from_phi(rng: &mut impl CryptoRngCore, phi: &EndoScalar<g1::Config>) -> Self {
        let k_scalar = Fr::rand(rng);
        let k = (Projective::<g1::Config>::generator() * k_scalar).into_affine();

        Self {
            phi: phi.clone(),
            k_scalar: Some(k_scalar),
            k,
        }
    }
}

impl RandomFromPhi<Affine<g2::Config>, EndoMacG2> for EndoMacKeyG2 {
    type Phi = EndoScalar<g2::Config>;

    fn random_from_phi(rng: &mut impl CryptoRngCore, phi: &EndoScalar<g2::Config>) -> Self {
        let k = get_curve_point_not_in_g2(rng);

        Self {
            phi: phi.clone(),
            k_scalar: None,
            k,
        }
    }
}

impl RandomFromPhi<Fq12, EndoMacFq12> for EndoMacKeyFq12 {
    type Phi = EndoScalar<g2::Config>;

    fn random_from_phi(rng: &mut impl CryptoRngCore, phi: &EndoScalar<g2::Config>) -> Self {
        Self {
            phi: phi.clone(),
            k_scalar: None,
            k: Bn254::pairing(
                Affine::<g1::Config>::rand(rng),
                Affine::<g2::Config>::rand(rng),
            )
            .0,
        }
    }
}

impl<G> MacKey<Affine<G>, EndoMac<G, Affine<G>>> for EndoMacKey<G, Affine<G>>
where
    G: GLVConfig + Clone,
    G: PSqModR,
    Self: RandomFromPhi<Affine<G>, EndoMac<G, Affine<G>>, Phi = EndoScalar<G>>,
{
    fn encode(&self, value: &Affine<G>) -> EndoMac<G, Affine<G>> {
        let phi_mul_value = self.phi.endo(*value);
        EndoMac {
            mac: (phi_mul_value + self.k).into_affine(),
            _marker: PhantomData,
        }
    }

    #[cfg(test)]
    fn decode(&self, _mac: &EndoMac<G, Affine<G>>) -> Affine<G> {
        unimplemented!()
    }

    fn random_key(rng: &mut impl CryptoRngCore) -> Self {
        let phi = EndoScalar::random(rng);
        Self::random_from_phi(rng, &phi)
    }
}

impl Mac<Fq12> for EndoMacFq12
where
    EndoMacKeyFq12: RandomFromPhi<Fq12, Self>,
{
    type Key = EndoMacKeyFq12;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> Fq12 {
        use ark_std::rand::{distributions::Standard, prelude::Distribution as _};

        Standard.sample(rng)
    }
}

impl MacKey<Fq12, EndoMacFq12> for EndoMacKeyFq12
where
    Self: RandomFromPhi<Fq12, EndoMacFq12, Phi = EndoScalar<g2::Config>>,
{
    fn encode(&self, value: &Fq12) -> EndoMacFq12 {
        let phi_mul_value = self.phi.endo(*value);
        EndoMac {
            mac: phi_mul_value * self.k,
            _marker: PhantomData,
        }
    }

    #[cfg(test)]
    fn decode(&self, _mac: &EndoMacFq12) -> Fq12 {
        unimplemented!()
    }

    fn random_key(rng: &mut impl CryptoRngCore) -> Self {
        let phi = EndoScalar::random(rng);
        Self::random_from_phi(rng, &phi)
    }
}

#[test]
fn test_endo() {
    use ark_bn254::g1::Config as G;
    use ark_ec::CurveConfig;
    use ark_ff::{BigInteger, PrimeField};

    {
        let endo = -(G::LAMBDA.square());

        let r = <G as CurveConfig>::ScalarField::MODULUS.to_bits_le();
        let r = <<G as CurveConfig>::BaseField as PrimeField>::BigInt::from_bits_le(&r);
        let r = <<G as CurveConfig>::BaseField as PrimeField>::from_bigint(r).unwrap();

        // This is p - r in Fp
        let neg_r = -r;
        let neg_r = neg_r.into_bigint().to_bits_le();
        let neg_r = <<G as CurveConfig>::ScalarField as PrimeField>::BigInt::from_bits_le(&neg_r);

        // This is p - r in Fr
        let neg_r = <<G as CurveConfig>::ScalarField as PrimeField>::from_bigint(neg_r);
        let p = neg_r.unwrap();
        let p_sq = p.square();

        assert_eq!(endo, p_sq);
    }
}

#[test]
fn test_gt_mac_commute() {
    use ark_bn254::g1::Config as G;
    use ark_bn254::{Bn254, G1Affine, G2Affine};
    use ark_ec::{AffineRepr, pairing::Pairing};
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    let point = G1Affine::rand(&mut rng);
    let g1_mac_key = EndoMacKey::<G, Affine<G>>::random_key(&mut rng);
    let g1_mac = g1_mac_key.encode(&point);

    let gt_point = Bn254::pairing(point, G2Affine::generator()).0;
    let gt_mac_key = EndoMacKeyFq12 {
        phi: g1_mac_key.phi.into(),
        k_scalar: None,
        k: Bn254::pairing(g1_mac_key.k, G2Affine::generator()).0,
    };
    let gt_mac = gt_mac_key.encode(&gt_point);

    assert_eq!(*gt_mac, Bn254::pairing(*g1_mac, G2Affine::generator()).0)
}

#[test]
/// Erasing any digit, including an erased 1 (whose recovery computes -6) and
/// sums that overflow u8, must recover the original checksummed array.
fn test_checksum_single_erasure() {
    type E = EndoScalar<g2::Config>;

    for digit in 0..ENDO_SIZE as u8 {
        let mut original = vec![E::from_u8(6); KAPPA_B - 1];
        original[0] = E::from_u8(digit);
        original.push(E::checksum(&original));

        for missing in 0..KAPPA_B {
            let mut erased: Vec<_> = original
                .iter()
                .map(|phi| Some(phi.as_u8() as usize))
                .collect();
            erased[missing] = None;
            assert!(
                E::decode(&erased).unwrap() == original,
                "digit {digit}, erased {missing}"
            );
        }
    }
}
