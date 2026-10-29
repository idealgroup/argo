//! Garbling tables for oblivious evaluation of bivariate polynomials

use std::{any::type_name, marker::PhantomData};

use ark_ec::{
    AffineRepr,
    short_weierstrass::{Affine, SWCurveConfig},
};
use ark_ff::{AdditiveGroup, Field};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand_core::CryptoRngCore;

use crate::{
    garble::{Circuit, digit_adaptor},
    mac::{IdentityMac, IdentityMacKey, Mac, MacKey, Random, digit::bytes},
    utils::{
        bits::{FromBits, NumBits, ToBits},
        error::{EvalError, GarbleError},
        group::FromLeBytesModOrder,
    },
};

#[cfg(test)]
use crate::{garble::Nonce, utils::aes_hash::aes_ctr::clear_set};
#[cfg(test)]
use ark_std::rand::{SeedableRng, rngs::StdRng};

/// Powers of a monomial where (i, j) represents x^i y^j.
#[derive(Debug, PartialEq, Eq, Clone, Copy, CanonicalDeserialize, CanonicalSerialize)]
pub(crate) struct Monomial(u8, u8);

impl Monomial {
    /// Weight of a monomial.
    #[inline]
    fn weight(&self) -> usize {
        // The diagonal
        let k = self.0 as usize + self.1 as usize;

        k * (k + 1) / 2 + self.1 as usize
    }

    #[inline]
    pub(crate) const fn new(x: u8, y: u8) -> Self {
        Self(x, y)
    }

    #[inline]
    pub(crate) const fn constant() -> Self {
        Self(0, 0)
    }
}

impl PartialOrd for Monomial {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Monomial {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.weight().cmp(&other.weight())
    }
}

/// true => x, false => y
type XY = bool;

/// The `(XY, Monomial)` of each digit adaptor table that `Table::garble`
/// emits, in order, for a polynomial with these monomials. Garbling reduces
/// each monomial by one degree in x (or else y), which can add lower ones.
fn table_monomials(monomials: &[Monomial]) -> Vec<(XY, Monomial)> {
    let len = monomials.iter().map(|m| m.weight() + 1).max().unwrap_or(0);
    let mut present = vec![None; len];
    for monomial in monomials {
        present[monomial.weight()] = Some(*monomial);
    }

    let mut tables = Vec::new();
    for idx in (0..len).rev() {
        let Some(Monomial(i, j)) = present[idx] else {
            continue;
        };
        let (xy, monomial) = match (i, j) {
            (0, 0) => continue,
            (0, j) => (false, Monomial(0, j - 1)),
            (i, j) => (true, Monomial(i - 1, j)),
        };
        present[monomial.weight()] = Some(monomial);
        tables.push((xy, monomial));
    }
    tables
}

/// Bivariate polynomial in coefficient form, mapping from monomial to
/// coefficient.
#[derive(Debug, Default, Clone)]
pub(crate) struct Poly<F>(Vec<(Option<Monomial>, F)>);

impl<F: Field> Poly<F> {
    #[inline]
    pub(crate) fn insert(&mut self, monomial: Monomial, coeff: F) {
        if self.0.len() < monomial.weight() + 1 {
            let padding = vec![(None, F::ZERO); monomial.weight() + 1 - self.0.len()];
            self.0.extend_from_slice(&padding);
        }
        self.0[monomial.weight()].0 = Some(monomial);
        self.0[monomial.weight()].1 += coeff;
    }

    #[inline]
    pub(crate) fn leading_coeff(&self) -> F {
        self.0
            .iter()
            .rev()
            .find(|(_, coeff)| *coeff != F::ZERO)
            .map(|(_, coeff)| coeff)
            .copied()
            .unwrap_or(F::ZERO)
    }

    #[inline]
    pub(crate) fn scale(&mut self, scalar: F) {
        self.0.iter_mut().for_each(|(_, coeff)| *coeff *= scalar);
    }

    fn eval(&self, x: F, y: F) -> F {
        self.0
            .iter()
            .map(|(monomial, coeff)| {
                monomial.map_or_else(
                    || F::ZERO,
                    |monomial| {
                        let xy_value = x.pow([monomial.0 as u64]) * y.pow([monomial.1 as u64]);
                        xy_value * coeff
                    },
                )
            })
            .sum::<F>()
    }

    pub(crate) fn biquadratic(coeffs: [Option<F>; 6]) -> Self {
        let mut poly: Poly<F> = Self::default();
        if let Some(coeff) = coeffs[0] {
            poly.insert(Monomial::constant(), coeff)
        }
        if let Some(coeff) = coeffs[1] {
            poly.insert(Monomial(1, 0), coeff)
        } // x
        if let Some(coeff) = coeffs[2] {
            poly.insert(Monomial(0, 1), coeff)
        } // y
        if let Some(coeff) = coeffs[3] {
            poly.insert(Monomial(2, 0), coeff)
        } // x^2
        if let Some(coeff) = coeffs[4] {
            poly.insert(Monomial(1, 1), coeff)
        } // xy
        if let Some(coeff) = coeffs[5] {
            poly.insert(Monomial(0, 2), coeff)
        } // y^2

        poly
    }

    pub(crate) fn to_biquadratic_coeffs(&self) -> [Option<F>; 6] {
        let mut coeffs = [None; 6];
        coeffs
            .iter_mut()
            .zip(self.0.iter())
            .for_each(|(coeff, poly)| {
                if poly.0.is_some() {
                    *coeff = Some(poly.1);
                }
            });

        coeffs
    }

    pub(crate) fn iter(&self) -> std::slice::Iter<'_, (Option<Monomial>, F)> {
        self.0.iter()
    }
}

/// Bivariate input (x, y)
#[derive(Debug, Clone, Copy)]
pub struct Input<F> {
    pub(crate) x: F,
    pub(crate) y: F,
}

impl<C> From<C> for Input<C::BaseField>
where
    C: AffineRepr,
    C::BaseField: Field,
{
    /// The identity has no affine coordinates and becomes (0, 0), which is on
    /// neither BN254 G1 nor its twist, so evaluation reveals the secret for it.
    fn from(value: C) -> Self {
        let (x, y) = value
            .xy()
            .unwrap_or((C::BaseField::ZERO, C::BaseField::ZERO));
        Self { x, y }
    }
}

impl<C> From<Input<C::BaseField>> for Affine<C>
where
    C: SWCurveConfig,
    C::BaseField: Field,
{
    fn from(val: Input<C::BaseField>) -> Self {
        Affine::new_unchecked(val.x, val.y)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InputMac<F> {
    pub(crate) x: bytes::DigitMac<F>,
    pub(crate) y: bytes::DigitMac<F>,
}

#[derive(Clone)]
pub struct InputMacKey<F> {
    pub(crate) x: bytes::DigitMacKey<F>,
    pub(crate) y: bytes::DigitMacKey<F>,
}

impl<F> MacKey<Input<F>, InputMac<F>> for InputMacKey<F>
where
    F: Field + NumBits + ToBits + FromBits<F, F> + Random,
{
    fn encode(&self, value: &Input<F>) -> InputMac<F> {
        InputMac {
            x: self.x.encode(&value.x),
            y: self.y.encode(&value.y),
        }
    }

    #[cfg(test)]
    fn decode(&self, mac: &InputMac<F>) -> Input<F> {
        Input {
            x: self.x.decode(&mac.x),
            y: self.y.decode(&mac.y),
        }
    }

    fn random_key(rng: &mut impl CryptoRngCore) -> Self {
        Self {
            x: bytes::DigitMacKey::random_key(rng),
            y: bytes::DigitMacKey::random_key(rng),
        }
    }
}

impl<F> Mac<Input<F>> for InputMac<F>
where
    F: Field + NumBits + ToBits + FromBits<F, F> + Random,
{
    type Key = InputMacKey<F>;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> Input<F> {
        Input {
            x: F::rand(rng),
            y: F::rand(rng),
        }
    }
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub(crate) struct Table<F>
where
    F: Field + NumBits + FromBits<bool, F> + Random,
    F::BasePrimeField: FromLeBytesModOrder,
{
    pub(crate) constant: F,
    pub(crate) tables: Vec<(XY, Monomial, digit_adaptor::Table<F>)>,
}

impl<F> Table<F>
where
    F: Field + NumBits + FromBits<bool, F> + Random,
    F::BasePrimeField: FromLeBytesModOrder,
{
    /// Whether this is the shape `garble` gives a polynomial with `monomials`.
    pub(crate) fn has_garbled_shape(&self, monomials: &[Monomial]) -> bool {
        let expected = table_monomials(monomials);
        self.tables.len() == expected.len()
            && self
                .tables
                .iter()
                .zip(expected)
                .all(|((xy, monomial, table), expected)| {
                    (*xy, *monomial) == expected && table.has_garbled_shape()
                })
    }
}

impl<F> Circuit<Input<F>, InputMac<F>, F, IdentityMac<F>> for Table<F>
where
    F: Field + NumBits + FromBits<bool, F> + Random + ToBits + FromBits<F, F>,
    F::BasePrimeField: FromLeBytesModOrder,
{
    type Aux = Poly<F>;

    fn garble(
        parent_nonce: &mut super::Nonce,
        rng: &mut impl CryptoRngCore,
        aux: Option<Self::Aux>,
        input_mac_key: &<InputMac<F> as Mac<Input<F>>>::Key,
    ) -> Result<(Self, <IdentityMac<F> as Mac<F>>::Key), GarbleError> {
        let mut nonce = parent_nonce.fork()?;

        let poly = aux
            .ok_or_else(|| GarbleError::AuxError(type_name::<Self::Aux>(), type_name::<Self>()))?;

        let mut constant = F::ZERO;
        let table_capacity = poly.0.iter().filter(|(m, _)| m.is_some()).count();
        let mut tables = Vec::with_capacity(table_capacity);

        let mut terms = poly.clone();
        for idx in (0..poly.0.len()).rev() {
            let (monomial, z) = terms.0[idx];
            let Some(Monomial(i, j)) = monomial else {
                continue;
            };

            if i == 0 && j == 0 {
                constant = z;
                continue;
            }

            let (xy, monomial, input_mac_key) = if i > 0 {
                (true, Monomial(i - 1, j), &input_mac_key.x)
            } else {
                (false, Monomial(i, j - 1), &input_mac_key.y)
            };

            let (table, output_mac_key) =
                digit_adaptor::Table::garble(&mut nonce, rng, Some(z), input_mac_key)?;

            let r = output_mac_key.from_bits_k()?;

            terms.insert(monomial, -r);

            tables.push((xy, monomial, table));
        }

        Ok((Self { constant, tables }, IdentityMacKey))
    }

    fn evaluate(
        &self,
        parent_nonce: &mut super::Nonce,
        input: &Input<F>,
        input_mac: &InputMac<F>,
    ) -> Result<(F, IdentityMac<F>), EvalError> {
        let mut nonce = parent_nonce.fork()?;

        let mut poly = Poly::default();
        for (xy, monomial, table) in self.tables.iter() {
            let (_, mac) = match xy {
                true => table.evaluate(&mut nonce, &input.x, &input_mac.x)?,
                false => table.evaluate(&mut nonce, &input.y, &input_mac.y)?,
            };

            let mac = mac.try_into_group_mac().map(|mac| *mac)?;

            poly.insert(*monomial, mac);
        }

        poly.insert(Monomial::constant(), self.constant);

        Ok((poly.eval(input.x, input.y), IdentityMac(PhantomData)))
    }
}

#[cfg(test)]
fn test_biquadratic<F>(coeffs: [Option<F>; 6], rng: &mut impl CryptoRngCore)
where
    F: Field + NumBits + FromBits<bool, F> + Random + ToBits + FromBits<F, F>,
    F::BasePrimeField: FromLeBytesModOrder,
{
    let poly = Poly::biquadratic(coeffs);

    let input_mac_key = InputMacKey::random_key(rng);

    let garbling_table = Table::garble(&mut Nonce::new(), rng, Some(poly.clone()), &input_mac_key)
        .unwrap()
        .0;
    clear_set();
    let monomials: Vec<_> = poly.iter().filter_map(|(monomial, _)| *monomial).collect();
    assert!(garbling_table.has_garbled_shape(&monomials));

    let input = <InputMac<F> as Mac<Input<F>>>::random_input(rng);
    let input_mac = input_mac_key.encode(&input);

    let output = poly.eval(input.x, input.y);

    let evaluated_output = garbling_table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .0;
    clear_set();

    assert_eq!(output, evaluated_output);
}

#[cfg(test)]
fn test_random_biquadratic<F>()
where
    F: Field + NumBits + FromBits<bool, F> + Random + ToBits + FromBits<F, F>,
    F::BasePrimeField: FromLeBytesModOrder,
{
    const SEED: u64 = 0;
    let mut rng = StdRng::seed_from_u64(SEED);

    let mut coeffs = [None; 6];
    coeffs.iter_mut().for_each(|coeff| {
        use ark_std::rand::Rng;

        if rng.gen_bool(0.5) {
            *coeff = Some(F::random(&mut rng))
        }
    });
    test_biquadratic::<F>(coeffs, &mut rng);
}

#[test]
fn test_random_biquadratic_fq() {
    test_random_biquadratic::<ark_bn254::Fq>();
}

#[test]
fn test_random_biquadratic_fq2() {
    test_random_biquadratic::<ark_bn254::Fq2>();
}

/// Obliviously evaluate the polynomial:
///     (B + x^3 - y^2) s
///   = sB + sx^3 -sy^2,
/// where `s` is the secret we want to leak.
///
/// If (x, y) is a valid curve point, then
///     y^2 = x^3 + B,
/// and the circuit evaluates to 0.
///
/// Otherwise,
///     (B + x^3 - y^2) = c != 0,
/// and the circuit evaluates to c * s.
///
/// s.t. if (x, y) is a valid curve point, this evaluates
#[cfg(test)]
fn test_curve_membership_secret_revelation<C>()
where
    C: SWCurveConfig,
    C::BaseField: NumBits
        + FromBits<bool, C::BaseField>
        + Random
        + ToBits
        + FromBits<C::BaseField, C::BaseField>,
    <C::BaseField as Field>::BasePrimeField: FromLeBytesModOrder,
{
    use ark_ff::UniformRand;
    use ark_std::Zero;

    const SEED: u64 = 0;
    let mut rng = StdRng::seed_from_u64(SEED);

    let secret = C::BaseField::random(&mut rng);

    let input_mac_key = InputMacKey::<C::BaseField>::random_key(&mut rng);

    let mut poly = Poly::default();
    poly.insert(Monomial::constant(), secret * C::COEFF_B);
    poly.insert(Monomial::new(3, 0), secret);
    poly.insert(Monomial::new(0, 2), -secret);

    let table = Table::garble(&mut Nonce::new(), &mut rng, Some(poly), &input_mac_key)
        .unwrap()
        .0;

    // Valid point should evaluate to 0.
    {
        let valid_point = Affine::<C>::rand(&mut rng);
        let input = valid_point.into();
        let input_mac = input_mac_key.encode(&input);

        let res = table
            .evaluate(&mut Nonce::new(), &input, &input_mac)
            .unwrap()
            .0;
        assert_eq!(res, C::BaseField::zero());
    }

    // Invalid point should evaluate to c * s, where
    //              (B + x^3 - y^2) = c.
    {
        let input = Input {
            x: C::BaseField::rand(&mut rng),
            y: C::BaseField::rand(&mut rng),
        };
        let input_mac = input_mac_key.encode(&input);

        let res = table
            .evaluate(&mut Nonce::new(), &input, &input_mac)
            .unwrap()
            .0;

        let c = C::COEFF_B + input.x.square() * input.x - input.y.square();
        assert_eq!(res, secret * c);
    }
}

#[test]
fn test_curve_membership_secret_revelation_fq() {
    test_curve_membership_secret_revelation::<ark_bn254::g1::Config>();
}

#[test]
fn test_curve_membership_secret_revelation_fq2() {
    test_curve_membership_secret_revelation::<ark_bn254::g2::Config>();
}
