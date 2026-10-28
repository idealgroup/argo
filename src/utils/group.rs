use std::sync::LazyLock;

use ark_bn254::{Bn254, Fq, Fq2, Fq12, Fr, g2};
use ark_ec::{AffineRepr, pairing::Pairing, short_weierstrass::Affine};
use ark_ff::{BigInt, PrimeField};
use ark_std::rand::rngs::StdRng;

use crate::utils::error::EvalError;

/// `Bn254::multi_pairing` without its panic on a zero Miller loop output,
/// which points decoded from a malformed table can cause.
pub(crate) fn checked_multi_pairing(
    a: impl IntoIterator<Item = impl Into<<Bn254 as Pairing>::G1Prepared>>,
    b: impl IntoIterator<Item = impl Into<<Bn254 as Pairing>::G2Prepared>>,
) -> Result<Fq12, EvalError> {
    Bn254::final_exponentiation(Bn254::multi_miller_loop(a, b))
        .map(|output| output.0)
        .ok_or(EvalError::DegeneratePairing)
}

/// A 17-byte offset in Bn254::Fq, i.e. Fq(2^{8 * 17})
/// Used in optimised from_le_bytes_mod_order for hash_to_field
/// This unwrap cannot fail as the value is smaller than the field modulus.
pub static FQ_LO_BYTES_OFFSET: LazyLock<Fq> =
    LazyLock::new(|| Fq::from_bigint(BigInt::one() << (8 * 17)).unwrap());

/// A 17-byte offset in Bn254::Fr, i.e. Fr(2^{8 * 17})
/// Used in optimised from_le_bytes_mod_order for hash_to_field
/// This unwrap cannot fail as the value is smaller than the field modulus.
pub static FR_LO_BYTES_OFFSET: LazyLock<Fr> =
    LazyLock::new(|| Fr::from_bigint(BigInt::one() << (8 * 17)).unwrap());

fn to_u64_array<const N: usize>(bytes: &[u8]) -> [u64; N] {
    let mut result = [0u64; N];

    for (i, word) in result.iter_mut().enumerate() {
        let offset = i * 8;
        if offset + 8 <= bytes.len() {
            // Fast path: read full u64
            // This unwrap cannot fail since it is hard-coded to 8 bytes
            *word = u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap());
        } else if offset < bytes.len() {
            // Slow path: partial bytes
            let remaining = bytes.len() - offset;
            let mut u64_bytes = [0u8; 8];
            u64_bytes[..remaining].copy_from_slice(&bytes[offset..]);
            *word = u64::from_le_bytes(u64_bytes);
        }
    }

    result
}

pub trait FromLeBytesModOrder {
    fn from_le_bytes_mod_order(bytes: &[u8]) -> Self;
}

impl FromLeBytesModOrder for Fq {
    /// Optimized implementation of from_le_bytes_mod_order for Bn254::Fq
    #[inline]
    fn from_le_bytes_mod_order(bytes: &[u8]) -> Fq {
        let num_modulus_bytes = Fq::MODULUS_BIT_SIZE.div_ceil(8) as usize;
        let num_bytes_to_directly_convert = ark_std::cmp::min(num_modulus_bytes - 1, bytes.len());

        // Copy the leading little-endian bytes directly into a field element.
        // The number of bytes directly converted must be less than the
        // number of bytes needed to represent the modulus, as we must begin
        // modular reduction once the data is of the same number of bytes as the
        // modulus.

        let (lo, hi) = bytes.split_at(bytes.len() - num_bytes_to_directly_convert);

        let lo: Fq = Fq::new_unchecked(BigInt::new(to_u64_array::<4>(lo)));
        let mut hi = Fq::new_unchecked(BigInt::new(to_u64_array::<4>(hi)));

        hi *= *FQ_LO_BYTES_OFFSET;
        hi += lo;

        // Sanity-check equivalence with arkworks unoptimised implementation
        #[cfg(test)]
        assert_eq!(
            hi * Fq::new_unchecked(Fq::R2),
            <Fq as PrimeField>::from_le_bytes_mod_order(bytes)
        );

        hi
    }
}

impl FromLeBytesModOrder for Fr {
    /// Optimized implementation of from_le_bytes_mod_order for Bn254::Fr
    /// FIXME test more cases?!
    #[inline]
    fn from_le_bytes_mod_order(bytes: &[u8]) -> Fr {
        let num_modulus_bytes = Fr::MODULUS_BIT_SIZE.div_ceil(8) as usize;
        let num_bytes_to_directly_convert = ark_std::cmp::min(num_modulus_bytes - 1, bytes.len());

        // Copy the leading little-endian bytes directly into a field element.
        // The number of bytes directly converted must be less than the
        // number of bytes needed to represent the modulus, as we must begin
        // modular reduction once the data is of the same number of bytes as the
        // modulus.

        let (lo, hi) = bytes.split_at(bytes.len() - num_bytes_to_directly_convert);

        let lo: Fr = Fr::new_unchecked(BigInt::new(to_u64_array::<4>(lo)));
        let mut hi = Fr::new_unchecked(BigInt::new(to_u64_array::<4>(hi)));

        hi *= *FR_LO_BYTES_OFFSET;
        hi += lo;

        // Sanity-check equivalence with arkworks unoptimised implementation
        #[cfg(test)]
        assert_eq!(
            hi * Fr::new_unchecked(Fr::R2),
            <Fr as PrimeField>::from_le_bytes_mod_order(bytes)
        );

        hi
    }
}

pub(crate) fn get_curve_point_not_in_g2(rng: &mut StdRng) -> Affine<g2::Config> {
    use ark_ff::UniformRand;
    use ark_std::Zero;

    loop {
        let x = Fq2::rand(rng);
        if let Some(point) = Affine::get_point_from_x_unchecked(x, false)
            && !point.mul_bigint(Fr::MODULUS).is_zero()
        {
            return point;
        }
    }
}
