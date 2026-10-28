use ark_bn254::{Fq, Fq2, Fr};
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
use std::{
    ops::{Add, Mul, MulAssign},
    sync::LazyLock,
};

/// Fq2 {c0: 0, c1: 1}.
/// This unwrap cannot fail as this is a valid Fq2 element.
static ALPHA: LazyLock<Fq2> =
    LazyLock::new(|| Fq2::from_base_prime_field_elems([Fq::ZERO, Fq::ONE]).unwrap());

pub trait FromBits<B, V> {
    /// Takes a bit representation where each bit is encoded as a value in `B`,
    /// and composes it to reconstruct a value in `V`.
    fn from_bits<I: DoubleEndedIterator<Item = B> + ExactSizeIterator>(bits: I) -> Option<V>;
}

pub trait NumBits {
    /// The number of bits in the bit representation of this value.
    const NUM_BITS: usize;
}

pub trait ToBits {
    /// Decomposes this value into its bit representation.
    fn to_bits(&self) -> Vec<bool>;
}

impl FromBits<bool, Fq> for Fq {
    fn from_bits<I: DoubleEndedIterator<Item = bool>>(bits: I) -> Option<Fq> {
        Fq::from_bigint(BigInteger::from_bits_le(&bits.collect::<Vec<_>>()))
    }
}

impl FromBits<bool, Fq2> for Fq2 {
    /// Returns `None` unless `bits` has length Fq::MODULUS_BIT_SIZE * 2.
    fn from_bits<I: DoubleEndedIterator<Item = bool> + ExactSizeIterator>(
        mut bits: I,
    ) -> Option<Fq2> {
        let fp_len = Fq::MODULUS_BIT_SIZE as usize;
        if bits.len() != fp_len * 2 {
            return None;
        }

        let c0 = Fq::from_bits(bits.by_ref().take(fp_len))?;
        let c1 = Fq::from_bits(bits.skip(fp_len))?;

        Fq2::from_base_prime_field_elems([c0, c1])
    }
}

impl FromBits<Fq, Fq> for Fq {
    fn from_bits<I: DoubleEndedIterator<Item = Fq>>(bits: I) -> Option<Fq> {
        Some(pow_two_lincomb::<_, Fq, Fq>(bits))
    }
}

impl FromBits<Fr, Fr> for Fr {
    fn from_bits<I: DoubleEndedIterator<Item = Fr>>(bits: I) -> Option<Fr> {
        Some(pow_two_lincomb::<_, Fr, Fr>(bits))
    }
}

impl FromBits<Fq, Fq2> for Fq2 {
    /// Returns `None` unless `bits` has length Fq::MODULUS_BIT_SIZE * 2.
    fn from_bits<I: DoubleEndedIterator<Item = Fq> + ExactSizeIterator>(
        mut bits: I,
    ) -> Option<Fq2> {
        let fp_len = Fq::MODULUS_BIT_SIZE as usize;
        if bits.len() != fp_len * 2 {
            return None;
        }

        let c0 = Fq::from_bits(bits.by_ref().take(fp_len))?;
        let c1 = Fq::from_bits(bits.skip(fp_len))?;

        Fq2::from_base_prime_field_elems([c0, c1])
    }
}

impl FromBits<Fq2, Fq2> for Fq2 {
    /// Returns `None` unless `bits` has length Fq::MODULUS_BIT_SIZE * 2.
    fn from_bits<I: DoubleEndedIterator<Item = Fq2> + ExactSizeIterator>(
        mut bits: I,
    ) -> Option<Fq2> {
        let fp_len = Fq::MODULUS_BIT_SIZE as usize;
        if bits.len() != fp_len * 2 {
            return None;
        }

        let c0_bits: Vec<_> = bits.by_ref().take(fp_len).collect();
        let c0 = pow_two_lincomb::<_, Fq2, Fq2>(c0_bits);

        let c1 = pow_two_lincomb::<_, Fq2, Fq2>(bits.map(|bit| bit * *ALPHA));

        Some(c0 + c1)
    }
}

impl NumBits for Fq {
    const NUM_BITS: usize = Self::MODULUS_BIT_SIZE as usize;
}

impl NumBits for Fr {
    const NUM_BITS: usize = Self::MODULUS_BIT_SIZE as usize;
}

impl NumBits for Fq2 {
    const NUM_BITS: usize = Fq::MODULUS_BIT_SIZE as usize * 2;
}

impl ToBits for Fq {
    #[inline]
    fn to_bits(&self) -> Vec<bool> {
        let mut bits = Vec::with_capacity(Self::MODULUS_BIT_SIZE as usize);
        bits.extend_from_slice(&self.into_bigint().to_bits_le()[..Self::MODULUS_BIT_SIZE as usize]);
        bits
    }
}

impl ToBits for Fr {
    #[inline]
    fn to_bits(&self) -> Vec<bool> {
        let mut bits = Vec::with_capacity(Self::MODULUS_BIT_SIZE as usize);
        bits.extend_from_slice(&self.into_bigint().to_bits_le()[..Self::MODULUS_BIT_SIZE as usize]);
        bits
    }
}

impl ToBits for Fq2 {
    #[inline]
    fn to_bits(&self) -> Vec<bool> {
        let base_elems = self.to_base_prime_field_elements();
        let mut bits = Vec::with_capacity(
            base_elems.size_hint().0 * <Fq2 as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize,
        );

        for v in base_elems {
            bits.extend_from_slice(&v.to_bits());
        }

        bits
    }
}

/// Computes ∑ v_i * 2^i using Horner's method
pub(crate) fn pow_two_lincomb<I, Value, Coeff>(values: I) -> Value
where
    I: IntoIterator<Item = Value>,
    I::IntoIter: DoubleEndedIterator,
    Value: Mul<Coeff, Output = Value>
        + MulAssign<Coeff>
        + Add<Value, Output = Value>
        + Copy
        + AdditiveGroup,
    Coeff: Copy,
{
    values
        .into_iter()
        .rev()
        .fold(Value::zero(), |acc, value| acc.double() + value)
}

/// Computes ∑ v_i * N^i using Horner's method
pub(crate) fn pow_n_lincomb<I, Value, Coeff>(values: I, n: Coeff) -> Value
where
    I: IntoIterator<Item = Value>,
    I::IntoIter: DoubleEndedIterator,
    Value: AdditiveGroup
        + for<'a> Mul<&'a Coeff, Output = Value>
        + MulAssign<Coeff>
        + Add<Value, Output = Value>
        + Copy,
    Coeff: Clone,
{
    values
        .into_iter()
        .rev()
        .fold(Value::zero(), |acc, value| acc * &n + value)
}
