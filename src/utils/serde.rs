use ark_bn254::{Fq, g2};
use ark_ec::short_weierstrass::Affine;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};

use crate::{
    garble::{g2_subgroup_check, groth16_verifier::KAPPA_B},
    utils::bits::NumBits,
};
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

/// The lengths a `BoundedVec` may decode with.
pub(crate) trait LenBound {
    fn allows(len: u64) -> bool;
}

/// Exactly `K` elements.
pub(crate) struct Len<const K: usize>;

impl<const K: usize> LenBound for Len<K> {
    fn allows(len: u64) -> bool {
        len == K as u64
    }
}

/// At most `K` elements.
pub(crate) struct AtMost<const K: usize>;

impl<const K: usize> LenBound for AtMost<K> {
    fn allows(len: u64) -> bool {
        len <= K as u64
    }
}

/// One element per bit of `F`.
pub(crate) struct Bits<F>(PhantomData<F>);

impl<F: NumBits> LenBound for Bits<F> {
    fn allows(len: u64) -> bool {
        len == F::NUM_BITS as u64
    }
}

/// `Vec<T>` with the same encoding, whose decoder rejects a length that `B`
/// does not allow before decoding any element. ark-serialize decodes as many
/// elements as the length prefix claims, and in a table the garbler writes
/// that prefix.
pub(crate) struct BoundedVec<T, B>(pub(crate) Vec<T>, PhantomData<fn() -> B>);

impl<T, B> From<Vec<T>> for BoundedVec<T, B> {
    fn from(values: Vec<T>) -> Self {
        Self(values, PhantomData)
    }
}

impl<T, B> Deref for BoundedVec<T, B> {
    type Target = Vec<T>;

    fn deref(&self) -> &Vec<T> {
        &self.0
    }
}

impl<T, B> DerefMut for BoundedVec<T, B> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        &mut self.0
    }
}

impl<T: Debug, B> Debug for BoundedVec<T, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: CanonicalSerialize, B> CanonicalSerialize for BoundedVec<T, B> {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.0.serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.0.serialized_size(compress)
    }
}

impl<T: Valid, B> Valid for BoundedVec<T, B> {
    const TRIVIAL_CHECK: bool = T::TRIVIAL_CHECK;

    fn check(&self) -> Result<(), SerializationError> {
        self.0.check()
    }
}

impl<T: CanonicalDeserialize, B: LenBound> CanonicalDeserialize for BoundedVec<T, B> {
    fn deserialize_with_mode<R: std::io::Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let len = u64::deserialize_with_mode(&mut reader, compress, validate)?;
        if !B::allows(len) {
            return Err(SerializationError::InvalidData);
        }
        (0..len)
            .map(|_| T::deserialize_with_mode(&mut reader, compress, validate))
            .collect::<Result<Vec<_>, _>>()
            .map(Self::from)
    }
}

/// `[T; N]` with the same encoding, kept on the heap so that a table's stack
/// size does not grow with `N`. ark-serialize 0.6.0's array impl leaks the
/// elements decoded before an error; collecting into a `Vec` drops them.
pub(crate) struct Array<T, const N: usize>(pub(crate) Box<[T; N]>);

impl<T, const N: usize> TryFrom<Vec<T>> for Array<T, N> {
    type Error = Vec<T>;

    fn try_from(values: Vec<T>) -> Result<Self, Vec<T>> {
        values
            .into_boxed_slice()
            .try_into()
            .map(Self)
            .map_err(Vec::from)
    }
}

impl<T, const N: usize> Deref for Array<T, N> {
    type Target = [T; N];

    fn deref(&self) -> &[T; N] {
        &self.0
    }
}

impl<T, const N: usize> DerefMut for Array<T, N> {
    fn deref_mut(&mut self) -> &mut [T; N] {
        &mut self.0
    }
}

impl<T: CanonicalSerialize, const N: usize> CanonicalSerialize for Array<T, N> {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.0.serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.0.serialized_size(compress)
    }
}

impl<T: Valid, const N: usize> Valid for Array<T, N> {
    const TRIVIAL_CHECK: bool = T::TRIVIAL_CHECK;

    fn check(&self) -> Result<(), SerializationError> {
        self.0.check()
    }
}

impl<T: CanonicalDeserialize, const N: usize> CanonicalDeserialize for Array<T, N> {
    fn deserialize_with_mode<R: std::io::Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let values = (0..N)
            .map(|_| T::deserialize_with_mode(&mut reader, compress, validate))
            .collect::<Result<Vec<_>, _>>()?;
        Self::try_from(values).map_err(|_| SerializationError::InvalidData)
    }
}

fn deserialize_box_vec<T, const N: usize, R>(
    mut reader: R,
    compress: Compress,
    validate: Validate,
) -> Result<Box<[T; N]>, SerializationError>
where
    T: CanonicalDeserialize + Debug,
    R: std::io::Read,
{
    let mut vec = Vec::with_capacity(N);
    for _ in 0..N {
        vec.push(T::deserialize_with_mode(&mut reader, compress, validate)?);
    }

    Ok(vec.into_boxed_slice().try_into().expect("N elements"))
}

impl CanonicalSerialize for g2_subgroup_check::Table {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.enc_s.serialize_with_mode(&mut writer, compress)?;
        self.r_ks.serialize_with_mode(&mut writer, compress)?;

        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.enc_s.serialized_size(compress) + self.r_ks.serialized_size(compress)
    }
}

impl CanonicalDeserialize for g2_subgroup_check::Table {
    fn deserialize_with_mode<R: std::io::Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let enc_s = Fq::deserialize_with_mode(&mut reader, compress, validate)?;

        // These are not g2 points, so don't validate that they are in the
        // subgroup
        let r_ks = deserialize_box_vec::<Affine<g2::Config>, { KAPPA_B }, _>(
            &mut reader,
            compress,
            Validate::No,
        )?;

        Ok(Self { enc_s, r_ks })
    }
}

impl Valid for g2_subgroup_check::Table {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::*;

    static LIVE: AtomicUsize = AtomicUsize::new(0);

    /// One byte on the wire, counted while alive.
    struct Counted;

    impl Drop for Counted {
        fn drop(&mut self) {
            LIVE.fetch_sub(1, Ordering::SeqCst);
        }
    }

    impl Valid for Counted {
        fn check(&self) -> Result<(), SerializationError> {
            Ok(())
        }
    }

    impl CanonicalDeserialize for Counted {
        fn deserialize_with_mode<R: std::io::Read>(
            reader: R,
            compress: Compress,
            validate: Validate,
        ) -> Result<Self, SerializationError> {
            u8::deserialize_with_mode(reader, compress, validate)?;
            LIVE.fetch_add(1, Ordering::SeqCst);
            Ok(Self)
        }
    }

    #[test]
    fn array_error_drops_decoded_prefix() {
        let result = Array::<Counted, 4>::deserialize_compressed(&[1u8, 2, 3][..]);
        assert!(result.is_err());
        assert_eq!(LIVE.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn bounded_vec_rejects_a_length_before_decoding_elements() {
        // Decoding an element would fail on the missing bytes with an IO error.
        let length_only = 3u64.to_le_bytes();
        for error in [
            BoundedVec::<u8, Len<2>>::deserialize_compressed(&length_only[..]).err(),
            BoundedVec::<u8, Len<4>>::deserialize_compressed(&length_only[..]).err(),
            BoundedVec::<u8, AtMost<2>>::deserialize_compressed(&length_only[..]).err(),
        ] {
            assert!(matches!(error, Some(SerializationError::InvalidData)));
        }

        let mut expected = Vec::new();
        vec![1u8, 2, 3].serialize_compressed(&mut expected).unwrap();
        let mut bytes = Vec::new();
        BoundedVec::<u8, Len<3>>::from(vec![1, 2, 3])
            .serialize_compressed(&mut bytes)
            .unwrap();
        assert_eq!(bytes, expected);
        for decoded in [
            BoundedVec::<u8, Len<3>>::deserialize_compressed(&bytes[..])
                .unwrap()
                .0,
            BoundedVec::<u8, AtMost<3>>::deserialize_compressed(&bytes[..])
                .unwrap()
                .0,
        ] {
            assert_eq!(decoded, [1, 2, 3]);
        }
    }

    #[test]
    fn array_encodes_like_a_fixed_array() {
        let values = [1u64, 2, 3];
        let mut expected = Vec::new();
        values.serialize_compressed(&mut expected).unwrap();
        let mut bytes = Vec::new();
        Array(Box::new(values))
            .serialize_compressed(&mut bytes)
            .unwrap();
        assert_eq!(bytes, expected);
        let decoded = Array::<u64, 3>::deserialize_compressed(&bytes[..]).unwrap();
        assert_eq!(*decoded, values);
    }
}
