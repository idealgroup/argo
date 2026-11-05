use ark_bn254::{Fq, g2};
use ark_ec::short_weierstrass::Affine;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};

use crate::garble::{g2_subgroup_check, groth16_verifier::KAPPA_B};
use std::fmt::Debug;
use std::ops::{Deref, DerefMut};

/// `[T; N]` with the same encoding. ark-serialize 0.6.0's array impl leaks
/// the elements decoded before an error; collecting into a `Vec` drops them.
pub(crate) struct Array<T, const N: usize>(pub(crate) [T; N]);

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
        values
            .try_into()
            .map(Self)
            .map_err(|_| SerializationError::InvalidData)
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
    fn array_encodes_like_a_fixed_array() {
        let values = [1u64, 2, 3];
        let mut expected = Vec::new();
        values.serialize_compressed(&mut expected).unwrap();
        let mut bytes = Vec::new();
        Array(values).serialize_compressed(&mut bytes).unwrap();
        assert_eq!(bytes, expected);
        let decoded = Array::<u64, 3>::deserialize_compressed(&bytes[..]).unwrap();
        assert_eq!(decoded.0, values);
    }
}
