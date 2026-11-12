use crate::mac::{Mac, MacKey, RandomFromPhi};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use derive_more::{Deref, From};
use rand_core::CryptoRngCore;

/// MAC from a bit to a 16-byte word
#[derive(Clone, Copy, CanonicalSerialize, CanonicalDeserialize, PartialEq, From, Deref)]
pub(crate) struct Bit16ByteMac(pub(crate) [u8; 16]);

#[derive(Clone, Copy, CanonicalSerialize, CanonicalDeserialize, PartialEq)]
pub(crate) struct Bit16ByteMacKey {
    pub(crate) phi: [u8; 16],
    pub(crate) k: [u8; 16],
}

/// Redacted: a label must not reach logs.
impl std::fmt::Debug for Bit16ByteMac {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Bit16ByteMac(..)")
    }
}

/// Redacted: the key holds both labels of a bit.
impl std::fmt::Debug for Bit16ByteMacKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Bit16ByteMacKey(..)")
    }
}

/// Samples `phi`, the XOR of a bit's two labels, which must not be zero.
pub(crate) fn random_offset(rng: &mut impl CryptoRngCore) -> [u8; 16] {
    loop {
        let mut phi = [0; 16];
        rng.fill_bytes(&mut phi);
        if phi != [0; 16] {
            return phi;
        }
    }
}

impl Bit16ByteMacKey {
    pub(crate) fn phi_xor_k(&self) -> [u8; 16] {
        let mut bytes = self.phi;
        bytes
            .iter_mut()
            .zip(self.k.iter())
            .for_each(|(phi, k)| *phi ^= k);

        bytes
    }
}

impl MacKey<bool, Bit16ByteMac> for Bit16ByteMacKey {
    fn encode(&self, value: &bool) -> Bit16ByteMac {
        if *value {
            self.phi_xor_k().into()
        } else {
            self.k.into()
        }
    }

    #[cfg(test)]
    fn decode(&self, mac: &Bit16ByteMac) -> bool {
        if mac.0 == self.k {
            false
        } else {
            assert_eq!(mac.0, self.phi_xor_k());
            true
        }
    }

    fn random_key(rng: &mut impl CryptoRngCore) -> Self {
        let phi = random_offset(rng);

        let mut k = [0; 16];
        rng.fill_bytes(&mut k);

        Self { phi, k }
    }
}

impl Mac<bool> for Bit16ByteMac {
    type Key = Bit16ByteMacKey;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> bool {
        use ark_std::rand::Rng;
        rng.gen_bool(0.5)
    }
}

impl RandomFromPhi<bool, Bit16ByteMac> for Bit16ByteMacKey {
    type Phi = [u8; 16];

    fn random_from_phi(rng: &mut impl CryptoRngCore, phi: &Self::Phi) -> Self {
        let mut k = [0; 16];
        rng.fill_bytes(&mut k);

        Self { phi: *phi, k }
    }
}

#[test]
fn random_offset_is_never_zero() {
    use rand_core::{CryptoRng, RngCore, impls};

    /// Gives sixteen zero bytes, then ones.
    struct ZeroFirst(usize);

    impl RngCore for ZeroFirst {
        fn next_u32(&mut self) -> u32 {
            impls::next_u32_via_fill(self)
        }

        fn next_u64(&mut self) -> u64 {
            impls::next_u64_via_fill(self)
        }

        fn fill_bytes(&mut self, dest: &mut [u8]) {
            for byte in dest {
                *byte = u8::from(self.0 >= 16);
                self.0 += 1;
            }
        }

        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
            self.fill_bytes(dest);
            Ok(())
        }
    }

    impl CryptoRng for ZeroFirst {}

    assert_eq!(random_offset(&mut ZeroFirst(0)), [1; 16]);
}
