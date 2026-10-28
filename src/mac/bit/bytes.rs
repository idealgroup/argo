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
        let mut phi = [0; 16];
        rng.fill_bytes(&mut phi);

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
