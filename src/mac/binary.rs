use std::{marker::PhantomData, ops::Deref};

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand_core::CryptoRngCore;

use crate::mac::{
    Mac, MacKey, RandomFromPhi,
    bit::bytes::{Bit16ByteMac, Bit16ByteMacKey},
};

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct BitMacKey<Op: BooleanOp> {
    pub(crate) key: Bit16ByteMacKey,
    pub(crate) _marker: PhantomData<Op>,
}

impl<Op: BooleanOp> From<Bit16ByteMacKey> for BitMacKey<Op> {
    fn from(key: Bit16ByteMacKey) -> Self {
        Self {
            key,
            _marker: PhantomData,
        }
    }
}

impl<Op: BooleanOp> From<BitMacKey<Op>> for Bit16ByteMacKey {
    fn from(value: BitMacKey<Op>) -> Self {
        value.key
    }
}

impl<Op: BooleanOp> RandomFromPhi<bool, BitMac<Op>> for BitMacKey<Op> {
    type Phi = [u8; 16];

    fn random_from_phi(rng: &mut impl CryptoRngCore, phi: &Self::Phi) -> Self {
        Self {
            key: Bit16ByteMacKey::random_from_phi(rng, phi),
            _marker: PhantomData,
        }
    }
}

impl<Op: BooleanOp> Deref for BitMacKey<Op> {
    type Target = Bit16ByteMacKey;

    fn deref(&self) -> &Self::Target {
        &self.key
    }
}

impl From<BitMacKey<()>> for BitMacKey<Xor> {
    fn from(value: BitMacKey<()>) -> Self {
        Self {
            key: value.key,
            _marker: PhantomData,
        }
    }
}

impl From<BitMacKey<Xor>> for BitMacKey<()> {
    fn from(value: BitMacKey<Xor>) -> Self {
        Self {
            key: value.key,
            _marker: PhantomData,
        }
    }
}

impl From<BitMacKey<()>> for BitMacKey<And> {
    fn from(value: BitMacKey<()>) -> Self {
        Self {
            key: value.key,
            _marker: PhantomData,
        }
    }
}

impl From<BitMacKey<And>> for BitMacKey<()> {
    fn from(value: BitMacKey<And>) -> Self {
        Self {
            key: value.key,
            _marker: PhantomData,
        }
    }
}

impl<Op: BooleanOp> MacKey<bool, BitMac<Op>> for BitMacKey<Op> {
    // (phi AND value) XOR k
    fn encode(&self, value: &bool) -> BitMac<Op> {
        let mac = self.key.encode(value);

        BitMac {
            mac,
            _marker: PhantomData,
        }
    }

    #[cfg(test)]
    fn decode(&self, mac: &BitMac<Op>) -> bool {
        self.key.decode(mac)
    }

    fn random_key(rng: &mut impl CryptoRngCore) -> Self {
        Self {
            key: Bit16ByteMacKey::random_key(rng),
            _marker: PhantomData,
        }
    }
}

/// FIXME do we need this type?
#[derive(Debug, Clone, Copy, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct BitMac<Op: BooleanOp> {
    pub(crate) mac: Bit16ByteMac,
    pub(crate) _marker: PhantomData<Op>,
}

impl<Op: BooleanOp> From<[u8; 16]> for BitMac<Op> {
    fn from(mac: [u8; 16]) -> Self {
        Self {
            mac: Bit16ByteMac::from(mac),
            _marker: PhantomData,
        }
    }
}

impl<Op: BooleanOp> From<Bit16ByteMac> for BitMac<Op> {
    fn from(mac: Bit16ByteMac) -> Self {
        Self {
            mac,
            _marker: PhantomData,
        }
    }
}

impl<Op: BooleanOp> From<BitMac<Op>> for Bit16ByteMac {
    fn from(value: BitMac<Op>) -> Self {
        value.mac
    }
}

impl<Op: BooleanOp> Deref for BitMac<Op> {
    type Target = Bit16ByteMac;

    fn deref(&self) -> &Self::Target {
        &self.mac
    }
}

impl<Op: BooleanOp> std::ops::BitXor for BitMac<Op> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut output = [0; 16];
        output
            .iter_mut()
            .zip(self.mac.iter())
            .zip(rhs.mac.iter())
            .for_each(|((output, lhs), rhs)| *output = lhs ^ rhs);

        Self {
            mac: output.into(),
            _marker: PhantomData,
        }
    }
}

impl<Op: BooleanOp> Mac<bool> for BitMac<Op> {
    type Key = BitMacKey<Op>;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> bool {
        use ark_std::rand::Rng;

        rng.gen_bool(0.5)
    }
}

pub(crate) trait BooleanOp: Copy + Clone + Send + Sync {}
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Xor;
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct And;

impl BooleanOp for Xor {}
impl BooleanOp for And {}
impl BooleanOp for () {}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct BinaryInput<Op: BooleanOp> {
    left: bool,
    right: bool,
    _marker: PhantomData<Op>,
}

impl<Op: BooleanOp> BinaryInput<Op> {
    pub(crate) fn new(left: bool, right: bool) -> Self {
        Self {
            left,
            right,
            _marker: PhantomData,
        }
    }

    pub(crate) fn right(&self) -> bool {
        self.right
    }

    pub(crate) fn xor(&self) -> bool {
        self.left ^ self.right
    }

    pub(crate) fn and(&self) -> bool {
        self.left & self.right
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct BinaryInputMac<Op: BooleanOp> {
    left: BitMac<Op>,
    right: BitMac<Op>,
}

impl<Op: BooleanOp> BinaryInputMac<Op> {
    pub(crate) fn new(left: BitMac<Op>, right: BitMac<Op>) -> Self {
        Self { left, right }
    }

    #[allow(unused)]
    pub(crate) fn left(&self) -> BitMac<Op> {
        self.left
    }

    pub(crate) fn right(&self) -> BitMac<Op> {
        self.right
    }

    pub(crate) fn xor(&self) -> BitMac<Op> {
        self.left ^ self.right
    }
}

impl<Op: BooleanOp> Mac<BinaryInput<Op>> for BinaryInputMac<Op> {
    type Key = BinaryInputMacKey<Op>;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> BinaryInput<Op> {
        use ark_std::rand::Rng;

        BinaryInput {
            left: rng.gen_bool(0.5),
            right: rng.gen_bool(0.5),
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct BinaryInputMacKey<Op: BooleanOp> {
    pub(crate) left: BitMacKey<Op>,
    pub(crate) right: BitMacKey<Op>,
}

impl<Op: BooleanOp> MacKey<BinaryInput<Op>, BinaryInputMac<Op>> for BinaryInputMacKey<Op> {
    fn encode(&self, value: &BinaryInput<Op>) -> BinaryInputMac<Op> {
        BinaryInputMac {
            left: self.left.encode(&value.left),
            right: self.right.encode(&value.right),
        }
    }

    #[cfg(test)]
    fn decode(&self, mac: &BinaryInputMac<Op>) -> BinaryInput<Op> {
        BinaryInput {
            left: self.left.decode(&mac.left),
            right: self.right.decode(&mac.right),
            _marker: PhantomData,
        }
    }

    // phi's have to be the same for left and right
    fn random_key(rng: &mut impl CryptoRngCore) -> Self {
        let mut phi = [0; 16];
        rng.fill_bytes(&mut phi);

        let left = BitMacKey::random_from_phi(rng, &phi);
        let right = BitMacKey::random_from_phi(rng, &phi);

        Self { left, right }
    }
}
