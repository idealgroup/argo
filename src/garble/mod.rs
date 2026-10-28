use rand_core::CryptoRngCore;

use crate::{
    mac::Mac,
    utils::error::{EvalError, GarbleError},
};

pub(crate) mod bilinear;
pub(crate) mod binary;
pub(crate) mod bit_adaptor;
pub mod bivariate;
pub(crate) mod conditional_reveal;
pub(crate) mod digit_adaptor;
pub mod field_mac_to_ec_mac;
pub(crate) mod g2_subgroup_check;
pub mod groth16_verifier;
pub mod keys;

pub trait Circuit<InputValue, InputMac, OutputValue, OutputMac>: Sized
where
    InputMac: Mac<InputValue>,
    OutputMac: Mac<OutputValue>,
{
    /// Private inputs used to construct garbling table
    type Aux;

    /// Given an input_mac_key, return a garbling table and an output MAC key
    fn garble(
        parent_nonce: &mut Nonce,
        rng: &mut impl CryptoRngCore,
        aux: Option<Self::Aux>,
        input_mac_key: &<InputMac as Mac<InputValue>>::Key,
    ) -> Result<(Self, <OutputMac as Mac<OutputValue>>::Key), GarbleError>;

    /// Given a garbling table, an input, and an input MAC, return an output
    /// value and an output MAC
    fn evaluate(
        &self,
        parent_nonce: &mut Nonce,
        input: &InputValue,
        input_mac: &InputMac,
    ) -> Result<(OutputValue, OutputMac), EvalError>;
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Nonce {
    // Our garbling tables are arranged in a tree, where each table contains
    // sub-tables. A sub-table can be thought of as the parent table's children
    // in the next level.
    //
    // Each counters[i] in this array tracks the number of tables on level i + 1.
    counters: [u16; 8],
    // The current level
    level: usize,
}

impl Nonce {
    /// Initializes a nonce with all counters set to 0.
    pub fn new() -> Self {
        Self {
            counters: [0; 8],
            level: 0,
        }
    }

    /// Returns self.counters as a [u8; 16], each counter little-endian.
    #[inline]
    pub fn bytes(&self) -> [u8; 16] {
        let mut bytes = [0; 16];
        for (bytes, counter) in bytes.chunks_exact_mut(2).zip(self.counters) {
            bytes.copy_from_slice(&counter.to_le_bytes());
        }
        bytes
    }

    /// Forks the parent nonce to return a child nonce
    pub fn fork(&mut self) -> Self {
        // Increment the counter at the current level to register that one more
        // child has been created
        self.update();

        // Return the child nonce by copying its parents counter, and
        // incrementing the level index
        Self {
            counters: self.counters,
            level: self.level + 1,
        }
    }

    #[inline]
    fn update(&mut self) {
        self.counters[self.level] += 1;
    }
}

#[test]
fn test_nonce_bytes_are_little_endian() {
    let mut nonce = Nonce::new();
    for _ in 0..0x0102 {
        nonce.fork();
    }
    let mut child = nonce.fork();
    child.fork();
    let mut expected = [0; 16];
    expected[..4].copy_from_slice(&[0x03, 0x01, 0x01, 0x00]);
    assert_eq!(child.bytes(), expected);
}
