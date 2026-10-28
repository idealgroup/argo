//! AND half-gate
//!
//! Our output_mac_key is such that:
//! - output_mac_key.phi = input_mac_key.left.phi,
//! - output_mac_key.k = hash(input_mac_key.right.encode(0))
//!
//! Enumerating through the cases:
//! 1. left = 0, right = 0, output = 0
//!    mac_left = [0; 16]
//!    mac_right = hash(input_mac_key.right.encode(0))
//!    mac_left ^ mac_right = hash(input_mac_key.right.encode(0)),
//!    which recovers the MAC of 0 under output_mac_key.
//! 2. left = 0, right = 1, output = 0
//!    mac_left = input_mac.left = input_mac_key.left.k
//!    mac_right = input_mac_key.left.k ^ hash(input_mac_key.right.encode(0))
//!    mac_left ^ mac_right = hash(input_mac_key.right.encode(0)),
//!    which recovers the MAC of 0 under output_mac_key.
//! 3. left = 1, right = 0, output = 0
//!    mac_left = [0; 16]
//!    mac_right = hash(input_mac_key.right.encode(0))
//!    mac_left ^ mac_right = hash(input_mac_key.right.encode(0)),
//!    which recovers the MAC of 0 under output_mac_key.
//! 4. left = 1, right = 1, output = 1
//!    mac_left = input_mac.left = input_mac_key.left.phi ^ input_mac_key.left.k
//!    mac_right = input_mac_key.left.k ^ hash(input_mac_key.right.encode(0))
//!    mac_left ^ mac_right = input_mac_key.left.phi ^ hash(input_mac_key.right.encode(0)),
//!    which recovers the MAC of 1 under output_mac_key.

use std::{any::type_name, marker::PhantomData};

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand_core::CryptoRngCore;

#[cfg(test)]
use crate::utils::aes_hash::aes_mitccr::clear_set;
use crate::{
    garble::{
        Circuit, Nonce,
        bit_adaptor::{self, bytes::aes_mitccr::Aux},
        groth16_verifier::GID,
    },
    mac::{
        binary::{And, BinaryInput, BinaryInputMac, BinaryInputMacKey, BitMac, BitMacKey},
        bit::bytes::{Bit16ByteMac, Bit16ByteMacKey},
    },
    utils::{
        aes_hash::{Hash, aes_mitccr::AesMiTCCR},
        error::{EvalError, GarbleError},
    },
};

pub(crate) type InputMac = BinaryInputMac<And>;

pub(crate) type Input = BinaryInput<And>;
pub(crate) type InputMacKey = BinaryInputMacKey<And>;

type OutputMac = BitMac<And>;
type OutputMacKey = BitMacKey<And>;

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub(crate) struct Table {
    gid: GID,
    bit_adaptor: bit_adaptor::Table<AesMiTCCR, Bit16ByteMac, Bit16ByteMac>,
}

impl Table {
    pub(crate) fn has_garbled_shape(&self, gid: &GID) -> bool {
        self.gid == *gid && self.bit_adaptor.has_garbled_shape(gid)
    }
}

impl Circuit<Input, InputMac, bool, OutputMac> for Table {
    type Aux = GID;

    fn garble(
        parent_nonce: &mut Nonce,
        rng: &mut impl CryptoRngCore,
        aux: Option<Self::Aux>,
        input_mac_key: &InputMacKey,
    ) -> Result<(Self, OutputMacKey), GarbleError> {
        let mut nonce = parent_nonce.fork();

        let gid = aux
            .ok_or_else(|| GarbleError::AuxError(type_name::<Self::Aux>(), type_name::<Self>()))?;

        // Bit adaptor table mapping from a MAC under input_mac_key.right to a
        // MAC under a mac_key s.t.
        // - mac_key.phi = input_mac_key.left.k,
        // - mac_key.k = hash(input_mac_key.right.encode(0))
        // This stores the encryption of mac_key.encode(1),
        // using input_mac_key.right.encode(1) as the key
        let (bit_adaptor, mut output_mac_key): (
            bit_adaptor::Table<AesMiTCCR, Bit16ByteMac, Bit16ByteMac>,
            Bit16ByteMacKey,
        ) = {
            let aux = Aux {
                gid,
                phi: input_mac_key.left.k,
            };

            bit_adaptor::Table::garble(&mut nonce, rng, Some(aux), &input_mac_key.right.key)?
        };

        output_mac_key.phi = input_mac_key.left.phi;

        Ok((Self { gid, bit_adaptor }, output_mac_key.into()))
    }

    fn evaluate(
        &self,
        parent_nonce: &mut Nonce,
        input: &Input,
        input_mac: &InputMac,
    ) -> Result<(bool, OutputMac), EvalError> {
        let mut nonce = parent_nonce.fork();

        let mac_left = if input.right() {
            // If input.right = 1, use input_mac.left as mac_left, i.e.
            input_mac.left()
        } else {
            // If input.right = 0, use the all-zeros string as mac_left
            BitMac {
                mac: Bit16ByteMac::from([0; 16]),
                _marker: PhantomData,
            }
        };

        let mac_right = if input.right() {
            // If input.right = 1, use the input_mac.right as the key
            // to decrypt the mac_right, to get
            // input_mac_key.left.k ^ hash(input_mac_key.right.encode(0))
            self.bit_adaptor
                .evaluate(&mut nonce, &input.right(), &input_mac.right())?
                .1
        } else {
            // If input.right = 0, derive mac_right by hashing input_mac.right
            // to get hash(input_mac_key.right.encode(0))
            let dst = bit_adaptor::Table::derive_dst(&self.gid, &nonce);

            let hash = AesMiTCCR::hash(&dst, &input_mac.right());

            hash.into()
        };

        Ok((input.and(), mac_left ^ mac_right.into()))
    }
}

#[test]
fn test_and_circuit() {
    use crate::mac::{Mac, MacKey, Random};
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    const N: usize = 100;
    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    for _ in 0..N {
        let gid = GID::random(&mut rng);
        let input = InputMac::random_input(&mut rng);

        let input_mac_key = InputMacKey::random_key(&mut rng);

        let input_mac = input_mac_key.encode(&input);

        let (circuit, output_mac_key) =
            Table::garble(&mut Nonce::new(), &mut rng, Some(gid), &input_mac_key).unwrap();
        clear_set();
        assert!(circuit.has_garbled_shape(&gid));

        let output_mac = circuit
            .evaluate(&mut Nonce::new(), &input, &input_mac)
            .unwrap()
            .1;
        clear_set();

        let output = input.and();
        let expected_output_mac = output_mac_key.encode(&output);

        assert_eq!(output_mac, expected_output_mac);
    }
}
