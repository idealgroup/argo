//! XOR garbling table

use std::marker::PhantomData;

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use rand_core::CryptoRngCore;

use crate::{
    garble::{Circuit, Nonce},
    mac::{
        Mac,
        binary::{BinaryInput, BinaryInputMac, BinaryInputMacKey, BitMac, BitMacKey, Xor},
        bit::bytes::Bit16ByteMacKey,
    },
    utils::error::{EvalError, GarbleError},
};

pub(crate) type InputMacKey = BinaryInputMacKey<Xor>;

pub(crate) type Input = BinaryInput<Xor>;

pub(crate) type InputMac = BinaryInputMac<Xor>;

type OutputMac = BitMac<Xor>;
// phi has to be the same as InputMacKey
// k is the XOR of InputMacKey.left.k, InputMacKey.right.k
type OutputMacKey = BitMacKey<Xor>;

impl InputMacKey {
    /// Derives output MAC key for A XOR B, given the input MAC keys for A, B.
    ///
    /// # Panics
    ///
    /// Panics if A.phi != B.phi.
    pub(crate) fn output_mac_key(&self) -> OutputMacKey {
        let phi = self.left.phi;
        assert_eq!(phi, self.right.phi);

        let mut k = [0; 16];
        k.iter_mut()
            .zip(self.left.k.iter())
            .zip(self.right.k.iter())
            .for_each(|((k, left), right)| *k = left ^ right);

        // OutputMacKey phi has to be the same as InputMacKey
        // OutputMacKey k is the XOR of InputMacKey.left.k, InputMacKey.right.k
        BitMacKey {
            key: Bit16ByteMacKey { phi, k },
            _marker: PhantomData,
        }
    }
}

/// XOR is free, so the table is empty and serializes to no bytes.
#[derive(Debug, Clone)]
pub(crate) struct Table;

// ark-serialize 0.6 can't derive these for a struct without fields.
impl Valid for Table {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalSerialize for Table {
    fn serialize_with_mode<W: Write>(&self, _: W, _: Compress) -> Result<(), SerializationError> {
        Ok(())
    }

    fn serialized_size(&self, _: Compress) -> usize {
        0
    }
}

impl CanonicalDeserialize for Table {
    fn deserialize_with_mode<R: Read>(
        _: R,
        _: Compress,
        _: Validate,
    ) -> Result<Self, SerializationError> {
        Ok(Self)
    }
}

impl Circuit<Input, InputMac, bool, OutputMac> for Table {
    type Aux = ();

    fn garble(
        _parent_nonce: &mut Nonce,
        _rng: &mut impl CryptoRngCore,
        _aux: Option<Self::Aux>,
        input_mac_key: &<BinaryInputMac<Xor> as Mac<BinaryInput<Xor>>>::Key,
    ) -> Result<(Self, <OutputMac as Mac<bool>>::Key), GarbleError> {
        Ok((Self, input_mac_key.output_mac_key()))
    }

    fn evaluate(
        &self,
        _parent_nonce: &mut Nonce,
        input: &BinaryInput<Xor>,
        input_mac: &BinaryInputMac<Xor>,
    ) -> Result<(bool, OutputMac), EvalError> {
        Ok((input.xor(), input_mac.xor()))
    }
}

/// FIXME test more cases
#[test]
fn test_xor_circuit() {
    use crate::mac::MacKey;
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    let input = InputMac::random_input(&mut rng);
    let input_mac_key = InputMacKey::random_key(&mut rng);
    let output_mac_key = input_mac_key.output_mac_key();
    let input_mac = input_mac_key.encode(&input);

    let circuit = Table::garble(&mut Nonce::new(), &mut rng, None, &input_mac_key)
        .unwrap()
        .0;
    let output_mac = circuit
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .1;

    let output = input.xor();
    let expected_output_mac = output_mac_key.encode(&output);

    assert_eq!(output_mac, expected_output_mac);
}
