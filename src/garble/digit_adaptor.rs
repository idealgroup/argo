//! Given an input_mac_key: Vec<Bit16ByteMacKey> and a value phi: F, derives an
//! output_mac_key: Vec<BitGroupMac<F>>.
//!
//! Recall that for a DigitMACKey, all its component BitMacKeys must share the
//! same `phi`.
//!
//! This is generic over digits in Fq, Fq2.

use crate::{
    garble::{Circuit, Nonce, bit_adaptor},
    mac::{
        Random,
        bit::{bytes::Bit16ByteMac, group::BitGroupMac},
        digit::{bytes, group},
    },
    utils::{
        aes_hash::aes_ctr::AesCtr,
        bits::{FromBits, NumBits, ToBits},
        error::{EvalError, GarbleError},
        group::FromLeBytesModOrder,
    },
};
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand_core::CryptoRngCore;

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub(crate) struct Table<F>(Vec<bit_adaptor::Table<AesCtr, Bit16ByteMac, BitGroupMac<F>>>)
where
    F: Field + NumBits + FromBits<bool, F> + Random,
    F::BasePrimeField: FromLeBytesModOrder;

impl<F> Table<F>
where
    F: Field + NumBits + FromBits<bool, F> + Random,
    F::BasePrimeField: FromLeBytesModOrder,
{
    /// Whether there is one well-formed bit adaptor per bit of `F`.
    pub(crate) fn has_garbled_shape(&self) -> bool {
        self.0.len() == F::NUM_BITS && self.0.iter().all(|table| table.has_garbled_shape())
    }
}

pub(crate) type Input<F> = F;
pub(crate) type InputMac<F> = bytes::DigitMac<F>;
pub(crate) type InputMacKey<F> = bytes::DigitMacKey<F>;

pub(crate) type Output<F> = F;
pub(crate) type OutputMac<F> = group::DigitMac<F>;
pub(crate) type OutputMacKey<F> = group::DigitMacKey<F>;

impl<F> Circuit<Input<F>, InputMac<F>, Output<F>, OutputMac<F>> for Table<F>
where
    F: Field + NumBits + ToBits + FromBits<F, F> + FromBits<bool, F> + Random,
    F::BasePrimeField: FromLeBytesModOrder,
{
    type Aux = F;

    #[inline(never)]
    fn garble(
        parent_nonce: &mut Nonce,
        rng: &mut impl CryptoRngCore,
        aux: Option<Self::Aux>,
        input_mac_key: &InputMacKey<F>,
    ) -> Result<(Self, OutputMacKey<F>), GarbleError> {
        let mut nonce = parent_nonce.fork()?;

        let mut bit_adaptor_tables = Vec::with_capacity(F::NUM_BITS);
        let mut output_mac_keys = Vec::with_capacity(F::NUM_BITS);

        for input_key in input_mac_key.iter() {
            let (table, output_mac_key) =
                bit_adaptor::Table::garble(&mut nonce, rng, aux, input_key)?;
            bit_adaptor_tables.push(table);
            output_mac_keys.push(output_mac_key);
        }

        Ok((Self(bit_adaptor_tables), output_mac_keys.into()))
    }

    fn evaluate(
        &self,
        parent_nonce: &mut Nonce,
        input: &F,
        input_mac: &InputMac<F>,
    ) -> Result<(F, OutputMac<F>), EvalError> {
        let mut nonce = parent_nonce.fork()?;

        let input_bits = input.to_bits();
        let mut bit_group_macs = Vec::with_capacity(F::NUM_BITS);

        for ((input, input_mac), table) in input_bits
            .iter()
            .take(F::NUM_BITS)
            .zip(input_mac.iter())
            .zip(self.0.iter())
        {
            let table = table.evaluate(&mut nonce, input, input_mac)?.1;
            bit_group_macs.push(table);
        }

        Ok((*input, bit_group_macs.into()))
    }
}

#[cfg(test)]
fn test_digit_mac_adaptor<F>()
where
    F: Field + NumBits + ToBits + FromBits<F, F> + FromBits<bool, F> + Random,
    F::BasePrimeField: FromLeBytesModOrder,
{
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    use crate::{mac::MacKey, utils::aes_hash::aes_ctr::clear_set};

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    let input = F::rand(&mut rng);
    let output = input;

    let input_mac_key = bytes::DigitMacKey::random_key(&mut rng);
    let phi = F::rand(&mut rng);

    let input_mac = input_mac_key.encode(&input);

    let (table, output_mac_key) =
        Table::garble(&mut Nonce::new(), &mut rng, Some(phi), &input_mac_key).unwrap();
    clear_set();
    assert!(table.has_garbled_shape());

    let expected_output_mac = output_mac_key.encode(&output);
    let evaluated_output_mac = table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .1;
    clear_set();

    assert_eq!(expected_output_mac, evaluated_output_mac);
}

#[test]
fn test_digit_mac_adaptor_fq() {
    use ark_bn254::Fq;
    test_digit_mac_adaptor::<Fq>();
}

#[test]
fn test_digit_mac_adaptor_fp2() {
    use ark_bn254::Fq2;
    test_digit_mac_adaptor::<Fq2>();
}
