//! This gadget is defined over a fixed constant `p` of length `n` bits.
//! It takes an input value and input MAC in bits (a_0, a_1, ..., a_{n-1}), and
//! reveals a secret if the input is not less than `p`.
//!
//! a_0 = false
//! a_i = (x_i + p_i) p_i + (1 + x_i + p_i) a_(i-1)
//!     = (x_i + p_i) (a_(i-1) + p_i) + a_(i-1)
//!
//! If x_i + p_i = true then x_i != p_i so return p_i = “x < p”
//! If x_i + p_i = false then x_i = p_i and x_i + p_i + 1 = true so we recurse
//! on the next bit
//! a_i is true if x truncated to i+1 bits is less than p truncated to i+1 bits
//! return a_{n-1}
//!
//! Constant wire ONE = phi + k
//! “at compile time” use the ONE wire if p_i = 1
//! y ~ NOT(x) then replace with y ~ XOR(x, ONE)
//!
//! Encrypt the secret under the MAC of 0

use std::{any::type_name, marker::PhantomData};

use ark_bn254::Fq;
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::RngCore;

#[cfg(test)]
use ark_bn254::Fr;
#[cfg(test)]
use ark_std::rand::{SeedableRng, rngs::StdRng};

use crate::{
    garble::{Circuit, bit_adaptor, groth16_verifier::GID},
    mac::{
        IdentityMac, IdentityMacKey, MacKey, Random, RandomFromPhi,
        bit::bytes::{Bit16ByteMac, Bit16ByteMacKey},
        digit::bytes::{DigitMac, DigitMacKey},
    },
    utils::{
        aes_hash::aes_ctr::AesCtr,
        bits::{FromBits, NumBits, ToBits},
        error::{EvalError, GarbleError},
    },
};

pub(crate) mod gate;

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct Table<F>
where
    F: PrimeField + FromBits<F, F> + Random + ToBits + NumBits,
{
    zero_mac: Bit16ByteMac,
    one_mac: Bit16ByteMac,
    adaptors: Vec<bit_adaptor::Table<AesCtr, Bit16ByteMac, Bit16ByteMac>>,
    gates: Vec<gate::Table>,
    enc_s: Fq,
    gid: GID,
    _marker: PhantomData<F>,
}

impl<F> Circuit<F, DigitMac<F>, Fq, IdentityMac<Fq>> for Table<F>
where
    F: PrimeField + FromBits<F, F> + Random + ToBits + NumBits,
{
    type Aux = (Fq, GID);

    fn garble(
        parent_nonce: &mut crate::garble::Nonce,
        rng: &mut ark_std::rand::prelude::StdRng,
        aux: Option<Self::Aux>,
        input_mac_key: &DigitMacKey<F>,
    ) -> Result<(Self, IdentityMacKey), GarbleError> {
        let mut nonce = parent_nonce.fork();
        let (secret, gid) = aux
            .ok_or_else(|| GarbleError::AuxError(type_name::<Self::Aux>(), type_name::<Self>()))?;

        let mut phi = [0; 16];
        rng.fill_bytes(&mut phi);

        let zero_mac_key = Bit16ByteMacKey::random_from_phi(rng, &phi);
        let one_mac_key = Bit16ByteMacKey::random_from_phi(rng, &phi);
        let p_bits = F::MODULUS.to_bits_le();

        // Adapt input to use a bits_mac_key with all the same `phi`s
        let adaptors: (Vec<_>, Vec<_>) = {
            input_mac_key
                .iter()
                .map(|input_mac_key| {
                    bit_adaptor::Table::garble(&mut nonce, rng, Some(phi), input_mac_key)
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .unzip()
        };

        let mut output_mac_key = zero_mac_key;
        let mut gates = Vec::with_capacity(input_mac_key.len());

        for (p, x_mac_key) in p_bits.iter().zip(adaptors.1.iter()) {
            let p_mac_key = if *p { one_mac_key } else { zero_mac_key };
            let input_mac_key = gate::InputMacKey {
                x: *x_mac_key,
                p: p_mac_key,
                a: output_mac_key,
            };

            let (gate, mac_key) = gate::Table::garble(&mut nonce, rng, Some(gid), &input_mac_key)?;

            output_mac_key = mac_key;

            gates.push(gate);
        }

        let enc_s = {
            let mac_false = output_mac_key.encode(&false);
            let pad: Fq = AesCtr::hash_to_field(*mac_false, &nonce);

            secret + pad
        };

        let table = Self {
            zero_mac: zero_mac_key.encode(&false),
            one_mac: one_mac_key.encode(&true),
            adaptors: adaptors.0,
            gates,
            enc_s,
            gid,
            _marker: PhantomData,
        };

        Ok((table, IdentityMacKey))
    }

    fn evaluate(
        &self,
        parent_nonce: &mut crate::garble::Nonce,
        input: &F,
        input_mac: &DigitMac<F>,
    ) -> Result<(Fq, IdentityMac<Fq>), EvalError> {
        let secret = self.evaluate_bits(parent_nonce, &input.to_bits(), input_mac)?;
        Ok((secret, IdentityMac(PhantomData)))
    }
}

impl<F> Table<F>
where
    F: PrimeField + FromBits<F, F> + Random + ToBits + NumBits,
{
    /// Evaluates on raw input bits, which may spell a value at or above the
    /// modulus that no `F` can hold.
    pub(crate) fn evaluate_bits(
        &self,
        parent_nonce: &mut crate::garble::Nonce,
        input_bits: &[bool],
        input_mac: &DigitMac<F>,
    ) -> Result<Fq, EvalError> {
        let mut nonce = parent_nonce.fork();

        let p_bits = F::MODULUS.to_bits_le();

        let mut x_mac = Vec::with_capacity(input_bits.len());
        for ((adaptor, input), input_mac) in self
            .adaptors
            .iter()
            .zip(input_bits.iter())
            .zip(input_mac.iter())
        {
            let mac = adaptor.evaluate(&mut nonce, input, input_mac)?;
            x_mac.push(mac);
        }

        let mut output = false;
        let mut output_mac = self.zero_mac;
        for ((gate, p), x) in self.gates.iter().zip(p_bits.iter()).zip(x_mac) {
            let input = gate::Input {
                x: x.0,
                p: *p,
                a: output,
            };

            let input_mac = gate::InputMac {
                x: x.1,
                p: if *p { self.one_mac } else { self.zero_mac },
                a: output_mac,
            };

            let (res, res_mac) = gate.evaluate(&mut nonce, &input, &input_mac)?;

            output = res;
            output_mac = res_mac;
        }

        let pad: Fq = AesCtr::hash_to_field(*output_mac, &nonce);
        Ok(self.enc_s - pad)
    }
}

#[cfg(test)]
fn less_than<F>(secret: Fq, input: &F) -> Fq
where
    F: PrimeField + FromBits<F, F> + Random + ToBits + NumBits,
{
    use crate::{
        garble::{Nonce, bit_adaptor::clear_set as bit_adaptor_clear_set},
        mac::digit::DigitMacKey,
        utils::aes_hash::{
            aes_ctr::clear_set as aes_ctr_clear_set, aes_mitccr::clear_set as aes_mitccr_clear_set,
        },
    };

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    let gid = GID::random(&mut rng);

    let input_mac_key = DigitMacKey::<F, Bit16ByteMac>::random_key(&mut rng);
    let input_mac = input_mac_key.encode(input);

    let table = Table::<F>::garble(
        &mut Nonce::new(),
        &mut rng,
        Some((secret, gid)),
        &input_mac_key,
    )
    .unwrap()
    .0;
    aes_ctr_clear_set();
    aes_mitccr_clear_set();
    bit_adaptor_clear_set();

    let output = table
        .evaluate(&mut Nonce::new(), input, &input_mac)
        .unwrap()
        .0;
    aes_ctr_clear_set();
    aes_mitccr_clear_set();
    bit_adaptor_clear_set();

    output
}

#[cfg(test)]
/// We should not recover the secret from a valid field element.
fn valid_less_than<F>()
where
    F: PrimeField + FromBits<F, F> + Random + ToBits + NumBits,
{
    const SEED: u64 = 0;
    let mut rng = StdRng::seed_from_u64(SEED);

    let input = F::random(&mut rng);
    let secret = Fq::random(&mut rng);

    let output = less_than::<F>(secret, &input);
    assert_ne!(output, secret);
}

#[cfg(test)]
/// We should recover the secret from an invalid field element.
fn invalid_less_than<F>(input: &F)
where
    F: PrimeField + FromBits<F, F> + Random + ToBits + NumBits,
{
    const SEED: u64 = 0;
    let mut rng = StdRng::seed_from_u64(SEED);

    let secret = Fq::random(&mut rng);

    let output = less_than::<F>(secret, input);
    assert_eq!(output, secret);
}

#[test]
fn test_valid() {
    valid_less_than::<Fr>();
    valid_less_than::<Fq>();
}

#[test]
fn test_invalid() {
    invalid_less_than::<Fr>(&Fr::new_unchecked(Fr::MODULUS));
    invalid_less_than::<Fq>(&Fq::new_unchecked(Fq::MODULUS));
}
