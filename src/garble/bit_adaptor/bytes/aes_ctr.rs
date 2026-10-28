//! Adaptor table using fixed-key AesCtr as the hash function. This should only
//! be used when the input MAC key has a unique random `phi`.

use std::any::type_name;

use ark_std::rand::rngs::StdRng;

use crate::{
    garble::{
        Circuit, Nonce,
        bit_adaptor::{DeriveOutputMacKey, Table},
    },
    mac::{
        Encrypt, MacKey,
        bit::bytes::{Bit16ByteMac, Bit16ByteMacKey},
    },
    utils::{
        aes_hash::{Hash, aes_ctr::AesCtr},
        error::{EvalError, GarbleError},
    },
};

impl<Mac1, Mac2> Encrypt<AesCtr, Mac1> for Mac2
where
    Mac1: Clone + Into<Bit16ByteMac> + From<Bit16ByteMac>,
    Mac2: Clone + Into<Bit16ByteMac> + From<Bit16ByteMac>,
{
    type Ciphertext = [u8; 16];

    fn encrypt(
        &self,
        _dst: Option<&[u8]>,
        parent_nonce: &mut Nonce,
        message: &Mac1,
    ) -> Result<Self::Ciphertext, GarbleError> {
        let seed: Bit16ByteMac = self.clone().into();
        let message: Bit16ByteMac = message.clone().into();

        let mut ciphertext = AesCtr::hash(&seed, &parent_nonce.bytes());

        ciphertext
            .iter_mut()
            .zip(message.iter())
            .for_each(|(pad, msg)| *pad ^= msg);

        Ok(ciphertext)
    }

    fn decrypt(
        &self,
        _dst: Option<&[u8]>,
        parent_nonce: &mut Nonce,
        ciphertext: &Self::Ciphertext,
    ) -> Result<Mac1, EvalError> {
        let seed: Bit16ByteMac = self.clone().into();

        let mut plaintext = AesCtr::hash(&seed, &parent_nonce.bytes());

        plaintext
            .iter_mut()
            .zip(ciphertext.iter())
            .for_each(|(pad, ciphertext)| *pad ^= ciphertext);

        Ok(Bit16ByteMac(plaintext).into())
    }
}

impl DeriveOutputMacKey<AesCtr, bool, bool, Bit16ByteMac, Bit16ByteMac> for Bit16ByteMacKey {
    type Phi = [u8; 16];

    fn derive_output_mac_key(
        &self,
        _dst: Option<&[u8; 16]>,
        nonce: &Nonce,
        phi: &Self::Phi,
    ) -> Result<Bit16ByteMacKey, GarbleError> {
        let mac = self.encode(&false);
        let k = AesCtr::hash(&mac, &nonce.bytes());

        Ok(Self { phi: *phi, k })
    }
}

impl Table<AesCtr, Bit16ByteMac, Bit16ByteMac> {
    pub(crate) fn has_garbled_shape(&self) -> bool {
        self.gid.is_none()
    }
}

/// A bit adaptor table mapping from a Bit16ByteMac to a Bit16ByteMac.
impl Circuit<bool, Bit16ByteMac, bool, Bit16ByteMac> for Table<AesCtr, Bit16ByteMac, Bit16ByteMac> {
    type Aux = [u8; 16];

    fn garble(
        parent_nonce: &mut Nonce,
        _rng: &mut StdRng,
        aux: Option<Self::Aux>,
        input_mac_key: &Bit16ByteMacKey,
    ) -> Result<(Self, Bit16ByteMacKey), GarbleError> {
        let phi = aux
            .ok_or_else(|| GarbleError::AuxError(type_name::<Self::Aux>(), type_name::<Self>()))?;

        // The output_mac_key is derived s.t.
        // - output_mac_key.phi = phi, and
        // - output_mac_key.k = hash(input_mac_key.encode(false)).
        let output_mac_key =
            <Bit16ByteMacKey as DeriveOutputMacKey<
                AesCtr,
                bool,
                bool,
                Bit16ByteMac,
                Bit16ByteMac,
            >>::derive_output_mac_key(input_mac_key, None, parent_nonce, &phi)?;

        // We encrypt the encoding of output_mac_key.encode(true), using
        // input_mac_key.encode(true) as the key. This ciphertext is stored
        // in the bit adaptor garbling table.
        let key = input_mac_key.encode(&true);
        let msg = output_mac_key.encode(&true);

        let ciphertext = <Bit16ByteMac as Encrypt<AesCtr, Bit16ByteMac>>::encrypt(
            &key,
            None,
            parent_nonce,
            &msg,
        )?;

        #[cfg(test)]
        // Check that each ciphertext is unique.
        assert!(
            super::super::CIPHERTEXT_SET.with(|set| set.borrow_mut().insert(ciphertext.to_vec()))
        );

        Ok((
            Self {
                gid: None,
                ciphertext,
            },
            output_mac_key,
        ))
    }

    fn evaluate(
        &self,
        parent_nonce: &mut Nonce,
        input: &bool,
        input_mac: &Bit16ByteMac,
    ) -> Result<(bool, Bit16ByteMac), EvalError> {
        let output_mac = if !(*input) {
            // If the input is `false`, the `output_mac` will be
            //                  phi * 0 + k = k;
            // but since output_mac_key.k = hash(input_mac_key.encode(false)),
            // we can directly derive `k` by hashing the `input_mac`.
            let hash = AesCtr::hash(input_mac, &parent_nonce.bytes());
            hash.into()
        } else {
            // If the input is `true`, we have to decrypt the table entry
            // using the `input_mac` as a key, to recover the plaintext
            // `output_mac`.
            <Bit16ByteMac as Encrypt<AesCtr, Bit16ByteMac>>::decrypt(
                input_mac,
                None,
                parent_nonce,
                &self.ciphertext,
            )?
        };

        Ok((*input, output_mac))
    }
}

#[test]
fn test_aes_ctr_bytes_to_bytes_adaptor() {
    use ark_std::rand::SeedableRng;

    use crate::{
        mac::{Mac, MacKey, Random},
        utils::aes_hash::aes_ctr::clear_set as aes_ctr_clear_set,
    };

    const N: usize = 100;
    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    for _ in 0..N {
        let input_mac_key = Bit16ByteMacKey::random_key(&mut rng);
        let phi = <[u8; 16]>::random(&mut rng);

        let (garbling_table, output_mac_key) = Table::<AesCtr, Bit16ByteMac, Bit16ByteMac>::garble(
            &mut Nonce::new(),
            &mut rng,
            Some(phi),
            &input_mac_key,
        )
        .unwrap();
        aes_ctr_clear_set();
        super::super::clear_set();
        assert!(garbling_table.has_garbled_shape());

        let input = Bit16ByteMac::random_input(&mut rng);
        let input_mac = input_mac_key.encode(&input);

        let output = input;
        let output_mac: Bit16ByteMac = output_mac_key.encode(&output);

        let evaluated_output_mac: Bit16ByteMac = garbling_table
            .evaluate(&mut Nonce::new(), &input, &input_mac)
            .unwrap()
            .1;
        aes_ctr_clear_set();
        super::super::clear_set();

        assert!(output_mac == evaluated_output_mac);
    }
}
