//! Adaptor table using re-keyed AES as instantiation of miTCCR hash function.
//! This can be called when the input MAC key shares the same `phi` with other
//! input MAC keys (i.e. in the free-XOR case).

use std::any::type_name;

use ark_std::rand::rngs::StdRng;

use crate::{
    garble::{
        Circuit, Nonce,
        bit_adaptor::{DeriveOutputMacKey, Table},
        groth16_verifier::GID,
    },
    mac::{
        Encrypt, MacKey,
        bit::bytes::{Bit16ByteMac, Bit16ByteMacKey},
    },
    utils::{
        aes_hash::{AES_BLOCK_SIZE, Hash, aes_mitccr::AesMiTCCR},
        error::{EvalError, GarbleError},
    },
};

impl<Mac1, Mac2> Encrypt<AesMiTCCR, Mac1> for Mac2
where
    Mac1: Clone + Into<Bit16ByteMac> + From<Bit16ByteMac>,
    Mac2: Clone + Into<Bit16ByteMac> + From<Bit16ByteMac>,
{
    type Ciphertext = [u8; 16];

    fn encrypt(
        &self,
        dst: Option<&[u8]>,
        parent_nonce: &mut Nonce,
        message: &Mac1,
    ) -> Result<Self::Ciphertext, GarbleError> {
        let dst = dst.ok_or(GarbleError::MissingDST)?;

        let input_mac: Bit16ByteMac = self.clone().into();
        let output_mac: Bit16ByteMac = message.clone().into();

        let mut key = [0; 16];
        key.iter_mut()
            .zip(dst.iter())
            .zip(parent_nonce.bytes().iter())
            .for_each(|((key, dst), nonce)| *key = dst ^ nonce);

        let mut ciphertext = [0; 16];
        let pad = AesMiTCCR::hash(&key, &input_mac);

        ciphertext
            .iter_mut()
            .zip(pad.iter())
            .zip(output_mac.iter())
            .for_each(|((ciph, pad), msg)| *ciph = pad ^ msg);

        Ok(ciphertext)
    }

    fn decrypt(
        &self,
        dst: Option<&[u8]>,
        parent_nonce: &mut Nonce,
        ciphertext: &Self::Ciphertext,
    ) -> Result<Mac1, EvalError> {
        let dst = dst.ok_or(EvalError::MissingDST)?;
        let input_mac: Bit16ByteMac = self.clone().into();

        let mut key = [0; 16];
        key.iter_mut()
            .zip(dst.iter())
            .zip(parent_nonce.bytes().iter())
            .for_each(|((key, dst), nonce)| *key = dst ^ nonce);

        let mut plaintext = [0; 16];
        let pad = AesMiTCCR::hash(&key, &input_mac);

        plaintext
            .iter_mut()
            .zip(pad.iter())
            .zip(ciphertext.iter())
            .for_each(|((plain, pad), ciphertext)| *plain = pad ^ ciphertext);

        Ok(Bit16ByteMac(plaintext).into())
    }
}

impl DeriveOutputMacKey<AesMiTCCR, bool, bool, Bit16ByteMac, Bit16ByteMac> for Bit16ByteMacKey {
    type Phi = [u8; 16];

    fn derive_output_mac_key(
        &self,
        dst: Option<&[u8; 16]>,
        _nonce: &Nonce,
        phi: &Self::Phi,
    ) -> Result<Bit16ByteMacKey, GarbleError> {
        let dst = dst.ok_or_else(|| GarbleError::DeriveOutputMacKeyError(type_name::<Self>()))?;
        let mac = self.encode(&false);
        let k: [u8; 16] = AesMiTCCR::hash(dst, &mac);

        Ok(Self { phi: *phi, k })
    }
}

pub(crate) struct Aux {
    pub(crate) gid: GID,
    pub(crate) phi: [u8; 16],
}

impl Table<AesMiTCCR, Bit16ByteMac, Bit16ByteMac> {
    pub(crate) fn has_garbled_shape(&self, gid: &GID) -> bool {
        self.gid == Some(*gid)
    }

    pub(crate) fn derive_dst(gid: &GID, nonce: &Nonce) -> [u8; 16] {
        let mut dst = [0; AES_BLOCK_SIZE];
        dst.iter_mut()
            .zip(gid.iter())
            .zip(nonce.bytes().iter())
            .for_each(|((dst, gid), nonce)| *dst = gid ^ nonce);

        dst
    }
}

/// A bit adaptor table mapping from a Bit16ByteMac to a Bit16ByteMac.
impl Circuit<bool, Bit16ByteMac, bool, Bit16ByteMac>
    for Table<AesMiTCCR, Bit16ByteMac, Bit16ByteMac>
{
    type Aux = Aux;

    fn garble(
        parent_nonce: &mut Nonce,
        _rng: &mut StdRng,
        aux: Option<Self::Aux>,
        input_mac_key: &Bit16ByteMacKey,
    ) -> Result<(Self, Bit16ByteMacKey), GarbleError> {
        let Aux { gid, phi } = aux
            .ok_or_else(|| GarbleError::AuxError(type_name::<Self::Aux>(), type_name::<Self>()))?;

        let dst = Self::derive_dst(&gid, parent_nonce);

        // The output_mac_key is derived s.t.
        // - output_mac_key.phi = phi, and
        // - output_mac_key.k = hash(input_mac_key.encode(false)).
        let output_mac_key =
            <Bit16ByteMacKey as DeriveOutputMacKey<
                AesMiTCCR,
                bool,
                bool,
                Bit16ByteMac,
                Bit16ByteMac,
            >>::derive_output_mac_key(input_mac_key, Some(&dst), parent_nonce, &phi)?;

        // We encrypt the encoding of output_mac_key.encode(true), using
        // input_mac_key.encode(true) as the key. This ciphertext is stored
        // in the bit adaptor garbling table.
        let key = input_mac_key.encode(&true);
        let msg = output_mac_key.encode(&true);

        let ciphertext = <Bit16ByteMac as Encrypt<AesMiTCCR, Bit16ByteMac>>::encrypt(
            &key,
            Some(&dst),
            parent_nonce,
            &msg,
        )?;

        #[cfg(test)]
        // Check that each ciphertext is unique.
        assert!(
            super::super::CIPHERTEXT_SET.with(|set| set.borrow_mut().insert(ciphertext.to_vec())),
        );

        Ok((
            Self {
                gid: Some(gid),
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
        let gid = self.gid.ok_or(EvalError::MissingGID(type_name::<Self>()))?;
        let dst = Self::derive_dst(&gid, parent_nonce);

        let output_mac = if !(*input) {
            // If the input is `false`, the `output_mac` will be
            //                  phi * 0 + k = k;
            // but since output_mac_key.k = hash(input_mac_key.encode(false)),
            // we can directly derive `k` by hashing the `input_mac`.
            let hash = AesMiTCCR::hash(&dst, input_mac);
            hash.into()
        } else {
            // If the input is `true`, we have to decrypt the table entry
            // using the `input_mac` as a key, to recover the plaintext
            // `output_mac`.
            <Bit16ByteMac as Encrypt<AesMiTCCR, Bit16ByteMac>>::decrypt(
                input_mac,
                Some(&dst),
                parent_nonce,
                &self.ciphertext,
            )?
        };

        Ok((*input, output_mac))
    }
}

#[test]
fn test_aes_mitccr_bytes_to_bytes_adaptor() {
    use ark_std::rand::SeedableRng;

    use crate::{
        mac::{Mac, MacKey, Random},
        utils::aes_hash::aes_mitccr::clear_set as aes_mitccr_clear_set,
    };

    const N: usize = 100;
    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    for _ in 0..N {
        let input_mac_key = Bit16ByteMacKey::random_key(&mut rng);

        let gid = GID::random(&mut rng);
        let phi = <[u8; 16]>::random(&mut rng);

        let aux = Aux { gid, phi };

        let (garbling_table, output_mac_key) =
            Table::<AesMiTCCR, Bit16ByteMac, Bit16ByteMac>::garble(
                &mut Nonce::new(),
                &mut rng,
                Some(aux),
                &input_mac_key,
            )
            .unwrap();
        aes_mitccr_clear_set();
        super::super::clear_set();
        assert!(garbling_table.has_garbled_shape(&gid));

        let input = Bit16ByteMac::random_input(&mut rng);
        let input_mac = input_mac_key.encode(&input);

        let output = input;
        let output_mac: Bit16ByteMac = output_mac_key.encode(&output);

        let evaluated_output_mac: Bit16ByteMac = garbling_table
            .evaluate(&mut Nonce::new(), &input, &input_mac)
            .unwrap()
            .1;
        aes_mitccr_clear_set();
        super::super::clear_set();

        assert!(output_mac == evaluated_output_mac);
    }
}
