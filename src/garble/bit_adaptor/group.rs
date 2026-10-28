use std::any::type_name;

use aes::{Block, cipher::BlockEncrypt};
use ark_ff::{BigInteger, Field, PrimeField};
use rand_core::CryptoRngCore;

use crate::{
    garble::{
        Circuit, Nonce,
        bit_adaptor::{DeriveOutputMacKey, Table},
    },
    mac::{
        Encrypt, MacKey, Random,
        bit::{
            bytes::{Bit16ByteMac, Bit16ByteMacKey},
            group::BitGroupMac,
        },
        group::GroupMacKey,
    },
    utils::{
        aes_hash::{AES_BLOCK_SIZE, aes_ctr::AesCtr},
        error::{EvalError, GarbleError},
        group::FromLeBytesModOrder,
    },
};

/// Given an input_mac_key: Bit16ByteMacKey and a group element phi: G,
/// derive an output_mac_key: GroupMacKey with s.t.
/// - output_mac_key.phi = phi, and
/// - output_mac_key.k = hash(input_mac_key.encode(false)).
impl<G> DeriveOutputMacKey<AesCtr, bool, bool, Bit16ByteMac, BitGroupMac<G>> for Bit16ByteMacKey
where
    G: Field + Random,
    G::BasePrimeField: FromLeBytesModOrder,
{
    type Phi = G;

    fn derive_output_mac_key(
        &self,
        _dst: Option<&[u8; 16]>,
        parent_nonce: &Nonce,
        phi: &G,
    ) -> Result<GroupMacKey<G>, GarbleError> {
        let mac = self.encode(&false);
        let k = AesCtr::hash_to_field(*mac, parent_nonce);

        Ok(GroupMacKey { phi: *phi, k })
    }
}

impl<G> Table<AesCtr, Bit16ByteMac, BitGroupMac<G>>
where
    G: Field + Random,
    G::BasePrimeField: FromLeBytesModOrder,
{
    /// Whether the ciphertext holds exactly one encrypted `G`.
    pub(crate) fn has_garbled_shape(&self) -> bool {
        self.gid.is_none() && self.ciphertext.len() == AesCtr::num_blocks::<G>() * AES_BLOCK_SIZE
    }
}

/// A bit adaptor table mapping from a Bit16ByteMac to a BitGroupMac.
impl<G> Circuit<bool, Bit16ByteMac, bool, BitGroupMac<G>>
    for Table<AesCtr, Bit16ByteMac, BitGroupMac<G>>
where
    G: Field + Random,
    G::BasePrimeField: FromLeBytesModOrder,
{
    type Aux = G;

    fn garble(
        parent_nonce: &mut Nonce,
        _rng: &mut impl CryptoRngCore,
        aux: Option<Self::Aux>,
        input_mac_key: &Bit16ByteMacKey,
    ) -> Result<(Self, GroupMacKey<G>), GarbleError> {
        let mut nonce = parent_nonce.fork();
        // The chosen `phi` for the output_mac_key.
        let phi = aux
            .ok_or_else(|| GarbleError::AuxError(type_name::<Self::Aux>(), type_name::<Self>()))?;

        // The output_mac_key is derived s.t.
        // - output_mac_key.phi = phi, and
        // - output_mac_key.k = hash(input_mac_key.encode(false)).
        let output_mac_key = <Bit16ByteMacKey as DeriveOutputMacKey<
            AesCtr,
            bool,
            bool,
            Bit16ByteMac,
            BitGroupMac<G>,
        >>::derive_output_mac_key(input_mac_key, None, &nonce, &phi)?;

        // We encrypt the encoding of output_mac_key.encode(true), using
        // input_mac_key.encode(true) as the key. This ciphertext is stored
        // in the bit adaptor garbling table.
        let key = input_mac_key.encode(&true);
        let msg = output_mac_key.encode(&true);
        let ciphertext = key.encrypt(None, &mut nonce, &msg)?;

        #[cfg(test)]
        // Check that each ciphertext is unique.
        assert!(super::CIPHERTEXT_SET.with(|set| set.borrow_mut().insert(ciphertext.to_vec())));

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
    ) -> Result<(bool, BitGroupMac<G>), EvalError> {
        let mut nonce = parent_nonce.fork();

        let output_mac = if !(*input) {
            // If the input is `false`, the `output_mac` will be
            //                  phi * 0 + k = k;
            // but since output_mac_key.k = hash(input_mac_key.encode(false)),
            // we can directly derive `k` by hashing the `input_mac`.
            AesCtr::hash_to_field::<G>(**input_mac, &nonce).into()
        } else {
            // If the input is `true`, we have to decrypt the table entry
            // using the `input_mac` as a key, to recover the plaintext
            // `output_mac`.
            input_mac.decrypt(None, &mut nonce, &self.ciphertext)?
        };

        Ok((*input, output_mac))
    }
}

impl<G> Encrypt<AesCtr, BitGroupMac<G>> for Bit16ByteMac
where
    G: Field,
    G::BasePrimeField: FromLeBytesModOrder,
{
    type Ciphertext = Vec<u8>;

    /// Encrypts a BitGroupMac(G) using a Bit16ByteMac([u8; 16]) as the key.
    /// Produces a ciphertext Vec<u8> of the same length as the number of
    /// bytes in `G`.
    ///
    /// # Panics
    ///
    /// Panics if AesCtr::num_blocks::<G>() > 32.
    fn encrypt(
        &self,
        _dst: Option<&[u8]>,
        parent_nonce: &mut Nonce,
        message: &BitGroupMac<G>,
    ) -> Result<Self::Ciphertext, GarbleError> {
        let num_blocks = AesCtr::num_blocks::<G>();
        let mut ciphertext = vec![0u8; num_blocks * AES_BLOCK_SIZE];

        let aes = AesCtr::get_instance(self);

        // Generate keystream
        for i in 0..num_blocks {
            let nonce = parent_nonce.fork();
            let mut block = Block::from(nonce.bytes());
            aes.encrypt_block(&mut block);

            let start = i * AES_BLOCK_SIZE;
            ciphertext[start..start + AES_BLOCK_SIZE].copy_from_slice(&block);
        }

        // XOR message
        let mut offset = 0;
        for elem in message.to_base_prime_field_elements() {
            let bytes = elem.into_bigint().to_bytes_le();
            let len = bytes.len().min(ciphertext.len() - offset);

            for i in 0..len {
                ciphertext[offset + i] ^= bytes[i];
            }

            offset += len;
            if offset >= ciphertext.len() {
                break;
            }
        }

        Ok(ciphertext)
    }

    fn decrypt(
        &self,
        _dst: Option<&[u8]>,
        parent_nonce: &mut Nonce,
        ciphertext: &Self::Ciphertext,
    ) -> Result<BitGroupMac<G>, EvalError> {
        let num_blocks = AesCtr::num_blocks::<G>();

        // Initialise the plaintext as an empty vector with the desired
        // number of AES blocks.
        let mut plaintext = Vec::with_capacity(num_blocks * AES_BLOCK_SIZE);

        let aes = AesCtr::get_instance(self);

        // Recover the one-time pad used to encrypt the ciphertext.
        (0..num_blocks).for_each(|_| {
            let nonce = parent_nonce.fork();

            let mut block = Block::from(nonce.bytes());
            aes.encrypt_block(&mut block);

            plaintext.extend_from_slice(&block);
        });

        // XOR the ciphertext with the one-time pad to recover the plaintext
        // byte representation of the group element.
        plaintext
            .iter_mut()
            .zip(ciphertext.iter())
            .for_each(|(pad, ciph)| *pad ^= ciph);

        // Cast the plaintext bytes as a group element to recover output_mac.
        G::from_random_bytes(&plaintext)
            .ok_or(EvalError::DecryptionError(type_name::<Self>()))
            .map(|mac| mac.into())
    }
}

#[cfg(test)]
fn test_bytes_to_group_adaptor<G>()
where
    G: Field + Random,
    G::BasePrimeField: FromLeBytesModOrder,
{
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    use crate::{
        mac::{Mac, MacKey},
        utils::aes_hash::aes_ctr::clear_set as aes_ctr_clear_set,
    };

    const N: usize = 100;
    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    for _ in 0..N {
        let input_mac_key = Bit16ByteMacKey::random_key(&mut rng);
        let phi = G::rand(&mut rng);

        let (garbling_table, output_mac_key) =
            Table::<AesCtr, Bit16ByteMac, BitGroupMac<G>>::garble(
                &mut Nonce::new(),
                &mut rng,
                Some(phi),
                &input_mac_key,
            )
            .unwrap();
        aes_ctr_clear_set();
        super::clear_set();
        assert!(garbling_table.has_garbled_shape());

        let input = Bit16ByteMac::random_input(&mut rng);
        let input_mac = input_mac_key.encode(&input);

        let output = input;
        let output_mac: BitGroupMac<G> = output_mac_key.encode(&output);

        let evaluated_output_mac: BitGroupMac<G> = garbling_table
            .evaluate(&mut Nonce::new(), &input, &input_mac)
            .unwrap()
            .1;
        aes_ctr_clear_set();
        super::clear_set();

        assert!(output_mac == evaluated_output_mac);
    }
}

#[test]
fn test_fr() {
    test_bytes_to_group_adaptor::<ark_bn254::Fr>();
}

#[test]
fn test_fq() {
    test_bytes_to_group_adaptor::<ark_bn254::Fq>();
}

#[test]
fn test_fq2() {
    test_bytes_to_group_adaptor::<ark_bn254::Fq2>();
}
