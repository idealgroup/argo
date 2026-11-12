//! DigitMac of a field element, where each bit is encoded as a Bit16ByteMac.

use ark_ff::{AdditiveGroup, Field};
use rand_core::CryptoRngCore;

use crate::{
    garble::{Nonce, bit_adaptor::DeriveOutputMacKey},
    mac::{
        Mac, MacKey, Random,
        bit::{
            bytes::{Bit16ByteMac, Bit16ByteMacKey},
            group::BitGroupMac,
        },
    },
    utils::{
        aes_hash::aes_ctr::AesCtr,
        bits::{FromBits, NumBits, ToBits},
        error::GarbleError,
        group::FromLeBytesModOrder,
    },
};

pub(crate) type DigitMac<G> = super::DigitMac<G, Bit16ByteMac>;
pub(crate) type DigitMacKey<G> = super::DigitMacKey<G, Bit16ByteMac>;

impl<G> Mac<G::Scalar> for DigitMac<G>
where
    G: AdditiveGroup + FromBits<G, G> + Random,
    G::Scalar: ToBits + NumBits + FromBits<G::Scalar, G::Scalar>,
{
    type Key = DigitMacKey<G>;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> G::Scalar {
        use ark_std::UniformRand;
        G::Scalar::rand(rng)
    }
}

impl<G> MacKey<G::Scalar, DigitMac<G>> for DigitMacKey<G>
where
    G: AdditiveGroup + FromBits<G, G> + Random,
    G::Scalar: ToBits + NumBits + FromBits<G::Scalar, G::Scalar>,
{
    fn encode(&self, value: &G::Scalar) -> DigitMac<G> {
        let mut macs = Vec::with_capacity(G::Scalar::NUM_BITS);
        value
            .to_bits()
            .iter()
            .zip(self.iter())
            .for_each(|(bit, key)| macs.push(key.encode(bit)));

        DigitMac::from(macs)
    }

    #[cfg(test)]
    fn decode(&self, mac: &DigitMac<G>) -> G::Scalar {
        G::Scalar::from_bits(
            self.iter()
                .zip(mac.iter())
                .map(|(key, mac)| G::Scalar::from(key.decode(mac))),
        )
        .unwrap()
    }

    fn random_key(rng: &mut impl CryptoRngCore) -> Self {
        let mut bit_mac_keys = Vec::with_capacity(G::Scalar::NUM_BITS);
        for _ in 0..G::Scalar::NUM_BITS {
            bit_mac_keys.push(Bit16ByteMacKey::random_key(rng));
        }
        bit_mac_keys.into()
    }
}

impl<G> DeriveOutputMacKey<AesCtr, G::Scalar, G::Scalar, DigitMac<G>, super::group::DigitMac<G>>
    for DigitMacKey<G>
where
    G: Field,
    G::BasePrimeField: FromLeBytesModOrder,
    G::Scalar: ToBits + NumBits + FromBits<G::Scalar, G::Scalar> + Random,
{
    type Phi = G;

    fn derive_output_mac_key(
        &self,
        dst: Option<&[u8; 16]>,
        parent_nonce: &Nonce,
        phi: &G,
    ) -> Result<super::group::DigitMacKey<G>, GarbleError> {
        let mut group_mac_keys = Vec::with_capacity(self.len());

        for input_key in self.iter() {
            let key = <Bit16ByteMacKey as DeriveOutputMacKey<
                AesCtr,
                bool,
                bool,
                Bit16ByteMac,
                BitGroupMac<G>,
            >>::derive_output_mac_key(input_key, dst, parent_nonce, phi)?;
            group_mac_keys.push(key);
        }

        Ok(group_mac_keys.into())
    }
}
