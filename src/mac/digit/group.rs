//! DigitMAC where the underlying BitMACs are group elements.
//! Every BitMAC must use the same `phi`.
//!
//! Taking a pow_two_lincomb of the DigitMac components amounts to computing a
//! MAC of the group element.

use ark_ff::AdditiveGroup;
use rand_core::CryptoRngCore;

use crate::{
    mac::{
        Mac, MacKey, Random, RandomFromPhi,
        bit::group::BitGroupMac,
        group::{GroupMac, GroupMacKey},
    },
    utils::{
        bits::{FromBits, NumBits, ToBits},
        error::{EvalError, GarbleError},
    },
};

pub(crate) type DigitMac<G> = super::DigitMac<G, BitGroupMac<G>>;
pub(crate) type DigitMacKey<G> = super::DigitMacKey<G, BitGroupMac<G>>;

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

impl<G> DigitMac<G>
where
    G: AdditiveGroup + FromBits<G, G> + Random,
{
    pub(crate) fn try_into_group_mac(&self) -> Result<GroupMac<G>, EvalError> {
        G::from_bits(self.iter().map(|mac| **mac))
            .map(|mac| mac.into())
            .ok_or(EvalError::DigitMacReconstructionError)
    }
}

impl<G> DigitMacKey<G>
where
    G: FromBits<G, G> + AdditiveGroup + Random,
{
    #[inline]
    pub(crate) fn from_bits_k(&self) -> Result<G, GarbleError> {
        let ks = self.iter().map(|key| key.k);
        G::from_bits(ks).ok_or(GarbleError::DigitMacKeyReconstructionError)
    }

    pub(crate) fn try_into_group_mac_key(&self) -> Option<GroupMacKey<G>> {
        let k = G::from_bits(self.iter().map(|key| key.k));

        k.map(|k| GroupMacKey {
            phi: self[0].phi,
            k,
        })
    }
}

impl<G> RandomFromPhi<G::Scalar, DigitMac<G>> for DigitMacKey<G>
where
    G: AdditiveGroup + FromBits<G, G> + Random,
    G::Scalar: ToBits + NumBits + FromBits<G::Scalar, G::Scalar>,
{
    type Phi = G;

    fn random_from_phi(rng: &mut impl CryptoRngCore, phi: &Self::Phi) -> Self {
        let mut keys = Vec::with_capacity(G::Scalar::NUM_BITS);
        for _ in 0..G::Scalar::NUM_BITS {
            keys.push(<GroupMacKey<G> as RandomFromPhi<bool, _>>::random_from_phi(
                rng, phi,
            ));
        }
        keys.into()
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
        let phi = <Self as RandomFromPhi<_, _>>::Phi::random(rng);
        Self::random_from_phi(rng, &phi)
    }
}
