use ark_ff::AdditiveGroup;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use derive_more::{Deref, From};
use rand_core::CryptoRngCore;

use crate::mac::{Mac, MacKey, Random, RandomFromPhi, group::GroupMacKey};

/// MAC from a bit to an additive group element
#[derive(Debug, Clone, Copy, CanonicalSerialize, CanonicalDeserialize, From, Deref)]
pub(crate) struct BitGroupMac<G: AdditiveGroup>(G);

impl<G> RandomFromPhi<bool, BitGroupMac<G>> for GroupMacKey<G>
where
    G: AdditiveGroup + Random,
{
    type Phi = G;

    fn random_from_phi(rng: &mut impl CryptoRngCore, phi: &Self::Phi) -> Self {
        let k = G::rand(rng);
        Self { phi: *phi, k }
    }
}

impl<G> MacKey<bool, BitGroupMac<G>> for GroupMacKey<G>
where
    G: AdditiveGroup + Random,
{
    fn encode(&self, value: &bool) -> BitGroupMac<G> {
        if *value {
            (self.phi + self.k).into()
        } else {
            self.k.into()
        }
    }

    #[cfg(test)]
    fn decode(&self, mac: &BitGroupMac<G>) -> bool {
        if **mac == self.phi + self.k {
            true
        } else if **mac == self.k {
            false
        } else {
            panic!()
        }
    }

    fn random_key(rng: &mut impl CryptoRngCore) -> Self {
        let phi = G::rand(rng);
        <Self as RandomFromPhi<bool, BitGroupMac<G>>>::random_from_phi(rng, &phi)
    }
}

impl<G> Mac<bool> for BitGroupMac<G>
where
    G: AdditiveGroup + Random,
{
    type Key = GroupMacKey<G>;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> bool {
        use ark_std::rand::Rng;
        rng.gen_bool(0.5)
    }
}

impl<G: AdditiveGroup> PartialEq for BitGroupMac<G> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
