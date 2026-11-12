use std::{marker::PhantomData, ops::Neg};

use ark_bn254::{Fq, Fq2, Fr};
use ark_ff::UniformRand;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use derive_more::Deref;
use rand_core::CryptoRngCore;

use crate::{
    garble::Nonce,
    utils::{
        aes_hash::Hash,
        error::{EvalError, GarbleError},
    },
};

pub(crate) mod binary;
pub(crate) mod bit;
pub(crate) mod ddh;
pub(crate) mod digit;
pub mod endo;
pub(crate) mod group;

pub trait Mac<Value>: Sized {
    // phi, k
    type Key: MacKey<Value, Self>;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> Value;
}

pub trait MacKey<V, M> {
    // phi * value + k
    fn encode(&self, value: &V) -> M;
    #[cfg(test)]
    fn decode(&self, mac: &M) -> V;
    fn random_key(rng: &mut impl CryptoRngCore) -> Self;
}

pub trait RandomFromPhi<V, M>: MacKey<V, M> {
    type Phi: Random;

    fn random_from_phi(rng: &mut impl CryptoRngCore, phi: &Self::Phi) -> Self;
}

pub trait Encrypt<H: Hash, Message> {
    type Ciphertext: CanonicalDeserialize + CanonicalSerialize;

    fn encrypt(
        &self,
        dst: Option<&[u8]>,
        parent_nonce: &mut Nonce,
        message: &Message,
    ) -> Result<Self::Ciphertext, GarbleError>;

    fn decrypt(
        &self,
        dst: Option<&[u8]>,
        parent_nonce: &mut Nonce,
        ciphertext: &Self::Ciphertext,
    ) -> Result<Message, EvalError>;
}

#[derive(Deref, Clone, CanonicalDeserialize, CanonicalSerialize)]
pub struct IteratedMac<Value, M, const N: usize>
where
    Value: Sync + Send,
    M: Mac<Value> + CanonicalDeserialize + CanonicalSerialize,
{
    #[deref]
    pub(crate) value: [M; N],
    _marker: PhantomData<Value>,
}

impl<Value, M, const N: usize> Neg for IteratedMac<Value, M, N>
where
    Value: Sync + Send,
    M: Mac<Value> + Clone + Neg<Output = M> + CanonicalDeserialize + CanonicalSerialize,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        let mut value = self.value;
        value.iter_mut().for_each(|v| {
            *v = -v.clone();
        });

        value.into()
    }
}

impl<Value, M, const N: usize> From<[M; N]> for IteratedMac<Value, M, N>
where
    Value: Sync + Send,
    M: Mac<Value> + CanonicalDeserialize + CanonicalSerialize,
{
    fn from(value: [M; N]) -> Self {
        Self {
            value,
            _marker: PhantomData,
        }
    }
}

impl<Value, M, const N: usize> PartialEq for IteratedMac<Value, M, N>
where
    Value: Sync + Send,
    M: PartialEq + Mac<Value> + CanonicalDeserialize + CanonicalSerialize,
{
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

/// Single value, multiple MAC keys
impl<BaseValue, BaseMac, BaseMacKey, const KAPPA: usize> Mac<BaseValue>
    for IteratedMac<BaseValue, BaseMac, KAPPA>
where
    BaseValue: PartialEq + Clone + Send + Sync,
    BaseMac: Mac<BaseValue, Key = BaseMacKey> + Clone + CanonicalDeserialize + CanonicalSerialize,
    BaseMacKey: MacKey<BaseValue, BaseMac> + Clone + Send + Sync,
{
    type Key = [BaseMacKey; KAPPA];

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> BaseValue {
        BaseMac::random_input(rng)
    }
}

impl<BaseValue, BaseMac, BaseMacKey, const KAPPA: usize>
    MacKey<BaseValue, IteratedMac<BaseValue, BaseMac, KAPPA>> for [BaseMacKey; KAPPA]
where
    BaseMacKey: MacKey<BaseValue, BaseMac> + Send + Sync,
    BaseMac: Mac<BaseValue> + Clone + CanonicalDeserialize + CanonicalSerialize,
    BaseValue: PartialEq + Clone + Send + Sync,
{
    fn encode(&self, value: &BaseValue) -> IteratedMac<BaseValue, BaseMac, KAPPA> {
        let mut macs = Vec::with_capacity(KAPPA);
        self.iter()
            .for_each(|base_key| macs.push(base_key.encode(value)));

        // This unwrap cannot fail because `macs` was constructed by iterating
        // over a fixed array [BaseMacKey; KAPPA].
        let macs: [BaseMac; KAPPA] = macs.try_into().unwrap_or_else(|_| panic!());

        IteratedMac::from(macs)
    }

    #[cfg(test)]
    fn decode(&self, mac: &IteratedMac<BaseValue, BaseMac, KAPPA>) -> BaseValue {
        let mut values = self
            .iter()
            .zip(mac.iter())
            .map(|(key, mac)| key.decode(mac));

        let first_value = values.next().expect("There are no values to decode.");
        assert!(values.all(|value| value == first_value));

        first_value
    }

    fn random_key(rng: &mut impl CryptoRngCore) -> Self {
        let mut keys = Vec::with_capacity(KAPPA);
        for _ in 0..KAPPA {
            keys.push(BaseMacKey::random_key(rng));
        }
        // This unwrap cannot fail because `keys` was constructed in a loop
        // iterating over 0..KAPPA.
        keys.try_into().unwrap_or_else(|_| panic!())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct IdentityMac<V>(pub PhantomData<V>);

#[derive(Debug, Clone)]
pub struct IdentityMacKey;

impl<V, M> MacKey<V, M> for IdentityMacKey {
    fn encode(&self, _value: &V) -> M {
        unimplemented!()
    }

    #[cfg(test)]
    fn decode(&self, _mac: &M) -> V {
        unimplemented!()
    }

    fn random_key(_rng: &mut impl CryptoRngCore) -> Self {
        unimplemented!()
    }
}

impl<V> Mac<V> for IdentityMac<V> {
    type Key = IdentityMacKey;

    #[cfg(test)]
    fn random_input(_rng: &mut impl CryptoRngCore) -> V {
        unimplemented!()
    }
}

pub trait Random {
    fn random(rng: &mut impl CryptoRngCore) -> Self;
}

impl Random for () {
    fn random(_rng: &mut impl CryptoRngCore) -> Self {}
}

impl Random for Fq {
    fn random(rng: &mut impl CryptoRngCore) -> Self {
        Fq::rand(rng)
    }
}

impl Random for Fr {
    fn random(rng: &mut impl CryptoRngCore) -> Self {
        Fr::rand(rng)
    }
}

impl Random for Fq2 {
    fn random(rng: &mut impl CryptoRngCore) -> Self {
        Fq2::rand(rng)
    }
}

impl Random for [u8; 16] {
    fn random(rng: &mut impl CryptoRngCore) -> Self {
        let mut bytes = [0u8; 16];
        rng.fill_bytes(&mut bytes);
        bytes
    }
}
