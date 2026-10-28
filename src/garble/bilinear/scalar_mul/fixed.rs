use std::{any::type_name, marker::PhantomData};

use ark_ec::{
    AdditiveGroup, CurveConfig, CurveGroup, PrimeGroup, ScalarMul,
    scalar_mul::glv::GLVConfig,
    short_weierstrass::{Affine, Projective},
};
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use rand_core::CryptoRngCore;

use crate::{
    garble::{Circuit, Nonce, bit_adaptor},
    mac::{
        IteratedMac, MacKey, Random, RandomFromPhi,
        bit::{bytes::Bit16ByteMac, group::BitGroupMac},
        ddh::{DDHMac, DDHMacKey},
        digit::{bytes, group},
        endo::{EndoMac, EndoMacKey, EndoScalar, PSqModR},
        group::GroupMacKey,
    },
    utils::{
        aes_hash::aes_ctr::AesCtr,
        bits::{FromBits, NumBits, ToBits},
        error::{EvalError, GarbleError},
        group::FromLeBytesModOrder,
    },
};

pub(crate) type Input<C> = <C as CurveConfig>::ScalarField;
pub(crate) type InputMacKey<C> = bytes::DigitMacKey<<C as CurveConfig>::ScalarField>;
pub(crate) type InputMac<C> = bytes::DigitMac<<C as CurveConfig>::ScalarField>;

pub(crate) type Output<C> = Affine<C>;
pub(crate) type OutputMac<C, const KAPPA: usize> =
    IteratedMac<Affine<C>, EndoMac<C, Affine<C>>, KAPPA>;
// { \phi_i, b • c_i }
pub(crate) type OutputMacKey<C, const KAPPA: usize> = [EndoMacKey<C, Affine<C>>; KAPPA];

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct Table<C: GLVConfig, const KAPPA: usize>
where
    C: GLVConfig,
    C::ScalarField: Random,
    <C::ScalarField as Field>::BasePrimeField: FromLeBytesModOrder,
{
    /// Converts input bit MACs into a DigitMAC, where each bit is MAC'd under
    /// the same `phi`.
    pub(crate) adaptors: Vec<bit_adaptor::Table<AesCtr, Bit16ByteMac, BitGroupMac<C::ScalarField>>>,
    /// The fixed base `P`.
    pub(crate) point: Affine<C>,
    /// S_i = [\phi_i]P + [a • c_i]P
    pub(crate) s: DDHMac<C, KAPPA>,
    /// T_i = [c_i]P
    pub(crate) bilinear_table: super::super::Table<C::ScalarField, C, Affine<C>, KAPPA>,
}

impl<C, const KAPPA: usize> Table<C, KAPPA>
where
    C: GLVConfig + Clone,
    C::ScalarField: Random + NumBits,
    <C::ScalarField as Field>::BasePrimeField: FromLeBytesModOrder,
{
    /// Whether there is one well-formed adaptor per bit of the scalar.
    pub(crate) fn has_garbled_shape(&self) -> bool {
        self.adaptors.len() == C::ScalarField::NUM_BITS
            && self.adaptors.iter().all(|table| table.has_garbled_shape())
    }

    /// Derives an `OutputMacKey: [EndoMacKey; KAPPA]` given an input_mac_key
    /// and an array of `phi`s
    pub(crate) fn output_mac_key_from_phis(
        rng: &mut impl CryptoRngCore,
        input_mac_key: &GroupMacKey<C::ScalarField>,
        phis: &[EndoScalar<C>; KAPPA],
    ) -> ([Affine<C>; KAPPA], OutputMacKey<C, KAPPA>) {
        // Sample `KAPPA` random `t_scalars
        let mut t_scalars = vec![C::ScalarField::ZERO; KAPPA];
        t_scalars.iter_mut().for_each(|t| {
            *t = C::ScalarField::rand(rng);
        });
        // t := [t_scalar]G
        let t = Projective::<C>::generator().batch_mul(&t_scalars);

        // Sample `KAPPA` random `k_scalars` of the form:
        //   input_mac_key.k * t
        let mut k_scalars = vec![C::ScalarField::ZERO; KAPPA];
        k_scalars
            .iter_mut()
            .zip(t_scalars.iter())
            .for_each(|(k, t)| *k = input_mac_key.k * t);

        // k := [k_scalar]G
        let k = Projective::<C>::generator().batch_mul(&k_scalars);

        // Construct the output MAC key using the given `phi`s and the randomly
        // sampled `k_scalars`.
        let mut keys = Vec::with_capacity(KAPPA);
        phis.iter()
            .zip(k_scalars)
            .zip(k)
            .for_each(|((phi, k_scalar), k)| {
                keys.push(EndoMacKey {
                    phi: phi.clone(),
                    k_scalar: Some(k_scalar),
                    k,
                })
            });

        (
            // This unwrap cannot fail since `t` was constructed from arrays of
            // length `KAPPA`.
            t.try_into().unwrap_or_else(|_| panic!()),
            // This unwrap cannot fail since `keys` was constructed from arrays of
            // length `KAPPA`.
            keys.try_into().unwrap_or_else(|_| panic!()),
        )
    }
}

impl<C, const KAPPA: usize> Circuit<Input<C>, InputMac<C>, Output<C>, OutputMac<C, KAPPA>>
    for Table<C, KAPPA>
where
    C: GLVConfig + Clone + PSqModR,
    C::ScalarField: Random + FromBits<C::ScalarField, C::ScalarField> + ToBits + NumBits,
    <C::ScalarField as Field>::BasePrimeField: FromLeBytesModOrder,
    EndoMacKey<C, Affine<C>>: RandomFromPhi<Affine<C>, EndoMac<C, Affine<C>>>,
{
    type Aux = (Affine<C>, [EndoScalar<C>; KAPPA]);

    fn garble(
        parent_nonce: &mut Nonce,
        rng: &mut impl CryptoRngCore,
        aux: Option<Self::Aux>,
        input_mac_key: &InputMacKey<C>,
    ) -> Result<(Self, OutputMacKey<C, KAPPA>), GarbleError> {
        let (point, phis) = aux.ok_or(GarbleError::AuxError(
            type_name::<Self::Aux>(),
            type_name::<Self>(),
        ))?;
        let mut nonce = parent_nonce.fork()?;

        // Adaptor tables for the scalar
        let mut adaptors = Vec::with_capacity(input_mac_key.len());
        // Digit MAC key
        let mut adapted_mac_key = Vec::with_capacity(input_mac_key.len());

        // Sample a random `phi` for the Digit MAC key
        let phi = C::ScalarField::rand(rng);
        for bit_mac_key in input_mac_key.iter() {
            let (table, mac_key) = bit_adaptor::Table::<
                AesCtr,
                Bit16ByteMac,
                BitGroupMac<C::ScalarField>,
            >::garble(&mut nonce, rng, Some(phi), bit_mac_key)?;
            adaptors.push(table);
            adapted_mac_key.push(mac_key);
        }

        let input_mac_key: group::DigitMacKey<C::ScalarField> = adapted_mac_key.into();
        // Reconstruct GroupMacKey from DigitMacKey
        let input_mac_key = input_mac_key
            .try_into_group_mac_key()
            .ok_or(GarbleError::DigitMacKeyReconstructionError)?;

        let (T, output_mac_key) = Self::output_mac_key_from_phis(rng, &input_mac_key, &phis);

        let ddh_mac_key = DDHMacKey {
            T,
            phis,
            a: -input_mac_key.phi,
        };
        let ddh_mac = ddh_mac_key.encode(&point);
        let bilinear_table = super::super::Table {
            T,
            _marker: PhantomData,
        };

        Ok((
            Self {
                adaptors,
                point,
                s: ddh_mac,
                bilinear_table,
            },
            output_mac_key.clone(),
        ))
    }

    fn evaluate(
        &self,
        parent_nonce: &mut Nonce,
        input: &Input<C>,
        input_mac: &InputMac<C>,
    ) -> Result<(Output<C>, OutputMac<C, KAPPA>), EvalError> {
        let mut nonce = parent_nonce.fork()?;

        let mut adapted_input_mac = Vec::with_capacity(self.adaptors.len());

        // Get Digit MAC by evaluating the adaptor tables.
        for ((adaptor, input), input_mac) in self
            .adaptors
            .iter()
            .zip(input.to_bits().iter())
            .zip(input_mac.iter())
        {
            let mac = adaptor.evaluate(&mut nonce, input, input_mac)?.1;
            adapted_input_mac.push(mac);
        }

        // Reconstruct GroupMAC from DigitMAC.
        let input_mac: group::DigitMac<C::ScalarField> = adapted_input_mac.into();
        let input_mac = input_mac.try_into_group_mac()?;

        //   [input_mac] t + [input] s
        let output_mac = self.bilinear_table.evaluate(input, &input_mac, &self.s)?;

        Ok(((self.point * input).into_affine(), output_mac.into()))
    }
}

#[test]
fn test_scalar_mul_fixed() {
    use crate::{
        garble::groth16_verifier::KAPPA_B, mac::MacKey, utils::aes_hash::aes_ctr::clear_set,
    };
    use ark_bn254::{Fr, G1Projective, g1::Config};
    use ark_std::rand::{SeedableRng, rngs::StdRng};
    use std::ops::Mul;

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    let point = G1Projective::rand(&mut rng);
    let input = Fr::rand(&mut rng);

    let input_mac_key = <InputMacKey<Config> as MacKey<Fr, _>>::random_key(&mut rng);
    let phis: [EndoScalar<Config>; KAPPA_B] = (0..KAPPA_B)
        .map(|_| EndoScalar::random(&mut rng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap_or_else(|_| panic!());

    let input_mac = input_mac_key.encode(&input);
    let (circuit, output_mac_key) = Table::garble(
        &mut Nonce::new(),
        &mut rng,
        Some((point.into_affine(), phis)),
        &input_mac_key,
    )
    .unwrap();
    clear_set();
    assert!(circuit.has_garbled_shape());

    let expected_output_mac = output_mac_key.encode(&point.mul(input).into_affine());

    let output_mac = circuit
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .1;
    clear_set();

    assert!(output_mac == expected_output_mac);
}
