//! The conditional_reveal table stores the MAC of 1 `one_mac`, and a hash
//! of the secret `enc_s`.
//!
//! When evaluated on an input != one and its MAC, it returns the `secret`.

use ark_bn254::{Bn254, Fq, Fq12, Fr, G1Affine, G2Affine, g2::Config as G2Config};
use ark_ec::{AffineRepr, pairing::Pairing, scalar_mul::glv::GLVConfig};
use ark_ff::{
    AdditiveGroup, BigInteger, Field, Fp12, PrimeField, batch_inversion,
    field_hashers::{DefaultFieldHasher, HashToField},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::{
    garble::groth16_verifier,
    mac::{
        MacKey,
        endo::{ENDO_SIZE, Endo, EndoMacKeyFq12, EndoMacKeyG1, EndoScalar, IteratedEndoMacFq12},
    },
    utils::{
        error::{EvalError, GarbleError},
        try_unwrap_single,
    },
};

/// Input is a single P::TargetField
type Input = Fq12;
pub(crate) type InputMac<const KAPPA: usize> = IteratedEndoMacFq12<KAPPA>;
type InputMacKey<const KAPPA: usize> = [EndoMacKeyFq12; KAPPA];

pub(crate) type Output = Fq;

/// e(G, h)^(2^i) for each bit of Fr, so that e(kG, h) is one `pow_with_table`.
fn target_powers_of_two(h: G2Affine) -> Vec<Fq12> {
    let mut power = Bn254::pairing(G1Affine::generator(), h).0;
    let mut powers = Vec::with_capacity(Fr::MODULUS_BIT_SIZE as usize);
    for _ in 0..Fr::MODULUS_BIT_SIZE {
        powers.push(power);
        power.square_in_place();
    }
    powers
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Table<const KAPPA: usize> {
    pub(crate) one_mac: InputMac<KAPPA>,
    pub enc_s: Fq,
}

impl<const KAPPA: usize> Table<KAPPA> {
    /// Derives the conditional reveal input_mac_key.
    ///
    /// # Panics
    ///
    /// Panics if verifier_key.c == Fq12::ZERO, since `c` must be in the
    /// multiplicative subgroup of Fq12.
    pub(crate) fn groth16_input_mac_key<const N: usize>(
        verifier_key: &groth16_verifier::VerifierKey<N>,
        pairing_output_mac_key: &[EndoMacKeyFq12; KAPPA],
        c_ec_mac_key: &[EndoMacKeyG1; KAPPA],
        x_G_output_mac_keys: &[[EndoMacKeyG1; KAPPA]; N],
    ) -> Result<InputMacKey<KAPPA>, GarbleError> {
        let h1_target_pow_2 = target_powers_of_two(verifier_key.H1);
        // With no garbled inputs there is no e(xG.k, H2) term.
        let h2_target_pow_2 = if N == 0 {
            Vec::new()
        } else {
            target_powers_of_two(verifier_key.H2)
        };

        let mut key = Vec::with_capacity(pairing_output_mac_key.len());

        // e(A,B) e(C, H_1) = c^{-1}
        for (i, (AB, C)) in pairing_output_mac_key
            .iter()
            .zip(c_ec_mac_key.iter())
            .enumerate()
        {
            // All these MAC keys use the same phi
            let phi: EndoScalar<G2Config> = C.phi.clone().into();
            let C_k_scalar = C
                .k_scalar
                .ok_or(GarbleError::MissingKScalar("C"))?
                .into_bigint();

            // e(G, H1)^{C_k_scalar}
            // This unwrap cannot fail because there are enough
            // `h1_target_pow_2` for Fr.
            let C_k_H1 = Fq12::pow_with_table(&h1_target_pow_2, C_k_scalar).unwrap();

            // e(G, H2)^{Σ_l xG_l_k_scalar}
            let xG_k_H2 = if N == 0 {
                Fq12::ONE
            } else {
                let mut xG_k_scalar = Fr::ZERO;
                for keys in x_G_output_mac_keys {
                    xG_k_scalar += keys[i].k_scalar.ok_or(GarbleError::MissingKScalar("x_G"))?;
                }
                // This unwrap cannot fail because there are enough
                // `h2_target_pow_2` for Fr.
                Fq12::pow_with_table(&h2_target_pow_2, xG_k_scalar.into_bigint()).unwrap()
            };

            // e(C.k, H1) e(xG.k, H2)
            let k = C_k_H1 * xG_k_H2;

            #[cfg(test)]
            {
                use ark_bn254::{Bn254, G1Projective};
                use ark_ec::{CurveGroup, pairing::Pairing};

                assert_eq!(C_k_H1, Bn254::pairing(C.k, verifier_key.H1).0);
                let xG_k: G1Projective = x_G_output_mac_keys.iter().map(|keys| keys[i].k).sum();
                assert_eq!(
                    k,
                    Bn254::multi_pairing(
                        vec![C.k, xG_k.into_affine()],
                        vec![verifier_key.H1, verifier_key.H2]
                    )
                    .0
                );
            }

            // c^{p^(2phi + 6)} = c^{-p^(2phi)}
            // This has the effect of multiplying the MAC'd value by c
            let c_term = phi.endo(
                verifier_key
                    .c
                    .inverse()
                    .ok_or(GarbleError::DegenerateVerifierKey)?,
            );
            let k = k * AB.k * c_term;

            key.push(EndoMacKeyFq12 {
                phi,
                k_scalar: None,
                k,
            });
        }

        // This unwrap cannot fail because `pairing_output_mac_key` and
        // `c_ec_mac_key` are fixed arrays of size `KAPPA`.
        Ok(key.try_into().unwrap_or_else(|_| panic!()))
    }

    pub(crate) fn hash_packed_phis<I, C: GLVConfig>(phis: I) -> Fq
    where
        I: IntoIterator<Item = EndoScalar<C>>,
        I::IntoIter: DoubleEndedIterator,
    {
        let packed_phis = EndoScalar::<C>::pack(phis);
        let hasher = <DefaultFieldHasher<blake3::Hasher> as HashToField<Fq>>::new(&[]);
        hasher.hash_to_field::<1>(&packed_phis.into_bigint().to_bytes_le())[0]
    }
}

impl<const KAPPA: usize> Table<KAPPA> {
    pub(crate) fn garble(enc_s: Fq, input_mac_key: &InputMacKey<KAPPA>) -> Self {
        let one_mac = input_mac_key.encode(&Fp12::ONE);

        Self { one_mac, enc_s }
    }

    /// This method takes in four InputMac's. Each InputMac is a sequence of
    /// [EndoMac; KAPPA_B].
    ///
    /// For each position `i` in KAPPA_B, we check for a match with the one_mac
    /// in at least one of the InputMac's.
    ///
    /// If none of the InputMac's matches the one_mac at a given `i`, we can
    /// recover phi_i using one of the InputMac's.
    ///
    /// Returns `None` when the input is one, so nothing is revealed.
    pub(crate) fn evaluate(
        &self,
        input: &Input,
        input_macs: &[InputMac<KAPPA>],
    ) -> Result<Option<Output>, EvalError> {
        let phis = EndoScalar::<G2Config>::iter();
        let input_exp = if *input == Fq12::ONE {
            vec![Fq12::ONE]
        } else {
            // Precompute the powers of input
            let mut input_exp = vec![Fq12::ZERO; ENDO_SIZE];

            input_exp
                .iter_mut()
                .zip(phis.iter())
                .for_each(|(input_exp, phi)| *input_exp = phi.endo(*input));

            input_exp
        };

        // If none of the input_macs is equal to one_mac, we can recover the `phi`s of
        // the input_mac_key in the following way:
        // - one_mac   = 1 ^ {phi_i} * k_i
        // - input_mac = input ^ {phi_i} * k_i
        // - input_mac / one_mac = input^{phi_i}
        let mut one_inv: Vec<_> = self.one_mac.value.iter().map(|v| **v).collect();
        batch_inversion(&mut one_inv);

        let input_mac_div_one = input_macs
            .iter()
            .map(|input_mac| {
                input_mac
                    .iter()
                    .zip(one_inv.iter())
                    .map(|(mac, one_inv)| **mac * one_inv)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // For each input^{phi_i}, brute force the `phi`. This is efficient
        // because there are only seven possible values of `phi`.
        let mut recovered_phis = Vec::with_capacity(KAPPA);
        (0..KAPPA).for_each(|idx| {
            let find_position = |val: Fq12| input_exp.iter().position(|&x| x == val);
            let input_mac_div_one_slice =
                input_mac_div_one.iter().map(|mac| find_position(mac[idx]));
            let phi = try_unwrap_single(input_mac_div_one_slice);

            recovered_phis.push(phi);
        });

        let phis = if recovered_phis.iter().all(Option::is_some) {
            recovered_phis
                .iter()
                // This unwrap cannot fail because all the recovered `phi`s are
                // guaranteed to be `Some(usize)` in this `if` branch.
                .map(|&idx| phis[idx.unwrap()].clone())
                .collect()
        } else {
            EndoScalar::<G2Config>::decode(&recovered_phis)?
        };

        if *input == Fq12::ONE && phis.iter().all(|phi| matches!(phi, EndoScalar::Zero(_))) {
            return Ok(None);
        }

        // Recover the secret using the phis.
        let secret = self.enc_s - Self::hash_packed_phis(phis);
        Ok(Some(secret))
    }
}

#[test]
fn test_conditional_reveal_valid() {
    use crate::garble::groth16_verifier::KAPPA_B;
    use ark_std::{
        UniformRand,
        rand::{SeedableRng, rngs::StdRng},
    };

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);
    let secret = Fq::rand(&mut rng);

    let input = Fq12::ONE;
    let input_mac_key = InputMacKey::random_key(&mut rng);
    let input_mac = input_mac_key.encode(&input);

    let enc_s = secret
        + Table::<KAPPA_B>::hash_packed_phis(input_mac_key.iter().map(|key| key.phi.clone()));

    let table = Table::<KAPPA_B>::garble(enc_s, &input_mac_key);

    let output = table.evaluate(&input, &[input_mac]).unwrap();

    assert_eq!(output, None);
}

#[test]
fn test_conditional_reveal_invalid() {
    use crate::garble::groth16_verifier::KAPPA_B;
    use ark_std::{
        UniformRand,
        rand::{SeedableRng, rngs::StdRng},
    };

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);
    let secret = Fq::rand(&mut rng);

    let input = Input::rand(&mut rng);
    let input_mac_key = InputMacKey::random_key(&mut rng);
    let input_mac = input_mac_key.encode(&input);

    let enc_s = secret
        + Table::<KAPPA_B>::hash_packed_phis(input_mac_key.iter().map(|key| key.phi.clone()));

    let table = Table::<KAPPA_B>::garble(enc_s, &input_mac_key);

    let output = table.evaluate(&input, &[input_mac]).unwrap();

    assert_eq!(output, Some(secret));
}

#[test]
fn test_target_powers_of_two() {
    use ark_ff::UniformRand;
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    let h = G2Affine::rand(&mut rng);
    let scalar = Fr::rand(&mut rng);
    let point = G1Affine::generator() * scalar;

    let pairing = Fq12::pow_with_table(&target_powers_of_two(h), scalar.into_bigint()).unwrap();
    assert_eq!(pairing, Bn254::pairing(point, h).0);
}
