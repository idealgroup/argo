//! Given the input MACs of (A, B): (G1, G2), returns the MAC of e(A, B).

use core::panic;

use ark_bn254::{Fq12, Fr, g1, g2};
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup, short_weierstrass::Affine};
use ark_ff::{AdditiveGroup, Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
#[cfg(test)]
use ark_std::UniformRand;
use num_bigint::BigInt;
use rand_core::CryptoRngCore;

use crate::{
    garble::groth16_verifier::{KAPPA_A, KAPPA_B},
    mac::{
        Mac, MacKey,
        ddh::{DDHMac, DDHMacKey},
        endo::{EndoMacKeyFq12, EndoMacKeyG1, EndoScalar, IteratedEndoMacFq12, IteratedEndoMacG1},
        group::GroupMac,
    },
    utils::{
        bits::pow_n_lincomb,
        constants::{R_MUL_COFACTOR_GENERATOR, TARGET_GENERATOR_POW_2},
        error::GarbleError,
        group::checked_multi_pairing,
    },
};

// This works only up to KAPPA_B = 65;
pub(crate) const GENERATOR_EXPONENT: usize = 3;

pub(crate) type Input = (Affine<g1::Config>, Affine<g2::Config>);
pub(crate) type InputMacKey = ([EndoMacKeyG1; KAPPA_A], DDHMacKey<g2::Config, KAPPA_B>);
pub(crate) type InputMac = (IteratedEndoMacG1<KAPPA_A>, DDHMac<g2::Config, KAPPA_B>);

pub(crate) type Output = Fq12;
pub(crate) type OutputMac = IteratedEndoMacFq12<KAPPA_B>;

impl Mac<Input> for InputMac {
    type Key = InputMacKey;

    #[cfg(test)]
    fn random_input(rng: &mut impl CryptoRngCore) -> Input {
        use ark_bn254::{G1Affine, G2Affine};

        (G1Affine::rand(rng), G2Affine::rand(rng))
    }
}

impl MacKey<Input, InputMac> for InputMacKey {
    fn encode(&self, value: &Input) -> InputMac {
        (self.0.encode(&value.0), self.1.encode(&value.1))
    }

    #[cfg(test)]
    fn decode(&self, mac: &InputMac) -> Input {
        (self.0.decode(&mac.0), self.1.decode(&mac.1))
    }

    fn random_key(_rng: &mut impl CryptoRngCore) -> Self {
        unimplemented!()
    }
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct Table(pub(crate) super::Table<Affine<g1::Config>, g2::Config, Fq12, KAPPA_B>);

impl Table {
    pub(crate) fn garble(
        rs: [Fr; KAPPA_B],
        input_mac_key: &<InputMac as Mac<Input>>::Key,
    ) -> Result<(Self, <OutputMac as Mac<Output>>::Key), GarbleError> {
        let (A_mac_key, B_mac_key) = input_mac_key;

        let A_ks_scalar: Result<Vec<_>, GarbleError> = A_mac_key
            .iter()
            .map(|key| {
                key.k_scalar
                    .ok_or(GarbleError::MissingKScalar("a_ec_mac_key"))
            })
            .collect();
        let A_ks_scalar = A_ks_scalar?;

        let k =
            pow_n_lincomb::<_, Fr, Fr>(A_ks_scalar, EndoScalar::<g1::Config>::two_minus_omega());

        // Compute output_ks
        let mut output_ks = [Fq12::ZERO; KAPPA_B];
        for (output_k, r) in output_ks.iter_mut().zip(rs.iter()) {
            let exp = (*r * k).into_bigint();
            // This unwrap cannot fail because we compute enough `powers_of_2`
            // for `Fr`.
            *output_k = Fq12::pow_with_table(&TARGET_GENERATOR_POW_2, exp).unwrap();
        }

        // Build output_mac_key
        let mut output_mac_key = Vec::with_capacity(KAPPA_B);
        for (phi, k_val) in B_mac_key.phis.iter().zip(output_ks.iter()) {
            output_mac_key.push(EndoMacKeyFq12 {
                phi: phi.clone(),
                k_scalar: None,
                k: *k_val,
            });
        }
        // This unwrap cannot fail because `B_phis`, `output_ks` are of length
        // `KAPPA_B`.
        let output_mac_key: [EndoMacKeyFq12; KAPPA_B] =
            output_mac_key.try_into().unwrap_or_else(|_| panic!());

        let bilinear_table = super::Table {
            T: B_mac_key.T,
            _marker: std::marker::PhantomData,
        };

        Ok((Self(bilinear_table), output_mac_key.clone()))
    }

    pub(crate) fn evaluate(
        &self,
        input: &Input,
        input_mac: &InputMac,
    ) -> Result<(Output, OutputMac), crate::utils::error::EvalError> {
        let (A, B) = input;
        let (A_mac, B_mac) = input_mac;

        let output = checked_multi_pairing([*A], [*B])?;

        let S = GroupMac::<Affine<g1::Config>>(
            pow_n_lincomb(
                A_mac.iter().map(|mac| mac.into_group()),
                EndoScalar::<g1::Config>::two_minus_omega(),
            )
            .into(),
        );

        let output_mac = self.0.evaluate(A, &S, B_mac)?;

        Ok((output, output_mac.into()))
    }
}

/// FIXME: This test takes a very long time to run.
#[allow(unused)]
fn test_generator() {
    use crate::mac::endo::Endo;
    use num_bigint::Sign;

    // # E'/Fp2 = n = h * r
    // Prime factors of h = 21888242871839275222246405745257275088844257914179612981679871602714643921549
    let prime_factors = [
        BigInt::from(10069),
        BigInt::from(5864401),
        // 1875725156269
        BigInt::new(Sign::Plus, vec![3119415213, 436]),
        // 197620364512881247228717050342013327560683201906968909
        BigInt::new(
            Sign::Plus,
            vec![
                2383251789, 2607680309, 252471992, 3923425572, 1462367600, 135217,
            ],
        ),
    ];

    // Check: (n / p_k) * G = G'_k != 0
    let g_ks = (0..4).map(|skip_idx| {
        let scalar = prime_factors
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != skip_idx)
            .map(|(_, factor)| factor)
            .product::<BigInt>();
        let g_k = R_MUL_COFACTOR_GENERATOR.mul_bigint(scalar.to_u64_digits().1);
        assert_ne!(g_k, Affine::<g2::Config>::identity());
        g_k
    });

    // Check: for all (i != j in KAPPA_B) that (phi + psi) i G'_k != (phi' + psi') j G'_k
    for g_k in g_ks {
        for i in 0..KAPPA_B {
            let i_g_k = g_k.mul_bigint(
                BigInt::from(GENERATOR_EXPONENT)
                    .pow(i as u32)
                    .to_u64_digits()
                    .1,
            );
            for j in (i + 1)..KAPPA_B {
                let j_g_k = g_k.mul_bigint(
                    BigInt::from(GENERATOR_EXPONENT)
                        .pow(j as u32)
                        .to_u64_digits()
                        .1,
                );
                for phi in EndoScalar::<g2::Config>::iter() {
                    for psi in EndoScalar::<g2::Config>::iter() {
                        for phi_prime in EndoScalar::<g2::Config>::iter() {
                            for psi_prime in EndoScalar::<g2::Config>::iter() {
                                let lhs =
                                    psi.endo(i_g_k.into_affine()) + phi.endo(i_g_k.into_affine());
                                let rhs = psi_prime.endo(j_g_k.into_affine())
                                    + phi_prime.endo(j_g_k.into_affine());

                                let lhs: Affine<g2::Config> = lhs.into();
                                let rhs: Affine<g2::Config> = rhs.into();

                                if !lhs.is_zero() || !rhs.is_zero() {
                                    assert_ne!(lhs, rhs);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn test_pairing_circuit() {
    use crate::garble::keys::{a_ec_mac_key, b_mac_key};
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    for seed in 0..100 {
        let mut rng = StdRng::seed_from_u64(seed);

        // Sample `KAPPA_B` random `r`s
        let mut rs = Box::new([Fr::ZERO; KAPPA_B]);
        for r in rs.iter_mut() {
            *r = Fr::rand(&mut rng);
        }

        // Sample x uniformly at random
        let x = Fr::rand(&mut rng);
        let a_ec_mac_key = a_ec_mac_key(&mut rng, x);
        let (b_ddh_mac_key, _) = b_mac_key(&mut rng, x, *rs);

        let input = InputMac::random_input(&mut rng);
        let input_mac_key = (a_ec_mac_key, b_ddh_mac_key);

        let input_mac = input_mac_key.encode(&input);

        let output = checked_multi_pairing([input.0], [input.1]).unwrap();

        let (circuit, output_mac_key) = Table::garble(*rs, &input_mac_key).unwrap();
        let expected_output_mac = output_mac_key.encode(&output);

        let output_mac = circuit.evaluate(&input, &input_mac).unwrap().1;

        for (expected, mac) in expected_output_mac.iter().zip(output_mac.iter()) {
            assert!(expected == mac);
        }
    }
}
