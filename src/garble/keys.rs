use std::marker::PhantomData;

use ark_bn254::{Fr, G1Projective, G2Projective, g1, g2};
use ark_ec::{
    AffineRepr, CurveGroup, PrimeGroup, ScalarMul,
    scalar_mul::glv::GLVConfig,
    short_weierstrass::{Affine, Projective},
};
use ark_ff::{AdditiveGroup, PrimeField, UniformRand, Zero};
use num_bigint::BigInt;
use rand_core::CryptoRngCore;

use crate::{
    garble::{
        bilinear::pairing::GENERATOR_EXPONENT,
        groth16_verifier::{KAPPA_A, KAPPA_B},
    },
    mac::{
        ddh::DDHMacKey,
        endo::{ENDO_SIZE, EndoMacKey, EndoScalar},
    },
    utils::constants::R_MUL_COFACTOR_GENERATOR,
};

// r (phi B + K) = phi (r B) + (r K) = r_m
// -r (phi B + K) = phi (-r B) - (r K) = -r_m
//
// We will publish r_K = r K in "cofactor group"
// We will CDS decode r_m and -r_m
//    i.e. we will take r_m - r_K =? phi(r B) for any phi in { NegInf, ... }
//         we will take -r_m - r_K =? phi(r B) for any phi in { NegInf, ... }
// At least one of them will always decode
//.   i.e. we will always find a phi in the first check or one in the second check
// Sometimes, we will find they *both* decode
//.   i.e. WLOG r_m is the correct one so
//.        r_m - r_K = phi (r B)
//.        BUT by coincidence on B
//.        -r_m - r_K = -(phi (r B)) - 2 r_K = psi (r B)
// This is because the cofactor group has small subgroups (technically could also occur in the Gt decoding)
// To solve this, we need to ensure the r_K are chosen so that this can occur at most one time
//    i.e. for any single r_K we can always cause a decoding error by maliciously choosing B
//.        pick a psi != phi, and let r B = -2 / (phi + psi) r_K
//.        but we can ensure that *at most* most one failure can occur
// for all (phi, psi, phi', psi') where phi != -psi and phi' != -psi'
// must have (phi + psi) r_(K,i) != (phi' + psi') r_(K,j)
// Note: r_K does not have to be random
// We should also choose the phi such that given n-1 of them we can always recover the last one
// i.e. the sum mod 7 is always zero
//
// Let G' = r * G
// Let K_i = (x * r_i * H) + GENERATOR_EXPONENT^i * G'
fn derive_b_ks(g2_b_ks: &[Affine<g2::Config>; KAPPA_B]) -> [Affine<g2::Config>; KAPPA_B] {
    let mut b_ks = [Projective::<g2::Config>::zero(); KAPPA_B];
    b_ks.iter_mut()
        .zip(g2_b_ks.iter())
        .enumerate()
        .for_each(|(i, (b_k, g2_b_k))| {
            *b_k = *g2_b_k
                + R_MUL_COFACTOR_GENERATOR.mul_bigint(
                    BigInt::from(GENERATOR_EXPONENT as u8)
                        .pow(i as u32)
                        .to_u64_digits()
                        .1,
                )
        });

    let b_ks = Projective::<g2::Config>::normalize_batch(&b_ks);

    // This unwrap cannot fail since g2_b_ks is a fixed array of length
    // `KAPPA_B`.
    b_ks.try_into().unwrap()
}

fn derive_phis_from_x(x: Fr) -> [EndoScalar<g1::Config>; KAPPA_A] {
    let phi_components = |z: u8| match z {
        0 => (0, 0),
        1 => (1, 0),
        2 => (0, 1),
        3 => (1, 1),
        4 => (-1, -1),
        5 => (0, -1),
        6 => (-1, 0),
        _ => unreachable!(),
    };

    let phi_mapping = |z: u8| match z {
        0 => EndoScalar::NegInf(PhantomData),
        1 => EndoScalar::Zero(PhantomData),
        2 => EndoScalar::Four(PhantomData),
        3 => EndoScalar::Five(PhantomData),
        4 => EndoScalar::Two(PhantomData),
        5 => EndoScalar::One(PhantomData),
        6 => EndoScalar::Three(PhantomData),
        _ => unreachable!(),
    };

    let mut endoscalars = Vec::with_capacity(KAPPA_A);

    // `a`, `b` are signed bigints
    let (mut a, mut b) = {
        let (a, b) = g1::Config::scalar_decomposition(x);

        let mut a_signed = BigInt::from(a.1.into_bigint());
        if !a.0 {
            a_signed = -a_signed
        };

        let mut b_signed = BigInt::from(b.1.into_bigint());
        if !b.0 {
            b_signed = -b_signed
        };

        let a = a_signed - &b_signed;
        let b = -b_signed;

        (a, b)
    };

    for _ in 0..KAPPA_A {
        let z: BigInt = (&a + 2 * &b) % ENDO_SIZE;
        let z = (BigInt::from(ENDO_SIZE) + z) % ENDO_SIZE;

        let z = z.to_bytes_le().1[0];
        let (d, e) = phi_components(z);

        let phi = phi_mapping(z);
        endoscalars.push(phi.clone());

        let a_prime: BigInt = a - d;
        let b_prime: BigInt = b - e;

        let u: BigInt = 3 * &a_prime - &b_prime;
        let v: BigInt = 2 * b_prime + a_prime;

        a = u / ENDO_SIZE;
        b = v / ENDO_SIZE;
    }

    // This unwrap cannot fail since `endoscalars` was constructed in a for
    // loop ranging from 0..KAPPA_A.
    endoscalars.try_into().unwrap_or_else(|_| panic!())
}

pub(crate) fn a_ec_mac_key(
    rng: &mut impl CryptoRngCore,
    x: Fr,
) -> [EndoMacKey<g1::Config, Affine<g1::Config>>; KAPPA_A] {
    let A_phis = derive_phis_from_x(x);

    // Sample A_ks_scalar directly into array
    let mut A_ks_scalar = [Fr::ZERO; KAPPA_A];
    for A_k_scalar in A_ks_scalar.iter_mut() {
        *A_k_scalar = Fr::rand(rng);
    }

    let A_ks = G1Projective::generator().batch_mul(&A_ks_scalar);

    #[cfg(test)]
    {
        let A_phis_scalar = A_phis.iter().map(|A_phi| A_phi.as_scalar());
        let expected_x = {
            use crate::utils::bits::pow_n_lincomb;

            pow_n_lincomb::<_, Fr, Fr>(A_phis_scalar, EndoScalar::<g1::Config>::two_minus_omega())
        };
        assert_eq!(x, expected_x);
    }

    // Build A_mac_key
    let mut A_mac_key = Vec::with_capacity(KAPPA_A);
    for ((phi, &k_scalar), &k) in A_phis.iter().zip(A_ks_scalar.iter()).zip(A_ks.iter()) {
        A_mac_key.push(EndoMacKey {
            phi: phi.clone(),
            k_scalar: Some(k_scalar),
            k,
        });
    }
    // This unwrap cannot fail because `A_phis`, `A_ks_scalar`, `A_ks` are
    // all fixed-size arrays of length `KAPPA_A`.
    A_mac_key.try_into().unwrap_or_else(|_| panic!())
}

pub(crate) fn b_mac_key(
    rng: &mut impl CryptoRngCore,
    x: Fr,
    rs: [Fr; KAPPA_B],
) -> (
    DDHMacKey<g2::Config, KAPPA_B>,
    [EndoMacKey<g2::Config, Affine<g2::Config>>; KAPPA_B],
) {
    // Compute g2_B_ks_scalar
    let mut g2_B_ks_scalar = [Fr::ZERO; KAPPA_B];
    g2_B_ks_scalar
        .iter_mut()
        .zip(rs.iter())
        .for_each(|(val, r)| *val = -*r * x);

    let g2_B_ks = G2Projective::generator().batch_mul(&g2_B_ks_scalar);
    // This unwrap cannot fail since `g2_B_ks_scalar` is a fixed array of
    // length `KAPPA_B`.
    let B_ks = derive_b_ks(&g2_B_ks.try_into().unwrap());

    let B_phis = EndoScalar::<g2::Config>::sample_endoscalars_with_checksum::<KAPPA_B>(rng);

    // This is a DDHMacKey
    // scalar is x, public vector is [r_i]G
    let ddh_mac_key = DDHMacKey {
        // This unwrap cannot fail since `rs` is a fixed array of
        // length `KAPPA_B`.
        T: G2Projective::generator().batch_mul(&rs).try_into().unwrap(),
        // This unwrap cannot fail since `B_phis` is a vector of
        // length `KAPPA_B`.
        phis: B_phis.clone().try_into().unwrap_or_else(|_| panic!()),
        a: -x,
    };

    // Build B_mac_key
    let mut B_mac_key = Vec::with_capacity(KAPPA_B);
    for ((phi, &k_scalar), &k) in B_phis.iter().zip(g2_B_ks_scalar.iter()).zip(B_ks.iter()) {
        B_mac_key.push(EndoMacKey {
            phi: phi.clone(),
            k_scalar: Some(k_scalar),
            k,
        });
    }
    // This unwrap cannot fail because `B_phis`, `g2_B_ks_scalar`, `B_ks`
    // are all of length `KAPPA_B`.
    let b_ec_mac_key = B_mac_key.try_into().unwrap_or_else(|_| panic!());

    (ddh_mac_key, b_ec_mac_key)
}
