use ark_bn254::{Fq, Fq2, Fr, G2Affine, g1, g2};
use ark_ec::{CurveConfig, short_weierstrass::SWCurveConfig};
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::{
    garble::{
        Circuit,
        binary::less_than,
        bivariate::{self, Monomial, Poly},
        g2_subgroup_check,
        groth16_verifier::{GID, Input, InputBits, InputMac, InputMacKey, KAPPA_B},
    },
    mac::{
        IteratedMac, Random,
        digit::bytes::DigitMac,
        endo::{EndoMacG2, EndoMacKeyG2},
    },
    utils::{
        bits::{FromBits, NumBits, ToBits},
        error::{EvalError, GarbleError},
    },
};

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Table<const N: usize> {
    // Checks that each garbled `x_l` is a valid Fr element
    x_range_check: [less_than::Table<Fr>; N],
    // Checks that `A.x`, `A.y` are valid Fq elements
    a_range_check: [less_than::Table<Fq>; 2],
    // Checks that A is a valid G1 curve point, leaking `secret` if not
    a_curve_check: bivariate::Table<<g1::Config as CurveConfig>::BaseField>,
    // Checks that `B.x`, `B.y` are valid Fq2 elements
    b_range_check: [less_than::Table<Fq>; 4],
    // Checks that B is a valid curve point, leaking `secret` if not
    b_curve_check: bivariate::Table<<g2::Config as CurveConfig>::BaseField>,
    // Checks that B is in G2, leaking `secret` if not
    b_g2_check: g2_subgroup_check::Table,
    // Checks that `C.x`, `C.y` are valid Fq elements
    c_range_check: [less_than::Table<Fq>; 2],
    // Checks that C is a valid G1 curve point, leaking `secret` if not
    c_curve_check: bivariate::Table<<g1::Config as CurveConfig>::BaseField>,
    // Global ID of this instance
    gid: GID,
}

pub(crate) struct Aux {
    pub(super) secret: Fq,
    pub(super) gid: GID,
    pub(super) b_ec_mac_key: Box<[EndoMacKeyG2; KAPPA_B]>,
}

/// Monomials of the curve membership polynomial B + x^3 - y^2.
const CURVE_MONOMIALS: [Monomial; 3] = [
    Monomial::constant(),
    Monomial::new(3, 0),
    Monomial::new(0, 2),
];

// TODO refactor to use Circuit trait?
impl<const N: usize> Table<N> {
    pub(crate) fn has_garbled_shape(&self, gid: &GID) -> bool {
        self.gid == *gid
            && self.x_range_check.iter().all(|t| t.has_garbled_shape(gid))
            && self
                .a_range_check
                .iter()
                .chain(&self.b_range_check)
                .chain(&self.c_range_check)
                .all(|t| t.has_garbled_shape(gid))
            && self.a_curve_check.has_garbled_shape(&CURVE_MONOMIALS)
            && self.b_curve_check.has_garbled_shape(&CURVE_MONOMIALS)
            && self.c_curve_check.has_garbled_shape(&CURVE_MONOMIALS)
    }

    pub(crate) fn garble(
        parent_nonce: &mut crate::garble::Nonce,
        rng: &mut ark_std::rand::prelude::StdRng,
        aux: &Aux,
        input_mac_key: &InputMacKey<N>,
    ) -> Result<Self, GarbleError> {
        let Aux {
            secret,
            gid,
            b_ec_mac_key,
        } = aux;

        //   (B + x^3 - y^2) s
        // = sB + sx^3 -sy^2
        fn curve_membership_poly<C: SWCurveConfig>(secret: C::BaseField) -> Poly<C::BaseField> {
            let mut poly = Poly::default();
            let [constant, x3, y2] = CURVE_MONOMIALS;
            poly.insert(constant, secret * C::COEFF_B);
            poly.insert(x3, secret);
            poly.insert(y2, -secret);

            poly
        }

        let mut a_range_check = Vec::with_capacity(2);
        for input_mac_key in [&input_mac_key.A.x, &input_mac_key.A.y].iter() {
            let table = less_than::Table::<Fq>::garble(
                parent_nonce,
                rng,
                Some((*secret, *gid)),
                input_mac_key,
            )?
            .0;
            a_range_check.push(table);
        }
        // This unwrap cannot fail because `input_mac_key` is a fixed array of
        // length 2.
        let a_range_check = a_range_check.try_into().unwrap();

        // Garbling table to check that `A` is a valid G1 curve point.
        // This table leaks `secret` if `A` is not a valid curve point.
        let a_curve_check = bivariate::Table::garble(
            parent_nonce,
            rng,
            Some(curve_membership_poly::<g1::Config>(*secret)),
            // Input MAC key for the (x, y) coordinates of `A`
            &input_mac_key.A,
        )?
        .0;

        let mut b_range_check = Vec::with_capacity(4);
        {
            let x0_bits = input_mac_key.B.x[..Fq::NUM_BITS].to_vec().into();
            let x1_bits = input_mac_key.B.x[Fq::NUM_BITS..].to_vec().into();

            let y0_bits = input_mac_key.B.y[..Fq::NUM_BITS].to_vec().into();
            let y1_bits = input_mac_key.B.y[Fq::NUM_BITS..].to_vec().into();

            for input_mac_key in [x0_bits, x1_bits, y0_bits, y1_bits].iter() {
                let table = less_than::Table::<Fq>::garble(
                    parent_nonce,
                    rng,
                    Some((*secret, *gid)),
                    input_mac_key,
                )?
                .0;
                b_range_check.push(table);
            }
        };
        // This unwrap cannot fail because `input_mac_key` is a fixed array of
        // length 4.
        let b_range_check = b_range_check.try_into().unwrap();

        // Garbling table to check that `B` is a valid curve point.
        // This table leaks `secret` if `B` is not a valid curve point.
        let b_curve_check = bivariate::Table::garble(
            parent_nonce,
            rng,
            Some(curve_membership_poly::<g2::Config>(
                Fq2::from_base_prime_field(*secret),
            )),
            // Input MAC key for the (x, y) coordinates of `B`
            &input_mac_key.B,
        )?
        .0;

        // Garbling table to check that `B` is in the G2 subgroup.
        // This table leaks `secret` if `B` is not in the G2 subgroup.
        let b_g2_check =
            g2_subgroup_check::Table::garble(parent_nonce, rng, Some(*secret), b_ec_mac_key)?.0;

        let mut c_range_check = Vec::with_capacity(2);
        for input_mac_key in [&input_mac_key.C.x, &input_mac_key.C.y].iter() {
            let table = less_than::Table::<Fq>::garble(
                parent_nonce,
                rng,
                Some((*secret, *gid)),
                input_mac_key,
            )?
            .0;
            c_range_check.push(table);
        }
        // This unwrap cannot fail because `input_mac_key` is a fixed array of
        // length 2.
        let c_range_check = c_range_check.try_into().unwrap();

        // Garbling table to check that `C` is a valid G1 curve point.
        // This table leaks `secret` if `C` is not a valid curve point.
        let c_curve_check = bivariate::Table::garble(
            parent_nonce,
            rng,
            Some(curve_membership_poly::<g1::Config>(*secret)),
            // Input MAC key for the (x, y) coordinates of `C`
            &input_mac_key.C,
        )?
        .0;

        // Garbling tables to check each `x_l` is a valid Fr element.
        // These tables leak `secret` if `x_l` is not a valid Fr element.
        let mut x_range_check = Vec::with_capacity(N);
        for input_mac_key in &input_mac_key.x {
            let table = less_than::Table::<Fr>::garble(
                parent_nonce,
                rng,
                Some((*secret, *gid)),
                input_mac_key,
            )?
            .0;
            x_range_check.push(table);
        }
        // This unwrap cannot fail because there is one table per garbled input.
        let x_range_check = x_range_check.try_into().unwrap_or_else(|_| panic!());

        let table = Self {
            x_range_check,
            a_range_check,
            a_curve_check,
            b_range_check,
            b_curve_check,
            b_g2_check,
            c_range_check,
            c_curve_check,
            gid: *gid,
        };

        Ok(table)
    }

    /// Check raw coordinates before any operation that assumes a curve point.
    /// Returns the proof as field elements, or `Err(secret)` if a component is
    /// at or above its modulus or a point is off its curve. The secret may be
    /// zero.
    pub(crate) fn evaluate_coordinates(
        &self,
        parent_nonce: &mut crate::garble::Nonce,
        bits: &InputBits<N>,
        input_mac: &InputMac<N>,
    ) -> Result<Result<Input<N>, Fq>, EvalError> {
        /// B + x^3 - y^2
        fn curve_check_offset<C: SWCurveConfig>(
            point: bivariate::Input<C::BaseField>,
        ) -> C::BaseField {
            C::COEFF_B + point.x.square() * point.x - point.y.square()
        }

        /// Range-checks one component on its raw bits, returning it as a field
        /// element, or `Err(secret)` if it is not canonical.
        fn range_check<F>(
            table: &less_than::Table<F>,
            parent_nonce: &mut crate::garble::Nonce,
            bits: &[bool],
            input_mac: &DigitMac<F>,
        ) -> Result<Result<F, Fq>, EvalError>
        where
            F: PrimeField + FromBits<F, F> + Random + ToBits + NumBits,
        {
            let secret = table.evaluate_bits(parent_nonce, bits, input_mac)?;
            Ok(F::from_bigint(F::BigInt::from_bits_le(bits)).ok_or(secret))
        }

        macro_rules! or_reveal {
            ($checked:expr) => {
                match $checked {
                    Ok(value) => value,
                    Err(secret) => return Ok(Err(secret)),
                }
            };
        }

        // Checks that A.x, A.y are valid Fq elements, returning the `secret`
        // otherwise.
        let A = {
            let [x_table, y_table] = &self.a_range_check;
            bivariate::Input {
                x: or_reveal!(range_check(
                    x_table,
                    parent_nonce,
                    bits.component(0),
                    &input_mac.A.x
                )?),
                y: or_reveal!(range_check(
                    y_table,
                    parent_nonce,
                    bits.component(1),
                    &input_mac.A.y
                )?),
            }
        };

        // Evaluate the curve validity check table for `A`. This evaluates to
        // `secret` if `A` is not a valid curve point.
        let a_curve_check = self
            .a_curve_check
            .evaluate(parent_nonce, &A, &input_mac.A)?
            .0;
        // If `A` is not a valid curve point, return `secret` early
        if let Some(inv_curve_check_offset) = curve_check_offset::<g1::Config>(A).inverse() {
            return Ok(Err(a_curve_check * inv_curve_check_offset));
        }

        // Checks that B.x, B.y are valid Fq2 elements, returning the `secret`
        // otherwise.
        let B = {
            let input_macs: [DigitMac<Fq>; 4] = [
                input_mac.B.x[..Fq::NUM_BITS].to_vec().into(),
                input_mac.B.x[Fq::NUM_BITS..].to_vec().into(),
                input_mac.B.y[..Fq::NUM_BITS].to_vec().into(),
                input_mac.B.y[Fq::NUM_BITS..].to_vec().into(),
            ];

            let mut values = [Fq::ZERO; 4];
            for (i, ((value, input_mac), table)) in values
                .iter_mut()
                .zip(input_macs.iter())
                .zip(self.b_range_check.iter())
                .enumerate()
            {
                *value = or_reveal!(range_check(
                    table,
                    parent_nonce,
                    bits.component(2 + i),
                    input_mac
                )?);
            }
            let [x0, x1, y0, y1] = values;
            bivariate::Input {
                x: Fq2::new(x0, x1),
                y: Fq2::new(y0, y1),
            }
        };

        // Evaluate the curve validity check table for `B`. This evaluates to
        // `secret` if `B` is not a valid curve point.
        let b_curve_check = self
            .b_curve_check
            .evaluate(parent_nonce, &B, &input_mac.B)?
            .0;
        // If `B` is not a valid curve point, return `secret` early
        if let Some(inv_curve_check_offset) = curve_check_offset::<g2::Config>(B).inverse() {
            let secret = b_curve_check * inv_curve_check_offset;
            // The committed secret was embedded in Fq2's base-field component.
            return Ok(Err(secret.c0));
        }

        // Checks that C.x, C.y are valid Fq elements, returning the `secret`
        // otherwise.
        let C = {
            let [x_table, y_table] = &self.c_range_check;
            bivariate::Input {
                x: or_reveal!(range_check(
                    x_table,
                    parent_nonce,
                    bits.component(6),
                    &input_mac.C.x
                )?),
                y: or_reveal!(range_check(
                    y_table,
                    parent_nonce,
                    bits.component(7),
                    &input_mac.C.y
                )?),
            }
        };

        // Evaluate the curve validity check table for `C`. This evaluates to
        // `secret` if `C` is not a valid curve point.
        let c_curve_check = self
            .c_curve_check
            .evaluate(parent_nonce, &C, &input_mac.C)?
            .0;
        // If `C` is not a valid curve point, return `secret` early
        if let Some(inv_curve_check_offset) = curve_check_offset::<g1::Config>(C).inverse() {
            return Ok(Err(c_curve_check * inv_curve_check_offset));
        }

        // Evaluate the range check for each `x_l`.
        let mut x = [Fr::ZERO; N];
        for (l, ((x, table), input_mac)) in x
            .iter_mut()
            .zip(self.x_range_check.iter())
            .zip(&input_mac.x)
            .enumerate()
        {
            *x = or_reveal!(range_check(
                table,
                parent_nonce,
                bits.component(8 + l),
                input_mac
            )?);
        }

        Ok(Ok(Input { A, B, C, x }))
    }

    /// Run only after coordinate checks and conversion of B have succeeded.
    pub(crate) fn evaluate_subgroup(
        &self,
        parent_nonce: &mut crate::garble::Nonce,
        input: &G2Affine,
        b_ec_mac: &IteratedMac<G2Affine, EndoMacG2, KAPPA_B>,
    ) -> Result<Option<Fq>, EvalError> {
        if input.is_in_correct_subgroup_assuming_on_curve() {
            return Ok(None);
        }
        // The subgroup gadget does not consume a nonce, so it can be deferred
        // until the B MAC is available without changing the raw-check nonces.
        let secret = self.b_g2_check.evaluate(parent_nonce, input, b_ec_mac)?.0;
        Ok(Some(secret))
    }
}

#[test]
/// If any of the input (A, B, C) is an invalid curve point, the circuit should
/// leak the same `secret`.
fn test_malformed_curve_points() {
    use ark_bn254::G1Affine;
    use ark_ff::PrimeField;
    use ark_std::{
        UniformRand,
        rand::{SeedableRng, rngs::StdRng},
    };

    use crate::garble::Nonce;
    use crate::mac::{Mac, MacKey, Random};
    use crate::utils::{
        aes_hash::{
            aes_ctr::clear_set as aes_ctr_clear_set, aes_mitccr::clear_set as aes_mitccr_clear_set,
        },
        group::get_curve_point_not_in_g2,
    };

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);
    let secret = Fq::rand(&mut rng);
    let gid = GID::random(&mut rng);

    let fq_modulus = Fq::new_unchecked(Fq::MODULUS);

    // Evaluate the same circuit on differently malformed inputs, check that
    // we recover the same secret
    let input = InputMac::random_input(&mut rng);
    let input_mac_key = InputMacKey::random_key(&mut rng);

    let b_ec_mac_key = <[EndoMacKeyG2; KAPPA_B]>::random_key(&mut rng);

    let aux = Aux {
        secret,
        gid,
        b_ec_mac_key: Box::new(b_ec_mac_key.clone()),
    };

    let table = Table::garble(&mut Nonce::new(), &mut rng, &aux, &input_mac_key).unwrap();
    assert!(table.has_garbled_shape(&gid));
    aes_ctr_clear_set();
    aes_mitccr_clear_set();

    let inputs = {
        let malformed_a: Vec<_> = {
            let invalid_x = G1Affine::new_unchecked(fq_modulus, Fq::rand(&mut rng));
            let invalid_y = G1Affine::new_unchecked(Fq::rand(&mut rng), fq_modulus);
            let invalid_curve_point =
                G1Affine::new_unchecked(Fq::rand(&mut rng), Fq::rand(&mut rng));

            [invalid_x, invalid_y, invalid_curve_point]
        }
        .iter()
        .map(|A| {
            let mut input = input;
            input.A = (*A).into();
            input
        })
        .collect();

        let malformed_b: Vec<_> = {
            let invalid_x0 = {
                let x = Fq2 {
                    c0: fq_modulus,
                    c1: Fq::rand(&mut rng),
                };
                let y = Fq2::rand(&mut rng);

                G2Affine::new_unchecked(x, y)
            };

            let invalid_x1 = {
                let x = Fq2 {
                    c0: Fq::rand(&mut rng),
                    c1: fq_modulus,
                };
                let y = Fq2::rand(&mut rng);

                G2Affine::new_unchecked(x, y)
            };

            let invalid_y0 = {
                let x = Fq2::rand(&mut rng);
                let y = Fq2 {
                    c0: fq_modulus,
                    c1: Fq::rand(&mut rng),
                };

                G2Affine::new_unchecked(x, y)
            };

            let invalid_y1 = {
                let x = Fq2::rand(&mut rng);
                let y = Fq2 {
                    c0: Fq::rand(&mut rng),
                    c1: fq_modulus,
                };

                G2Affine::new_unchecked(x, y)
            };

            let invalid_curve_point =
                G2Affine::new_unchecked(Fq2::rand(&mut rng), Fq2::rand(&mut rng));
            let non_g2_point = get_curve_point_not_in_g2(&mut rng);

            [
                invalid_x0,
                invalid_x1,
                invalid_y0,
                invalid_y1,
                invalid_curve_point,
                non_g2_point,
            ]
        }
        .iter()
        .map(|B| {
            let mut input = input;
            input.B = (*B).into();
            input
        })
        .collect();

        let malformed_c: Vec<_> = {
            let invalid_x = G1Affine::new_unchecked(fq_modulus, Fq::rand(&mut rng));
            let invalid_y = G1Affine::new_unchecked(Fq::rand(&mut rng), fq_modulus);
            let invalid_curve_point =
                G1Affine::new_unchecked(Fq::rand(&mut rng), Fq::rand(&mut rng));

            [invalid_x, invalid_y, invalid_curve_point]
        }
        .iter()
        .map(|C| {
            let mut input = input;
            input.C = (*C).into();
            input
        })
        .collect();

        let malformed_x = {
            let mut input = input;
            input.x = [Fr::new_unchecked(Fr::MODULUS)];
            input
        };

        malformed_a
            .into_iter()
            .chain(malformed_b)
            .chain(malformed_c)
            .chain(Some(malformed_x))
    };

    let mut secrets = inputs.map(|input| {
        aes_ctr_clear_set();
        aes_mitccr_clear_set();

        let input_mac = input_mac_key.encode(&input);
        let b_ec_mac = b_ec_mac_key.encode(&input.B.into());
        let mut nonce = Nonce::new();
        let result = table
            .evaluate_coordinates(&mut nonce, &InputBits::from(&input), &input_mac)
            .unwrap();
        match result {
            Err(secret) => secret,
            Ok(_) => table
                .evaluate_subgroup(&mut nonce, &input.B.into(), &b_ec_mac)
                .unwrap()
                .unwrap(),
        }
    });

    assert!(secrets.all(|recovered_secret| recovered_secret == secret));
}
