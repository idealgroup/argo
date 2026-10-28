//! Maps the MAC of an affine curve point (P.x, P.y) to its Jacobian form.
//! Takes in MAC of bits (P.x, P.y); evaluates to iterated MAC of Jacobian
//! coordinates of P, in the form MAC(P) = phi * P + k, where phi is an
//! endoscalar.
//!
//! This is generic over inputs in Fq and Fq2.

use std::any::type_name;

#[cfg(test)]
use crate::garble::groth16_verifier::{KAPPA_A, KAPPA_B};

use ark_bn254::Fq;
use ark_ec::{AffineRepr, scalar_mul::glv::GLVConfig, short_weierstrass::Affine};
use ark_ff::{Field, batch_inversion};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand_core::CryptoRngCore;

use crate::{
    garble::{
        Circuit, Nonce,
        bivariate::{self, Input, InputMac, InputMacKey, Monomial, Poly},
    },
    mac::{
        MacKey, Random, RandomFromPhi,
        endo::{Endo, EndoMac, EndoMacKey, EndoScalar, IteratedEndoMac, PSqModR},
    },
    utils::{
        bits::{FromBits, NumBits, ToBits},
        error::{EvalError, GarbleError},
        group::FromLeBytesModOrder,
    },
};

pub(crate) type Output<Config> = Affine<Config>;
pub(crate) type OutputMac<Config, const KAPPA: usize> =
    IteratedEndoMac<Config, Affine<Config>, KAPPA>;
pub type OutputMacKey<Config, const KAPPA: usize> = [EndoMacKey<Config, Affine<Config>>; KAPPA];

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Table<C, const KAPPA: usize>
where
    C: GLVConfig,
    C::BaseField: Field + NumBits + FromBits<bool, C::BaseField> + Random,
    <C::BaseField as Field>::BasePrimeField: FromLeBytesModOrder,
{
    is_full: bool,
    pub(crate) x: Vec<bivariate::Table<C::BaseField>>,
    pub(crate) y: Option<Vec<bivariate::Table<C::BaseField>>>,
    pub(crate) z: Vec<bivariate::Table<C::BaseField>>,
    // Per replica, the secret encrypted under the input labels of
    // phi^{-1}(K), the one input where the chord formula yields (0, 0, 0).
    pub(crate) doubling: Vec<[u8; 48]>,
}

/// Monomials of the polynomials `garble` builds for X, Y and Z, in the order
/// [1, X, Y, X^2, XY, Y^2] of `Poly::biquadratic`.
const X_MONOMIALS: [Monomial; 4] = [
    Monomial::constant(),
    Monomial::new(1, 0),
    Monomial::new(0, 1),
    Monomial::new(2, 0),
];
const Y_MONOMIALS: [Monomial; 5] = [
    Monomial::constant(),
    Monomial::new(0, 1),
    Monomial::new(2, 0),
    Monomial::new(1, 1),
    Monomial::new(0, 2),
];
const Z_MONOMIALS: [Monomial; 2] = [Monomial::constant(), Monomial::new(1, 0)];

/// Hash of the labels of every input bit, which only the evaluator holding
/// those labels can compute.
fn label_digest<F>(input_mac: &InputMac<F>) -> blake3::Hash {
    let mut hasher = blake3::Hasher::new_derive_key("argo field_mac_to_ec_mac doubling v1");
    for label in input_mac.x.iter().chain(input_mac.y.iter()) {
        hasher.update(&label.0);
    }
    hasher.finalize()
}

fn apply_doubling_pad(bytes: &mut [u8; 48], labels: &blake3::Hash, replica: usize) {
    let mut hasher = blake3::Hasher::new_keyed(labels.as_bytes());
    hasher.update(&(replica as u64).to_le_bytes());
    let mut pad = [0; 48];
    hasher.finalize_xof().fill(&mut pad);
    bytes
        .iter_mut()
        .zip(pad)
        .for_each(|(byte, pad)| *byte ^= pad);
}

impl<C, const KAPPA: usize> Table<C, KAPPA>
where
    C: GLVConfig,
    C::BaseField: Field + NumBits + FromBits<bool, C::BaseField> + Random,
    <C::BaseField as Field>::BasePrimeField: FromLeBytesModOrder,
{
    /// Whether this is the shape `garble` gives `KAPPA` replicas, with Y
    /// tables exactly when `is_full`.
    pub(crate) fn has_garbled_shape(&self, is_full: bool) -> bool {
        let replicas = |tables: &[bivariate::Table<C::BaseField>], monomials: &[Monomial]| {
            tables.len() == KAPPA
                && tables
                    .iter()
                    .all(|table| table.has_garbled_shape(monomials))
        };
        self.is_full == is_full
            && replicas(&self.x, &X_MONOMIALS)
            && replicas(&self.z, &Z_MONOMIALS)
            && match &self.y {
                Some(y) => is_full && replicas(y, &Y_MONOMIALS),
                None => !is_full,
            }
            && self.doubling.len() == KAPPA
    }

    /// Returns the secret if `input_mac` holds the labels of some replica's
    /// doubling input, for which the converted MAC would be meaningless.
    pub(crate) fn reveal(&self, input_mac: &InputMac<C::BaseField>) -> Option<Fq> {
        let labels = label_digest(input_mac);
        self.doubling
            .iter()
            .enumerate()
            .find_map(|(replica, ciphertext)| {
                let mut plaintext = *ciphertext;
                apply_doubling_pad(&mut plaintext, &labels, replica);
                if plaintext[32..] != [0; 16] {
                    return None;
                }
                Fq::deserialize_compressed(&plaintext[..32]).ok()
            })
    }
}

impl<Config, F, const KAPPA: usize>
    Circuit<Input<F>, InputMac<F>, Output<Config>, OutputMac<Config, KAPPA>>
    for Table<Config, KAPPA>
where
    Config: GLVConfig<BaseField = F> + Clone,
    F: Field + NumBits + ToBits + FromBits<F, F> + FromBits<bool, F> + Random,
    F::BasePrimeField: FromLeBytesModOrder,
    Config: PSqModR,
    EndoMacKey<Config, Affine<Config>>:
        RandomFromPhi<Affine<Config>, EndoMac<Config, Affine<Config>>>,
{
    type Aux = (bool, OutputMacKey<Config, KAPPA>, Fq);

    /// # Panics
    ///
    /// Panics if Config::COEFF_A is nonzero.
    fn garble(
        parent_nonce: &mut Nonce,
        rng: &mut impl CryptoRngCore,
        aux: Option<Self::Aux>,
        input_mac_key: &InputMacKey<F>,
    ) -> Result<(Self, OutputMacKey<Config, KAPPA>), GarbleError> {
        assert_eq!(Config::COEFF_A, F::ZERO);

        let mut nonce = parent_nonce.fork()?;
        let (is_full, output_mac_key, secret) = aux
            .ok_or_else(|| GarbleError::AuxError(type_name::<Self::Aux>(), type_name::<Self>()))?;

        fn x_aux<C, F>(mac_key: &EndoMacKey<C, Affine<C>>, a2: F) -> Result<Poly<F>, GarbleError>
        where
            C: GLVConfig<BaseField = F>,
            C: PSqModR,
            F: Field,
        {
            let B = C::COEFF_B;
            let (x, y) = mac_key
                .k
                .xy()
                .ok_or_else(|| GarbleError::InvalidEndoMacKeyK(format!("{:?}", mac_key.k)))?;
            // f(X, Y) = phi * (X, Y) + K = (a X, b Y) + K
            let mut cs = {
                //  (6, 1)                 # c0
                let c0 = Some(B.double());
                //  (xQ_^2, xP_)           # c1
                let c1 = Some(x.square());
                //  (-2*yQ_, yP_)          # c2
                let c2 = Some(-y.double());
                //  (xQ_, xP_^2)           # c3
                let c3 = Some(x);
                //  (0, xP_ * yP_)         # c4 = 0
                let c4 = None;
                //  (0, yP_^2)             # c5 = 0
                let c5 = None;

                Poly::biquadratic([c0, c1, c2, c3, c4, c5])
            };

            // Scale by random a2 = a^2
            cs.scale(a2);
            let cs = mac_key.phi.endo_biquadratic_poly(cs);

            Ok(cs)
        }

        fn y_aux<C, F>(mac_key: &EndoMacKey<C, Affine<C>>, a3: F) -> Result<Poly<F>, GarbleError>
        where
            C: GLVConfig<BaseField = F>,
            C: PSqModR,
            F: Field,
        {
            let B = C::COEFF_B;
            let (x, y) = mac_key
                .k
                .xy()
                .ok_or_else(|| GarbleError::InvalidEndoMacKeyK(format!("{:?}", mac_key.k)))?;

            let mut cs = {
                //  (9*yQ_, 1)                  # c0
                let c0 = Some(F::from(3) * B * y);
                //  (0,   xP_),                 # c1 = 0
                let c1 = None;
                //  (-(yQ_^2 + 9), yP_)         # c2
                let c2 = Some(-(y.square() + F::from(3) * B));
                //  (3 * xQ_ * yQ_, xP_^2),     # c3
                let c3 = Some(F::from(3) * x * y);
                //  (-3 * xQ_^2, xP_ * yP_)     # c4
                let c4 = Some(-F::from(3) * x.square());
                //  (yQ_, yP_^2),               # c5
                let c5 = Some(y);

                Poly::biquadratic([c0, c1, c2, c3, c4, c5])
            };
            // scale by random a3 = a^3
            cs.scale(a3);

            let cs = mac_key.phi.endo_biquadratic_poly(cs);

            Ok(cs)
        }

        fn z_aux<C, F>(mac_key: &EndoMacKey<C, Affine<C>>, a: F) -> Result<Poly<F>, GarbleError>
        where
            C: GLVConfig<BaseField = F>,
            C: PSqModR,
            F: Field,
        {
            let x = mac_key
                .k
                .x()
                .ok_or_else(|| GarbleError::InvalidEndoMacKeyK(format!("{:?}", mac_key.k)))?;

            let mut cs = {
                //  (-xQ_,      1)]       # c0
                let c0 = Some(-x);
                //  (1, xP_)              # c1
                let c1 = Some(F::ONE);
                let c2 = None;
                let c3 = None;
                let c4 = None;
                let c5 = None;

                Poly::biquadratic([c0, c1, c2, c3, c4, c5])
            };
            // scale by random `a`
            cs.scale(a);
            let cs = mac_key.phi.endo_biquadratic_poly(cs);

            Ok(cs)
        }

        let mut x = Vec::with_capacity(output_mac_key.len());
        let mut y = Vec::with_capacity(output_mac_key.len());
        let mut z = Vec::with_capacity(output_mac_key.len());
        let mut doubling = Vec::with_capacity(output_mac_key.len());

        for (replica, key) in output_mac_key.iter().enumerate() {
            // Generate random scalar `a`
            let a = F::rand(rng);

            // Scale z coordinate by `a`
            let z_table =
                bivariate::Table::garble(&mut nonce, rng, Some(z_aux(key, a)?), input_mac_key)?.0;
            z.push(z_table);

            // Scale x coordinate by a^2
            let a2 = a.square();
            let x_table =
                bivariate::Table::garble(&mut nonce, rng, Some(x_aux(key, a2)?), input_mac_key)?.0;
            x.push(x_table);

            if is_full {
                // Scale y coordinate by a^3
                let a3 = a2 * a;

                let y_table = bivariate::Table::garble(
                    &mut nonce,
                    rng,
                    Some(y_aux(key, a3)?),
                    input_mac_key,
                )?
                .0;
                y.push(y_table);
            }

            // Only the holder of phi^{-1}(K)'s labels can decrypt `secret`.
            let doubling_input = EndoScalar::<Config>::iter()
                .into_iter()
                .take(6)
                .map(|inverse| inverse.endo(key.k))
                .find(|point| key.phi.endo(*point) == key.k);
            let mut ciphertext = [0; 48];
            match doubling_input {
                Some(point) => {
                    secret.serialize_compressed(&mut ciphertext[..32]).unwrap();
                    let labels = label_digest(&input_mac_key.encode(&point.into()));
                    apply_doubling_pad(&mut ciphertext, &labels, replica);
                }
                None => rng.fill_bytes(&mut ciphertext),
            }
            doubling.push(ciphertext);
        }

        Ok((
            Self {
                is_full,
                x,
                y: if is_full { Some(y) } else { None },
                z,
                doubling,
            },
            output_mac_key.clone(),
        ))
    }

    fn evaluate(
        &self,
        parent_nonce: &mut Nonce,
        input: &Input<Config::BaseField>,
        input_mac: &InputMac<Config::BaseField>,
    ) -> Result<(Affine<Config>, OutputMac<Config, KAPPA>), EvalError> {
        let mut nonce = parent_nonce.fork()?;

        let mut xs = Vec::with_capacity(self.x.len());
        let mut ys = if self.is_full {
            Vec::with_capacity(self.x.len())
        } else {
            vec![]
        };
        let mut zs = Vec::with_capacity(self.z.len());

        let y: &[_] = match (&self.y, self.is_full) {
            (Some(y), true) => y,
            (None, false) => &[],
            _ => return Err(EvalError::MissingYTablesError),
        };

        for (idx, (x_table, z_table)) in self.x.iter().zip(self.z.iter()).enumerate() {
            let z_table = z_table.evaluate(&mut nonce, input, input_mac)?.0;
            zs.push(z_table);

            let x_table = x_table.evaluate(&mut nonce, input, input_mac)?.0;
            xs.push(x_table);

            if self.is_full {
                let y_table = y.get(idx).ok_or(EvalError::MissingYTablesError)?;
                ys.push(y_table.evaluate(&mut nonce, input, input_mac)?.0);
            }
        }

        let mut zs_inv = zs;
        batch_inversion(&mut zs_inv);

        // Z = 0 exactly when phi(P) = -K, whose sum is the identity, or when
        // phi(P) = K, where X = 0 too and only `reveal` is meaningful.
        if xs
            .iter()
            .zip(&zs_inv)
            .any(|(x, z_inv)| x.is_zero() && z_inv.is_zero())
        {
            return Err(EvalError::DoublingInput);
        }

        let mut macs = Vec::with_capacity(KAPPA);
        for (idx, (x, z_inv)) in xs.into_iter().zip(zs_inv).enumerate() {
            if z_inv.is_zero() {
                macs.push(EndoMac::from(Affine::identity()));
                continue;
            }
            // Use Jacobian coordinates, so x / z^2, y / z^3
            let z2 = z_inv.square();
            let x = x * z2;

            let y = if self.is_full {
                ys[idx] * z_inv * z2
            } else {
                // y^2 = x^3 + b, which has no solution for an x from a
                // malformed table.
                (x.square() * x + Config::COEFF_B)
                    .sqrt()
                    .ok_or(EvalError::InvalidMacPoint)?
            };

            macs.push(EndoMac::from(Affine::new_unchecked(x, y)));
        }

        let macs: [EndoMac<Config, Affine<Config>>; KAPPA] =
            macs.try_into().map_err(|_| EvalError::MalformedTable)?;

        Ok((Affine::new_unchecked(input.x, input.y), macs.into()))
    }
}

#[cfg(test)]
fn test_field_mac_to_ec_mac<C, const KAPPA: usize>(is_full: bool, seed: u64)
where
    C: GLVConfig + Clone,
    C: PSqModR,
    C::BaseField: Field
        + NumBits
        + FromBits<bool, C::BaseField>
        + Random
        + ToBits
        + FromBits<C::BaseField, C::BaseField>,
    <C::BaseField as Field>::BasePrimeField: FromLeBytesModOrder,
    EndoMacKey<C, Affine<C>>: RandomFromPhi<Affine<C>, EndoMac<C, Affine<C>>>,
{
    use crate::{
        garble::bit_adaptor::clear_set as bit_adaptor_clear_set, mac::MacKey,
        utils::aes_hash::aes_ctr::clear_set as aes_ctr_clear_set,
    };
    use ark_std::{
        UniformRand,
        rand::{SeedableRng, rngs::StdRng},
    };

    let mut rng = StdRng::seed_from_u64(seed);

    let input_mac_key = InputMacKey::random_key(&mut rng);
    let output_mac_key = OutputMacKey::<_, KAPPA>::random_key(&mut rng);

    let input_point = Affine::<C>::rand(&mut rng);

    let input = input_point.into();
    let input_mac = input_mac_key.encode(&input);

    let output = input_point;
    let output_mac = output_mac_key.encode(&output);

    let garbling_table = Table::garble(
        &mut Nonce::new(),
        &mut rng,
        Some((is_full, output_mac_key, Fq::from(42u64))),
        &input_mac_key,
    )
    .unwrap()
    .0;
    aes_ctr_clear_set();
    bit_adaptor_clear_set();
    assert!(garbling_table.has_garbled_shape(is_full));
    assert!(!garbling_table.has_garbled_shape(!is_full));

    let evaluated_output = garbling_table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .1;
    aes_ctr_clear_set();
    bit_adaptor_clear_set();

    for (expected, evaluated) in output_mac.iter().zip(evaluated_output.iter()) {
        if **expected != **evaluated {
            if !is_full {
                assert_eq!(**expected, -**evaluated);
            } else {
                panic!()
            }
        }
    }
}

#[test]
fn test_field_mac_to_ec_mac_g1() {
    for seed in 0..5 {
        test_field_mac_to_ec_mac::<ark_bn254::g1::Config, KAPPA_A>(true, seed);
    }
    for seed in 0..5 {
        test_field_mac_to_ec_mac::<ark_bn254::g1::Config, KAPPA_B>(false, seed);
    }
}

#[test]
fn test_field_mac_to_ec_mac_g2() {
    for seed in 0..5 {
        test_field_mac_to_ec_mac::<ark_bn254::g2::Config, KAPPA_B>(false, seed);
    }
}

#[cfg(test)]
// Roundtrip serialisation and deserialisation of the table.
fn test_serde_roundtrip<C, const KAPPA: usize>(name: &str, is_full: bool)
where
    C: GLVConfig + Clone,
    C: PSqModR,
    C::BaseField: Field<BasePrimeField = Fq>
        + NumBits
        + FromBits<bool, C::BaseField>
        + Random
        + ToBits
        + FromBits<C::BaseField, C::BaseField>,
    EndoMacKey<C, Affine<C>>: RandomFromPhi<Affine<C>, EndoMac<C, Affine<C>>>,
{
    use crate::{
        garble::{Circuit, Nonce},
        mac::MacKey,
        utils::aes_hash::aes_ctr::clear_set,
    };
    use ark_ff::UniformRand;
    use ark_std::rand::{SeedableRng, rngs::StdRng};
    use std::fs::File;
    use std::io::{BufReader, BufWriter, Write};

    const SEED: u64 = 0;

    let mut rng = StdRng::seed_from_u64(SEED);

    let input_point = Affine::<C>::rand(&mut rng);
    let input = input_point.into();

    let input_mac_key = InputMacKey::random_key(&mut rng);
    let output_mac_key = OutputMacKey::<_, KAPPA>::random_key(&mut rng);

    let original_table = Table::<C, KAPPA>::garble(
        &mut Nonce::new(),
        &mut rng,
        Some((is_full, output_mac_key, Fq::from(42u64))),
        &input_mac_key,
    )
    .unwrap()
    .0;
    clear_set();

    let input_mac = input_mac_key.encode(&input);

    let original_output = original_table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .0;
    clear_set();

    std::fs::create_dir_all("bin").expect("Could not create directory /bin");
    let file_name = "bin/".to_owned() + name + ".bin";
    let file = File::create(&file_name).expect("Could not create file");
    let mut writer = BufWriter::new(file);
    original_table.serialize_compressed(&mut writer).unwrap();
    writer.flush().unwrap();

    drop(original_table);

    let file = File::open(&file_name).expect("Could not open file");
    let mut reader = BufReader::new(file);
    let deserialised_table = Table::<C, KAPPA>::deserialize_compressed(&mut reader).unwrap();
    let deserialised_output = deserialised_table
        .evaluate(&mut Nonce::new(), &input, &input_mac)
        .unwrap()
        .0;
    clear_set();

    assert_eq!(original_output, deserialised_output);
}

#[test]
fn test_A_serde_roundtrip() {
    test_serde_roundtrip::<ark_bn254::g1::Config, KAPPA_A>(&"A_field_to_ec_mac", true);
}

#[test]
fn test_B_serde_roundtrip() {
    test_serde_roundtrip::<ark_bn254::g2::Config, KAPPA_B>(&"B_field_to_ec_mac", false);
}

#[test]
fn test_C_serde_roundtrip() {
    test_serde_roundtrip::<ark_bn254::g1::Config, KAPPA_B>(&"C_field_to_ec_mac", false);
}
