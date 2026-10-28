use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
#[cfg(test)]
use ark_std::rand::Rng;
use ark_std::rand::RngCore;

use crate::{
    garble::{
        Circuit, Nonce,
        binary::{and, xor},
        groth16_verifier::GID,
    },
    mac::{
        Mac, MacKey, RandomFromPhi,
        binary::{self, And, BinaryInput, BinaryInputMac, Xor},
        bit::bytes::{Bit16ByteMac, Bit16ByteMacKey},
    },
    utils::error::{EvalError, GarbleError},
};

/// (x + p) (a + p) + a
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct Table {
    // (x + p)
    x_p: xor::Table,
    // (a + p)
    a_p: xor::Table,
    // x_p & a_p
    xp_ap: and::Table,
    // xp_ap XOR a
    output: xor::Table,
}

impl Table {
    pub(crate) fn has_garbled_shape(&self, gid: &GID) -> bool {
        self.xp_ap.has_garbled_shape(gid)
    }
}

#[derive(Debug)]
pub(crate) struct Input {
    pub(super) x: bool,
    pub(super) p: bool,
    pub(super) a: bool,
}

impl Input {
    #[cfg(test)]
    fn output(&self) -> bool {
        let Input { x, p, a } = self;
        ((x ^ p) & (a ^ p)) ^ a
    }
}

pub(crate) struct InputMac {
    pub(super) x: Bit16ByteMac,
    pub(super) p: Bit16ByteMac,
    pub(super) a: Bit16ByteMac,
}

pub(crate) struct InputMacKey {
    pub(super) x: Bit16ByteMacKey,
    pub(super) p: Bit16ByteMacKey,
    pub(super) a: Bit16ByteMacKey,
}

impl Mac<Input> for InputMac {
    type Key = InputMacKey;

    #[cfg(test)]
    fn random_input(rng: &mut ark_std::rand::prelude::StdRng) -> Input {
        Input {
            x: rng.gen_bool(0.5),
            p: rng.gen_bool(0.5),
            a: rng.gen_bool(0.5),
        }
    }
}

impl MacKey<Input, InputMac> for InputMacKey {
    fn encode(&self, value: &Input) -> InputMac {
        InputMac {
            x: self.x.encode(&value.x),
            p: self.p.encode(&value.p),
            a: self.a.encode(&value.a),
        }
    }

    #[cfg(test)]
    fn decode(&self, mac: &InputMac) -> Input {
        Input {
            x: self.x.decode(&mac.x),
            p: self.p.decode(&mac.p),
            a: self.a.decode(&mac.a),
        }
    }

    fn random_key(rng: &mut ark_std::rand::prelude::StdRng) -> Self {
        let mut phi = [0; 16];
        rng.fill_bytes(&mut phi);
        Self {
            x: Bit16ByteMacKey::random_from_phi(rng, &phi),
            p: Bit16ByteMacKey::random_from_phi(rng, &phi),
            a: Bit16ByteMacKey::random_from_phi(rng, &phi),
        }
    }
}

impl Circuit<Input, InputMac, bool, Bit16ByteMac> for Table {
    type Aux = [u8; 16];

    fn garble(
        parent_nonce: &mut Nonce,
        rng: &mut ark_std::rand::prelude::StdRng,
        aux: Option<Self::Aux>,
        input_mac_key: &<InputMac as Mac<Input>>::Key,
    ) -> Result<(Self, <Bit16ByteMac as Mac<bool>>::Key), GarbleError> {
        let mut nonce = parent_nonce.fork();

        // (x + p)
        let (x_p, xp_output_mac_key) = {
            let input_mac_key = binary::BinaryInputMacKey {
                left: input_mac_key.x.into(),
                right: input_mac_key.p.into(),
            };

            xor::Table::garble(&mut nonce, rng, None, &input_mac_key)?
        };

        // (a + p)
        let (a_p, ap_output_mac_key) = {
            let input_mac_key = binary::BinaryInputMacKey {
                left: input_mac_key.a.into(),
                right: input_mac_key.p.into(),
            };

            xor::Table::garble(&mut nonce, rng, None, &input_mac_key)?
        };

        // x_p & a_p
        let (xp_ap, xp_ap_output_mac_key) = {
            let input_mac_key = binary::BinaryInputMacKey::<And> {
                left: (*xp_output_mac_key).into(),
                right: (*ap_output_mac_key).into(),
            };

            and::Table::garble(&mut nonce, rng, aux, &input_mac_key)?
        };

        // xp_ap XOR a
        let (output, output_mac_key) = {
            let input_mac_key = binary::BinaryInputMacKey::<Xor> {
                left: (*xp_ap_output_mac_key).into(),
                right: input_mac_key.a.into(),
            };

            xor::Table::garble(parent_nonce, rng, None, &input_mac_key)?
        };

        let table = Self {
            x_p,
            a_p,
            xp_ap,
            output,
        };

        Ok((table, *output_mac_key))
    }

    fn evaluate(
        &self,
        parent_nonce: &mut Nonce,
        input: &Input,
        input_mac: &InputMac,
    ) -> Result<(bool, Bit16ByteMac), EvalError> {
        let mut nonce = parent_nonce.fork();

        let (x_p, xp_mac) = {
            let input = BinaryInput::new(input.x, input.p);
            let input_mac = BinaryInputMac::new(input_mac.x.into(), input_mac.p.into());
            self.x_p.evaluate(&mut nonce, &input, &input_mac)?
        };

        let (a_p, ap_mac) = {
            let input = BinaryInput::new(input.a, input.p);
            let input_mac = BinaryInputMac::new(input_mac.a.into(), input_mac.p.into());
            self.a_p.evaluate(&mut nonce, &input, &input_mac)?
        };

        let (xp_ap, xp_ap_mac) = {
            let input = BinaryInput::new(x_p, a_p);
            let input_mac = BinaryInputMac::<And>::new((*xp_mac).into(), (*ap_mac).into());

            self.xp_ap.evaluate(&mut nonce, &input, &input_mac)?
        };

        let (output, output_mac) = {
            let input = BinaryInput::new(xp_ap, input.a);
            let input_mac = BinaryInputMac::<Xor>::new((*xp_ap_mac).into(), input_mac.a.into());

            self.output.evaluate(&mut nonce, &input, &input_mac)?
        };

        Ok((output, *output_mac))
    }
}

#[test]
fn test_gate() {
    use crate::{mac::Random, utils::aes_hash::aes_mitccr::clear_set};
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    const SEED: u64 = 0;
    const N: usize = 100;

    let mut rng = StdRng::seed_from_u64(SEED);
    let gid = GID::random(&mut rng);

    for _ in 0..N {
        let input = InputMac::random_input(&mut rng);

        let input_mac_key = InputMacKey::random_key(&mut rng);
        let input_mac = input_mac_key.encode(&input);

        let (circuit, output_mac_key) =
            Table::garble(&mut Nonce::new(), &mut rng, Some(gid), &input_mac_key).unwrap();
        clear_set();
        assert!(circuit.has_garbled_shape(&gid));

        let output_mac = circuit
            .evaluate(&mut Nonce::new(), &input, &input_mac)
            .unwrap()
            .1;
        clear_set();

        let output = input.output();
        let expected_output_mac = output_mac_key.encode(&output);

        assert_eq!(output_mac, expected_output_mac);
    }
}
