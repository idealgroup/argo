//! Golden vectors: hashes of instances garbled from fixed seeds. A change to
//! sampling, nonce order or serialization fails here, before garblers and
//! evaluators running different versions disagree on an instance.

use ark_bn254::{Bn254, G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;

use super::*;

/// Hashes the table, the secret and every label pair garbled from `seed`.
fn instance_hash<const N: usize>(seed: u8) -> String {
    let mut rng = ChaCha20Rng::from_seed([!seed; 32]);
    let verifier_key = VerifierKey::<N> {
        G1: std::array::from_fn(|_| G1Affine::rand(&mut rng)),
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Bn254::pairing(G1Affine::rand(&mut rng), G2Affine::generator()).0,
    };
    let garbling = garble(&verifier_key, [seed; 32]).unwrap();

    let mut bytes = Vec::new();
    garbling.table.serialize_compressed(&mut bytes).unwrap();
    garbling.secret.serialize_compressed(&mut bytes).unwrap();
    for pair in garbling.input_mac_key.label_pairs() {
        bytes.extend(pair.as_flattened());
    }
    blake3::hash(&bytes).to_hex().to_string()
}

#[test]
fn golden_instance_hashes() {
    let hashes: Vec<_> = [0, 1].into_iter().map(instance_hash::<1>).collect();
    assert_eq!(
        hashes,
        [
            "c10aefe9bc1b75dbcba4aba93af99c3cab4ab4c50d0d0aa2626ce6c016dc2b18",
            "49810b3fb7577cd584cc965ecc2facf252dfb84c0fa9e2c773bee0dc57a20363",
        ]
    );
}

#[test]
fn golden_instance_hashes_without_garbled_inputs() {
    let hashes: Vec<_> = [0, 1].into_iter().map(instance_hash::<0>).collect();
    assert_eq!(
        hashes,
        [
            "cad6f7719a06fa08bf0805f5c2fe07e01bb267127a969cb82f1f0ced27d259b3",
            "b63461a4a1684e2539977092780c8961b9b213b4d2be72d96c31580dda531811",
        ]
    );
}
