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
            "b9c5cd4e0ca79da9a5d6d6e49eeb553021d06a424d05ff40b1ecf1b6d4830eab",
            "0848afc311b88dc89a9d1311780772c374812a74e9ffd3412c1728d872a2bf63",
        ]
    );
}

#[test]
fn golden_instance_hashes_without_garbled_inputs() {
    let hashes: Vec<_> = [0, 1].into_iter().map(instance_hash::<0>).collect();
    assert_eq!(
        hashes,
        [
            "c171e627cb9f81bb90f8ef926b232c8b0a02cdc49eb8db23d70d2778342abb3b",
            "6fae3f82e1132eb7ea80d11ec72cfee285219f5fcc6b8b4bc8c761248a7aeb08",
        ]
    );
}
