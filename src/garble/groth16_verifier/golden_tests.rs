//! Golden vectors: hashes of tables garbled from fixed seeds. A change to
//! sampling, nonce order or serialization fails here, before garblers and
//! evaluators running different versions disagree on a table.

use ark_bn254::{Bn254, Fq, G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_serialize::CanonicalSerialize;
use ark_std::{
    UniformRand,
    rand::{SeedableRng, rngs::StdRng},
};

use super::*;

fn table_hash(seed: u64) -> String {
    let mut rng = StdRng::seed_from_u64(seed);
    let secret = Fq::rand(&mut rng);
    let verifier_key = VerifierKey {
        G1: G1Affine::rand(&mut rng),
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Bn254::pairing(G1Affine::rand(&mut rng), G2Affine::generator()).0,
    };
    let input_mac_key = InputMacKey::random_key(&mut rng);
    let gid = GID::random(&mut rng);
    let table = garble_groth16(seed, secret, verifier_key, &input_mac_key, gid).unwrap();

    let mut bytes = Vec::new();
    table.serialize_compressed(&mut bytes).unwrap();
    blake3::hash(&bytes).to_hex().to_string()
}

#[test]
fn golden_table_hashes() {
    let hashes: Vec<_> = [0, 1].into_iter().map(table_hash).collect();
    assert_eq!(
        hashes,
        [
            "382e1551acc43cdb32c070a72b4956def23621296031a36d166175f67f3b9bcd",
            "56cd98274b573243512176b22881ed4ef0e649fcfe2c7b6a77b683a9880644bf",
        ]
    );
}
