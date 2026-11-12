//! Golden vectors: hashes of instances garbled from fixed seeds. A change to
//! sampling, nonce order or serialization fails here, before garblers and
//! evaluators running different versions disagree on an instance.

use ark_bn254::{Bn254, G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;

use super::*;

fn verifier_key<const N: usize>(seed: u8) -> VerifierKey<N> {
    let mut rng = ChaCha20Rng::from_seed([!seed; 32]);
    VerifierKey {
        G1: std::array::from_fn(|_| G1Affine::rand(&mut rng)),
        H1: G2Affine::rand(&mut rng),
        H2: G2Affine::rand(&mut rng),
        c: Bn254::pairing(G1Affine::rand(&mut rng), G2Affine::generator()).0,
    }
}

/// Hashes the table, the secret and every label pair garbled from `seed`.
fn instance_hash<const N: usize>(seed: u8) -> String {
    let garbling = garble(&verifier_key::<N>(seed), [seed; 32]).unwrap();

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
            "8ab6ed88de5790fa6e2bc329349169a08d69df46711a6e73b423e41f19611fa9",
            "55d654e6eec81543e865d358765d113548bedf06c696a991a1b9e5581c82e1d5",
        ]
    );
}

/// Deserialization stops at `garbled_size`, so it must be the exact length
/// of every garbled table, for each `N` and both encodings.
#[test]
fn garbled_size_is_the_serialized_size() {
    fn check<const N: usize>() {
        let table = garble(&verifier_key::<N>(0), [0; 32]).unwrap().table;
        for compress in [Compress::Yes, Compress::No] {
            let mut bytes = Vec::new();
            table.serialize_with_mode(&mut bytes, compress).unwrap();
            assert_eq!(bytes.len(), Table::<N>::garbled_size(compress));
            let decoded =
                Table::<N>::deserialize_with_mode(&bytes[..], compress, Validate::Yes).unwrap();
            let mut again = Vec::new();
            decoded.serialize_with_mode(&mut again, compress).unwrap();
            assert!(again == bytes);
        }
    }
    check::<0>();
    check::<1>();
    check::<2>();
}

#[test]
fn golden_instance_hashes_without_garbled_inputs() {
    let hashes: Vec<_> = [0, 1].into_iter().map(instance_hash::<0>).collect();
    assert_eq!(
        hashes,
        [
            "464f6cc0f93d18afc1ec19d84c20e4a41ef8791fe3b369c300a23bcca5ee6d86",
            "e4d63ffd7f546b3133b2b1e599878c2d8e9fb79e9fe36ac69b69f16f981cda6d",
        ]
    );
}
