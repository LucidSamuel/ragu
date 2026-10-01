//! Byte round trips of the minimal form of production-rank proofs.

use ragu_pcd::MinimalProof;
use ragu_primitives::wire::{Decode, Encode, Limits, Minimize};
use ragu_testing::pcd::nontrivial::{InternalNode, LeafNode};
use rand::{SeedableRng, rngs::StdRng};

mod nontrivial_support;
use nontrivial_support::{C, R, app, deep, leaf};

fn assert_round_trip(bytes: &[u8]) {
    let decoded = MinimalProof::<C, R>::from_bytes(bytes, Limits::default()).unwrap();
    assert_eq!(decoded.to_bytes(), bytes);
}

#[test]
fn seed_proof_round_trips() {
    let app = app();
    let mut rng = StdRng::seed_from_u64(0x5eed);
    let (proof, _) = leaf(&app, &mut rng, 7).into_parts();
    assert_round_trip(&proof.minimize().to_bytes());
}

// Proves seven production-rank proofs, so it runs with the scheduled heavy
// tests (`cargo test -- --ignored`) rather than on the PR gate.
#[test]
#[ignore]
fn fused_proof_round_trips() {
    let app = app();
    let (proof, data) = deep(&app).into_parts();
    let bytes = proof.minimize().to_bytes();
    assert_round_trip(&bytes);
    let decoded = MinimalProof::<C, R>::from_bytes(&bytes, Limits::default()).unwrap();
    assert!(
        app.verify_minimal::<_, InternalNode>(decoded, data, StdRng::seed_from_u64(0xdec1de))
            .unwrap()
    );
}

#[test]
fn decoded_proof_expands_and_verifies() {
    let app = app();
    let mut rng = StdRng::seed_from_u64(0x5eed);
    let (proof, data) = leaf(&app, &mut rng, 7).into_parts();
    let bytes = proof.minimize().to_bytes();
    let decoded = MinimalProof::<C, R>::from_bytes(&bytes, Limits::default()).unwrap();
    let expanded = app.expand(decoded).unwrap();
    // Expansion preserves the retained fields. The unit tests compare the
    // derived fields too, through the semantic proof comparison helper.
    assert_eq!(expanded.minimize().to_bytes(), bytes);
    assert!(
        app.verify(&expanded.carry::<LeafNode>(data), &mut rng)
            .unwrap()
    );
}

#[test]
fn minimal_proof_verifies_and_a_tampered_one_does_not() {
    let app = app();
    let mut rng = StdRng::seed_from_u64(0x5eed);
    let (proof, data) = leaf(&app, &mut rng, 7).into_parts();
    let bytes = proof.minimize().to_bytes();
    let decoded = MinimalProof::<C, R>::from_bytes(&bytes, Limits::default()).unwrap();
    assert!(
        app.verify_minimal::<_, LeafNode>(decoded, data, &mut rng)
            .unwrap()
    );

    // Another bridge alpha decodes fine, but the `ab` stage rebuilt from it
    // no longer matches the shipped commitment.
    let mut tampered = bytes;
    tampered[1..33].fill(0);
    tampered[1] = 2;
    let decoded = MinimalProof::<C, R>::from_bytes(&tampered, Limits::default()).unwrap();
    assert!(
        !app.verify_minimal::<_, LeafNode>(decoded, data, &mut rng)
            .unwrap()
    );
}

#[test]
fn malformed_proof_bytes_are_rejected() {
    let app = app();
    let mut rng = StdRng::seed_from_u64(0x5eed);
    let (proof, _) = leaf(&app, &mut rng, 7).into_parts();
    let bytes = proof.minimize().to_bytes();
    // Every strict prefix is missing at least one trailing value.
    for length in [0, 1, bytes.len() / 2, bytes.len() - 1] {
        MinimalProof::<C, R>::from_bytes(&bytes[..length], Limits::default())
            .err()
            .expect("truncated proof");
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(MinimalProof::<C, R>::from_bytes(&trailing, Limits::default()).is_err());
    let mut wrong_version = bytes;
    wrong_version[0] = ragu_primitives::wire::VERSION.wrapping_add(1);
    assert!(MinimalProof::<C, R>::from_bytes(&wrong_version, Limits::default()).is_err());
}

/// Decode a complete proof captured with the pre-Udon implementation, without
/// regenerating it using the current prover or RNG implementation.
#[test]
fn pre_udon_proof_decodes_and_verifies() {
    use ragu_core::pasta::Fp;
    use ragu_primitives::wire::Scalar;

    let bytes = include_bytes!("fixtures/wire/pre_udon_proof.bin");
    let header = include_bytes!("fixtures/wire/pre_udon_header.bin");
    let data = <Fp as Decode<Scalar>>::from_bytes(header, Limits::default()).unwrap();
    let decoded = MinimalProof::<C, R>::from_bytes(bytes, Limits::default()).unwrap();
    assert_eq!(decoded.to_bytes(), bytes);
    assert!(
        app()
            .verify_minimal::<_, LeafNode>(decoded, data, StdRng::seed_from_u64(0xdec1de))
            .unwrap()
    );
}
