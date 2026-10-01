//! Proof decoding must preserve values and reject malformed protocol layouts.

use ragu_circuits::polynomials::ProductionRank;
use ragu_core::pasta::Pasta;
use ragu_primitives::wire::{Compress, Decode, Encode, Limits};
use rand::{SeedableRng, rngs::StdRng};

use super::CompressedProof;
use crate::ApplicationBuilder;

#[test]
fn decoded_proof_preserves_derived_fields_and_rejects_wrong_vector_lengths() {
    let app = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .finalize(crate::pasta::baked())
        .unwrap();
    let mut rng = StdRng::seed_from_u64(0x5eed);
    let pcd = app.bootstrap_pcd();
    assert!(app.verify(&pcd, &mut rng).unwrap());
    let (proof, ()) = pcd.into_parts();
    let bytes = proof.compress().to_bytes();
    let decode = |bytes: &[u8]| {
        CompressedProof::<Pasta, ProductionRank>::from_bytes(bytes, Limits::default()).unwrap()
    };
    let expanded = app.expand(decode(&bytes)).unwrap();
    assert_eq!(proof.test_mismatch(&expanded), None);
    assert!(app.verify(&expanded.carry::<()>(()), &mut rng).unwrap());

    // Each vector has a protocol-fixed length. Test both missing and surplus
    // entries independently, including the commitment side of each pair.
    macro_rules! reject_lengths {
        ($($field:ident),* $(,)?) => {$(
            for extra in [false, true] {
                let mut compressed = proof.compress();
                if extra {
                    compressed.$field.push(compressed.$field[0].clone());
                } else {
                    compressed.$field.pop().unwrap();
                }
                let malformed = compressed.to_bytes();
                assert!(
                    !app.verify_compressed::<_, ()>(decode(&malformed), (), &mut rng).unwrap(),
                    "{} (extra: {extra})", stringify!($field),
                );
            }
        )*};
    }
    reject_lengths!(
        native_bind_challenges_rxs,
        native_bind_challenges_commitments,
        native_endoscaling_step_rxs,
        native_endoscaling_step_commitments,
        nested_endoscaling_step_rxs,
        nested_endoscaling_step_commitments,
    );
}
