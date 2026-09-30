//! Pin the embedded generators independently of their derivation and storage
//! representation by comparing their canonical coordinates with the original.

use ragu_core::{Cycle, FixedGenerators, pasta::Pasta};
use udon::{curve::Affine, field::Field};

#[test]
fn baked_points_match_original_parameters() {
    fn append<C: Affine<Base: Field>>(out: &mut Vec<u8>, generators: &impl FixedGenerators<C>) {
        for point in generators.g().iter().chain([generators.h()]) {
            let (x, y) = point.coordinates().expect("nonidentity generator");
            out.extend_from_slice(x.to_bytes().as_ref());
            out.extend_from_slice(y.to_bytes().as_ref());
        }
    }

    let params = ragu_pcd::pasta::baked();
    let mut loaded = Vec::new();
    append(&mut loaded, Pasta::nested_generators(params));
    append(&mut loaded, Pasta::host_generators(params));
    assert_eq!(loaded.len(), 16_386 * 64);

    // BLAKE2b-256 of the original canonical generator blob at Ragu commit
    // 4df34e723c4ee3a1541921aa24821ff86daf4c76, before the Udon migration.
    let digest = blake2b_simd::Params::new().hash_length(32).hash(&loaded);
    assert_eq!(
        digest.to_hex().as_str(),
        "f5b1146e2b607c83dcfd8630d117af24c8ea12593395a764100d81efca818ef2"
    );
}
