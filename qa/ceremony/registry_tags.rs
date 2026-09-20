//! Derives an application's registry tags from a beacon output and manifest digest.
//!
//! QA tooling for the temporary registry-collision workaround. The caller
//! chooses the beacon and setup procedure; this tool only derives the tags.
//!
//! ```text
//! cargo run -p ragu_ceremony --bin registry_tags -- <beacon-hex> <manifest-digest-hex>
//! ```
//!
//! `<beacon-hex>` is the beacon output as hex, for example the hash of the
//! Bitcoin block the ceremony selected. `<manifest-digest-hex>` is the digest of
//! the canonical, versioned setup manifest covering the code and complete
//! setup of both registries, as hex. Both inputs are decoded to raw bytes
//! before deriving the tags.
//! The documented ceremony uses SHA-256 of `setup.manifest`, whose artifact
//! digests bind the actual code and parameter bytes. A Git commit ID, or a
//! hash of that ID, is not a substitute. See `qa/ceremony/README.md`.
//! Prints the native and nested tags as big-endian hex, ready to pin next to
//! the inputs and timestamp proof. See the "Registry Tags" section of the
//! book for the procedure and [`RegistryTags::from_beacon`]
//! for the sampling requirement. Use [`ApplicationBuilder::with_registry_tags`](ragu_pcd::ApplicationBuilder::with_registry_tags)
//! to build an application with these tags.

use ragu_arithmetic::ff::PrimeField;
use ragu_pasta::Pasta;
use ragu_pcd::RegistryTags;

fn main() {
    let mut args = std::env::args().skip(1);
    let (Some(beacon_hex), Some(manifest_digest_hex), None) =
        (args.next(), args.next(), args.next())
    else {
        eprintln!("usage: registry_tags <beacon-hex> <manifest-digest-hex>");
        std::process::exit(2);
    };
    let beacon = decode_hex(&beacon_hex).unwrap_or_else(|e| {
        eprintln!("invalid beacon hex: {e}");
        std::process::exit(2);
    });
    let manifest_digest = decode_hex(&manifest_digest_hex).unwrap_or_else(|e| {
        eprintln!("invalid manifest digest hex: {e}");
        std::process::exit(2);
    });

    let tags = RegistryTags::<Pasta>::from_beacon(&beacon, &manifest_digest);
    println!("beacon ({} bytes): {}", beacon.len(), be_hex_bytes(&beacon));
    println!(
        "manifest digest ({} bytes): {}",
        manifest_digest.len(),
        be_hex_bytes(&manifest_digest)
    );
    println!("native tag (Fp): 0x{}", be_hex(tags.native.value()));
    println!("nested tag (Fq): 0x{}", be_hex(tags.nested.value()));
}

fn decode_hex(s: &str) -> Result<Vec<u8>, String> {
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.is_empty() || !s.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("expected a nonempty ASCII hex string".into());
    }
    if !s.len().is_multiple_of(2) {
        return Err("odd number of hex digits".into());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}

fn be_hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Big-endian hex of a field element, matching the `fp!`/`fq!` literal format.
fn be_hex<F: PrimeField>(f: F) -> String {
    f.to_repr()
        .as_ref()
        .iter()
        .rev()
        .map(|b| format!("{b:02x}"))
        .collect()
}
