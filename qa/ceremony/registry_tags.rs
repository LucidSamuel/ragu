//! Derives an application's registry tags from a beacon output and code hash.
//!
//! ```text
//! cargo run -p ragu_ceremony --bin registry_tags -- <beacon-hex> <code-hash-hex>
//! ```
//!
//! `<beacon-hex>` is the beacon output as hex, for example the hash of the
//! Bitcoin block the ceremony selected. `<code-hash-hex>` is the committed
//! code hash as hex. Both are decoded to raw bytes before deriving the tags.
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
    let (Some(beacon_hex), Some(code_hash_hex), None) = (args.next(), args.next(), args.next())
    else {
        eprintln!("usage: registry_tags <beacon-hex> <code-hash-hex>");
        std::process::exit(2);
    };
    let beacon = decode_hex(&beacon_hex).unwrap_or_else(|e| {
        eprintln!("invalid beacon hex: {e}");
        std::process::exit(2);
    });
    let code_hash = decode_hex(&code_hash_hex).unwrap_or_else(|e| {
        eprintln!("invalid code hash hex: {e}");
        std::process::exit(2);
    });

    let tags = RegistryTags::<Pasta>::from_beacon(&beacon, &code_hash);
    println!("beacon ({} bytes): {}", beacon.len(), be_hex_bytes(&beacon));
    println!(
        "code hash ({} bytes): {}",
        code_hash.len(),
        be_hex_bytes(&code_hash)
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
