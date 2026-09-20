//! Derives an application's registry tags from a randomness-beacon output.
//!
//! ```text
//! cargo run -p ragu_pcd --example registry_tags -- <beacon-hex>
//! ```
//!
//! `<beacon-hex>` is the beacon output as hex, for example the hash of the
//! Bitcoin block the ceremony selected. Prints the native and nested tags as
//! big-endian hex, ready to pin next to the beacon output and the timestamp
//! proof. See the "Registry Tags" section of the book for the procedure and
//! [`Tag`](ragu_circuits::registry::Tag) for the requirement the beacon output
//! must satisfy.

use ragu_arithmetic::ff::PrimeField;
use ragu_pasta::Pasta;
use ragu_pcd::RegistryTags;

fn main() {
    let arg = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: registry_tags <beacon-hex>");
        std::process::exit(2);
    });
    let beacon = decode_hex(&arg).unwrap_or_else(|e| {
        eprintln!("invalid beacon hex: {e}");
        std::process::exit(2);
    });

    let tags = RegistryTags::<Pasta>::from_beacon(&beacon);
    println!("beacon ({} bytes): {}", beacon.len(), be_hex_bytes(&beacon));
    println!("native tag (Fp): 0x{}", be_hex(tags.native.value()));
    println!("nested tag (Fq): 0x{}", be_hex(tags.nested.value()));
}

fn decode_hex(s: &str) -> Result<Vec<u8>, String> {
    let s = s.strip_prefix("0x").unwrap_or(s);
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
