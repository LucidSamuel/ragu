<p align="center">
  <img width="300" height="80" src="https://tachyon.z.cash/assets/ragu/v1/github-600x160.png">
</p>

# `ragu_pcd`

This crate contains internal implementation code for the [`ragu`](https://crates.io/crates/ragu) crate.

The [`pasta`](src/pasta/) module owns Ragu's fixed generator derivation and
loading. With the `baked` feature, `build.rs` derives the generators on the host
using `pasta_curves` only for hash-to-curve, converts them to checked Udon points,
and writes them through Bento POD. The runtime embeds those typed points with
Bento; `pasta::baked()` adapts them once into Udon's parameter containers without
decoding coordinates. The derivation preserves Ragu's existing generators. The
feature enables `alloc` and supports `no_std`.

## Experimental proof bytes

`Proof::minimize` (through `ragu_primitives::wire::Minimize`) produces a
`MinimalProof`. Its `Encode::to_bytes` and `Decode::from_bytes` methods carry
the prover-provided fields and checked commitments. Use
`Application::verify_minimal` with the accompanying header data to verify a
decoded proof. Decoding establishes encoding validity; expansion reconstructs
omitted fields; neither substitutes for verification.

The optional `serde` feature carries the same bytes. The IPA representation
in [#462](https://github.com/tachyon-zcash/ragu/pull/462) needs its own codec
integration.

### Compatibility policy

These bytes are experimental and are not a stable interchange format. The
single version byte identifies the experimental envelope, not a proof schema,
curve suite, rank, application, or registry setup. Until a stable envelope is
specified, communicating parties must agree out of band on the implementation
revision, concrete proof types, application configuration and parameters, and
header interpretation. Successful decoding does not confirm that context.

The pre-Udon fixtures exercise selected primitive encodings and one complete
leaf proof against the current decoder and verifier. They protect those
migration cases; they do not promise compatibility with arbitrary past or
future revisions. Before publishing a stable format, specify schema and
context identifiers, rules for incompatible-version rejection, and migration
and compatibility tests. The wire envelope version is distinct from the
transcript's domain-separation tag.

### Resource limits

Direct decoding requires an explicit `Limits` value. Its defaults allow
1,048,576 aggregate container elements and 64 MiB of requested vector storage.
Temporary and normalized polynomial buffers both count. These are resource
policy limits, not rank-derived bounds or a guarantee that every valid proof
fits. They do not bound verifier computation, allocator overhead, or buffers
owned by an outer deserializer.

Serde uses those defaults and separately rejects encoded byte strings over
64 MiB. Its sequence visitor grows fallibly from observed bytes without
trusting a size hint. A format's deserializer may buffer input before calling
the visitor, so applications must also bound input at their transport layer.
Call the wire decoder directly when an application needs different limits.

Before declaring support for a proof configuration, validate its limits with
representative seed and recursive proofs and adversarial sparse layouts,
including normalization storage. A future rank-derived policy must account
for the number of retained polynomials and protocol vectors as well as rank;
increasing a global cap alone is not such a policy.

Fixed-length protocol encoding, consuming minimization, and size and timing
measurements can be evaluated independently of this experimental API.

## License

This library is distributed under the terms of both the MIT license and the Apache License (Version 2.0). See [LICENSE-APACHE](./LICENSE-APACHE), [LICENSE-MIT](./LICENSE-MIT) and [COPYRIGHT](./COPYRIGHT).
