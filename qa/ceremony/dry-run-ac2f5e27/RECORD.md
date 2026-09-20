# Registry tag ceremony — dry run for `ac2f5e27`

Prepared QA record for the temporary registry-collision workaround described
in [the ceremony guide](../README.md). It uses Pasta production parameters
and the built-in circuits, with no application-defined steps.

**Status:** the manifest is prepared. No timestamp has been submitted, and
no Bitcoin beacon output or registry tags have been selected. Pending fields
in `attestation.txt`, `beacon.txt`, and `tags.txt` will be filled by
`./continue.sh`; `setup.manifest.ots` will be created when it stamps the
manifest.

## Frozen setup

```rust
ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
    .with_registry_tags(tags)
    .finalize(Pasta::baked())?
```

The backend is `ReferenceBackend`. Both registries use rank 13, with four
header elements; there are 15 native circuits and 23 nested circuits.
`insecure-test-registry-tag` is disabled. Registering application steps
changes the description and requires a new manifest and tags.

- Source commit: `ac2f5e27c51ae9590d604cddab43e1d38d5bf20d` (`commit.txt`).
- Entire codebase SHA-256: `e4f871b7fde3cb801c11cac0fd99c90296faf793ef3c8600634775b3e2d414e2`.
- Manifest SHA-256: `3b91865817fcb38e83f398ce6c9257bb9701ae9650e115ac5d1dd0b94ec06708` (`manifest_digest.txt`).

`setup.manifest` uses the canonical encoding in the guide. It fixes the
ordered circuits, fields and domains, capacities, transcript rules and
labels, public parameters, toolchain, target, build features and setup
choices. Inspect it with `python3 -m json.tool setup.manifest`.

## Content binding

The source digest covers all 723 files tracked by the source commit,
including the book. The manifest also includes the full Git commit ID as
provenance. This record was created afterward and is outside that snapshot,
so the commitment is not self-referential. Recompute the digests from this
directory without retaining an archive:

```sh
git archive --format=tar "$(cat commit.txt)" | shasum -a 256
git show "$(cat commit.txt):Cargo.lock" | shasum -a 256
shasum -a 256 setup.manifest
```

The manifest hashes `Cargo.lock`, which pins all 156 external registry
packages by SHA-256 crate-archive checksums. `source:path` references resolve
inside the frozen source; `dependencies:crate-version/path` references
resolve inside the pinned crate archive. Public parameters are identified
by their SHA-256 digest and by the generation and serialization code in the
frozen source. No tarballs or parameter binaries are stored in this record.

The production libraries were built from the frozen source with the pinned
dependencies, using Rust 1.97.1:

```sh
cargo +1.97.1 build --release --offline --locked --lib \
  -p ragu_pcd -p ragu_pasta --features ragu_pasta/baked \
  --target aarch64-apple-darwin
```

The resolved features and generated `ragu_pasta` parameter bytes matched
the manifest. The latter are written to
`target/aarch64-apple-darwin/release/build/ragu_pasta-*/out/pasta_parameters.bin`.

## Continue

Run `./continue.sh` from this directory to stamp and verify `setup.manifest`.
Once its Bitcoin attestation is verified and block `N + 100` exists, the
script records that block's hash and derives the tags from it and the
manifest digest. Verification requires a Bitcoin Core node configured for
OpenTimestamps. An explicit block-height argument exercises a dry run
without the ordering guarantee; the script records that selection rule.

Keep `commit.txt`, `setup.manifest`, `manifest_digest.txt`,
`setup.manifest.ots`, `attestation.txt`, `beacon.txt`, and `tags.txt` together.
