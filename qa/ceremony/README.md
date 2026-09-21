# Example registry tag ceremony

This directory contains QA tooling and example records for the temporary
registry-collision workaround in [#78](https://github.com/tachyon-zcash/ragu/issues/78).
The API change is temporary setup-time tag injection. The manifest format,
OpenTimestamps service, Bitcoin beacon, and block-selection rule below are
choices for exercising that API in QA, not a production ceremony specification.
Consumers can use their own setup procedure while satisfying the
[sampling requirement](../../book/src/guide/configuration.md#registry-tags).

This example commits to the complete setup of both registries before the
Bitcoin beacon output is known. `registry_tags` derives the tags from the
beacon bytes and `X = SHA-256(setup.manifest)`. The manifest binds the actual
code, dependency, and public-parameter artifacts by SHA-256 content digests.
The Rust `manifest_digest` argument receives `X`.
For Git-based source snapshots, include their full commit IDs in `provenance`.
These IDs are covered by the manifest digest and timestamp along with the
artifact digests. Hashing a SHA-1 commit ID again does not strengthen its
binding to the code contents.

## Prepare the manifest

Freeze the entire application and Ragu codebase at identified revisions first.
Hash the complete source snapshots. Create the ceremony records separately
afterward: the manifest, timestamp proof, beacon record, and derived tags refer
to those frozen snapshots and are not part of them.

Copy [setup.manifest.example.json](setup.manifest.example.json) to `setup.json`
in a new ceremony directory. Replace every placeholder with the exact setup;
expand the example lists and maps as needed. Record application steps in
registration order and all inputs that determine their circuits. Values
already fixed by committed code can refer to an artifact, path, and item in
that code instead of being repeated. Include every remaining build and setup
choice.

The example records keep digests and reproduction details, without storing
source archives or parameter binaries. For a Git snapshot, hash the archive
stream directly:

```sh
git archive --format=tar <source-commit> | shasum -a 256
```

This covers the snapshot's contents, including the book. Record how each
input can be reconstructed in `artifacts`, along with its SHA-256 digest.
Registry dependencies can be bound through a hashed `Cargo.lock` whose
`checksum` entries are SHA-256 digests of the crate archives. Dependencies
without those checksums need separate content digests. Hash generated public
parameter bytes and identify their generator and encoding in the frozen code.
A filename or Git commit ID does not replace a content digest.

For `ragu-setup-manifest-v1`, use JSON objects, arrays, strings, integers,
booleans, and null; duplicate object keys and floating-point numbers are
not allowed. Canonical bytes are the ASCII output of Python's `json.dumps`
with `sort_keys=True`, `ensure_ascii=True`, and `separators=(",", ":")`,
followed by one LF byte. Array order is preserved. These are this format's
encoding rules, including for any additional setup fields.

Run the following from the new ceremony directory to write `setup.manifest`
and write `X` to `manifest_digest.txt`:

```python
import hashlib
import json
from pathlib import Path

def unique_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate key: {key}")
        result[key] = value
    return result

def reject_number(value):
    raise ValueError(f"non-integer number: {value}")

manifest = json.loads(
    Path("setup.json").read_text(encoding="utf-8"),
    object_pairs_hook=unique_keys,
    parse_float=reject_number,
    parse_constant=reject_number,
)
if manifest["format"] != "ragu-setup-manifest-v1":
    raise ValueError("unsupported manifest format")
encoded = (json.dumps(manifest, sort_keys=True, ensure_ascii=True,
                      separators=(",", ":"), allow_nan=False) + "\n").encode("ascii")
Path("setup.manifest").write_bytes(encoded)
digest = hashlib.sha256(encoded).hexdigest()
Path("manifest_digest.txt").write_text(digest + "\n", encoding="ascii")
print(digest)
```

This serializes the supplied description; it does not check completeness or
whether its artifact digests match the deployed setup.

## Timestamp and derive

The example uses the following steps after freezing the manifest, including
the beacon selection rule and derivation labels:

1. Run `ots stamp setup.manifest` and keep `setup.manifest.ots`. Once a
   calendar transaction confirms, run `ots upgrade setup.manifest.ots`.
2. Run `ots verify setup.manifest.ots` against a configured Bitcoin Core
   node. Use the earliest **verified** attestation height `N`. `ots info`
   displays metadata but does not verify the timestamp.
3. Wait for block `N + 100` and record its hash `B` from more than one source.
   A future Bitcoin block provides unpredictability after commitment, not
   unbiasability; this assumes miners do not selectively withhold blocks or
   reorganize the chain to bias the tags.
4. Derive the tags below, then record the inputs, outputs, and timestamp proof
   together so the derivation can be reproduced.

With `B` and `X` both expressed as hex, run from the repository root:

```sh
cargo run -p ragu_ceremony --bin registry_tags -- B X
```

Keep the canonical manifest, timestamp proof, beacon selection record, and
resulting tag pair together, with access to the referenced source and inputs.
A changed description needs a fresh ceremony; do not reuse a known beacon
output to regenerate these records.

To check a record, match the artifact digests to the setup, recompute `X`,
verify the timestamp, check block `N + 100`'s hash independently, and repeat
the tag derivation.

## Example record

Each `dry-run-<commit>/` directory is a flat record named after its source
revision. `RECORD.md` describes the setup and status; `commit.txt` records the
full source commit ID. `setup.manifest` and `manifest_digest.txt` add the
complete setup commitment to the original `attestation.txt`, `beacon.txt`,
and `tags.txt` fields.

Run the record's `./continue.sh` to timestamp the manifest and, once its
attestation is verified and the beacon block exists, derive the tags. The
proof is `setup.manifest.ots`, created when the manifest is timestamped.
An explicit block-height argument exercises a dry run without the ordering
guarantee. Pending fields are marked as such; they are not usable setup tags.

The shared [continue.sh](continue.sh) implements this example. Its offline
regressions run with `python3 qa/ceremony/test_continue.py`.
