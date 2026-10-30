# Fuse fixtures

Golden fixtures for the fuse pipeline and the compressed verifier, checked by
`tests/fuse_fixtures.rs` and by the `fuse fixtures` CI job. They pin what
`Application::fuse` produces and what `Application::verify_compressed`
accepts, so a change to either fails CI instead of passing silently.

The prover side follows the golden-proof harness of zakura-common's `sensei`
crate: the prover replays a committed randomness tape and must reproduce the
committed proof byte for byte, consuming exactly the tape. Sensei exposes only
a prover, so its goldens stop there; the verifier fixtures here are the
extension ragu's verifier allows.

## Profiles

Each profile has its own directory: `standard/` for the wallet's profile and
`aggregator/` for the aggregator's. Both prove the same scenarios from the
same seeds, so a diff between the directories is exactly what the profile
changes. Until the aggregator's decompression circuits land, the profile
declares nothing and its proofs are the standard ones, so the two directories
are identical; they diverge when it does.

## Scenarios

One fixture per node of a fixed tree of fuses over the harness's own steps
(`Seed`, `Merge`, `UnitLeft`, and `UnitRight`, which is registered but never
fused), at production rank with header size 4, on the baked Pasta parameters:

| Scenario      | Header  | Fuses                                              |
| ------------- | ------- | -------------------------------------------------- |
| `bootstrap`   | `()`    | the bootstrap step over two dummy proofs           |
| `seed_a`..`d` | `Value` | a seed with salt 13, 17, 19, 23 over `bootstrap`   |
| `unit_left`   | `Value` | `UnitLeft` over `bootstrap` and `seed_a`           |
| `merge_ab`    | `Value` | `Merge` over `seed_a` and `seed_b`                 |
| `merge_cd`    | `Value` | `Merge` over `seed_c` and `seed_d`                 |
| `merge_abcd`  | `Value` | `Merge` over `merge_ab` and `merge_cd`             |
| `rerandomize` | `Value` | the rerandomize step over `merge_abcd`             |

The `bootstrap` scenario re-proves the bootstrap proof under the fixture
randomness and installs it in the application, since `finalize` proves it
under `StdRng`, whose output `Cargo.lock` pins but `rand`'s API does not, and
every seed fuses it as both children. The `rerandomize` tape also covers the
seeded trivial proof the step fuses against, which the application proves on
first use.

## Files

Each scenario has three files.

- `<scenario>.rng-u64s-le`: the randomness the fuse drew, as little-endian
  `u64` words. Checking replays it and fails if the prover asks for more or
  leaves any unused.
- `<scenario>.proof`: the header data, then the compressed proof, in the
  harness's own encoding: an eight-byte tag, canonical field and point
  encodings, little-endian `u32` lengths. It is a fixture format, not a wire
  format. The prover must reproduce these bytes, and the verifier must accept
  them as committed, without re-proving. Compression draws a megabyte of
  blinding per proof, too much to commit as a tape, so its randomness comes
  from the harness's frozen generator under a fixed seed and is pinned by its
  word count and these bytes.
- `<scenario>.digests`: `key = value` lines. One BLAKE2b-256 digest per
  primary field of the uncompressed proof, in declaration order, over the
  field's canonical bytes (every coefficient of a polynomial, zeros included);
  then `rng.fuse.words`, `rng.compress.words` and `proof.bytes`. The
  uncompressed proof is over ten megabytes at production rank, so this stands
  in for committing it. A mismatch names the fields that drifted, and the
  file's diff in a pull request reads as the list of stages a change touched.

The verifier test also checks three tampered copies of each proof: a wrong
IPA scalar on either curve, and a wrong claimed `v`. Each must be rejected.
These are checked, not committed.

## Regenerating

After an intended change to the prover, run

```console
RAGU_FIXTURES=write cargo test --release -p ragu_pcd --all-features --lib proof::fuse_fixture_tests
```

and review the diff before committing it. The `.digests` diff should name
exactly the stages the change was meant to touch; a change to
`rng.fuse.words` means the randomness schedule moved. Fresh tapes come from
the harness's
SplitMix64 generator, which is not cryptographically secure and exists only to
make synthetic test data reproducible; it must never produce a real proof.

The tests are ignored without `--release`: production-rank proving is
impractically slow in debug builds.
