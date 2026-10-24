# Correctness Review Policy

## Scope

Review safety, correctness, and robustness in Rust source files. Focus on code
that could cause unsoundness, panics, or subtle bugs.

## Error Handling

- No `unwrap()` or `expect()` in library code unless the invariant is documented
  and truly impossible to violate. Prefer propagating errors or using `assert!`
  for internal invariants.
- No `unsafe` without a `// SAFETY:` comment explaining why it's sound. The
  comment should address each safety requirement of the unsafe operation.
- Verify that the safety argument holds for the actual bounds, initialization,
  aliasing, lifetimes, and thread access. The presence of a comment is not enough.
- Trace errors through callers, callbacks, iterators, and early returns. Check
  for discarded failures, false success, incomplete cleanup, or partial state.
- Distinguish invalid external input from internal invariant violations. Input
  the API must reject must not reach assertions or unchecked access.

## Numeric Safety

- Avoid `as` casts between numeric types; prefer `try_into()` or explicit
  conversion functions that handle overflow. `as` casts silently truncate,
  which is almost never what you want in cryptographic code.
- Check empty and singleton inputs, exact bounds, and values just outside those
  bounds. Trace overflow, underflow, shifts, indexing, and size calculations in
  release mode and on supported integer widths.
- Verify length agreement where iterators are zipped or data is chunked. Silent
  truncation or a dropped remainder can lose required work without an error.

## State, Resources, and Concurrency

- Check ownership and cleanup on success, failure, and cancellation, including
  resource lifetimes, repeated effects on retry, and stale state.
- Check synchronization, lock order, and assumptions about task completion or
  ordering. Race or deadlock findings need a reachable interleaving.
- Check that cache keys and invalidation cover relevant inputs and configuration.
- Assess work and allocation driven by input size. Support resource or
  performance findings with a concrete input and cost argument or measurement.

## Test Quality

- Check that tests would fail for the suspected defect and assert the intended
  contract rather than repeat the implementation's calculation.
- Negative tests must reach the intended check and distinguish its failure from
  setup errors or panics. Include valid controls and relevant failure cases.
- Check that round trips or differential tests have a useful oracle: two paths
  sharing the same faulty helper can agree on an incorrect result.
- Recommend coverage for specific untested behavior; missing tests alone do not
  establish a production bug or justify requiring tests for every edit.

## Cryptographic Code

- Cryptographic code must be constant-time where timing side-channels matter.
  Document when constant-time behavior is required and verified.

## Assertions

- Use `assert!`, not `debug_assert!`. If an assertion is cheap enough to keep,
  keep it always. If it's too expensive for production, it's too expensive for
  debugging — write a test instead.
- Assertions guard invariants that correct callers cannot violate through the
  API. An assertion should never fire unless there's a bug in *this* code, not
  the caller's.

## Invariant Design

- Design code so invariants can be checked cheaply. If protecting an invariant
  requires an expensive assertion, restructure the code so the invariant is
  inherent (e.g., types that make invalid states unrepresentable) or move the
  check to a test.
- Expensive assertions are a code smell — they suggest either the invariant
  isn't worth checking at runtime, or the data structure doesn't make the
  invariant easy to verify.
- Move runtime checks to tests only when construction or an established contract
  guarantees the invariant for runtime inputs; preserve necessary input validation.
