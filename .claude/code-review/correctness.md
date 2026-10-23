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
  for discarded failures, misleading success results, incomplete cleanup, and
  partially updated state that later operations can observe.
- Distinguish invalid external input from an internal invariant violation.
  Check that supported callers cannot trigger an assertion or unchecked access
  with input the API is meant to reject through its error path.

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

- Follow ownership and cleanup on success, failure, and cancellation paths.
  Check resource lifetimes and whether retries can repeat externally visible
  effects or leave stale state behind.
- For shared state, check synchronization, lock order, and assumptions about
  task completion or ordering. Explain a reachable interleaving for a race or
  deadlock finding.
- Check that cache keys and invalidation cover the inputs and configuration
  that determine the cached value.
- Assess work and allocation driven by input size. Support resource or
  performance findings with a concrete input and cost argument or measurement.

## Test Quality

- Find tests for the changed behavior and check whether they would fail with
  the suspected defect. Assertions should establish the intended result or
  contract rather than repeat the implementation's calculation.
- Check valid controls and relevant failure cases. A negative test must reach
  the intended check, and its expected error must distinguish that failure from
  an unrelated setup error or panic.
- Check that round trips or differential tests have a useful oracle: two paths
  sharing the same faulty helper can agree on an incorrect result.
- Recommend additional coverage for a specific untested behavior. Do not infer
  a production bug from an absent test or require new tests for every edit.

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
- Tests supplement runtime validation. Moving a check to a test is appropriate
  only when runtime inputs already satisfy the invariant by construction or
  through an established contract; it must not remove necessary input validation.
