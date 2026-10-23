---
name: tal-review
description: Review a PR, diff, or design using Tal Derei's evidence-based Ragu review style, emphasizing end-to-end verification, ordering, meaningful tests, API boundaries, and documentation fidelity. Use when Tal's review perspective is requested.
---

# Tal review

Apply the review priorities distilled from TalDerei's Ragu feedback. Produce
your own review; do not present it as Tal's review or approval. The historical
examples establish priorities, not the current protocol or merge policy.

Identify the requested files or diff and the exact base and head. Read the
affected callers, tests, and relevant current repository policies. Use history
when a deletion or refactor may undo a deliberate fix. Review locally unless
the user also asks you to publish feedback.

## Follow the claim through the implementation

Trace what is produced, encoded, committed, stored in the proof, recomputed,
and checked. Name the point where each value becomes authoritative. Check
that the native prover, circuit, verifier, and public instance describe the
same computation. A field being present in a proof or an application hook
returning a claim does not establish that the verifier consumes it.

For recursion, distinguish the current step from child proofs and the checks
deferred to a later step. Track the curve and field at each transition. Explain
transitive binding through the actual commitments and equality constraints;
do not substitute an honest witness generator for an adversarial check.

## Treat order and coverage as invariants

Inspect field serialization, reversal, Horner powers, polynomial queries,
claim iteration, stage registration, and commitment traversal together when
one changes. Matching counts do not prove matching order or coverage.

Prefer one authoritative enumeration or shared construction when it removes
real drift between callers. Check special fields outside the main enum too.
Investigate removed assertions and tests before calling them redundant, and
remove a check if the surrounding structure actually makes it tautological.

## Ask tests to exercise the claimed behavior

Choose a test that reaches the changed production path. Witness construction
alone does not exercise circuit synthesis; a smoke test does not verify every
stage; a trivial proof can make a corruption check vacuous.

Look for asymmetric dimensions when symmetric parameters hide indexing bugs,
zero and one at meaningful boundaries, both success and error controls, and
Known/Unknown combinations under nested routines. When testing recursion or
binding, use a valid nontrivial baseline and change the relevant component.
State exactly what rejection demonstrates. Do not call finite tests a proof
of soundness. Extend an existing property test when it covers the invariant
more directly than another overlapping test module.

## Preserve contracts across boundaries

Check what survives driver remapping, scope restoration, staging, and error
returns. Gadget constraints concern wires; a witness value is not itself a
constraint. A context-free consistency operation must work after prior
constraints have been stripped, even when an optimized equality operation is
safe in its original context.

Distinguish a contract violation from a presently reachable exploit. Add
defensive checks where they protect a real invariant; examine whether they
are too restrictive or already implied before prescribing them everywhere.

## Reduce friction without moving it to callers

Check the dependency graph and the intended consumer of an API. Put shared
logic at the layer that can own it without reversing dependencies. Challenge
unused public methods, test-only production APIs, and new traits or crates
without a concrete need. Consider semantic structs, aliases, and shared
helpers when they make existing call sites clearer.

Judge a refactor from the application developer's side: does it eliminate
bookkeeping, or require the caller to understand another internal distinction?
Keep unrelated API redesigns separate from a focused correctness change.

## Account for actual work and actual documentation

Follow allocations, deep clones, borrowed data, reference-counted sharing,
copy-on-write behavior, and repeated commitments through the real hot path.
An Arc around a cloned value does not remove the deep clone. A cache is useful
only when the expensive work is actually reused. Evaluate a performance
claim against the relevant workload and baseline, including whole fuse/proof
generation when that is the stated benefit; keep counts and timings distinct.

Check affected book pages, examples, comments, tests, and benchmarks for stale
names and changed contracts. Explain what the code does at this revision;
label proposals and incomplete wiring. Distinguish encoding from verification,
constraints from native arithmetic, and a proof component from a stage.
Prefer a motivating overview and then the concrete flow. Avoid duplicate
implementations or fragile numeric inventories in prose.

## Give feedback in Tal's manner

Start with the concrete concern and its cross-file consequence. Use a short
question when the invariant or design intent is unclear, then give the
specific check, test, or minimal change that would resolve it. Reference a
previous discussion only when it supplies necessary rationale.

Separate must-fix defects or demonstrated contract violations from unresolved
questions, suggestions, and nits. Say when a pass was limited or preliminary.
Do not turn an intuitive concern into a confirmed bug, infer merge readiness
from a local check, or issue an approval on Tal's behalf. Return only useful
findings, with current file locations and the validation actually performed;
there is no minimum finding count.

Read [references/evidence.md](references/evidence.md) when calibrating these
priorities, checking an apparent exception, or explaining their provenance.
