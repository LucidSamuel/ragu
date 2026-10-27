---
name: tal-review
description: "Review Ragu changes using Tal Derei's priorities: end-to-end verification, ordering, meaningful tests, and API boundaries. Use when Tal's perspective is requested."
---

# Tal review

Apply the relevant priorities below to the requested scope and exact revisions,
using current code, affected callers, tests, and repository policies. Give your
own review, not Tal's approval. Keep feedback local unless publication is
authorized.

## Follow the claim through the implementation

Trace what is produced, encoded, committed, stored, recomputed, and checked.
Name where each value becomes authoritative. The native prover, circuit,
verifier, and public instance must describe the same computation; a proof field
or application claim is not verified merely by being present.

For recursion, separate the current step, child proofs, and deferred checks;
track curves and fields. Explain transitive binding through commitments and
equalities rather than honest witness generation.

## Treat order and coverage as invariants

Inspect serialization, reversal, Horner powers, polynomial queries, claim
iteration, stage registration, and commitment traversal together. Equal counts
do not establish order or coverage. Prefer one authoritative enumeration or
construction where it prevents drift, including special fields outside enums.
Use history before dismissing a removed check or test; remove checks that are
actually implied by surrounding invariants.

## Ask tests to exercise the claimed behavior

Tests must reach the changed production path. Witness construction does not
exercise synthesis, smoke tests do not cover every stage, and trivial proofs
can make corruption tests vacuous. Use asymmetric dimensions, meaningful zero
and one cases, success/error controls, and Known/Unknown combinations in nested
routines. For binding tests, mutate a relevant component of a valid nontrivial
baseline and state what rejection demonstrates. Finite tests are not soundness
proofs; extend an existing property test when it covers the invariant directly.

## Preserve contracts across boundaries

Check driver remapping, scope restoration, staging, and error returns. Gadget
contracts concern wires, not witness values; context-free consistency must
work after prior constraints are stripped. Distinguish a contract violation
from a reachable exploit. Defensive checks need a real obligation and must not
reject valid cases or duplicate existing enforcement.

## Reduce friction without moving it to callers

Put shared logic in the layer that owns it without reversing dependencies.
Challenge unused public methods, test-only production APIs, and traits or crates
without consumers. Use semantic types or helpers when they simplify real calls.
Assess refactors from the application developer's side: remove bookkeeping
without moving internal distinctions to callers. Keep unrelated redesign separate.

## Account for actual work and actual documentation

Follow allocations, deep clones, borrowing, reference-counted sharing,
copy-on-write, caching, and repeated commitments through the hot path. Wrapping
a clone in Arc does not remove it. Match performance claims to the actual
workload and baseline, including full fuse/proof generation when claimed;
distinguish operation counts from timings.

Check book pages, examples, comments, tests, and benches for stale contracts.
Describe current behavior and label proposals. Distinguish encoding from
verification, native arithmetic from constraints, and components from stages.
Start with motivation and concrete flow; avoid duplicate implementations and
fragile numeric inventories.

## Give feedback in Tal's manner

Lead with the concrete concern and cross-file consequence. For uncertainty,
ask the specific question and identify the check or change that would settle
it. Cite prior discussions only for necessary rationale. Separate defects and
demonstrated contract violations from questions, suggestions, and nits. Do not
turn an intuitive concern into a confirmed bug. Report current locations,
checks, and coverage limits; local validation alone does not establish merge
readiness. There is no finding quota.

Consult [references/evidence.md](references/evidence.md) when provenance is
requested or an ambiguity about applying a priority could change a finding.
Historical examples do not override current code, protocol, or repository
policies.
