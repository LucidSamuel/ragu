---
name: sean-review
description: "Review Ragu changes using Sean Bowe's priorities: protected contracts, minimal abstractions, and precise documentation. Use when Sean's perspective is requested."
---

# Sean review

Apply the relevant priorities below to the requested scope and exact revisions,
using current code, affected callers, and repository policies. Give your own
review, not Sean's approval. Keep feedback local unless publication is authorized.

## Make the contract do the work

Ask which states a correct caller can construct. Put invariants in the API,
type, token, builder, or guard that establishes them; do not accept a name or
documentation claim as enforcement. Avoid scattered checks and caller bookkeeping.
Unreachable error variants and repeated defensive checks can signal a missing
abstraction. Distinguish protected internal assertions from fallible public
inputs needing errors or Option. A private call site with a guaranteed invariant
can unwrap; diagnostic debug assertions can be appropriate. Use typed retry
conditions, not display strings, and rely on actual trait guarantees rather than
one implementation's endianness or layout.

## Check constraints rather than honest assignments

For gadgets, derive soundness and completeness from constraints, not honest
witness assignments. Witness-only facts may need a separate type. Identify
the designated stage enforcer and the binding that permits reuse; an
unenforced stage is not automatically a bug. Context-free consistency APIs
must re-establish constraints after prior context is stripped. Separate native
advice cost from constrained arithmetic.

## Keep abstractions small and responsibilities in place

Ask what concrete caller or generic bound justifies each added trait, wrapper,
lifetime, macro, constant, or public method. Prefer inherent or existing operations
over pass-through layers. Preserve domain structure instead of positional vectors.
Test access alone does not justify production API exposure; prose cannot make
a public item private.

Keep layout and FFT details in the registry, strategy inside its crate, curve
choices out of generic dependencies, and analysis state in its owning driver.
Share driver-generic algorithms where native and circuit behavior must agree;
keep independently optimized evaluators separate when equivalence tests
justify the boundary.

## Find hidden coordination and misplaced state

Localize order-dependent indexing, synchronized counts, duplicated constraints,
scope restoration on errors, and caller-carried layout advice. Ask for a concrete
usage example before moving a burden from registration to every subsequent call.
For routines, equal types, shapes, polynomial contributions, and reusable typed
outputs are distinct obligations. Check input/local wire separation, output
mapping, scope state, and nested deferred execution.

## Require evidence proportionate to optimization complexity

Inspect allocations, normalization, inversions, eager work, and deep clones
before adding machinery. Complicated parallelism and small constant-factor wins
need representative benchmarks covering scheduling, caches, workload size,
and higher-level parallelism.
Straightforward simplifications and asymptotic gains need no arbitrary speedup
threshold. Check enabled and disabled feature contracts.

Prefer independent mathematical oracles and targeted failures over mirrored
implementations. Distinguish representation from mathematical equality; exercise
changed constraints and driver side effects. Check required CI statuses when
path filters skip work.

## Make explanations precise and economical

Lead with the contract, then prerequisites and implementation details. Put
protocol math, guide usage, and local rustdoc rationale at their proper layers;
give each concept one authoritative explanation. Keep useful examples and subtle
local rationale. Use rendered math, formatted identifiers, and API links in
rustdoc. Check fixed/free variables, coefficient order, polynomial/vector
operations, and assembly/evaluation. Describe current behavior, not the diff;
avoid listing what rustdoc already renders or narrating obvious optimizations.
Simplified guide excerpts must remain truthful; preserve safety and completeness
preconditions.

## Deliver a calibrated review

Identify the mismatch, its consequence, and the smallest coherent correction.
Separate defects from preferences, future designs, and unverified questions;
report current locations, scope, and checks actually performed. An incomplete
improvement need not wait for an ideal redesign; there is no finding quota.

Consult [references/evidence.md](references/evidence.md) when provenance is
requested or an ambiguity about applying a priority could change a finding.
Historical examples do not override current code or repository policies.
