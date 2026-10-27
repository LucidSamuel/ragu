---
name: sean-review
description: Review Ragu code or designs from Sean Bowe's perspective when requested.
---

# Sean review

Apply the relevant priorities below to the requested scope and exact revisions,
using current code, affected callers, and repository policies. Give your own
review, not Sean's approval. Keep feedback local unless publication is authorized.

## Contracts and constraints

Put invariants in the API, type, token, builder, or guard that establishes them;
avoid scattered checks and caller bookkeeping. Distinguish protected internal
assertions from fallible public inputs needing errors or Option. Private
unwrapping and diagnostic debug assertions can be appropriate. Use typed
retry conditions, not display strings, and rely on actual trait guarantees
rather than one implementation's endianness or layout.

For gadgets, derive soundness and completeness from constraints, not honest
witness assignments. Witness-only facts may need a separate type. Identify
the designated stage enforcer and the binding that permits reuse; an
unenforced stage is not automatically a bug. Context-free consistency APIs
must re-establish constraints after prior context is stripped. Separate native
advice cost from constrained arithmetic.

## Abstraction and ownership

Require a concrete caller or generic bound for each trait, wrapper, lifetime,
macro, constant, or public method. Prefer inherent or existing operations over
pass-through layers. Preserve domain structure instead of positional vectors.
Test access alone does not justify production API exposure; prose cannot make
a public item private.

Keep layout and FFT details in the registry, strategy inside its crate, curve
choices out of generic dependencies, and analysis state in its owning driver.
Share driver-generic algorithms where native and circuit behavior must agree;
keep independently optimized evaluators separate when equivalence tests
justify the boundary.

Localize order-dependent indexing, synchronized counts, duplicated constraints,
scope restoration on errors, and caller-carried layout advice. For routines,
equal types, shapes, polynomial contributions, and reusable typed outputs are
distinct obligations. Check input/local wire separation, output mapping, scope
state, and nested deferred execution.

## Costs and tests

Inspect allocations, normalization, inversions, eager work, and deep clones
before adding machinery. Complicated parallelism needs representative evidence
covering scheduling, caches, workload size, and higher-level parallelism.
Straightforward simplifications and asymptotic gains need no arbitrary speedup
threshold. Check enabled and disabled feature contracts.

Prefer independent mathematical oracles and targeted failures over mirrored
implementations. Distinguish representation from mathematical equality; exercise
changed constraints and driver side effects. Check required CI statuses when
path filters skip work.

## Explanations and feedback

Lead with the contract, then prerequisites and implementation details. Put
protocol math, guide usage, and local rustdoc rationale at their proper layers;
give each concept one authoritative explanation. Keep useful examples and subtle
local rationale. Use rendered math, formatted identifiers, and API links in
rustdoc. Check fixed/free variables, coefficient order, polynomial/vector
operations, and assembly/evaluation. Describe current behavior. Simplified guide
excerpts must remain truthful; preserve safety and completeness preconditions.

Identify the mismatch, its consequence, and the smallest coherent correction.
Separate defects from preferences, future designs, and unverified questions;
report current locations, scope, and checks actually performed. An incomplete
improvement need not wait for an ideal redesign; there is no finding quota.

Historical examples are optional: consult only a relevant section of
[references/evidence.md](references/evidence.md) to resolve a specific ambiguity
about these priorities or a provenance request. Do not load it for routine
reviews or treat historical preferences as current contracts.
