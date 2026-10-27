---
name: alex-review
description: Review Ragu code or designs from Alex Xiong's perspective when requested.
---

# Alex review

Apply the relevant priorities below to the requested scope and exact revisions,
using current protocol descriptions, code, callers, tests, and repository policies.
Give your own review, not Alex's approval. Keep feedback local unless publication
is authorized.

## Protocol and adversarial argument

Identify the objects, their mathematical meaning, and when the prover fixes
values and learns challenges. Track commitments and evaluations across stages,
accumulator updates, and both curves; confirm new state replaces old state.
Check algebra and implementation independently. A convention can differ from
the book without breaking correctness. Distinguish public data, binding, hiding,
and non-identity requirements before removing blinding.

Try a concrete deviation: substitute a circuit, repeat a step, move witness
support, vary dimensions, or reuse a routine identity. Name the verification
equation it passes and the intended equation it violates. Then seek the binding
that defeats the attack. Configuration may be encoded in a registered circuit
without being a public input; changing honest synthesis alone does not show
verifier acceptance. Withdraw concerns defeated by that binding.

Separate honest-prover completeness from malicious-prover soundness. A local
counterexample can expose an obligation without demonstrating a forged proof.
Proposed fixes must use information the verifier has: commitments and openings
do not necessarily reveal coefficients for a support check.

## Invariants and equivalence

Find dependencies split across helpers, flags, callbacks, scope setup, caches,
and wire remapping; illustrate them concretely. Localize transitions and their
invariants, or add a targeted test. Verify shortened cache keys over the queried
domain and distinguish local counts from absolute indices. Defensive fields
and assertions need specific failures not already excluded by an invariant.

For fingerprints and memoization, distinguish equal types, input/output types,
constraint counts, polynomial contributions, and interchangeable output wires.
Check the consumer's required equivalence against zero constraints, nested
invocations, relative wire positions, and configurable routine bodies. Identity
computation must leave useful work to cache; recomputing expensive evaluations
can defeat the optimization. Keep type-erasure and identity proposals provisional
until their full obligations are justified.

## Actual costs and concrete APIs

Check whether benchmarks include setup and allocation, measure their named
operation, and reach the claimed hot path. Use instruction counts and whole
workload timing for their respective questions; microbenchmark wins or noise
do not establish fuse throughput. Qualify historical figures by rank and
configuration.

Inspect collections, iterator cloning, copy-on-write, repeated evaluations,
and hand unrolling. Identify where deferred tasks actually run concurrently
and join. Check relevant features and worker counts. Preserve simple serial
paths when parallel abstractions add allocation. Deterministic benchmark inputs
are useful when the measurement requires them, not a universal rule.

Read signatures as a caller: prefer clear names, flatter arguments, and existing
implementations. A wireless emulator may already provide native behavior for
a driver-generic circuit. Require consumers for new traits, aliases, wrappers,
and getters; semantic types help only when they clarify a role. Consider derive
improvements before manual or unsafe boilerplate. Check proposals against actual
driver bounds, gadget types, and returns.

## Explanation and feedback

Make algebra, assumptions, and rationale auditable. Start with motivation,
define conventions, and use a worked example when needed. Link to rustdoc;
let guides add usage examples. Distinguish final stage/whole circuit,
local/accumulated counts, child/parent, and application/shared stages. Recursion
depth and security-model claims need arguments beyond implementation support.

Give a specific equation, counterexample, signature, rewrite, or measurement
that resolves each concern. Separate defects, open proof obligations, performance
questions, and nits; a convention mismatch is not automatically a security bug.
Report current locations and validation limits, revise mistaken arguments, and
avoid finding quotas.

Historical examples are optional: consult only a relevant section of
[references/evidence.md](references/evidence.md) to resolve a specific ambiguity
about these priorities or a provenance request. Do not load it for routine
reviews or treat historical examples as current security verdicts.
