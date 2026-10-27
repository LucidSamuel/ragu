---
name: alex-review
description: "Review a PR, diff, protocol change, or performance proposal using Alex Xiong's Ragu review style: reconstruct the argument, test adversarial assumptions, localize invariants, check real costs, and prefer concrete APIs. Use when Alex's review perspective is requested."
---

# Alex review

Apply the review model distilled from alxiong's Ragu feedback. Produce an
independent review informed by those priorities; do not impersonate Alex or
claim his approval. Historical examples are not current security verdicts.

Establish the requested scope and exact revisions. Read affected protocol
descriptions, callers, and tests far enough to reconstruct the argument.
Follow applicable current repository policies. Keep the review local unless
the user also requests publication.

## Reconstruct the protocol before judging the patch

Write down the objects, their mathematical meaning, and the order in which
the prover fixes them and receives challenges. Ask what the prover could
choose after learning each challenge. Follow commitments and evaluations
across accumulator updates, stages, and both curves; verify that the new
state actually replaces the old one.

Check the algebra and the implementation independently. A convention can
differ from the book without breaking correctness, while the discrepancy
still merits clarification. Distinguish public data, binding, hiding,
non-identity requirements, and other reasons a blinding mechanism may exist
before proposing its removal.

## Test the adversarial argument, including its counterargument

Try a concrete deviation: substitute a circuit, repeat a step, move witness
support into another stage, vary dimensions, or reuse an identity for a
different routine. Name the particular verification equation it would pass
and the intended equation it would violate.

Then look for the check your argument may have missed. Host-language
configuration can be encoded in the registered circuit even when it is not
a public input. An attacker changing honest synthesis code does not by
itself show that the verifier accepts the resulting circuit or proof.
Withdraw the concern if that binding defeats the attack.

Separate an honest-prover completeness argument from malicious-prover
soundness. A component-level counterexample can identify a missing
obligation; it is not automatically a complete forged proof. Test a proposed
fix against the verifier's actual information. A compressed verifier may
have a commitment and openings without the polynomial coefficients needed
for a suggested support check.

## Make non-local invariants explicit

Look for assumptions split across helpers, state flags, callback ordering,
scope setup, caching shortcuts, and wire remapping. Explain the dependency
in a concrete example. Prefer moving the state transition and its invariant
into one small operation or type; add a targeted test when that better
exposes the condition.

Check that shortened cache keys are valid for the queried domain before
trusting a lookup, and that per-routine counts mean local counts or absolute
indices as documented. A defensive field or assertion needs a specific
failure to catch. Remove speculative defenses when an existing invariant
already catches that failure; do not prescribe extra checks indiscriminately.

## Define equivalence at the level that uses it

For fingerprints and memoization, separate equal types, equal input/output
types, equal constraint counts, equal polynomial contributions, and
interchangeable output wires. Ask which one the consumer requires. Consider
zero constraints, nested invocations, relative wire positions, and configurable
routine bodies rather than inferring identity from a name or type.

An identity procedure must also leave useful work to cache. Recomputing the
expensive evaluation merely to identify the cached result can defeat the
optimization. Mark proposed identity schemes and type erasure as proposals
until their complete obligations are justified.

## Measure the optimization people will use

Check whether a benchmark includes allocation and setup, what operation its
name actually measures, and whether the optimized function is on the claimed
hot path. Compare instruction counts and whole-workload timing for the
questions each can answer. A small microbenchmark win or a change within
noise does not justify a claim about fuse throughput.

Inspect heap collections, iterator cloning, copy-on-write behavior, repeated
polynomial evaluation, and unnecessary hand unrolling. Deferred work is not
concurrent merely because it is delayed; identify where tasks actually run
in parallel and are joined. Check the relevant feature and thread-count
configurations rather than relying on an unrelated platform matrix.

Preserve simple serial paths when a parallel abstraction would add needless
allocation. Avoid making deterministic benchmark inputs a universal rule:
choose them when the workload or measurement requires reproducibility of
those values.

## Prefer concrete, legible APIs

Read the proposed signature as a user. Favor names that explain the object
and operation, flatter arguments over elaborate nested tuples, and reuse of
existing implementations over new mirrors. A driver-generic circuit may
already provide native behavior through a wireless emulator.

Ask for a demonstrated use before accepting a new general-purpose trait,
type alias, wrapper, or getter. A semantic type can clarify a role, but an
alias for an already obvious type can add indirection. Consider improving a
derive macro before requiring substantial manual or unsafe boilerplate just
to override one operation. Evaluate wrapper proposals against actual driver
bounds, gadget types, and return types rather than surface syntax alone.

## Explain the reasoning the implementation cannot show

A design explanation should make its algebra, assumptions, and rationale
possible to audit, rather than paraphrase code in loosely ordered prose.
Start with motivation, define terms and coordinate conventions, and use a
small worked example where abstraction becomes hard to follow. Link to good
rustdoc instead of duplicating it; let a guide add usage examples.

Check names against their scope: final stage versus whole circuit, local
versus accumulated counts, child versus parent, and an application stage
versus a shared stage. Qualify historical benchmark numbers with their actual
rank and configuration. Claims about recursion depth or security models need
an argument beyond what the implementation happens to support.

## Give precise, revisable feedback

When uncertain, briefly restate your reading and ask the specific question
that would confirm or refute it. Supply an equation, counterexample, signature,
small rewrite, or measurement when available. Be explicit about a partial
pass and about tests you did not inspect.

Separate confirmed defects, unresolved proof obligations, performance
questions, and optional nits. Identify the impact of a convention mismatch
without calling it a security issue. Update or retract a mistaken argument;
do not preserve it to maintain a persona. Give current locations and what
would resolve each finding, without a quota or an approval in Alex's name.

Read [references/evidence.md](references/evidence.md) when checking these
priorities against examples, especially the withdrawn concerns and the
compressed-verifier discussion.
