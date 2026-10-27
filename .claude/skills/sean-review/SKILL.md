---
name: sean-review
description: "Review a PR, diff, API, or technical explanation using Sean Bowe's Ragu review priorities: protected contracts, minimal abstractions, correct circuit semantics, architectural boundaries, and precise economical documentation. Use when Sean's review perspective is requested."
---

# Sean review

Apply the decision-making distilled from ebfull's Ragu feedback. Produce your
own review; do not claim to be Sean or give his approval. Use current source
and applicable repository policies to resolve details. Historical suggestions
are evidence of reasoning, not permanent implementation requirements.

Establish the requested scope and exact base and head. Read enough callers
and surrounding code to understand the abstraction before suggesting a local
cleanup. Keep feedback local unless publishing it is also requested.

## Make the contract do the work

Ask which states a correct caller can construct. Prefer an API, type, token,
builder, or guard that prevents a real misuse over scattered checks and
caller-maintained bookkeeping. Trace the obligation to the operation that
establishes it; do not accept a name or documentation claim as enforcement.

Distinguish internal bugs from caller-triggerable failures. An assertion is
appropriate for a protected invariant; fallible public input generally needs
an error or Option. A private guaranteed call site can unwrap locally.
Unreachable error variants and repeated defensive checks can indicate a
missing abstraction. Debug assertions can still be appropriate for diagnostic
checks that protect no invariant. There is no blanket ban on unwraps or
debug assertions.

If a caller must distinguish retryable failure from other errors, use a typed
condition rather than a display string. Rely on the actual trait contract:
an implementation's endianness, layout, or behavior is not automatically a
guarantee of the trait.

## Check constraints rather than honest assignments

An allocated boolean or a witness computation does not prove its value.
Derive the equations and check all relevant cases for both soundness and
completeness. Gadget contracts concern their wires; witness-only facts may
need a separate type rather than another Gadget implementation.

An unenforced stage is not automatically a defect. Identify the designated
enforcer and the binding that lets other circuits reuse the same stage.
Conversely, constraints must be re-established when a consistency API promises
to work without prior context. Account for native advice and constrained
arithmetic separately, especially when claiming fewer gates.

## Keep abstractions small and responsibilities in place

Ask what concrete caller or generic bound justifies each added trait,
wrapper, lifetime, constant, macro, and public method. If no code is generic
over a trait, inherent methods may suffice. Prefer existing operations over
pass-through layers. Preserve useful domain structure instead of flattening
everything into vectors whose positions callers must remember.

Let the registry own layout, circuit processing, and FFT details. Keep
implementation strategies inside the appropriate crate, and downstream curve
choices out of generic dependencies. Test access alone does not justify a new
production API. Public visibility defines what is exposed; calling an exposed
item an internal detail in prose does not hide it.

Simplification does not always mean one implementation. Independently
optimized polynomial evaluators can belong in separate modules with strong
equivalence tests. Reuse driver-generic algorithms where native and circuit
behavior must agree, without erasing a justified optimization boundary.

## Find hidden coordination and misplaced state

Look for order-dependent indexing, manually synchronized counts, duplicated
constraint logic, state restoration on error paths, and caller-carried layout
advice. Prefer a local invariant or generated/shared source when it removes
that coordination. Ask for a concrete usage example before shifting a burden
from registration to every subsequent call.

For routines, equal Rust types, equal shapes, and equal polynomial
contributions are different claims. Memoized typed output reconstruction adds
another obligation beyond algebraic equivalence. Check input/local wire
separation, output mapping, scope state, and nested deferred execution. Do not
make the emulator responsible for analysis state belonging to another driver.

## Require evidence proportionate to optimization complexity

Examine redundant allocations, normalization, inversions, eager evaluation,
and deep clones before adding machinery. Compare native operation cost with
circuit constraint cost. An inversion supplied as checked advice can have a
different cost from performing batch inversion inside the circuit.

Expect representative benchmarks before accepting complicated parallelism or
small constant-factor wins. Consider scheduling overhead, cache behavior,
problem size, and opportunities to parallelize at a higher level. Clear
asymptotic improvements and straightforward simplifications do not need an
arbitrary performance threshold. Feature combinations must preserve the
intended public API; check relevant enabled and disabled configurations.

Prefer tests with an independent mathematical oracle or a targeted failure
over tests that reproduce the implementation. Distinguish representation
equality from mathematical equality. Check that changed constraints and driver
side effects are exercised, and that any required CI check still reports on
PRs whose changed paths cause work to be skipped.

## Make explanations precise and economical

Lead with the contract or concept the reader needs. Introduce prerequisites
before implementation detail. Explain protocol math at the protocol layer,
API usage in the guide, and local implementation nuance in rustdoc. Give a
concept one authoritative explanation and link to it. Preserve a useful
example or subtle local rationale when removing it would force the reader to
reconstruct the argument.

Use rendered math in rustdoc, code formatting for identifiers, and links for
related API items. Check fixed versus free variables, coefficient order,
polynomial versus coefficient-vector operations, and assembly versus
evaluation. Document the present behavior, not the diff or a comparison with
a former API. Scope special notation narrowly and avoid introducing it when
a simpler abstraction explains the same relationship.

A guide can use an explicitly simplified trait excerpt and reveal details
later. Do not make it a false executable contract. Avoid exposing private
fields, listing information already rendered from code, narrating obvious
optimizations, or spelling out generic consequences of violating a contract.
Keep actual safety requirements and completeness preconditions explicit.

## Deliver a calibrated review

Be direct: identify the mismatch, explain why the abstraction or equation
requires something else, and propose the smallest coherent correction.
Separate blockers from non-blocking preferences and future design ideas.
An incomplete improvement can still be useful; do not hold it for an ideal
redesign. An uncertain hypothesis remains a question until checked.

Return current locations, consequences, and concrete fixes. State the scope
and validation limits. Do not manufacture nits, treat every style preference
as a merge blocker, or infer Sean's endorsement from these instructions.

Read [references/evidence.md](references/evidence.md) for source examples and
exceptions, especially before turning a preference into a universal rule.
