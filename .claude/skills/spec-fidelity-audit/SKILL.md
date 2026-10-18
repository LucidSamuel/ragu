---
name: spec-fidelity-audit
description: Three-way fidelity audit between a design spec (gist, HackMD, design doc, issue, book page), its implementation (PR or branch), and its formalization (Lean, Coq, any proof artifact) when one exists. Finds what the spec is missing or gets wrong, where the implementation deviates from it, where the proofs do not cover it, and what the proofs silently rest on, then tags every gap by who is right. Use it whenever a PR links a design document and the question is "does the code match the design", "is the spec complete or missing anything", "does the formalization follow the protocol", "which of these is wrong", "the docs say X is verified, is it", "does this proof actually constrain the code", "what axioms or admits does this endpoint rest on", or "do we accept the same encodings, signatures, or points as other implementations" — even when only one is asked, because the answer depends on all three artifacts. Use it with no design doc too; the Lean definitions then stand in for the spec. Also use it after a correctness review that found no bugs.
user-invocable: true
---

# Spec fidelity audit

Do the spec, the implementation, and the formalization describe the same
thing, and does each state what the others rely on? A correct
implementation of an incomplete spec misleads the next reader; a green
proof of a wrong or disconnected definition looks like coverage. Output: a
list of gaps, each tagged by who is right.

## Gather

- **Spec**: the cited doc plus everything it defers to (base gist, review
  thread, sanity-check writeup). Fetch every link; if one is unreachable,
  say so and name what you checked instead. No design doc: the Lean
  definitions translated from the code are the spec corner. A translated
  model cannot disagree with its source, so the only independent check is
  whether the property theorems would fail for the bugs the code could
  have. Relations, games, and adversary classes still come from design
  intent (book, ZIP, design thread), never from the circuit, and get the
  Definition seam.
- **Implementation**: the diff, pinned counts and tests, in-tree docstrings
  and book pages.
- **Formalization**: proof files, stated assumptions, the axiom census or
  trust boundary, the proof-to-code mechanism (fingerprints, extraction,
  generated models). None: skip Pass 3, keep the coverage map.

Reduce the spec to a claim list: definitions and encodings, formulas and
constants, preconditions, contracts (who enforces what, where, how often),
costs, security bounds, deferred caveats. Every pass walks it.

## Pass 1: spec completeness

For each thing the code or a proof relies on, find where the spec says it.
Recurring omissions:

- Input preconditions carried only in a type or unchecked assumption
  (nonzero, on-curve, in-range, distinct, prime order).
- The mirror side of a contract: "constrain once in X" needs the same on
  the nested, verifier, second-curve, or second-stage side.
- Consumers missing from the budget, including tests, fuzzers, and tooling
  that pin the old shape. An omitted consumer usually forced an
  undocumented redesign.
- Exceptional or degenerate cases flagged "needs an argument", never given.
- Silent assumptions shared by all three artifacts: parameters that must
  agree across components (root of unity, endianness, generator index),
  tested but never stated. Nothing will contradict these.
- Constraints living only in a review thread or sanity-check doc.
- Security tables listing some widened parameters, not all.
- In-tree restatements drifting from both spec and proofs. Check each
  stated bound, count, and claim against the proven one.

## Pass 2: spec correctness and implementation fidelity

- Re-derive every formula and constant from the spec, never prose against
  prose: two artifacts can share one author's mistake. Settle deviations by
  derivation, not majority.
- Rework the spec's arguments, not just its formulas, against the math and
  against the spec's own stated goal (the goal is taken as given; unstated
  is a Pass 1 finding): injectivity and
  non-degeneracy reasoning, security bounds, attack analyses. Bounds by
  computation, arguments by their cases, constants the deployed ones. A
  wrong argument the code follows is the top-severity tag and invisible to
  Pass 1, since nothing is missing.
- Check cost claims by arithmetic against pinned counts; the residual
  points at an omitted consumer or a wrong claim.
- Every implementation of a claim: backends, platform paths, fallbacks,
  generic-versus-specialized instantiations each need their own check.
  Differential testing across them is the cheap substitute for a proof.
- Mandated checks as executed: on the executed path, able to fire given the
  types (a bound a `u32` cannot reach is no bound), outcome known when it
  fires: error, panic, or silent accept. A panic on attacker input is a
  divergence even where the spec is silent.

## Pass 3: formalization fidelity

Seven seams, in order:

- **Definition.** Re-derive each formal definition, relation, and constant
  from the spec, not the implementation. Where one side is derived from the
  other (extracted model, captured fingerprint), the derived side cannot
  disagree with its source; re-derive the hand-written side. A definition
  translated from the code has nothing to re-derive it from: for each bug
  class the code could have (under-constrained gate, missing check, wrong
  bound), ask whether the theorem would fail if the definition mirrored it.
  A property that would still hold, or one meaning only "computes what the
  code computes", is too weak.
- **Model bridge.** Is the theorem about the definition the artifact is
  proven to compute? Two "obviously equal" definitions with no lemma between
  them means there is no theorem about the code. Grep who imports the
  lemma; a result only the census references is applied nowhere.
- **Instantiation.** Numeric hypotheses discharged at the deployed
  parameters, or only generically? A sibling that is instantiated shows it
  was feasible.
- **Assumed vs proven.** Every caller obligation and what discharges it.
  Stated external obligation: fine. Unstated: a gap.
- **Scope.** What is modeled (an affine-formula model, one gadget) versus
  what the protocol needs (the group law, cross-component composition), and
  whether prose saying "verified" names the larger thing.
- **Trusted base.** Open the census. Per endpoint, list every non-standard
  axiom, `sorry`/`admit`/`assume`, `native_decide`, `implemented_by`/
  `extern`, `csimp` lemma, or the prover's equivalents, reached
  transitively. Each: disclosed where the prose claims coverage?
  independently true (an admitted intrinsic is a test obligation, not a
  fact)? pin tier equal to the tier the prose claims? Note what the census
  does not reach: a declaration nothing censused depends on is checked by
  nothing.
- **Vacuity.** In a scratch worktree, perturb each side in turn (a constant
  in the formal definition, then a line in the code) and confirm the proof
  or fingerprint fails both times; revert. Survives: vacuous. Fails only
  under definition mutation: about the definition, not the code. Prefer a
  checked-in witness (mutation test, corrupted-wire test).

## Tags

One per finding; keep the wording.

| Tag | Meaning | Fix |
|---|---|---|
| Spec incomplete, implementation or formalization fills it | Code or proof relies on a fact, contract, or assumption the spec never states (a crypto assumption living only in a proof docstring counts) | Write it into the spec, the document users read |
| Spec wrong in a claim, implementation correctly ignores it | Spec asserts something false (often a cost); code is right | Correct the spec; check nothing downstream used it |
| Spec wrong, implementation follows it | A bug in both | Fix code first |
| Implementation diverges from a correct spec | Bug or undocumented redesign | Decide by derivation; fix code or document |
| Spec underdetermines acceptance | Spec and code agree but leave open an accept/reject decision peers settled (malleability, canonical encodings, point validation) | Decide, write it in, check interop |
| Formalization incomplete, independent of the spec | Proofs exist but a bridge, instantiation, or scope is missing (a verified circuit never connected to the theorem about its model) | Connect or instantiate the existing proofs |
| Formalization proves a different statement | Wrong definition, parameter, or weaker spec than the prose claims | Fix the definition or parameter and re-prove; downgrade the prose claim until then |
| Formalization vacuous | Proof passes independent of the implementation: admit or axiom on the bridge, or the definition is not what the artifact computes | Remove the admit; report the claim unproven until the mutation test fails |

Severity: real defects (wrong-and-followed, buggy divergences), then
vacuous, then proves-a-different-statement, then underdetermined
acceptance, then spec-wrong-but-ignored, then the additive tags. Audited
surfaces with no gap get a positive label, not silence: **Implementation
faithfully implements the spec** or **Formalization faithfully follows the
spec**.

## Report

Name the commit audited. One lead line answering: spec complete? code
faithful? proofs faithful? trusted base disclosed? Then three lists (spec
gaps, implementation fidelity, formalization gaps), one tagged line each
with a one-clause fix. Then a coverage map, per claim: proof / test / both
/ neither. A proof counts only if its property has meaning beyond the
definition (Definition seam); a test only if its oracle is independent of
the code and it actually runs (not ignored, no persisted failures left
unreplayed);
proof-only on a cheaply testable claim is a smell, neither is a gap. Close
with the positive labels and the claims not checked, so the audited surface
is exact. Keep "wrong" and "incomplete" visibly separate; asked whether the
spec is wrong, answer with tag counts.
