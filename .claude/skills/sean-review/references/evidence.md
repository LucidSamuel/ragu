# Evidence for Sean Bowe's review model

Source: account [ebfull](https://github.com/ebfull) in [tachyon-zcash/ragu](https://github.com/tachyon-zcash/ragu), captured on 2026-10-23.

The complete collection contains 1,712 account-attributed records across 352 PRs: 733 review events, 873 inline comments, and 106 PR discussion comments. Of these records, 1,126 have text. The primary style evidence is 845 nonempty contributions on 211 PRs authored by others; 281 nonempty contributions on the account's own PRs were retained as author-response context.

Empty review events describe review activity, not articulated priorities. Exact duplicate bodies were collapsed for reading, with original IDs retained in the collection. The examples below are selected evidence for the distilled decisions, not an exhaustive list of feedback or a quantitative ranking of beliefs. Account attribution does not establish that each word was written without AI assistance; the corpus includes explicitly disclosed assisted feedback.

The skill infers reusable review behavior from this history. Each link is historical: retrieve current source before reusing a technical claim. A comment can be tentative, corrected later, or superseded. The examples do not certify current PRs, supply a soundness theorem, or authorize remote actions.

## Protect the invariant at its origin

The Key discussion works backwards from an unreachable error, through caller reachability, to a type that prevents zero and can cache the inverse. This is a design argument, not a universal preference for assertions.

Sources: [PR #363 review 3684407242](https://github.com/tachyon-zcash/ragu/pull/363#pullrequestreview-3684407242), [PR #767 inline 3773365744](https://github.com/tachyon-zcash/ragu/pull/767#discussion_r3773365744), [PR #449 inline 3162443886](https://github.com/tachyon-zcash/ragu/pull/449#discussion_r3162443886).

## Check actual constraints and completeness

An allocated boolean chosen by the prover is not an enforced equality. The is_zero explanation derives both branches and existence of a witness; a discarded product still needs its constraint.

Sources: [PR #125 inline 2561007007](https://github.com/tachyon-zcash/ragu/pull/125#discussion_r2561007007), [PR #277 review 3614099166](https://github.com/tachyon-zcash/ragu/pull/277#pullrequestreview-3614099166), [PR #643 inline 3074272525](https://github.com/tachyon-zcash/ragu/pull/643#discussion_r3074272525).

## Distinguish wire contracts from witness facts

A witness-only certification does not become a gadget merely by wrapping an Element. Contracts should describe what users can rely on without exposing temporary internal repairs.

Sources: [PR #767 inline 3773563864](https://github.com/tachyon-zcash/ragu/pull/767#discussion_r3773563864), [PR #744 inline 3327065924](https://github.com/tachyon-zcash/ragu/pull/744#discussion_r3327065924), [PR #767 review 4924584023](https://github.com/tachyon-zcash/ragu/pull/767#pullrequestreview-4924584023).

## Locate the designated stage enforcer

Unenforced reuse of a stage can be intentional if another circuit checks its invariants and the shared stage is bound. Adding a trait that forbids all such reuse solves the wrong problem.

Sources: [PR #383 review 3699671189](https://github.com/tachyon-zcash/ragu/pull/383#pullrequestreview-3699671189), [PR #388 inline 2751836503](https://github.com/tachyon-zcash/ragu/pull/388#discussion_r2751836503), [PR #166 review 3520853194](https://github.com/tachyon-zcash/ragu/pull/166#pullrequestreview-3520853194).

## Demand a concrete consumer for an abstraction

Remove a trait used only to place methods in scope, avoid premature deferral layers, and avoid merely moving step-index bookkeeping into tuples of application-carried handles.

Sources: [PR #422 inline 2795138549](https://github.com/tachyon-zcash/ragu/pull/422#discussion_r2795138549), [PR #415 review 3759789481](https://github.com/tachyon-zcash/ragu/pull/415#pullrequestreview-3759789481), [PR #415 discussion 3856938959](https://github.com/tachyon-zcash/ragu/pull/415#issuecomment-3856938959), [PR #514 review 3873967791](https://github.com/tachyon-zcash/ragu/pull/514#pullrequestreview-3873967791).

## Keep implementation details at the proper layer

The registry owns FFT and layout details; generic circuit crates should not depend on a concrete curve crate. Test-only helpers should not expose internal production types.

Sources: [PR #374 discussion 3792131344](https://github.com/tachyon-zcash/ragu/pull/374#issuecomment-3792131344), [PR #390 inline 2740504406](https://github.com/tachyon-zcash/ragu/pull/390#discussion_r2740504406), [PR #504 review 3836120250](https://github.com/tachyon-zcash/ragu/pull/504#pullrequestreview-3836120250), [PR #413 review 3787778809](https://github.com/tachyon-zcash/ragu/pull/413#pullrequestreview-3787778809).

## Preserve valid specialization and reuse

Separate direct polynomial evaluators can enable distinct optimizations and be checked against one another. Conversely, algorithms whose native/circuit behavior must agree should share a driver-generic implementation.

Sources: [PR #352 review 3673432132](https://github.com/tachyon-zcash/ragu/pull/352#pullrequestreview-3673432132), [PR #125 inline 2553809635](https://github.com/tachyon-zcash/ragu/pull/125#discussion_r2553809635), [PR #600 inline 2972014430](https://github.com/tachyon-zcash/ragu/pull/600#discussion_r2972014430).

## Reason about routine identity and outputs separately

Same-type routines may synthesize differently. Matching polynomial contributions does not automatically justify typed output substitution; tests revealed count and wire-separation collisions in an early approach.

Sources: [PR #413 inline 2756499118](https://github.com/tachyon-zcash/ragu/pull/413#discussion_r2756499118), [PR #511 discussion 3991763656](https://github.com/tachyon-zcash/ragu/pull/511#issuecomment-3991763656), [PR #669 discussion 4356337542](https://github.com/tachyon-zcash/ragu/pull/669#issuecomment-4356337542).

## Keep deferred execution ordered and scoped

The nested-thunk review identifies both lost deferred work and incorrect DFS ordering, then discusses hiding the recovery mechanism inside the evaluator. Caller-provided layout advice has a separate API cost.

Sources: [PR #476 inline 2870647360](https://github.com/tachyon-zcash/ragu/pull/476#discussion_r2870647360), [PR #476 inline 2870660203](https://github.com/tachyon-zcash/ragu/pull/476#discussion_r2870660203), [PR #476 review 3874209363](https://github.com/tachyon-zcash/ragu/pull/476#pullrequestreview-3874209363).

## Use the right cost model and evidence

Benchmark parallelism before adding it; consider granularity and cache effects. Native batch inversion and in-circuit inversion have different costs, and a streaming implementation needs evidence before being replaced by more complex materialization.

Sources: [PR #46 review 3338147591](https://github.com/tachyon-zcash/ragu/pull/46#pullrequestreview-3338147591), [PR #366 discussion 3773464503](https://github.com/tachyon-zcash/ragu/pull/366#issuecomment-3773464503), [PR #391 inline 2732823770](https://github.com/tachyon-zcash/ragu/pull/391#discussion_r2732823770), [PR #479 discussion 4017674770](https://github.com/tachyon-zcash/ragu/pull/479#issuecomment-4017674770).

## Test semantics independently of representation

Tests should compare a mathematical relation rather than duplicate the implementation. Structural polynomial equality may disagree with mathematical equality. Missing driver-aware serialization can omit constraints.

Sources: [PR #153 inline 2588661270](https://github.com/tachyon-zcash/ragu/pull/153#discussion_r2588661270), [PR #101 inline 2528081181](https://github.com/tachyon-zcash/ragu/pull/101#discussion_r2528081181), [PR #522 inline 2881409658](https://github.com/tachyon-zcash/ragu/pull/522#discussion_r2881409658).

## Document the contract, not the diff

Use accurate mathematical types, fixed/free variables, and assembly/evaluation terminology. Keep general notation minimal and place reader prerequisites before details. Avoid narrating generic consequences of violating a contract.

Sources: [PR #396 inline 2737184214](https://github.com/tachyon-zcash/ragu/pull/396#discussion_r2737184214), [PR #424 inline 2792107891](https://github.com/tachyon-zcash/ragu/pull/424#discussion_r2792107891), [PR #209 review 3558604790](https://github.com/tachyon-zcash/ragu/pull/209#pullrequestreview-3558604790), [PR #532 inline 2983372596](https://github.com/tachyon-zcash/ragu/pull/532#discussion_r2983372596), [PR #634 inline 3069072246](https://github.com/tachyon-zcash/ragu/pull/634#discussion_r3069072246).

## Keep useful context despite a brevity policy

Several comments reject automated policy suggestions that delete useful local explanation. Simplified guide excerpts can stage the exposition; they do not license false executable contracts or security claims.

Sources: [PR #532 inline 2972072931](https://github.com/tachyon-zcash/ragu/pull/532#discussion_r2972072931), [PR #532 inline 2903069252](https://github.com/tachyon-zcash/ragu/pull/532#discussion_r2903069252), [PR #532 inline 2903080866](https://github.com/tachyon-zcash/ragu/pull/532#discussion_r2903080866), [PR #652 inline 3088756213](https://github.com/tachyon-zcash/ragu/pull/652#discussion_r3088756213).

## Use trait guarantees and structured error conditions

The endoscalar review separates correctness on Pasta from a missing generic endianness guarantee, a retryable typed error, and stale protocol documentation. It explicitly states that these requests are not Pasta soundness problems.

Sources: [PR #767 inline 3797687940](https://github.com/tachyon-zcash/ragu/pull/767#discussion_r3797687940), [PR #767 inline 3797687949](https://github.com/tachyon-zcash/ragu/pull/767#discussion_r3797687949), [PR #767 inline 3797687961](https://github.com/tachyon-zcash/ragu/pull/767#discussion_r3797687961), [PR #767 review 4953246649](https://github.com/tachyon-zcash/ragu/pull/767#pullrequestreview-4953246649).

## Keep features and CI obligations coherent

Public signatures should remain consistent across additive features. Required checks must still report on changes that skip the work guarded by paths.

Sources: [PR #46 inline 2434411467](https://github.com/tachyon-zcash/ragu/pull/46#discussion_r2434411467), [PR #46 inline 2434455827](https://github.com/tachyon-zcash/ragu/pull/46#discussion_r2434455827), [PR #732 inline 3294883740](https://github.com/tachyon-zcash/ragu/pull/732#discussion_r3294883740).

## Distinguish preferences from blockers

The corpus explicitly permits diagnostic debug assertions, labels notation changes non-blocking, and accepts additive improvements before a full rewrite. A strict style persona should not invent a universal blocking checklist.

Sources: [PR #365 inline 2709842501](https://github.com/tachyon-zcash/ragu/pull/365#discussion_r2709842501), [PR #209 review 3558604790](https://github.com/tachyon-zcash/ragu/pull/209#pullrequestreview-3558604790), [PR #364 review 3688359515](https://github.com/tachyon-zcash/ragu/pull/364#pullrequestreview-3688359515), [PR #320 review 3722139043](https://github.com/tachyon-zcash/ragu/pull/320#pullrequestreview-3722139043), [PR #610 inline 2977409436](https://github.com/tachyon-zcash/ragu/pull/610#discussion_r2977409436).

## Calibration and exceptions

- The existing local Picky Standards role is not primary evidence for these skills. The GitHub feedback contains exceptions to blanket bans on debug assertions and rigid demands to minimize every explanation.
- Do not canonize a proposed architecture from a long review: several proposals end by deferring the redesign or acknowledging trade-offs.
- Do not translate simplified exposition into permission to give inaccurate mathematical or executable contracts. Reveal omitted details progressively and identify illustrative snippets.
- A CHANGES_REQUESTED event alone is weak evidence of severity: PR #610 explicitly says that state was selected by mistake while the substantive review was otherwise ACK.
