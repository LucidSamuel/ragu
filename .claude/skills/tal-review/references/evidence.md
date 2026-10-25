# Evidence for Tal Derei's review model

Source: account [TalDerei](https://github.com/TalDerei) in [tachyon-zcash/ragu](https://github.com/tachyon-zcash/ragu), captured on 2026-10-23.

The complete collection contains 3,218 account-attributed records across 460 PRs: 1,126 review events, 1,689 inline comments, and 403 PR discussion comments. Of these records, 2,278 have text. The primary style evidence is 1,245 nonempty contributions on 229 PRs authored by others; 1,033 nonempty contributions on the account's own PRs were retained as author-response context.

Empty review events describe review activity, not articulated priorities. Exact duplicate bodies were collapsed for reading, with original IDs retained in the collection. The examples below are selected evidence for the distilled decisions, not an exhaustive list of feedback or a quantitative ranking of beliefs. Account attribution does not establish that each word was written without AI assistance; the corpus includes explicitly disclosed assisted feedback.

The skill infers reusable review behavior from this history. Each link is historical: retrieve current source before reusing a technical claim. A comment can be tentative, corrected later, or superseded. The examples do not certify current PRs, supply a soundness theorem, or authorize remote actions.

## Trace the instance into verification

The recurring concern is drift between the authoritative circuit instance and a verifier that reconstructs it by hand. Follow the whole path before accepting a local fix.

Sources: [PR #100 inline 2552100054](https://github.com/tachyon-zcash/ragu/pull/100#discussion_r2552100054), [PR #146 inline 2561813338](https://github.com/tachyon-zcash/ragu/pull/146#discussion_r2561813338), [PR #701 inline 3249546364](https://github.com/tachyon-zcash/ragu/pull/701#discussion_r3249546364).

## Check order and complete coverage

Serialization, query powers, and traversals need an explicit shared ordering. An enum can remove drift, but fields outside that enum still need coverage.

Sources: [PR #290 inline 2656606596](https://github.com/tachyon-zcash/ragu/pull/290#discussion_r2656606596), [PR #284 inline 2652372046](https://github.com/tachyon-zcash/ragu/pull/284#discussion_r2652372046), [PR #656 inline 3118212297](https://github.com/tachyon-zcash/ragu/pull/656#discussion_r3118212297).

## Make tests reach the behavior they claim

Distinguish constructing a witness from executing its circuit, and cover nested Known/Unknown paths rather than only an easy path.

Sources: [PR #353 inline 2702571349](https://github.com/tachyon-zcash/ragu/pull/353#discussion_r2702571349), [PR #524 review 3886738550](https://github.com/tachyon-zcash/ragu/pull/524#pullrequestreview-3886738550), [PR #787 discussion 5247298217](https://github.com/tachyon-zcash/ragu/pull/787#issuecomment-5247298217).

## Use meaningful corruption baselines and controls

Reject vacuous checks against trivial proofs; require an honest control and target all relevant components. Prefer extending coherent coverage over accumulating overlapping smoke tests.

Sources: [PR #498 inline 2834794564](https://github.com/tachyon-zcash/ragu/pull/498#discussion_r2834794564), [PR #498 inline 2834797610](https://github.com/tachyon-zcash/ragu/pull/498#discussion_r2834797610), [PR #498 inline 2834824678](https://github.com/tachyon-zcash/ragu/pull/498#discussion_r2834824678), [PR #467 inline 2834851830](https://github.com/tachyon-zcash/ragu/pull/467#discussion_r2834851830), [PR #417 review 3834001639](https://github.com/tachyon-zcash/ragu/pull/417#pullrequestreview-3834001639).

## Exercise dimensions and boundary conditions

Symmetric parameters can conceal M/N mistakes; zero and one can expose missing preconditions. Choose boundaries dictated by the operation rather than a generic checklist.

Sources: [PR #253 inline 2621623629](https://github.com/tachyon-zcash/ragu/pull/253#discussion_r2621623629), [PR #253 inline 2624793958](https://github.com/tachyon-zcash/ragu/pull/253#discussion_r2624793958), [PR #182 inline 2595440634](https://github.com/tachyon-zcash/ragu/pull/182#discussion_r2595440634).

## Preserve context-free gadget obligations

An equality optimization valid with existing constraints may break a consistency operation used after those constraints are stripped. Explain the contract violation separately from present exploitability.

Sources: [PR #741 inline 3318545075](https://github.com/tachyon-zcash/ragu/pull/741#discussion_r3318545075), [PR #741 inline 3324507089](https://github.com/tachyon-zcash/ragu/pull/741#discussion_r3324507089), [PR #760 inline 3368526199](https://github.com/tachyon-zcash/ragu/pull/760#discussion_r3368526199).

## Keep the consumer and dependency graph in view

Locate an abstraction at its actual layer and check that a proposed API has a real downstream consumer. A returned polynomial-query claim is incomplete if fuse discards it.

Sources: [PR #106 inline 2525771368](https://github.com/tachyon-zcash/ragu/pull/106#discussion_r2525771368), [PR #701 inline 3249535033](https://github.com/tachyon-zcash/ragu/pull/701#discussion_r3249535033), [PR #701 inline 3249546364](https://github.com/tachyon-zcash/ragu/pull/701#discussion_r3249546364), [PR #699 review 4239813599](https://github.com/tachyon-zcash/ragu/pull/699#pullrequestreview-4239813599).

## Avoid moving internal distinctions onto the caller

A superficially cleaner internal split can make a circuit developer choose between paths they previously did not need to understand. Assess the call-site burden explicitly.

Sources: [PR #527 review 3891358193](https://github.com/tachyon-zcash/ragu/pull/527#pullrequestreview-3891358193), [PR #527 review 3906039835](https://github.com/tachyon-zcash/ragu/pull/527#pullrequestreview-3906039835), [PR #701 inline 3249586774](https://github.com/tachyon-zcash/ragu/pull/701#discussion_r3249586774).

## Inspect real memory and computation costs

Distinguish borrowed witnesses, deep clones, cheap Arc clones, streaming algorithms, and materialized intermediates. Do not erase a commitment optimization during structural cleanup.

Sources: [PR #561 review 3932909504](https://github.com/tachyon-zcash/ragu/pull/561#pullrequestreview-3932909504), [PR #561 inline 2921333457](https://github.com/tachyon-zcash/ragu/pull/561#discussion_r2921333457), [PR #479 inline 2815115896](https://github.com/tachyon-zcash/ragu/pull/479#discussion_r2815115896), [PR #515 inline 2869645946](https://github.com/tachyon-zcash/ragu/pull/515#discussion_r2869645946).

## Keep explanations faithful across surfaces

Encoding is not verification. Trace renames and behavioral changes through the guide, examples, diagrams, tests, and comments; preserve the actual separation between registry-level and mask-level operations.

Sources: [PR #304 inline 2673582846](https://github.com/tachyon-zcash/ragu/pull/304#discussion_r2673582846), [PR #635 inline 3063171821](https://github.com/tachyon-zcash/ragu/pull/635#discussion_r3063171821), [PR #602 inline 2969707616](https://github.com/tachyon-zcash/ragu/pull/602#discussion_r2969707616), [PR #644 inline 3076054316](https://github.com/tachyon-zcash/ragu/pull/644#discussion_r3076054316).

## Separate optional redesign from a reviewable change

Keep a focused fix coherent and narrow. Caller-free API expansion can wait, and a supposedly cosmetic lifetime removal must not silently grow into ownership changes throughout the pipeline.

Sources: [PR #561 review 3949390494](https://github.com/tachyon-zcash/ragu/pull/561#pullrequestreview-3949390494), [PR #699 review 4239813599](https://github.com/tachyon-zcash/ragu/pull/699#pullrequestreview-4239813599), [PR #456 review 3782168391](https://github.com/tachyon-zcash/ragu/pull/456#pullrequestreview-3782168391), [PR #596 review 3981804544](https://github.com/tachyon-zcash/ragu/pull/596#pullrequestreview-3981804544).

## Calibrate conclusions and revise assumptions

A preliminary pass is not a complete review. Acknowledge an overly restrictive assertion or a missing binding in an attack argument instead of preserving the initial objection.

Sources: [PR #253 review 3581042653](https://github.com/tachyon-zcash/ragu/pull/253#pullrequestreview-3581042653), [PR #508 inline 2850384279](https://github.com/tachyon-zcash/ragu/pull/508#discussion_r2850384279), [PR #353 inline 2820225247](https://github.com/tachyon-zcash/ragu/pull/353#discussion_r2820225247), [PR #669 discussion 4361788775](https://github.com/tachyon-zcash/ragu/pull/669#issuecomment-4361788775).

## Calibration and exceptions

- Do not infer a permanent preference for more assertions: the corpus also questions tautological checks and retracts over-restrictive ones (PRs #621 and #508).
- Do not infer that every review must start a new broad test suite: many comments consolidate duplicate tests and favor one stronger existing property test.
- A historical optimistic ACK is not a current security verdict, a complete audit, or authorization to merge anything.
