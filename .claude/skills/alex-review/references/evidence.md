# Evidence for Alex Xiong's review model

Source: account [alxiong](https://github.com/alxiong) in [tachyon-zcash/ragu](https://github.com/tachyon-zcash/ragu), captured on 2026-10-23.

The complete collection contains 740 account-attributed records across 146 PRs: 300 review events, 352 inline comments, and 88 PR discussion comments. Of these records, 494 have text. The primary style evidence is 268 nonempty contributions on 80 PRs authored by others; 226 nonempty contributions on the account's own PRs were retained as author-response context.

Empty review events describe review activity, not articulated priorities. Exact duplicate bodies were collapsed for reading, with original IDs retained in the collection. The examples below are selected evidence for the distilled decisions, not an exhaustive list of feedback or a quantitative ranking of beliefs. Account attribution does not establish that each word was written without AI assistance; the corpus includes explicitly disclosed assisted feedback.

The skill infers reusable review behavior from this history. Each link is historical: retrieve current source before reusing a technical claim. A comment can be tentative, corrected later, or superseded. The examples do not certify current PRs, supply a soundness theorem, or authorize remote actions.

## Fix objects before deriving their checking challenges

Reconstruct the actual commitment/challenge dependency, rather than checking only final equations. The early NARK comments ask when the wiring and public-input polynomials become bound.

Sources: [PR #141 inline 2575852295](https://github.com/tachyon-zcash/ragu/pull/141#discussion_r2575852295), [PR #141 inline 2580662294](https://github.com/tachyon-zcash/ragu/pull/141#discussion_r2580662294), [PR #141 inline 2582044995](https://github.com/tachyon-zcash/ragu/pull/141#discussion_r2582044995).

## Check state transitions and mathematical roles

Ask whether accumulator state actually updates, distinguish conventional folding order from an actual correctness error, and test whether a proposed staged interface covers nested commitments as well as field elements.

Sources: [PR #35 inline 2572708189](https://github.com/tachyon-zcash/ragu/pull/35#discussion_r2572708189), [PR #142 inline 2575562887](https://github.com/tachyon-zcash/ragu/pull/142#discussion_r2575562887), [PR #909 inline 4360423601](https://github.com/tachyon-zcash/ragu/pull/909#discussion_r4360423601).

## Refute your own proposed attack

The step-repetition concern in #353 was explicitly withdrawn after identifying how gadget indexing changes the registered circuit. The model should reproduce the counterargument, not repeat the withdrawn security claim.

Sources: [PR #353 inline 2819927503](https://github.com/tachyon-zcash/ragu/pull/353#discussion_r2819927503), [PR #353 inline 2820276476](https://github.com/tachyon-zcash/ragu/pull/353#discussion_r2820276476).

## Separate completeness, soundness, and verifier visibility

The grouped-mask discussion progresses from an honest-trace argument to a component counterexample. A subsequent reply rejects coefficient-inspection remediation for a compressed verifier. This documents a proof obligation and a historical debate, not an audit of the current head.

Sources: [PR #688 review 4189901815](https://github.com/tachyon-zcash/ragu/pull/688#pullrequestreview-4189901815), [PR #688 review 4225586815](https://github.com/tachyon-zcash/ragu/pull/688#pullrequestreview-4225586815), [PR #688 discussion 4476640663](https://github.com/tachyon-zcash/ragu/pull/688#issuecomment-4476640663).

## Localize invariants instead of relying on coordination

An implicit placeholder gate assumption, short-circuit cache preconditions, non-local allocator choices, and intertwined remapping state all motivate smaller locally auditable operations.

Sources: [PR #496 inline 2833513490](https://github.com/tachyon-zcash/ragu/pull/496#discussion_r2833513490), [PR #458 discussion 3938099458](https://github.com/tachyon-zcash/ragu/pull/458#issuecomment-3938099458), [PR #647 inline 3085920395](https://github.com/tachyon-zcash/ragu/pull/647#discussion_r3085920395), [PR #557 inline 3117578030](https://github.com/tachyon-zcash/ragu/pull/557#discussion_r3117578030).

## Match identity to its actual consumer

Type names and shapes do not uniquely identify configurable routines. Examine counts, zero constraints, nested output placement, and the cost of identifying a routine before reusing its work.

Sources: [PR #503 inline 2853564105](https://github.com/tachyon-zcash/ragu/pull/503#discussion_r2853564105), [PR #511 inline 2909283519](https://github.com/tachyon-zcash/ragu/pull/511#discussion_r2909283519), [PR #557 inline 2937837091](https://github.com/tachyon-zcash/ragu/pull/557#discussion_r2937837091), [PR #511 inline 2878983741](https://github.com/tachyon-zcash/ragu/pull/511#discussion_r2878983741).

## Measure the actual workload and concurrency

Decide whether allocation belongs in the measured operation; a deferred call is not a concurrent call. A locally observed fuse result within noise did not justify hand-unrolled Horner code.

Sources: [PR #390 inline 2730487632](https://github.com/tachyon-zcash/ragu/pull/390#discussion_r2730487632), [PR #476 discussion 3951819893](https://github.com/tachyon-zcash/ragu/pull/476#issuecomment-3951819893), [PR #589 discussion 4302177082](https://github.com/tachyon-zcash/ragu/pull/589#issuecomment-4302177082), [PR #510 inline 2867434236](https://github.com/tachyon-zcash/ragu/pull/510#discussion_r2867434236).

## Prefer useful concrete APIs to speculative generality

A type alias may add mental indirection, a general equality trait may be premature, and an extra helper API needs sufficient benefit. Straightforward Arc usage can be clearer than an alias.

Sources: [PR #329 discussion 3757895136](https://github.com/tachyon-zcash/ragu/pull/329#issuecomment-3757895136), [PR #449 discussion 3883322458](https://github.com/tachyon-zcash/ragu/pull/449#issuecomment-3883322458), [PR #564 review 3954519398](https://github.com/tachyon-zcash/ragu/pull/564#pullrequestreview-3954519398), [PR #704 inline 3260287570](https://github.com/tachyon-zcash/ragu/pull/704#discussion_r3260287570).

## Improve existing abstractions before adding mirrors or boilerplate

Use the wireless driver to reuse an existing sponge instead of maintaining a native mirror. Derive customization can remove substantial handwritten gadget code; proposed driver wrappers must fit the actual trait bounds and output types.

Sources: [PR #802 inline 3517488113](https://github.com/tachyon-zcash/ragu/pull/802#discussion_r3517488113), [PR #449 review 4161750730](https://github.com/tachyon-zcash/ragu/pull/449#pullrequestreview-4161750730), [PR #651 inline 3090553623](https://github.com/tachyon-zcash/ragu/pull/651#discussion_r3090553623).

## Explain first principles with useful examples

A design page should expose the reasoning to audit rather than paraphrase source. Prefer linking good rustdoc and adding guide examples; the introduction should show a small application before deeper fusing details.

Sources: [PR #599 review 4105480035](https://github.com/tachyon-zcash/ragu/pull/599#pullrequestreview-4105480035), [PR #371 inline 2712802423](https://github.com/tachyon-zcash/ragu/pull/371#discussion_r2712802423), [PR #320 inline 2674298360](https://github.com/tachyon-zcash/ragu/pull/320#discussion_r2674298360), [PR #599 inline 3080555990](https://github.com/tachyon-zcash/ragu/pull/599#discussion_r3080555990).

## Use precise names, claims, and measurement context

Disambiguate final versus overall witnesses and local versus absolute counters. Question security-model claims about depth, and qualify old measurements when the production rank changes.

Sources: [PR #370 inline 2710950531](https://github.com/tachyon-zcash/ragu/pull/370#discussion_r2710950531), [PR #483 inline 2844195863](https://github.com/tachyon-zcash/ragu/pull/483#discussion_r2844195863), [PR #320 inline 2674242161](https://github.com/tachyon-zcash/ragu/pull/320#discussion_r2674242161), [PR #899 inline 4245794754](https://github.com/tachyon-zcash/ragu/pull/899#discussion_r4245794754).

## Keep preferences revisable and defenses motivated

The record retracts a seeded-benchmark-RNG preference, accepts a fingerprint split provisionally, and rejects a speculative defense already covered by a constraint count. These are explicit limits on turning historical comments into unconditional rules.

Sources: [PR #390 inline 2734572973](https://github.com/tachyon-zcash/ragu/pull/390#discussion_r2734572973), [PR #557 inline 2944537042](https://github.com/tachyon-zcash/ragu/pull/557#discussion_r2944537042), [PR #557 inline 3116862622](https://github.com/tachyon-zcash/ragu/pull/557#discussion_r3116862622), [PR #521 discussion 3997435364](https://github.com/tachyon-zcash/ragu/pull/521#issuecomment-3997435364).

## Calibration and exceptions

- Do not encode the withdrawn #353 attack or the initial deterministic-RNG preference as established requirements.
- Do not confuse a component-level counterexample in #688 with a complete forged compressed proof. The later compressed-verifier objection is part of the same reasoning.
- The sparseness simplification proposed in #605 and the no_std trade-off in #525 are contextual design opinions, not permanent repository architecture rules.
- Use tentative questions to surface an explicit uncertainty, not to disguise a demonstrated bug or avoid checking the relevant constraint.
