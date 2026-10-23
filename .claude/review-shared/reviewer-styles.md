# Reviewer styles distilled from Ragu history

Captured 2026-10-23. These are three review models based on account-attributed
GitHub feedback, with shared technical concerns and different emphases. They
are qualitative interpretations of the evidence, not claims to reproduce a
person or predict their approval.

## Collection coverage

All 621 accessible PRs in tachyon-zcash/ragu were enumerated, including open,
closed, and merged PRs. PR numbers run from #2 to #914; issues occupy other
numbers. The PR creation dates span 2025-10-02 through 2026-10-23.

The repository-wide collection contains 2,312 submitted review events, 3,113
inline review comments, and 884 PR discussion comments. The three selected
accounts contributed 5,670 records, including 3,898 nonempty text records,
across 541 distinct PRs.

| Account | Review events | Nonempty review bodies | Inline comments | PR discussion comments | PRs with account activity |
| --- | ---: | ---: | ---: | ---: | ---: |
| TalDerei | 1,126 | 186 | 1,689 | 403 | 460 |
| ebfull | 733 | 147 | 873 | 106 | 352 |
| alxiong | 300 | 54 | 352 | 88 | 146 |

Review events include empty submissions accompanying inline comments. Their
bodies and inline comments are separate records; an empty approval does not
establish a review principle.

To avoid mistaking an author's implementation explanation for reviewer
feedback, source roles were separated:

| Reviewer | Nonempty contributions on others' PRs | Distinct PRs for those contributions | Nonempty contributions on own PRs |
| --- | ---: | ---: | ---: |
| Tal | 1,245 | 229 | 1,033 |
| Sean | 845 | 211 | 281 |
| Alex | 268 | 80 | 226 |

The first column supplies the primary style evidence. Own-PR responses and
other participants' replies provide context, corrections, and outcomes. The
collection includes reviews of PRs authored by these three people and reviews
they left on PRs authored by anyone else in the repository. It is limited to
Ragu; it does not claim coverage of their other repositories.

## What each reviewer adds

| Reviewer | Characteristic question | Strongest recurring emphasis | Typical useful feedback |
| --- | --- | --- | --- |
| Tal | Where does this value or obligation go, and does the next layer actually check it? | End-to-end claim flow, prover/verifier agreement, exhaustive ordering and coverage, meaningful tests, consumer-facing API friction, documentation drift | Trace the relevant call path, identify the mismatch, and suggest a shared source or focused test. |
| Sean | Why does this abstraction exist, and does its contract make misuse hard? | Protected invariants, small APIs, architectural ownership, precise circuit semantics, minimal coordination, economical explanations | Identify the faulty contract or abstraction boundary and propose a smaller coherent design. |
| Alex | What is the argument, what could a malicious prover change, and does the optimization pay for itself? | Protocol timing, mathematical assumptions, concrete counterexamples, local invariants, equivalence definitions, real performance costs, auditable rationale | Restate the argument, test its assumptions, and offer an equation, counterexample, measurement, or clearer interface. |

All three review soundness, APIs, tests, performance, and documentation. These
are differences of emphasis, not exclusive specialties. Their wording and
level of detail also vary with the patch and maturity of the design.

### Tal

Tal often connects the local patch to a wider invariant: a header encoding
must agree with the verifier's instance construction, a traversal must cover
fields outside its main enum, a consistency method must survive a staging
boundary, and a polynomial query must reach the fuse consumer. He often uses
prior PRs to recover rationale and notices stale references after refactors.

Test feedback asks whether the test reaches the behavior in its name:
construction versus synthesis, trivial versus seeded/nontrivial proofs,
symmetric versus asymmetric dimensions, and nested Known/Unknown paths. The
goal is useful coverage; many comments also remove duplicate tests.

The reusable communication pattern is an observation with a concrete
cross-file consequence, followed by a focused question or small correction.
Partial passes and optional redesigns should remain labeled that way.

Sources and exceptions: [Tal evidence](../skills/tal-review/references/evidence.md).

### Sean

Sean's feedback frequently asks whether the API itself can establish an
invariant instead of making callers remember checks, indices, layout advice,
or extra handles. He challenges traits without generic consumers, wrappers
that only forward calls, abstractions placed in the wrong crate, and public
interfaces added for tests.

The emphasis on precise, short explanations comes with limits. He repeatedly
preserves useful local rationale that a policy would delete, accepts staged
exposition in a guide, and labels many style preferences non-blocking. His
feedback is not accurately represented by an unconditional ban on unwraps or
debug assertions, a universal function-length limit, or treating all nits as
merge blockers.

The reusable communication pattern states the underlying contract or
mathematical fact, explains the mismatch, and offers the smallest coherent
correction. Uncertain architectural ideas remain proposals.

Sources and exceptions: [Sean evidence](../skills/sean-review/references/evidence.md).

### Alex

Alex often reconstructs the protocol, algebra, or cost argument before
judging the code. He asks when commitments are fixed relative to challenges,
whether accumulator state is really updated, which equivalence relation a
cache uses, and what a compressed verifier can actually see.

He favors examples that make non-local assumptions auditable and questions
extra abstraction when the concrete API is already clear. Performance
feedback checks setup costs, heap collections, real concurrency, and whether
a small local result matters to the full fuse workload.

The reusable communication pattern is a tentative but specific interpretation,
then a falsifiable question or counterexample. Retractions are part of the
model: the repeated-step attack in #353 was withdrawn when registration
binding was identified. The #688 component counterexample and the later
compressed-verifier objection must be understood together.

Sources and exceptions: [Alex evidence](../skills/alex-review/references/evidence.md).

## How the history became instructions

The complete collection was normalized by account, PR, record type, source
role, date, and stable GitHub record ID. Review summaries, inline feedback,
and PR discussions were considered together. Exact duplicate text was
collapsed for reading while the original records were retained. Substantive
reviewer comments were examined across the history, with longer arguments
and relevant follow-up replies inspected for conditions and retractions.

The evidence references select 142 source placements across the three
profiles; the machine-readable manifest records their IDs, themes, URLs, and
body hashes. A source can support more than one theme, so this is not a count
of independent observations. Repeated priorities become review heuristics;
one-off architectural proposals remain examples. Quoted remarks by another
participant and bare acknowledgments do not independently establish a rule.

The existing repository policies and local Sean reviewer configuration were
inspected for compatibility, but they were not used as proof that Sean holds
every rule they contain. The GitHub examples supply the attribution. Some
posts disclose AI-assisted feedback; account attribution does not imply that
every sentence is handwritten.

The skills use the historical priorities to inspect current code. They do
not inherit old approval states, merge authority, circuit counts, current
protocol assumptions, or historical security verdicts. Every new review must
establish its own scope, revisions, findings, and evidence.

## Reproducing the collection

The capture used authenticated, read-only GitHub API requests:

- GraphQL repository pullRequests(first: 50), ordered by creation time and
  paginated to completion. Each PR includes its author, metadata, head/base
  IDs, and reviews(first: 100) with author, body, state, date, URL, and commit.
- REST repos/tachyon-zcash/ragu/pulls/comments?per_page=100, all pages, for
  inline comments, original diff hunks, commits, and reply IDs.
- REST repos/tachyon-zcash/ragu/issues/comments?per_page=100, all pages,
  filtered to the enumerated PR numbers for PR discussions.

The normalization asserted that the PR count equals GraphQL totalCount,
every PR's review list equals its nested totalCount, no nested review list
has another page, and inline/discussion IDs are unique. If a future capture
has more than 100 reviews on a PR, its nested reviews must also be paginated.
No source text was truncated in the saved collection.

See [the capture manifest](reviewer-corpus-2026-10-23.json) for exact counts,
retrieval time, selected evidence, and SHA-256 hashes of the raw captures.
The raw JSON, normalized records, and analysis scripts from this run are in
/private/tmp/ragu-review-styles-20261023; that temporary directory is not part
of the portable skills and is not durable storage.

Deleted or inaccessible comments and unsubmitted drafts cannot be recovered.
The paginated capture is not an atomic snapshot. This work analyzes review
feedback; it does not re-audit the code changes in all 621 historical PRs.

## Using the reviewers

Use $tal-review, $sean-review, or $alex-review with a PR, diff, file, or design.
Each skill contains its own instructions and evidence reference, so it can
be used independently. The named perspective should be selected when
requested; routine reviews do not need to load all three.

The three models can also inform future reviewer-agent prompts. Choosing a
skill does not launch agents, publish a GitHub review, modify a PR, or imply
the real person's endorsement.
