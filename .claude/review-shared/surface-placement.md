# Surface Placement Policy

What belongs in the book vs. rustdoc.

## Math lives in the book

- The book is the primary home for math — it supports custom macros, display
  environments, and cross-referencing that rustdoc cannot.
- In rustdoc, math must survive three nested layers (Rust comment syntax,
  markdown parsing, LaTeX delimiters) that fight over escaping, line width,
  and special characters. Prefer the book for anything beyond a short inline
  formula.
- Exception: algorithms and constructions too narrow or internal for the user
  guide must be documented mathematically in the code, including whatever
  derivations are needed to maintain them.
- Code should still use math notation (shared with the book) whenever
  describing a concept or object that exists in the book. The notation home
  is the book; code references it.

## Code owns API truth

- Rustdoc is the authority for API specifics: signatures, bounds, feature
  behavior, error semantics, safety contracts, preconditions, postconditions,
  and invariants.
- A reader relying only on rustdoc should be able to correctly use every
  public item and implement every required trait.
- The book may cover the same topics at a higher level (motivation, design
  rationale, composition guidance) but defers to code documentation for
  specifics.
- If the book states a constraint more precisely than rustdoc, that precision
  must move to rustdoc.
- Code snippets in the book may intentionally omit trait items, bounds, or
  other details that the surrounding text is not ready to discuss. This is
  not dishonest — the reader will encounter the full trait in rustdoc, and
  the book is not meant to be a comprehensive API reference. Do not expand
  book snippets to include items just for completeness.

## Describe behavior, not prohibitions the type already prevents

- A warning against an action the type makes impossible adds noise, not safety.
  When a signature, a narrowed argument type, or a restricting wrapper removes
  the ability to misuse an item, drop the "must not" wording and state what the
  item does instead — the implementer's only latitude is to perform that
  operation correctly.
- Favor a plain account of the operation performed over a list of forbidden
  steps. "Writes each field in declaration order" reads better than "must write
  every field and may do nothing else."
- A type introduced to enforce a contract is itself the statement of that
  contract. Document the single operation it permits, not the enforcement
  retold as a duty still owed by the implementer. Repeating a guarantee the
  type already provides only inflates the apparent complexity of an API that is
  usually intricate enough already.
- This sharpens the per-surface "API Contracts" rule (state the contract, not
  the fallout of breaking it). That rule governs obligations the caller must
  meet; an obligation the type discharges on the caller's behalf needs no prose
  at all.

## Don't write the same thing twice

- For any given topic, decide which components belong on which surface. The
  book typically owns the conceptual overview; the code owns the lower-level
  details. This split can be ad-hoc per topic.
- Each piece of information has one canonical home.
- When both surfaces need to reference the same content, use summary + link
  rather than parallel full descriptions.
- Rustdoc may fully state API requirements (preconditions, invariants,
  safety contracts, behavioral descriptions of public items) even when
  the book covers the same topic — each surface must serve its audience
  independently. This is not duplication; it is each surface doing its job.
- Pure design rationale or motivational exposition that adds no API
  insight should not be duplicated — use summary + link instead.
- Exception: design rationale that is too nuanced or implementation-coupled
  for the book — and that directly helps a developer understand *why* an API
  is shaped the way it is — belongs in rustdoc even if it reads as
  motivational. Not all "why" prose is dispensable exposition; some of it is
  essential context that has no better home.
- Do not condense rustdoc that already provides a brief, self-contained
  orientation to a module's concepts. If the existing prose is already
  concise, it is not "duplication" — it is the rustdoc doing its job for
  readers who never open the book.

## Same topic, different register on each surface

- A topic that genuinely belongs on both surfaces should be written from a
  different vantage on each. The book addresses the reader and the path they
  are expected to take, with enough motivation to justify it. Rustdoc addresses
  whoever arrived at a particular item and wants to know what it does: local,
  exact, and complete for that item.
- Decide what goes in the book by asking whether it sits on the reader's path,
  not whether it happens to be accurate. Obligations that fall only on
  implementers, fallbacks meant for internal use, and routes a typical reader
  should never take all fail that test, and including them obscures the path
  that matters. Keep them in rustdoc. If a route is not one a reader should
  follow, the guide is usually better off omitting it, or noting it in a single
  line that redirects to the recommended approach.
- Rustdoc may name such a fallback, explain why it exists, and steer the reader
  toward the preferred alternative; they are already looking at the item and
  should learn it is not the default choice. The guide stays silent, having
  never sent the reader there.
- Keep the explanation of why something exists beside whatever depends on it —
  frequently a different type or trait than the one being described — and treat
  that as its only home. Elsewhere, summarize and link rather than repeat.
- Show users a finished abstraction. Do not document internal lifecycle states,
  such as an invariant lapsing for a moment or a value passing through an
  invalid intermediate form, when the framework restores them before anything
  observable happens; and do not explain a function by the repair work it does
  behind the scenes. Tell the reader what holds, not how it is kept holding.

## Code changes; the book should not become redundant

- Volatile, implementation-coupled facts (optimizations, representation
  choices, algorithm variants) belong in code docs.
- Exception: a brief, concrete example of an implementation strategy is
  welcome in the book when it illuminates *why* a design decision exists —
  e.g., sketching how synthesis drivers stash wires to explain why `alloc`
  cannot be implemented generically. These examples build intuition and are
  harmless even if the implementation later changes.
- The book stays abstract enough that routine code changes don't invalidate
  it.
- Content that interacts with the book in limited or compartmentalized ways
  is better documented only in the code.
- Never strip explanatory detail from rustdoc unless a book page already
  exists to absorb it and a cross-link replaces the removed text. Condensing
  rustdoc into a terse summary without a destination for the detail is a net
  loss of documentation.

## The book can cross-cut; rustdoc is item-scoped

- Rustdoc is structurally tied to items (modules, types, functions).
  Explanations that span multiple items or modules are awkward in rustdoc —
  you have to pick one item to attach them to.
- The book has no such constraint. Concepts that span the crate boundary,
  involve multiple traits interacting, or require narrative buildup belong
  in the book.

## Proximity keeps docs accurate

- Docs next to the code they describe are more likely to be updated when the
  code changes. The farther documentation is from its subject, the faster it
  drifts.
- This reinforces placing implementation-specific details in code docs, not
  just to avoid book redundancy, but because proximity to the code is a
  maintenance incentive.

## Discovery paths differ

- Users find book content by reading linearly or via table of contents; they
  find rustdoc by searching for a type, trait, or function.
- Place content where its audience will look. API specifics in rustdoc because
  that's where users land when they need API info; conceptual overviews in the
  book because that's where users go when learning.

## The book serves non-Rust readers

- Researchers, protocol designers, and auditors may read the book without
  looking at code. The book should be self-contained for understanding the
  system conceptually without requiring Rust literacy.

## Linking is asymmetric

- Every mention of "the book" in rustdoc must be a clickable link to the
  relevant section. Bare prose references like "see the Foo chapter in the
  book" without a hyperlink are not acceptable — the reader should be one
  click away.
- Book-to-rustdoc links are stable (item paths are crate-structural).
  Rustdoc-to-book links are fragile (anchors and structure can move).
- The fragile direction (rustdoc → book) needs more resilient summaries so
  that a broken link degrades gracefully rather than leaving the reader
  stranded.

## Code has better examples

- Rustdoc examples compile and test — they are the canonical runnable samples
  and the least likely to bitrot.
- The book should reuse tested snippets (doctests, examples, tests) where
  possible; use pseudocode when runnable code isn't practical.
- `rust,ignore` in the book is a last resort.
