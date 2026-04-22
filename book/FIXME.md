# Book Review FIXMEs

Tracked issues from structural review that are deferred for later. Use
`/book-refine` to turn feedback into policy improvements when addressing these.

## Deferred Issues

### Section ordering in `guide/getting_started.md`

"Configuration at a Glance" appears before the reader knows what they're
building. Consider moving it after "Overview: Building a Merkle Tree with
Proofs" so readers understand WHAT they're building before seeing configuration
parameters. (Blocked: file is modified in PR #659.)

### Redundant Header trait explanation

`guide/getting_started.md` (Step 1) and `guide/writing_circuits.md` (Working
with Headers) cover near-identical Header trait implementations. Consider
consolidating: keep the minimal example in getting_started.md and have
writing_circuits.md reference it with deeper explanation. (Blocked: both
files are modified in PR #659.)

### Wire variable case inconsistency between allocation and drivers pages

`guide/primitives/allocation.md` uses uppercase $(A, B, C, D)$ for gate
wires while `guide/drivers/index.md` uses lowercase $(a, b, c, d)$. The
rustdoc source uses uppercase. Align both pages to one convention
(preferably uppercase to match the source).

### Empty category heading for `implementation/drivers/`

SUMMARY.md line 48 `[Drivers]()` has no index.md, with only 2 child pages
(emulator.md has content, custom.md is a TODO stub). Revisit when custom.md
is written — may need a substantive index.md or flattening.
