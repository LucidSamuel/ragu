# Book Review FIXMEs

Tracked issues from structural review that are deferred for later. Use
`/book-refine` to turn feedback into policy improvements when addressing these.

## Deferred Issues

### Wire variable case inconsistency between allocation and drivers pages

`guide/primitives/allocation.md` uses uppercase $(A, B, C, D)$ for gate
wires while `guide/drivers/index.md` uses lowercase $(a, b, c, d)$. The
rustdoc source uses uppercase. Align both pages to one convention
(preferably uppercase to match the source).

### Empty category heading for `implementation/drivers/`

SUMMARY.md line 48 `[Drivers]()` has no index.md, with only 2 child pages
(emulator.md has content, custom.md is a TODO stub). Revisit when custom.md
is written — may need a substantive index.md or flattening.
