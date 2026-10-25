# Design Review Policy

## Scope

Review naming, code structure, and API design in Rust source files. Focus on
readability, maintainability, and consistency with project conventions.

## Naming

- Variable names should reflect their mathematical or domain meaning. Prefer
  `acc` over `a` for accumulators, `coeff` over `c` for coefficients — unless
  the single-letter name is standard notation in the relevant paper/protocol.
- Avoid abbreviations that aren't universally understood. `poly` for polynomial
  is fine; `cmt` for commitment is not.
- Boolean variables and functions should read as predicates: `is_zero()`,
  `has_input`, not `zero()` or `input`.
- Type names should be nouns; trait names should be adjectives or capabilities
  (e.g., `Driver`, `Gadget`).

## Code Structure

- Functions should do one thing. If a function has sections separated by blank
  lines with different purposes, consider splitting it.
- Avoid deep nesting. Prefer early returns, `let-else`, or extracting helpers.
  More than 3 levels of indentation is a code smell.
- Keep functions short enough to fit on one screen (~50 lines). Long functions
  hide bugs.
- Group related items together. Private helpers should be near their callers.

## API Design

- Public APIs should be hard to misuse. Prefer newtypes over raw integers/arrays
  when the type carries semantic meaning.
- Generic bounds should be minimal. Don't require `Clone` if you don't clone.
- Avoid output parameters; return values instead. Rust's tuples and structs make
  this easy.
- Default trait implementations should be overridable for performance without
  changing semantics.
- Identify where values are validated and which operations preserve their
  invariants; check that conversions and mutation cannot bypass that boundary.

## Compatibility and Configuration

- Trace changes to accepted inputs, defaults, results, errors, and public types
  through callers. Check the new contract and consistent caller migration.
- Check feature and dependency changes in affected supported configurations,
  including `no_std`, default features disabled, and serial builds.
- Recommend abstractions or refactors to address a concrete duplication, misuse,
  or maintenance problem. Keep the proposed change proportional to that problem.

## What Not to Do

- Don't leave commented-out code. Delete it; git remembers.
- Don't add/modify dependencies without justification. This is a `no_std` crate;
  dependencies are expensive.
- Don't add features "for later". Implement what's needed now.
