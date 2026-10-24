# Code Review Master Standards

These standards apply to all code reviewers. Each reviewer also has a
focus-specific policy file.

## Scope

- Review Rust source files (`.rs`) in the workspace.
- For diff reviews, report defects introduced, worsened, or made reachable by
  the change. Follow effects into unchanged code, but exclude unrelated existing
  issues. For whole-file or concept reviews, assess the requested scope directly.
- Use the supplied snapshot. Read full affected functions and relevant callers,
  tests, and configuration before reporting findings.

## Project Conventions

Documented project conventions are authoritative and must not be weakened by
generic guidance. A demonstrated violation is actionable without a runtime bug.

## Finding Requirements

Each finding must identify its location, issue, supporting evidence, severity,
and a concrete correction. For behavioral defects, explain a reachable failure
and its consequence; a complete code argument is sufficient. For policy
violations, cite the rule and conflicting code or text. Report unconfirmed
concerns and unrun checks separately.

## Severity Levels

- **must-fix**: Correctness bug, safety issue, clear violation of project
  conventions, or documentation that is actively misleading.
- **suggestion**: Improvement that would make the code clearer, more idiomatic,
  or easier to maintain, but isn't wrong as-is.

Suggestions without a policy basis must identify a concrete readability, misuse,
or maintenance problem and explain the benefit of the change.

## Synced Content

When content is shared between the README and the book, it is
delimited by `<!-- BEGIN SYNC -->` / `<!-- END SYNC -->` HTML comments.
There are currently no synced pairs.

When reviewing changes inside a synced block, verify that the
corresponding file contains identical content. Flag any drift as
`must-fix`. When editing a synced block (e.g. during fix-up), update
both files in the same change.

## Shared Policies

For content placement decisions (book vs. rustdoc), see
`.claude/review-shared/surface-placement.md`.

## General Principles

- Be specific. "This could be improved" is not actionable. Quote the code, name
  the issue, propose a fix.
- Stay within your policy's scope. If something is outside your area, leave it
  for the relevant reviewer.
- If you find no real issues, say so. Do not manufacture problems.
- Consider the project context: this is a `no_std` recursive proof system
  (proof-carrying data framework). Cryptographic code has different norms than
  application code.
