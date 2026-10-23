# Code Review Master Standards

These standards apply to all code reviewers. Each reviewer also has a
focus-specific policy file.

## Scope

- Review Rust source files (`.rs`) in the workspace.
- For diff reviews, report defects introduced, worsened, or made reachable by
  the change. Follow effects into unchanged code, but exclude unrelated existing
  issues. For whole-file or concept reviews, assess the requested scope directly.
- Use the supplied review snapshot. Read complete affected functions and relevant
  callers, tests, and configuration to establish how a suspected failure is
  reached and whether another layer already handles it.

## Finding Requirements

Each finding must include:

- **Location**: The smallest useful file/line range, preferably in the diff for
  a change review. Cite affected callers as supporting context.
- **Issue**: A reachable triggering condition, the expected and actual behavior,
  and the concrete consequence. Identify the affected caller or contract and,
  for a diff review, explain how the change causes the problem. For suggestions,
  describe the concrete clarity or maintenance problem instead of inventing a
  behavioral defect.
- **Evidence**: A reproducer or a complete code argument supporting the claim.
  State what was verified and which assumptions remain. A runnable
  reproducer is useful but is not required for a defect established by the code.
- **Suggestion**: A concrete correction and, where useful, a regression check
  that distinguishes the broken and corrected behavior.
- **Severity**: `must-fix` or `suggestion`, justified by the consequence or the
  explicit project requirement being violated.

Confidence describes the strength of the evidence; severity describes the
consequence. Report unconfirmed failure paths as open questions, separate from
confirmed findings. Missing validation is not by itself a production defect.

## Severity Levels

- **must-fix**: Correctness bug, safety issue, violation of an explicit project
  requirement, or documentation that is actively misleading.
- **suggestion**: Improvement that would make the code clearer, more idiomatic,
  or easier to maintain, but isn't wrong as-is.

Style heuristics alone do not justify `must-fix`. For suggestions, explain the
specific readability, misuse, or maintenance problem and the benefit of the
proposed change. Avoid preference-only rewrites.

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
