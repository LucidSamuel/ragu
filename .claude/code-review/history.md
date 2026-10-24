# History & Context Review Policy

## Scope

Use git history to find context-dependent bugs, regressions, and patterns that
a static read of the code would miss.

## Procedure

1. Identify the files and functions being reviewed.
2. Run `git log --oneline -20 {revision} -- {file}` at the supplied revision and
   inspect relevant commit diffs.
3. Run `git blame -L {start},{end} {revision} -- {file}` on reviewed lines. For
   local changes, also inspect the captured diff and contents.
4. Compare changed functions and affected callers with the comparison base.
   Follow renames or older history to clarify unexplained invariants.
5. Assess historical intent against the current contract. Old code, messages, or
   approvals do not establish correctness or require preserving old behavior.

## What to Look For

- **Regressions**: Does the new code revert or contradict a previous deliberate
  fix? Check if a recent commit message explains *why* something was done a
  certain way.
- **Incomplete migrations**: If a pattern was recently changed elsewhere in the
  file (e.g., error handling style, naming convention), does the reviewed code
  follow the new pattern or accidentally use the old one?
- **Lost invariants**: If `git blame` shows that a safety check or assertion was
  added in a targeted fix, does the reviewed code preserve that check?
- **Copy-paste drift**: If the reviewed code is structurally similar to another
  block in the same file, check whether both blocks have been kept in sync with
  recent changes.
- **Weakened regression tests**: If a test is removed or rewritten, check whether
  its replacement still detects the original failure and exercises the affected
  path.

Cite the revision and lost invariant; distinguish regressions from inherited
limitations or deliberate contract changes. Report unavailable or shallow
history as a limit rather than inventing rationale.

## What NOT to Look For

- General code quality unrelated to history context.
- In a diff review, unrelated issues on lines unaffected by the change.
- Style or formatting — other reviewers and automated checks handle that.
