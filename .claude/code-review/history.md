# History & Context Review Policy

## Scope

Use git history to find context-dependent bugs, regressions, and patterns that
a static read of the code would miss.

## Procedure

1. Identify the files and functions being reviewed.
2. Use the supplied review revision, not an unrelated local branch. Start with
   `git log --oneline -20 {revision} -- {file}` to see recent evolution, then
   inspect the relevant commit diffs rather than relying on commit subjects.
3. Run `git blame -L {start},{end} {revision} -- {file}` on the specific lines
   under review. For local changes, also inspect the captured diff and contents;
   committed history does not explain uncommitted behavior.
4. If the reviewed code modifies or extends an existing function, check what the
   function and its affected callers looked like at the comparison base. Follow
   renames or search older history when a relevant invariant remains unexplained.
5. Connect historical intent to the current contract and a reachable failure.
   Previous code, commit messages, and old review approvals are context, not
   proof that the behavior was correct or must remain unchanged.

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

Cite the relevant revision and explain what invariant was lost. Distinguish
reintroduced defects from inherited limitations and deliberate contract changes.
If history is unavailable or shallow, report that limit instead of inventing
design rationale.

## What NOT to Look For

- General code quality unrelated to history context.
- In a diff review, unrelated issues on lines unaffected by the change.
- Style or formatting — other reviewers and automated checks handle that.
