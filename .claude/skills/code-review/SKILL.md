---
name: code-review
description: Review Rust changes, files, or PRs using project policies and validated findings
user-invocable: true
---

# Code Review

Review code specified by `$ARGUMENTS`, using the project's code review policies.

## Step 1: Figure Out What to Review

The user's `$ARGUMENTS` could be anything. Interpret them:

| Arguments | What to do |
|-----------|-----------|
| *(empty)* | Run `git diff HEAD -- '*.rs'` for the combined staged/unstaged changes and `git ls-files --others --exclude-standard -- '*.rs'` for untracked source files. Read the untracked files too. If neither contains changes to review, say so and stop. |
| Staged changes | Use `git diff --cached -- '*.rs'` and read file contents from the index, which may differ from the worktree. |
| A file path | Read that file. Review it. |
| A file path with lines (`foo.rs:50-80`) | Read that file. Focus the review on those lines (but read the full file for context). |
| Multiple file paths | Read all of them. Review each, and also look for consistency across them. |
| A PR number or URL (`#123`, URL) | Resolve the full PR base/head SHAs, determine the comparison base, and obtain the diff and corresponding file contents at those revisions. |
| A module or concept name | Use Grep/Glob to find where that code lives. Read those files. Review them. |
| A mix of the above | Handle each part, then review the union. |

If you're unsure what the user means, clarify the scope before starting review.

### Establish the Review Snapshot

Record the selected files, scope, and full revision identifiers. For a PR, record
the base tip, comparison base (normally the merge base), and head. Read the full
affected files at those revisions through Git or an isolated checkout; the
current working directory may be on a different branch.

For local changes, record HEAD and capture the selected diff and file contents,
including untracked files. Honor an explicit staged-only scope. Give reviewers
the same captured inputs and identify the checkout or snapshot used for checks.
Preserve the user's existing edits when preparing an isolated snapshot.

Recheck the selected inputs before reporting. If they changed during review,
refresh the affected review and validation or clearly identify the older
snapshot and unfinished work. Do not combine evidence from different snapshots.

## Step 2: Prepare Review Coverage

Review every applicable policy area, including its required shared policies.

1. Use Glob to find all `.claude/code-review/*.md` files.
2. Read `.claude/code-review/standards.md` (master standards shared by all
   reviewers).
3. Treat the remaining policy files as review areas. The engine decides how to
   group and assign those areas. Prepare context using this template, including
   the policies for the assigned areas:

   > You are reviewing Rust code in the ragu project (a recursive proof system /
   > proof-carrying data framework).
   >
   > Read these files:
   > - `.claude/code-review/standards.md` (master standards that always apply)
   > - {paths to `.claude/code-review/` policies for the assigned review areas}
   {if documentation is among the assigned areas, also include:}
   > - `.claude/review-shared/writing.md` (shared writing rules)
   > - `.claude/review-shared/math.md` (shared math rules)
   > - `.claude/review-shared/surface-placement.md` (book vs. rustdoc placement rules)
   >
   > **What to review:** {provide the scope, revision identifiers, captured diff
   > or selected contents, and paths to matching full files and context. State
   > whether this is a diff, whole-file, or concept review.}
   >
   > {If the scope is a diff, add: "Read affected callers and surrounding code
   > for context. Report only issues introduced, worsened, or made reachable
   > by the change."}
   >
   > {If the scope is a narrow range, add: "Focus findings on the selected range.
   > Read surrounding code and callers to understand its behavior."}
   >
   > {If the scope spans multiple files or a concept, add: "Pay attention to
   > consistency across the files. Flag contradictions, redundancies, or
   > inconsistencies as they span these locations."}
   >
   > Use the finding format and evidence requirements in `standards.md`.
   > Report open questions separately. Include the scope inspected, any checks
   > actually performed, useful test targets, and anything left unreviewed.
   > Leave source edits and external comments to the follow-up step.
   >
   > **Do NOT flag:**
   > - For diff reviews, unrelated pre-existing issues
   > - Things that linters or compilers already catch (formatting, imports,
   >   type errors) — automated checks run separately
   > - Pedantic nitpicks or style preferences not backed by project policy
   > - An intentional behavior change solely because it differs from the old
   >   behavior — still check the intended new contract and project policies
   > - The specific lint diagnostic explicitly waived by an ignore/allow
   >   attribute — still review that code for independent correctness issues
   >
   > **Tool usage rules:**
   > - Use the Grep tool for searching file contents — do NOT run `grep` or `rg`
   >   as a Bash command.
   > - Use the Read tool to read files — do NOT use `cat`, `head`, or `tail`.
   > - Use the Glob tool to find files — do NOT use `find` or `ls`.
   > - When you do use Bash, the command must be a clean shell command with NO
   >   comment lines (`#`) prepended. Put your reasoning in the `description`
   >   parameter, not in the command itself.
   >
   > Stay within the assigned review areas. Be specific. If you find no real
   > issues, say so — don't manufacture problems.

## Step 3: Run Required Checks and Targeted Tests

Use the relevant `.github/workflows/` files to identify the repository's
commands, toolchains, and feature configurations. Rust code and
build-configuration reviews require these baseline checks:

1. Formatting with the repository's pinned nightly rustfmt and configuration.
2. Workspace Clippy with the repository's required targets/features and warnings
   denied.
3. Rustdoc with the repository's required features, private items included, and
   warnings denied.

Run targeted tests that exercise changed behavior. Inspect existing coverage and
incorporate useful test targets proposed by reviewers. Targeted tests supplement
the baseline checks; compilation and lint success do not replace behavioral
tests.
Run shared checks once against the reviewed snapshot, and broaden testing for
failures, shared behavior, or repository requirements.

For documentation-only changes, run checks for the edited surface, such as
rustdoc for API comments or the book build for book content. Record which Rust
checks are not applicable and why; the full Rust suite is not required solely
for prose or review-policy edits. If a required check cannot run, report
incomplete validation and the reason rather than silently waiving it.

Record commands, relevant configuration, and results. For targeted tests, verify
that the intended cases actually ran and record passed/failed/ignored counts;
zero selected tests does not validate the intended behavior. Distinguish test
failures from setup/tool failures and unrun checks. Include useful diagnostics
in the report, without counting an automated diagnostic as a separate duplicate
review finding.

## Step 4: Validate Candidate Findings

Before synthesis, check each candidate against the full affected code, relevant
callers, and applicable project policies. For behavioral defects, try to disprove
the failure path: look for existing validation, unreachable triggering conditions,
or an intentional contract change that satisfies the new contract. For policy
violations, verify the cited rule and the conflicting code or text; absence of a
runtime bug does not invalidate the finding.
For diff reviews, establish how the change introduces, worsens, or exposes the
issue; its existence at the comparison base does not rule out a regression
in severity or reachability. Verify the consequence and the cited locations.

Use a focused reproducer where useful; a complete code argument can also
establish a defect. Resolve reviewer disagreements using evidence rather than
votes. Keep unconfirmed concerns as open questions and missing checks as
validation gaps. Merge findings sharing a root cause, including those reported
at different locations.

## Step 5: Synthesize

Account for every discovered review area in the engine's results: completed,
incomplete, or not applicable with a reason. Every applicable area must be
evaluated before coverage is complete. Missing or failed review work means
incomplete coverage, not an absence of findings.
Present:

- The reviewed scope and snapshot, coverage completion, and check results
- **Must-fix** issues first
- **Suggestions** second
- For each finding, note which reviewer(s) identified it
- Open questions, validation gaps, and unreviewed areas, when present

Within each severity group, organize findings by file path and line number.
If there are no supported findings, say so for the inspected scope and retain
any limits on review coverage or validation.

If the review scope was cross-file or conceptual, add a short section about
cross-cutting observations (consistency, naming conventions, etc.).

## Step 6: Follow Up When Requested

Deliver the review before follow-up actions. If the user requested only a review,
end with the report. Apply fixes or publish a comment when requested, including
authorization already given with the review request; do not ask again for the
same authorized action.

### Local Mode (file paths, diff, concept)

For findings the user requests to fix:

1. Read the target file to get the current content.
2. Apply the correction, preserving unrelated edits.
3. Run relevant regression tests. For Rust code or build-configuration fixes,
   run `just ci_local`; for documentation-only fixes, use the surface-specific
   checks described in Step 3.
4. Report what changed, the validation results, and any remaining findings.

Keep findings the user skips as deferred, with a reason if supplied. Choosing
not to fix a finding does not establish that it was incorrect or resolved.

### PR Mode (`#123` or PR URL)

When the user requests publication, verify that the findings still apply to the
PR head and refresh affected findings if it has changed. Post the synthesis via
`gh pr comment`. Format findings as a numbered list with code links using the
full reviewed commit SHA and line ranges (`L[start]-L[end]`), and include any
coverage or validation limits relevant to interpreting the review.
