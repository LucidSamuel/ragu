# GitHub integration

After this workflow lands on `main`:

1. Create a GitHub App installed **only on tachyon-zcash/ragu**, with repository
   permissions **Checks: write**, **Pull requests: write**, and **Contents: read**.
   No webhook is needed.
2. Create two Ragu Actions environments, both restricted to the `main` branch:
   `ragu-audit-publisher`, containing secret `RAGU_AUDIT_APP_PRIVATE_KEY`, and
   `ragu-audit-model`, containing secret `ANTHROPIC_API_KEY`.
   Keep these credentials out of repository and organization-wide secrets.
3. Set repository variables `RAGU_AUDIT_APP_ID` to the App's numeric ID,
   `RAGU_AUDIT_MODEL=claude-opus-5-5`, and `RAGU_AUDIT_EFFORT=xhigh`.
   The same model and effort apply to all four passes and their subagents.
   Claude Code is pinned to 2.1.310 in the runner and installation script.
4. Set `RAGU_AUDIT_ENABLED=true` and post exactly `/ragu-audit` as a new PR
   conversation comment. The command requires live write, maintain, or admin
   permission. PR updates and pushes do not trigger the audit workflow.
5. After a successful test run, require `ragu-audit/completed` on `main`, selecting
   this App as the expected publisher. Enable "Require branches to be up to date
   before merging" to enforce review against the current base. Keep the existing
   CI and approval rules.

One App-owned comment contains the four reports; complete reports and native
Claude results are also retained as workflow artifacts for 30 days. Missing or
failed native runs, missing reports, modified source, and moved revisions fail
the completion check. Checks attach to commits; identical snapshots across PRs
can share a result, while each invocation updates its own PR comment. Findings
do not automatically block this check; maintainers resolve them through normal
review.

The core code-review pass runs first. Sean, Tal, and Alex then run concurrently,
each with the core report and its validation evidence, a separate source
worktree, and separate Claude state. Specialists cannot read each other's
reports or state, or modify another checkout. Cargo's download cache is shared
within the fresh runner; adequate recorded validation can be reused instead of
running the same checks four times. Per-pass durations are recorded in the
receipt, with native token usage and cost in each Claude result artifact.

New commits need another `/ragu-audit` comment. A required check blocks an
unreviewed head without running a workflow. Completed checks do not update when
`main` advances; requiring up-to-date branches forces a new head and review.
GitHub can show skipped runs for other issue comments because comment-body
filtering happens at the job level. Those runs do not access either environment.

Review skills and policies come from the workflow's trusted `main` revision,
not the PR. Claude runs noninteractively with a required Bash sandbox, protected
controller/report paths, and an API key helper outside that sandbox. The model
job has no App key; publisher jobs never execute PR code. Required Rust
toolchains are installed before the model key is made available. Tests can
write scratch files and Cargo dependencies, but no caches are saved afterward.
The controller prepares the Cargo home, executable directory, and readable
configuration files before starting Claude; the protected paths stay unwritable
to review tools. Ordinary Cargo
commands use the fixed network allowlist; per-command domain arguments cannot
widen it. Claude's saved tool output lives separately from the credential
directory. Review tools can read that output but cannot modify CLI state.
Incomplete comments name unfinished passes and fixed diagnostics without
publishing model text, tool arguments, or stderr as the failure reason.

Trusted system instructions mark PR files, test output, and earlier reports as
untrusted evidence. Project hooks/MCP configuration do not load, skill shell
preprocessing is disabled, and shell commands cannot retry outside the sandbox.
Native tests deliberately attempt credential reads and report tampering after
reading injected instructions. These test containment with a fake API, not
Opus's resistance to misleading text. Review coverage and findings remain
model-reported and need human assessment.

A new command can cancel an older review on that PR; stale results cannot
publish. GitHub labels jobs that use an environment as deployments. Regression
tests run in the existing Workflow audit CI, without audit credentials or paid
model calls. Merge queues are not supported by this comment-only workflow.
A required check cannot substitute for human review or establish soundness.

Retire the separate `tachyon-zcash/ragu-audit` repository after this integration
lands and an authenticated comment-triggered review succeeds. This workflow
has no dependency on that repository.
