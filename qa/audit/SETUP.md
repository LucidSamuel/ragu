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
4. Set `RAGU_AUDIT_ENABLED=true`, open or update a PR, and post `/ragu-audit` as
   a new PR conversation comment. The command requires live write, maintain, or
   admin permission; PR updates only queue a blocked check and spend no model
   tokens. Workflow dispatch is also available.
5. After a successful test run, require `ragu-audit/completed` on `main`, selecting
   this App as the expected publisher. Keep the existing CI and approval rules.

One App-owned comment contains the four reports; complete reports and native
Claude results are also retained as workflow artifacts for 30 days. Missing or
failed native runs, missing reports, modified source, and moved revisions fail
the completion check. Identical snapshots across PRs reuse the same check;
manual invocations retain their own PR comments. Findings do not automatically
block this completion check; maintainers resolve them through normal review.

Review skills and policies come from the workflow's trusted `main` revision,
not the PR. Claude runs noninteractively with a required Bash sandbox, protected
controller/report paths, and an API key helper outside that sandbox. The model
job has no App key; publisher jobs never execute PR code. Required Rust
toolchains are installed before the model key is made available. Tests can
write scratch files and Cargo dependencies, but no caches are saved afterward.

Trusted system instructions mark PR files, test output, and earlier reports as
untrusted evidence. Project hooks/MCP configuration do not load, skill shell
preprocessing is disabled, and shell commands cannot retry outside the sandbox.
Native tests deliberately attempt credential reads and report tampering after
reading injected instructions. These test containment with a fake API, not
Opus's resistance to misleading text. Review coverage and findings remain
model-reported and need human assessment.

Automatic events queue checks without cancelling model jobs. A new manual
invocation can cancel an older review on that PR; stale results cannot publish.
The workflow queues fresh checks for open PRs when `main` moves. Merge queues
are not configured here; add and validate `merge_group` handling before enabling
one. A required check cannot substitute for human review or establish soundness.

Retire the separate `tachyon-zcash/ragu-audit` repository after this integration
lands and an authenticated comment-triggered review succeeds. This workflow
has no dependency on that repository.
