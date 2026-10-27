# Ragu audit

`/ragu-audit` runs Ragu's code-review skill, then the Sean, Tal, and Alex review
skills in parallel against the same PR revision, sharing the core report and
its validation evidence. These are complementary review
perspectives; checks follow the changes and relevant project policies.
CI owns formatting, linting, documentation builds, and routine test suites.
The bot runs focused tests only to investigate suspected bugs.

Post the exact command as a new PR comment with write access. Commits do not
trigger the bot. The bot posts merged **Must-fix** findings and **Suggestions**
as inline review comments, with evidence and reviewer attribution. A short
source-checking pass refines the findings; if it cannot finish, verified
reviewer findings are still published. One status comment links to the inline
reviews and preserves the collapsed original reports. Findings with no cited
line in the diff remain in that comment.
Delete the original command comment to stop its review.

Identical reviews reuse verified results; retries resume unfinished passes.
All four reviewers and reconciliation use Sonnet 5.5 at high effort.
An internal spending limit stops runaway reviews.

Require `ragu-audit/completed` to gate merging on all four passes finishing.
After pushing new commits, post the command again. Completion records finished
passes, not approval.

The runner and skills live in this repository. [Setup](SETUP.md).
