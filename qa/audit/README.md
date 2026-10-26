# Ragu audit

`/ragu-audit` runs Ragu's code-review skill, then the Sean, Tal, and Alex review
skills in parallel against the same PR revision, sharing the core report and
its validation evidence. These are complementary review
perspectives; checks follow the changes and relevant project policies.
CI owns formatting, linting, documentation builds, and routine test suites.
The bot runs focused tests only to investigate suspected bugs.

Post the exact command as a new PR comment with write access. Commits do not
trigger the bot. It updates one summary comment with each pass's findings and
links to the full reports.
Delete the command comment to stop its review.

Require `ragu-audit/completed` to gate merging on all four passes finishing.
After pushing new commits, post the command again. Completion records finished
passes, not approval.

The runner and skills live in this repository. [Setup](SETUP.md).
