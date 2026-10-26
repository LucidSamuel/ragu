"""Check evaluation isolation and cost-stop behavior without paid requests."""

from decimal import Decimal
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import compare_effort
import runner
from test_audit import BASE, HEAD, ENV, native


class EffortTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        root = Path(self.directory.name)
        self.root, self.private, self.work, self.out = [root / name for name in ("root", "private", "work", "out")]
        self.env = patch.dict(os.environ, ENV)
        self.env.start()
        self.addCleanup(self.env.stop)

    def compare(self, execute):
        with patch.object(runner, "review", side_effect=execute), \
             patch.object(runner, "verify", return_value={"phases": [{"skill": "code-review"}]}):
            compare_effort.compare(self.root, self.private, self.work, self.out, HEAD, BASE, Decimal("10"))

    def test_pair_has_identical_snapshot_and_only_remaining_budget(self):
        requests = []

        def execute(root, run, work, out, private, **kwargs):
            self.assertTrue(kwargs["core_only"])
            self.assertEqual((run["head"], run["base"], run["configuration"]), (HEAD, BASE, BASE))
            self.assertEqual(run["model"], ENV["RAGU_AUDIT_MODEL"])
            requests.append(run)
            out.mkdir(parents=True)
            runner.write_json(out / "code-review.json", {**native(), "total_cost_usd": 2.5})

        self.compare(execute)
        self.assertEqual([item["effort"] for item in requests], ["high", "xhigh"])
        self.assertEqual([Decimal(item["evaluation_budget_usd"]) for item in requests], [Decimal("10"), Decimal("7.5")])
        self.assertIn("$2.50", (self.out / "comparison.md").read_text())
        self.assertEqual(os.environ["RAGU_AUDIT_EFFORT"], "xhigh")

    def test_missing_usage_or_exhaustion_never_starts_another_paid_session(self):
        requests = []

        def execute(root, run, work, out, private, **kwargs):
            requests.append(run)
            out.mkdir(parents=True)
            runner.write_json(out / "code-review.json", native())

        with self.assertRaisesRegex(ValueError, "comparison incomplete"):
            self.compare(execute)
        self.assertEqual(len(requests), 1)
        self.assertTrue((self.out / "comparison.md").is_file())

    def test_invalid_or_unbounded_evaluation_budget_is_rejected(self):
        for value in ("0", "-1", "NaN", "Infinity", "26", "not a number"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                compare_effort.budget(value)

    def test_production_sessions_cannot_silently_enable_evaluation_budget(self):
        run = {"model": "claude-opus-5-5", "effort": "xhigh", "evaluation_budget_usd": "10"}
        with self.assertRaisesRegex(ValueError, "evaluation budget"):
            runner.command("code-review", "claude", self.root, run, self.work, self.out, self.private,
                           self.root / "plugin", self.root / "scratch", "Review source.", runner.SCHEMA, runner.TOOLS)


if __name__ == "__main__":
    unittest.main()
