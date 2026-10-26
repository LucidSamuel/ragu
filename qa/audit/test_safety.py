"""Exercise the internal API safety limit without publishing spend amounts."""

from decimal import Decimal
import json
import time
import unittest

import github
import reuse
import runner
from test_audit import native
from test_findings import group
import test_audit
import test_reuse
import test_runner


class SafetyTests(unittest.TestCase):
    def fixture(self, kind=test_audit.AuditTests):
        fixture = kind()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        return fixture

    def test_parallel_reviews_cannot_each_spend_the_whole_run_limit(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        self.assertEqual(runner.MAX_RUN_COST_USD, Decimal("25"))
        budgets = [runner.phase_budget(run, role, fixture.out) for role in runner.SKILLS]
        self.assertEqual(budgets, [Decimal("6")] * 4)
        self.assertLess(sum(budgets), runner.MAX_RUN_COST_USD)

    def test_reconciliation_uses_all_remaining_budget(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        outputs = {role: {**native(), "total_cost_usd": cost}
                   for role, cost in zip(runner.SKILLS, (3.81, 3.26, 4.53, 3.70))}
        fixture.reports(run, outputs)
        self.assertEqual(runner.phase_budget(run, runner.RECONCILER, fixture.out), Decimal("9.70"))

    def test_reused_reviews_do_not_consume_new_invocation_budget(self):
        fixture = self.fixture(test_reuse.ReuseTests)
        fixture.seed()
        phases, _ = reuse.restore(fixture.current, fixture.root, fixture.cached)
        self.assertEqual(len(phases), 4)
        self.assertEqual(runner.phase_budget(fixture.current, runner.RECONCILER, fixture.root), Decimal("25"))

    def test_budget_result_immediately_stops_the_process(self):
        fixture = self.fixture(test_runner.ProcessTests)
        result = {"type": "result", "subtype": "error_max_budget_usd", "is_error": True,
                  "total_cost_usd": 6.25}
        script = f"import time; print({json.dumps(result)!r}, flush=True); time.sleep(10)"
        started = time.monotonic()
        with self.assertRaisesRegex(ValueError, "safety limit"):
            fixture.execute(script, timeout=3)
        self.assertLess(time.monotonic() - started, 2)
        self.assertEqual(runner.read_json(fixture.out / "code-review.status.json")["state"], "budget")

    def test_core_exhaustion_never_starts_specialists(self):
        fixture = self.fixture(test_runner.RunnerTests)
        calls = []

        def execute(command, **kwargs):
            calls.append(kwargs["skill"])
            self.assertEqual(command[command.index("--max-budget-usd") + 1], "6.0000")
            return {"type": "result", "subtype": "error_max_budget_usd", "is_error": True,
                    "total_cost_usd": 6.25}

        with self.assertRaisesRegex(ValueError, "safety limit"):
            fixture.invoke(execute)
        self.assertEqual(calls, ["code-review"])

    def test_exhausted_reviewer_fails_gate_without_displaying_costs(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        receipt = fixture.reports(run)
        receipt["phases"] = [phase for phase in receipt["phases"] if phase["skill"] != "tal-review"]
        runner.write_json(fixture.out / "receipt.json", receipt)
        runner.write_json(fixture.out / "tal-review.json", {
            "type": "result", "subtype": "error_max_budget_usd", "is_error": True, "total_cost_usd": 6.25})
        with self.assertRaisesRegex(ValueError, "audit did not complete"):
            github.publish(fixture.api, run, fixture.out, "failure")
        body = fixture.api.comments[0]["body"]
        self.assertIn("3/4 reviews completed", body)
        self.assertIn("the review reached its safety limit", body)
        self.assertNotIn("6.25", body)
        self.assertNotIn("25.00", body)
        self.assertNotIn("$", body)
        self.assertEqual(fixture.api.checks[0]["conclusion"], "failure")

    def test_invalid_or_exhausted_native_estimate_cannot_authorize_completion(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        for cost in (None, True, "1", -1, float("nan"), float("inf"), 10**400, 6, 6.25):
            with self.subTest(cost_type=type(cost).__name__):
                fixture.reports(run, {"tal-review": {**native(), "total_cost_usd": cost}})
                with self.assertRaises(ValueError):
                    runner.verify(run, fixture.out)

    def test_reconciliation_safety_limit_keeps_verified_reports_and_summary(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        result = native("Original review.")
        result["structured_output"]["findings"] = [test_audit.candidate()]
        fixture.reports(run, {role: result for role in runner.SKILLS})
        fixture.reconciliation(run, [group(*[f"{role}:1" for role in runner.SKILLS])])
        result = runner.read_json(fixture.out / "reconcile.json")
        result.update(subtype="error_max_budget_usd", is_error=True, total_cost_usd=25.25)
        runner.write_json(fixture.out / "reconcile.json", result)
        record = runner.read_json(fixture.out / "reconciliation-receipt.json")
        record["result_sha256"] = runner.digest(fixture.out / "reconcile.json")
        runner.write_json(fixture.out / "reconciliation-receipt.json", record)
        github.publish(fixture.api, run, fixture.out, "success")
        body = fixture.api.comments[0]["body"]
        self.assertIn("4/4 reviews completed", body)
        self.assertIn("**Incorrect result**", body)
        self.assertNotIn("25.25", body)
        self.assertEqual(fixture.api.checks[0]["conclusion"], "success")


if __name__ == "__main__":
    unittest.main()
