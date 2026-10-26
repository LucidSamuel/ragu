"""Exercise the internal API safety limit without publishing spend amounts."""

from decimal import Decimal
import json
import time
import unittest

import github
import findings
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

    def test_one_pool_can_be_spent_flexibly_across_all_roles(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        self.assertEqual(runner.MAX_RUN_COST_USD, Decimal("25"))
        budget = runner.RunBudget(run)
        budget.finish("code-review", {"total_cost_usd": 12})
        self.assertEqual(budget.remaining(), Decimal("13"))
        for role in runner.SKILLS[1:]:
            budget.finish(role, {"total_cost_usd": 1})
        budget.finish(runner.RECONCILER, {"total_cost_usd": 9})
        self.assertEqual(budget.remaining(), Decimal("1"))

    def test_reconciliation_uses_all_remaining_budget(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        budget = runner.RunBudget(run)
        for role, cost in zip(runner.SKILLS, (3.81, 3.26, 4.53, 3.70)):
            budget.finish(role, {"total_cost_usd": cost})
        self.assertEqual(budget.remaining(), Decimal("9.70"))

    def test_reused_reviews_do_not_consume_new_invocation_budget(self):
        fixture = self.fixture(test_reuse.ReuseTests)
        fixture.seed()
        phases, _ = reuse.restore(fixture.current, fixture.root, fixture.cached)
        self.assertEqual(len(phases), 4)
        self.assertEqual(runner.RunBudget(fixture.current).remaining(), Decimal("25"))

    def test_stream_usage_is_deduplicated_and_reconciled_with_native_cost(self):
        fixture = self.fixture()
        budget = runner.RunBudget(github.queue(fixture.api, 9))
        message = {"id": "m1", "model": "claude-opus-5-5", "usage": {
            "input_tokens": 1000000, "output_tokens": 100000, "cache_creation_input_tokens": 1000000,
            "cache_read_input_tokens": 1000000, "cache_creation": {"ephemeral_1h_input_tokens": 500000}}}
        budget.observe("code-review", {"type": "stream_event", "event": {"type": "message_start", "message": message}})
        budget.observe("code-review", {"type": "assistant", "message": message})
        budget.observe("code-review", {"type": "stream_event", "event": {"type": "message_delta", "usage": {"output_tokens": 100000}}})
        self.assertEqual(budget.remaining(), Decimal("12.30"))
        budget.finish("code-review", {"total_cost_usd": 12.7})
        self.assertEqual(budget.remaining(), Decimal("12.30"))
        budget.finish("code-review", {"total_cost_usd": 12.8})
        self.assertEqual(budget.remaining(), Decimal("12.20"))

    def test_concurrent_roles_charge_the_same_pool_and_stop_together(self):
        fixture = self.fixture()
        budget = runner.RunBudget(github.queue(fixture.api, 9))
        for role in runner.SKILLS[1:3]:
            budget.observe(role, {"type": "assistant", "message": {
                "id": "same-id-in-separate-processes", "model": "claude-opus-5-5", "usage": {"input_tokens": 2250000}}})
        with self.assertRaises(runner.SafetyLimit):
            budget.observe("alex-review", {"type": "assistant", "message": {
                "id": "m3", "model": "claude-opus-5-5", "usage": {"input_tokens": 2250000}}})
        for role in runner.ROLES:
            with self.assertRaises(runner.SafetyLimit):
                budget.check()

    def test_stream_estimate_matches_the_pinned_cli_reference_usage(self):
        fixture = self.fixture()
        budget = runner.RunBudget(github.queue(fixture.api, 9))
        budget.observe("code-review", {"type": "assistant", "message": {
            "id": "reference", "model": "claude-opus-5-5", "usage": {
                "input_tokens": 118, "output_tokens": 56902, "cache_creation_input_tokens": 221059,
                "cache_read_input_tokens": 7831331}}})
        self.assertEqual(budget.remaining(), Decimal("21.1899268"))
        budget.finish("code-review", {"total_cost_usd": 3.8100732})
        self.assertEqual(budget.remaining(), Decimal("21.1899268"))

    def test_final_report_at_budget_stop_is_retained_as_completed_evidence(self):
        fixture = self.fixture(test_runner.RunnerTests)

        def execute(command, **kwargs):
            result = fixture.result(command)
            result["total_cost_usd"] = 26
            result["structured_output"]["findings"] = [test_audit.candidate()]
            return result

        with self.assertRaisesRegex(runner.SafetyLimit, "safety limit"):
            fixture.invoke(execute)
        receipt = runner.verify(fixture.run, fixture.out, partial=True)
        self.assertEqual([phase["skill"] for phase in receipt["phases"]], ["code-review"])
        self.assertEqual(len(runner.candidates(fixture.run, fixture.out, partial=True)["findings"]), 1)

    def test_finished_reconciliation_at_the_limit_is_still_available(self):
        fixture = self.fixture(test_runner.RunnerTests)

        def execute(command, **kwargs):
            result = fixture.reconcile_result(command, **kwargs)
            if kwargs["skill"] == runner.RECONCILER:
                result["total_cost_usd"] = 25
            return result

        with self.assertRaisesRegex(runner.SafetyLimit, "safety limit"):
            fixture.invoke(execute)
        self.assertEqual(len(runner.verify_reconciliation(fixture.run, fixture.out)[1]), 1)

    def test_unsupported_pricing_fails_closed_before_further_requests(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        with self.assertRaises(ValueError):
            runner.RunBudget({**run, "model": "claude-unknown"})
        budget = runner.RunBudget(run)
        with self.assertRaises(runner.SafetyLimit):
            budget.observe("code-review", {"type": "assistant", "message": {
                "id": "m", "model": "claude-opus-5-5", "usage": {"input_tokens": -1}}})
        self.assertTrue(budget.stopped.is_set())

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
            self.assertEqual(command[command.index("--max-budget-usd") + 1], "25.00")
            return {"type": "result", "subtype": "error_max_budget_usd", "is_error": True,
                    "total_cost_usd": 6.25}

        with self.assertRaisesRegex(ValueError, "safety limit"):
            fixture.invoke(execute)
        self.assertEqual(calls, ["code-review"])

    def test_exhausted_reviewer_fails_gate_without_displaying_costs(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        outputs = {}
        for role in runner.SKILLS:
            result = native(f"Original {role} report.")
            result["structured_output"]["findings"] = [test_audit.candidate(
                title=f"Preserved {role} finding", cause=f"Distinct {role} cause")]
            outputs[role] = result
        receipt = fixture.reports(run, outputs)
        receipt["phases"] = [phase for phase in receipt["phases"] if phase["skill"] != "tal-review"]
        runner.write_json(fixture.out / "receipt.json", receipt)
        runner.write_json(fixture.out / "tal-review.json", {
            "type": "result", "subtype": "error_max_budget_usd", "is_error": True, "total_cost_usd": 6.25})
        with self.assertRaisesRegex(ValueError, "audit did not complete"):
            github.publish(fixture.api, run, fixture.out, "failure")
        body = fixture.api.comments[0]["body"]
        self.assertIn("3/4 reviews completed", body)
        self.assertIn("#### Must-fix (3)", body)
        for role in ("code-review", "sean-review", "alex-review"):
            self.assertIn(f"**Preserved {role} finding**", body)
            self.assertIn(f"<summary>{findings.REVIEWER_NAMES[role]}</summary>", body)
            self.assertIn(f"Original {role} report.", body)
        self.assertNotIn("Preserved tal-review finding", body)
        self.assertIn("the review reached its safety limit", body)
        self.assertNotIn("6.25", body)
        self.assertNotIn("25.00", body)
        self.assertNotIn("$", body)
        self.assertEqual(fixture.api.checks[0]["conclusion"], "failure")

    def test_invalid_or_exhausted_native_estimate_cannot_authorize_completion(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        for cost in (None, True, "1", -1, float("nan"), float("inf"), 10**400, 25, 25.25):
            with self.subTest(cost_type=type(cost).__name__):
                fixture.reports(run, {"tal-review": {**native(), "total_cost_usd": cost}})
                with self.assertRaises(ValueError):
                    runner.verify(run, fixture.out)
        fixture.reports(run, {"code-review": {**native(), "total_cost_usd": 12}})
        runner.verify(run, fixture.out)

    def test_final_reviewer_at_the_limit_still_publishes_findings_and_the_stop_reason(self):
        fixture = self.fixture()
        run = github.queue(fixture.api, 9)
        result = native("Original completed review.")
        result["structured_output"]["findings"] = [test_audit.candidate()]
        fixture.reports(run, {role: result for role in runner.SKILLS})
        runner.write_json(fixture.out / "alex-review.status.json", {
            "run": run, "skill": "alex-review", "state": "budget"})
        with self.assertRaisesRegex(ValueError, "audit did not complete"):
            github.publish(fixture.api, run, fixture.out, "failure")
        body = fixture.api.comments[0]["body"]
        self.assertIn("4/4 reviews completed", body)
        self.assertIn("invocation reached its safety limit", body)
        self.assertIn("**Incorrect result**", body)
        self.assertNotIn("$", body)

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
        with self.assertRaisesRegex(ValueError, "audit did not complete"):
            github.publish(fixture.api, run, fixture.out, "failure")
        body = fixture.api.comments[0]["body"]
        self.assertIn("4/4 reviews completed", body)
        self.assertIn("**Incorrect result**", body)
        self.assertNotIn("25.25", body)
        self.assertEqual(fixture.api.checks[0]["conclusion"], "failure")


if __name__ == "__main__":
    unittest.main()
