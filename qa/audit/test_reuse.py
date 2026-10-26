"""Exercise trusted provenance, partial recovery, and duplicate suppression."""

import copy
import json
import os
import unittest
from unittest.mock import patch
from urllib.error import HTTPError

import findings
import github
import reuse
import runner
from test_audit import API, native, candidate
import test_audit
import test_runner
from test_findings import group


class ReuseAPI(API):
    def __init__(self):
        super().__init__()
        self.runs, self.artifacts = {}, {}

    def call(self, path, data=None, method=None):
        if data is None and "/actions/runs/" in path:
            return copy.deepcopy(self.runs[int(path.rsplit("/", 1)[-1])])
        return super().call(path, data, method)

    def pages(self, path, key=None):
        if path.endswith("/artifacts"):
            return iter(copy.deepcopy(self.artifacts.get(int(path.split("/")[-2]), [])))
        return super().pages(path, key)

    def source(self, run, *, status="completed", conclusion="success"):
        self.runs[run["run_id"]] = {
            "id": run["run_id"], "run_attempt": run["attempt"], "status": status, "conclusion": conclusion,
            "event": "issue_comment", "head_branch": "main", "head_sha": run["configuration"],
            "path": ".github/workflows/audit.yml", "repository": {"full_name": github.REPOSITORY},
            "head_repository": {"full_name": github.REPOSITORY},
        }
        self.artifacts[run["run_id"]] = [{"id": 123, "name": f"ragu-audit-reports-{run['run_id']}-{run['attempt']}", "expired": False}]


class ReuseTests(unittest.TestCase):
    def setUp(self):
        self.fixture = test_audit.AuditTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.api = ReuseAPI()
        self.old = github.queue(self.api, 9, comment_id=12)
        self.api.source(self.old)
        self.api.checks[0].update(status="completed", conclusion="success")
        self.base = self.fixture.out
        self.cached = self.base / "cache"
        self.cached.mkdir()
        self.fixture.out = self.cached
        with patch.dict(os.environ, {"GITHUB_RUN_ID": str(self.old["run_id"] + 1)}):
            self.current = github.queue(self.api, 9, comment_id=12)
        self.root = self.base / "new"
        self.root.mkdir()

    def seed(self, *, findings_present=False, missing=(), reconciled=False):
        outputs = None
        if findings_present:
            result = native("Original prose review.")
            result["structured_output"]["findings"] = [candidate()]
            outputs = {role: copy.deepcopy(result) for role in runner.SKILLS}
        receipt = self.fixture.reports(self.old, outputs)
        if missing:
            receipt["phases"] = [item for item in receipt["phases"] if item["skill"] not in missing]
            runner.write_json(self.cached / "receipt.json", receipt)
        if reconciled:
            if findings_present:
                self.fixture.reconciliation(self.old, [group(*[f"{role}:1" for role in runner.SKILLS])])
            else:
                bundle = runner.candidates(self.old, self.cached)
                runner.write_json(self.cached / "findings.json", bundle)
                runner.write_json(self.cached / "reconciliation-receipt.json", {
                    "run": self.old, "state": "empty", "input_sha256": findings.fingerprint(bundle)})
        runner.write_json(self.cached.parent / "reuse-plan.json", {
            "current": self.current, "source": {key: self.old[key] for key in ("run_id", "attempt", "check_id", "pr")}})
        runner.write_json(self.root / "receipt.json", {
            "run": self.current, "claude_version": runner.CLAUDE_VERSION, "phases": []})
        return receipt

    def test_plan_uses_only_exact_app_checks_and_trusted_workflow_artifacts(self):
        selection = reuse.plan(self.api, self.current)
        self.assertEqual(selection["artifact_ids"], [123])
        self.assertEqual(selection["source"]["run_id"], self.old["run_id"])
        for field, value in (("path", ".github/workflows/zizmor.yml"), ("head_sha", "c" * 40),
                             ("head_branch", "attacker"), ("event", "pull_request"), ("run_attempt", 0),
                             ("head_repository", {"full_name": "attacker/ragu"})):
            with self.subTest(field=field):
                metadata = copy.deepcopy(self.api.runs[self.old["run_id"]])
                self.api.runs[self.old["run_id"]][field] = value
                self.assertEqual(reuse.plan(self.api, self.current)["artifact_ids"], [])
                self.api.runs[self.old["run_id"]] = metadata
        self.api.artifacts[self.old["run_id"]][0]["expired"] = True
        self.assertEqual(reuse.plan(self.api, self.current)["artifact_ids"], [])

    def test_active_duplicate_keeps_the_running_check_after_authorization(self):
        self.api.checks = self.api.checks[:1]
        self.api.checks[0].update(status="in_progress")
        self.api.source(self.old, status="in_progress", conclusion=None)
        mutations = len(self.api.mutations)
        with patch.dict(os.environ, {"GITHUB_RUN_ID": str(self.current["run_id"])}):
            self.assertIsNone(github.request(self.api, self.fixture.event(), "issue_comment"))
        self.assertEqual(len(self.api.mutations), mutations)
        self.api.comment = None
        with self.assertRaises(HTTPError):
            github.request(self.api, self.fixture.event(), "issue_comment")
        self.assertIsNone(reuse.active(self.api, self.current))

    def test_same_workflow_retry_can_recover_an_earlier_attempt(self):
        self.seed(missing=("tal-review",))
        retry = {**self.current, "run_id": self.old["run_id"], "attempt": 2}
        self.api.runs[self.old["run_id"]].update(run_attempt=2, status="in_progress", conclusion=None)
        self.api.checks = self.api.checks[:1]
        self.api.checks[0]["status"] = "in_progress"  # The older check may be stranded.
        self.assertIsNone(reuse.active(self.api, retry))
        selection = reuse.plan(self.api, retry)
        self.assertEqual(selection["source"]["attempt"], 1)
        self.assertEqual(selection["artifact_ids"], [123])
        runner.write_json(self.cached.parent / "reuse-plan.json", selection)
        runner.write_json(self.root / "receipt.json", {
            "run": retry, "claude_version": runner.CLAUDE_VERSION, "phases": []})
        self.assertEqual(len(reuse.restore(retry, self.root, self.cached)[0]), 3)

    def test_inactive_or_foreign_configuration_does_not_suppress_new_review(self):
        self.api.checks = self.api.checks[:1]
        self.api.checks[0].update(status="in_progress")
        # A stranded in-progress check from a finished workflow is not a live run.
        self.assertIsNone(reuse.active(self.api, self.current))
        self.api.source(self.old, status="in_progress", conclusion=None)
        for key, value in (("head", "c" * 40), ("base", "c" * 40), ("configuration", "c" * 40),
                           ("model", "claude-sonnet-5-5"), ("effort", "high"),
                           ("reconcile_model", "claude-opus-5-5"), ("reconcile_effort", "high")):
            with self.subTest(key=key):
                self.assertIsNone(reuse.active(self.api, {**self.current, key: value}))

    def test_recover_partial_reviews_and_bind_specialists_to_the_original_core(self):
        self.seed(missing=("tal-review",))
        phases, reconciled = reuse.restore(self.current, self.root, self.cached)
        self.assertFalse(reconciled)
        self.assertEqual([item["skill"] for item in phases], ["code-review", "sean-review", "alex-review"])
        self.assertEqual(len(runner.verify(self.current, self.root, partial=True)["phases"]), 3)
        for item in phases:
            self.assertEqual(item["reused_from"], runner.reuse_origin(self.old))
        (self.root / "code-review.md").write_text("Different core evidence")
        with self.assertRaises(ValueError):
            runner.verify(self.current, self.root)

    def test_changed_snapshot_settings_plan_or_core_are_never_reused(self):
        for key, value in (("head", "c" * 40), ("base", "c" * 40), ("configuration", "c" * 40),
                           ("model", "claude-sonnet-5-5"), ("effort", "high"),
                           ("reconcile_model", "claude-opus-5-5"), ("reconcile_effort", "high")):
            with self.subTest(key=key):
                self.seed()
                changed = {**self.current, key: value}
                self.assertEqual(reuse.restore(changed, self.root, self.cached), ([], False))
        self.seed()
        (self.cached / "code-review.md").write_text("UNVERIFIED_CACHE_CANARY")
        self.assertEqual(reuse.restore(self.current, self.root, self.cached), ([], False))
        self.assertNotIn("UNVERIFIED_CACHE_CANARY", (self.root / "receipt.json").read_text())

    def test_damaged_specialist_does_not_discard_verified_siblings(self):
        self.seed()
        (self.cached / "tal-review.json").unlink()
        phases, reconciled = reuse.restore(self.current, self.root, self.cached)
        self.assertEqual(len(phases), 3)
        self.assertFalse(reconciled)
        self.assertNotIn("tal-review", [phase["skill"] for phase in phases])

    def test_complete_reports_and_reconciliation_can_be_reused_without_model_calls(self):
        self.seed(findings_present=True, reconciled=True)
        phases, reconciled = reuse.restore(self.current, self.root, self.cached)
        self.assertEqual(len(phases), 4)
        self.assertTrue(reconciled)
        self.assertEqual(len(runner.verify_reconciliation(self.current, self.root)[1]), 1)
        usage = "\n".join(github.usage_details(self.current, self.root))
        self.assertEqual(usage.count("([reused]"), 5)
        self.assertIn("$0.00", usage)
        (self.root / "reuse-receipt.json").write_text("{}")
        with self.assertRaises((KeyError, ValueError)):
            runner.verify(self.current, self.root)

    def test_reusing_zero_findings_needs_no_reconciliation_call(self):
        self.seed(reconciled=True)
        _, reconciled = reuse.restore(self.current, self.root, self.cached)
        self.assertTrue(reconciled)
        self.assertEqual(runner.verify_reconciliation(self.current, self.root)[1], [])

    def test_scheduler_reruns_only_the_missing_specialist(self):
        self.seed(missing=("tal-review",))
        fixture = test_runner.RunnerTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.run = self.current
        calls = []

        def execute(command, **kwargs):
            calls.append(kwargs["skill"])
            return fixture.result(command)

        with patch.object(runner, "comment_exists", return_value=True):
            fixture.invoke(execute, reuse=self.cached)
        self.assertEqual(calls, ["tal-review"])
        self.assertEqual(len(runner.verify(self.current, fixture.out)["phases"]), 4)

    def test_scheduler_makes_no_model_calls_for_a_completed_identical_review(self):
        self.seed(findings_present=True, reconciled=True)
        fixture = test_runner.RunnerTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.run = self.current
        with patch.object(runner, "comment_exists", return_value=True):
            fixture.invoke(lambda *args, **kwargs: self.fail("reused review invoked a paid session"), reuse=self.cached)
        self.assertEqual(len(runner.verify_reconciliation(self.current, fixture.out)[1]), 1)

    def test_costs_tokens_and_duration_are_shown_without_untrusted_text(self):
        self.seed()
        result = native()
        result.update(total_cost_usd=3.81, duration_ms=571399,
                      usage={"input_tokens": 118, "cache_creation_input_tokens": 221059,
                             "cache_read_input_tokens": 7831331, "output_tokens": 56902})
        self.fixture.reports(self.old, {"code-review": result})
        text = "\n".join(github.usage_details(self.old, self.cached))
        self.assertIn("$3.81", text)
        self.assertIn("221,177 / 7,831,331 / 56,902", text)
        self.assertIn("571s", text)
        result.update(total_cost_usd=float("nan"), usage={"output_tokens": "SECRET_CANARY"})
        self.fixture.reports(self.old, {"code-review": result})
        self.assertNotIn("SECRET_CANARY", "\n".join(github.usage_details(self.old, self.cached)))

    def test_corrupt_failed_session_usage_cannot_break_publication(self):
        receipt = self.seed(missing=("tal-review",))
        runner.write_json(self.cached / "tal-review.status.json", {"run": self.old, "skill": "tal-review", "state": "protocol"})
        runner.write_json(self.cached / "tal-review.json", [])
        text = github.summary(self.old, "incomplete", self.cached)
        self.assertIn("3/4 reviews completed", text)
        self.assertIn("### Usage", text)
        self.assertEqual(len(receipt["phases"]), 3)


if __name__ == "__main__":
    unittest.main()
