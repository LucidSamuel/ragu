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

    def test_serialized_queue_rechecks_commands_authorized_before_either_started(self):
        self.api.checks.clear()
        # Both request jobs finish before the first serialized queue job starts.
        with patch.dict(os.environ, {"GITHUB_RUN_ID": str(self.old["run_id"])}):
            self.assertEqual(github.request(self.api, self.fixture.event(), "issue_comment"), (9, self.old["head"]))
        with patch.dict(os.environ, {"GITHUB_RUN_ID": str(self.current["run_id"])}):
            self.assertEqual(github.request(self.api, self.fixture.event(), "issue_comment"), (9, self.current["head"]))
        with patch.dict(os.environ, {"GITHUB_RUN_ID": str(self.old["run_id"])}):
            first = github.queue(self.api, 9, comment_id=12)
        self.api.source(first, status="in_progress", conclusion=None)
        mutations = len(self.api.mutations)
        output = self.root / "outputs"
        with patch.dict(os.environ, {"GITHUB_RUN_ID": str(self.current["run_id"]), "GITHUB_OUTPUT": str(output)}), \
             patch.object(github, "GitHub", return_value=self.api), \
             patch("sys.argv", ["github.py", "queue", "--pr", "9", "--head", first["head"],
                                "--comment-id", "12", "--run", str(self.root / "run.json")]):
            github.main()
        self.assertEqual(len(self.api.mutations), mutations)
        self.assertEqual(len(self.api.checks), 1)
        self.assertFalse(output.exists(), "coalesced command must not start review or publication jobs")
        self.assertFalse((self.root / "run.json").exists())

    def test_deleted_workflows_and_unscoped_checks_do_not_block_a_fresh_request(self):
        self.api.checks = self.api.checks[:1]
        self.api.checks[0].update(status="in_progress")
        call = self.api.call

        def deleted(path, *args, **kwargs):
            if path.endswith(f"/actions/runs/{self.old['run_id']}"):
                raise HTTPError(path, 404, "Not Found", {}, None)
            return call(path, *args, **kwargs)

        with patch.object(self.api, "call", side_effect=deleted):
            self.assertIsNone(reuse.active(self.api, self.current))
            self.assertEqual(reuse.plan(self.api, self.current)["artifact_ids"], [])
            self.assertEqual(github.request(self.api, self.fixture.event(), "issue_comment"), (9, self.current["head"]))
        self.api.checks[0]["external_id"] = None
        self.assertIsNone(reuse.active(self.api, self.current))
        self.assertEqual(reuse.plan(self.api, self.current)["artifact_ids"], [])

    def test_deleted_artifact_listing_does_not_prevent_fallback_to_an_older_run(self):
        older = copy.deepcopy(self.old)
        older["run_id"] -= 1
        older["check_id"] -= 1
        self.api.source(older)
        self.api.artifacts[older["run_id"]][0]["id"] = 122
        check = copy.deepcopy(self.api.checks[0])
        check.update(id=older["check_id"], external_id=github.scope(older) + f"9:{older['run_id']}:1")
        self.api.checks.append(check)
        pages = self.api.pages

        def deleted(path, key=None):
            if path.endswith(f"/actions/runs/{self.old['run_id']}/artifacts"):
                raise HTTPError(path, 410, "Gone", {}, None)
            return pages(path, key)

        with patch.object(self.api, "pages", side_effect=deleted):
            selection = reuse.plan(self.api, self.current)
        self.assertEqual(selection["artifact_ids"], [122])
        self.assertEqual(selection["source"]["run_id"], older["run_id"])

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

    def test_unsafe_specialist_files_do_not_discard_verified_siblings(self):
        for kind in ("symlink", "oversized", "directory"):
            with self.subTest(kind=kind):
                self.seed()
                path = self.cached / "tal-review.json"
                path.unlink()
                if kind == "symlink":
                    path.symlink_to(self.cached / "sean-review.json")
                elif kind == "oversized":
                    with path.open("wb") as stream:
                        stream.truncate(9 * 1024 * 1024 + 1)
                else:
                    path.mkdir()
                try:
                    phases, reconciled = reuse.restore(self.current, self.root, self.cached)
                    self.assertEqual([item["skill"] for item in phases], ["code-review", "sean-review", "alex-review"])
                    self.assertFalse(reconciled)
                    self.assertEqual(len(runner.verify(self.current, self.root, partial=True)["phases"]), 3)
                finally:
                    path.rmdir() if kind == "directory" else path.unlink()

    def test_unsafe_optional_reconciliation_does_not_discard_completed_reviews(self):
        self.seed(findings_present=True, reconciled=True)
        (self.cached / "reconcile.json").unlink()
        (self.cached / "reconcile.json").symlink_to(self.cached / "code-review.json")
        phases, reconciled = reuse.restore(self.current, self.root, self.cached)
        self.assertEqual(len(phases), 4)
        self.assertFalse(reconciled)
        self.assertEqual(len(runner.verify(self.current, self.root)["phases"]), 4)

    def test_output_write_failure_does_not_start_fresh_work_over_partial_restoration(self):
        self.seed()
        write = runner.write_json

        def fail_receipt(path, value):
            if path == self.root / "receipt.json":
                raise OSError("disk unavailable")
            return write(path, value)

        with patch.object(runner, "write_json", side_effect=fail_receipt), self.assertRaises(OSError):
            reuse.restore(self.current, self.root, self.cached)

    def test_unavailable_cache_or_symlinked_directory_never_authorizes_reuse(self):
        self.assertEqual(reuse.restore(self.current, self.root, self.base / "absent/reports"), ([], False))
        self.seed()
        link = self.base / "reports-link"
        link.symlink_to(self.cached, target_is_directory=True)
        self.assertEqual(reuse.restore(self.current, self.root, link), ([], False))

    def test_complete_reports_and_reconciliation_can_be_reused_without_model_calls(self):
        self.seed(findings_present=True, reconciled=True)
        phases, reconciled = reuse.restore(self.current, self.root, self.cached)
        self.assertEqual(len(phases), 4)
        self.assertTrue(reconciled)
        self.assertEqual(len(runner.verify_reconciliation(self.current, self.root)[1]), 1)
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

    def test_pr_comment_never_promotes_native_costs_into_the_summary(self):
        self.seed()
        result = native("Original source review.")
        result["total_cost_usd"] = 3.21
        self.fixture.reports(self.old, {role: result for role in runner.SKILLS})
        text = github.summary(self.old, "completed", self.cached)
        self.assertNotIn("3.21", text)
        self.assertNotIn("Estimated API cost", text)
        self.assertNotIn("Known estimated spend", text)
        self.assertEqual(runner.read_json(self.cached / "code-review.json")["total_cost_usd"], 3.21)

    def test_corrupt_failed_session_cannot_break_publication(self):
        receipt = self.seed(missing=("tal-review",))
        runner.write_json(self.cached / "tal-review.status.json", {"run": self.old, "skill": "tal-review", "state": "protocol"})
        runner.write_json(self.cached / "tal-review.json", [])
        text = github.summary(self.old, "incomplete", self.cached)
        self.assertIn("3/4 reviews completed", text)
        self.assertNotIn("### Usage", text)
        self.assertEqual(len(receipt["phases"]), 3)


if __name__ == "__main__":
    unittest.main()
