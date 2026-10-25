"""Exercise review scheduling and failure handling without model calls."""

from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch

import runner


class RunnerTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        base = Path(directory.name).resolve()
        self.root, self.work, self.out, self.private = [base / name for name in ("root", "work", "out", "private")]
        self.root.mkdir()
        self.run = {"head": "a" * 40, "base": "b" * 40, "configuration": "b" * 40,
                    "model": "claude-opus-5-5", "effort": "xhigh"}
        for skill in runner.SKILLS:
            path = self.root / ".claude/skills" / skill
            path.mkdir(parents=True)
            (path / "SKILL.md").write_text("Trusted skill\n")

    def prepare(self, *args):
        for skill in runner.SKILLS:
            (self.work / skill).mkdir()
        return self.run["base"]

    def invoke(self, execute, changed_skill=None):
        def git(source, command, *args):
            if command == "rev-parse":
                return self.run["head"]
            self.assertEqual(command, "diff")
            return "tracked source was modified" if source.name == changed_skill else ""

        with patch.dict(os.environ, {"PATH": os.environ["PATH"], "HOME": str(self.root), "CARGO_HOME": str(self.work / "cargo"),
                                     "GH_TOKEN": "dummy-parent-token"}, clear=True), \
             patch.object(runner.shutil, "which", return_value=sys.executable), \
             patch.object(runner.subprocess, "check_output", return_value=runner.CLAUDE_VERSION + " (Claude Code)\n"), \
             patch.object(runner, "prepare", side_effect=self.prepare), patch.object(runner, "git", side_effect=git), \
             patch.object(runner.subprocess, "run", side_effect=execute):
            runner.review(self.root, self.run, self.work, self.out, self.private)

    def result(self, command, complete=True, returncode=0):
        return subprocess.CompletedProcess(command, returncode, json.dumps({
            "type": "result", "subtype": "success", "is_error": False, "permission_denials": [],
            "structured_output": {"complete": complete, "report": "Recorded review and validation evidence."},
        }), "")

    def test_specialists_overlap_after_core_and_receipt_order_is_deterministic(self):
        specialists = threading.Barrier(3)
        release = threading.Event()
        snapshots, states = [], {}
        write_json = runner.write_json

        def record(path, value):
            write_json(path, value)
            if path.name == "receipt.json":
                names = [phase["skill"] for phase in value["phases"]]
                snapshots.append(names)
                if names == ["code-review", "alex-review"]:
                    release.set()

        def execute(command, **kwargs):
            env = kwargs["env"]
            skill = Path(env["CLAUDE_CONFIG_DIR"]).name
            states[skill] = env["CLAUDE_CONFIG_DIR"]
            # Linux cannot hide a read-denied file that does not exist when a
            # Bash sandbox starts, including reports a peer will write later.
            self.assertTrue(all((self.out / f"{name}.{suffix}").is_file()
                                for name in runner.SKILLS for suffix in ("md", "json", "stderr")))
            self.assertEqual(env["TMPDIR"], env["CLAUDE_CODE_TMPDIR"])
            self.assertEqual(Path(env["TMPDIR"]).name, skill)
            self.assertLess(len(str(Path(env["TMPDIR"]) / f"claude-{os.getuid()}")), 60)
            self.assertTrue(Path(env["TMPDIR"]).is_dir())
            self.assertEqual(command[command.index("--model") + 1], self.run["model"])
            self.assertEqual(command[command.index("--effort") + 1], "xhigh")
            self.assertNotIn("GH_TOKEN", env)
            self.assertNotIn("ANTHROPIC_API_KEY", env)
            previous = command[-1].split("Previous pass reports: ")[1].split(". Challenge")[0]
            if skill == "code-review":
                self.assertEqual(previous, "none")
            else:
                self.assertEqual(previous, str(self.out / "code-review.md"))
                self.assertIn("Recorded review and validation evidence", (self.out / "code-review.md").read_text())
                specialists.wait(timeout=5)
                if skill != "alex-review":
                    self.assertTrue(release.wait(timeout=5), "early specialist result was not recorded")
            return self.result(command)

        with patch.object(runner, "write_json", side_effect=record):
            self.invoke(execute)
        receipt = runner.verify(self.run, self.out)
        self.assertIn(["code-review", "alex-review"], snapshots)
        self.assertEqual([phase["skill"] for phase in receipt["phases"]], list(runner.SKILLS))
        self.assertEqual(len(set(states.values())), 4)
        self.assertTrue(all(phase["duration_seconds"] >= 0 for phase in receipt["phases"]))

    def test_incomplete_core_never_starts_specialists(self):
        calls = []

        def execute(command, **kwargs):
            calls.append(Path(kwargs["env"]["CLAUDE_CONFIG_DIR"]).name)
            return self.result(command, complete=False)

        with self.assertRaisesRegex(ValueError, "code-review: review incomplete"):
            self.invoke(execute)
        self.assertEqual(calls, ["code-review"])
        self.assertEqual(runner.read_json(self.out / "receipt.json")["phases"], [])
        with self.assertRaises(ValueError):
            runner.verify(self.run, self.out)

    def test_failed_specialist_preserves_siblings_and_cannot_pass_gate(self):
        specialists = threading.Barrier(3)

        def execute(command, **kwargs):
            skill = Path(kwargs["env"]["CLAUDE_CONFIG_DIR"]).name
            if skill != "code-review":
                specialists.wait(timeout=5)
            return self.result(command, complete=skill != "tal-review")

        with self.assertRaisesRegex(ValueError, "review incomplete: tal-review"):
            self.invoke(execute)
        phases = runner.read_json(self.out / "receipt.json")["phases"]
        self.assertEqual([phase["skill"] for phase in phases], ["code-review", "sean-review", "alex-review"])
        self.assertTrue(all((self.out / f"{skill}.json").is_file() for skill in runner.SKILLS))
        with self.assertRaises(ValueError):
            runner.verify(self.run, self.out)

    def test_timeout_preserves_siblings_without_logging_command_text(self):
        def execute(command, **kwargs):
            if Path(kwargs["env"]["CLAUDE_CONFIG_DIR"]).name == "sean-review":
                raise subprocess.TimeoutExpired("UNTRUSTED_COMMAND_CANARY", 3300)
            return self.result(command)

        output = io.StringIO()
        with redirect_stdout(output), self.assertRaisesRegex(ValueError, "review incomplete: sean-review"):
            self.invoke(execute)
        self.assertNotIn("UNTRUSTED_COMMAND_CANARY", output.getvalue())
        phases = runner.read_json(self.out / "receipt.json")["phases"]
        self.assertEqual([phase["skill"] for phase in phases], ["code-review", "tal-review", "alex-review"])
        with self.assertRaises(ValueError):
            runner.verify(self.run, self.out)

    def test_modified_specialist_source_cannot_pass_gate(self):
        with self.assertRaisesRegex(ValueError, "review incomplete: sean-review"):
            self.invoke(lambda command, **kwargs: self.result(command), changed_skill="sean-review")
        phases = runner.read_json(self.out / "receipt.json")["phases"]
        self.assertEqual([phase["skill"] for phase in phases], ["code-review", "tal-review", "alex-review"])
        with self.assertRaises(ValueError):
            runner.verify(self.run, self.out)

    def test_peer_state_reports_and_worktrees_are_protected(self):
        for skill in runner.SKILLS:
            source = self.work / skill
            scratch = self.work / "scratch"
            settings = runner.settings(self.root, source, self.work, self.out, self.private, self.work / "trusted-plugin", scratch)
            filesystem = settings["sandbox"]["filesystem"]
            self.assertIn(str(source), filesystem["allowWrite"])
            self.assertNotIn(str(source), filesystem["denyWrite"])
            self.assertNotIn(str(self.work / "claude" / skill), filesystem["denyRead"])
            self.assertNotIn(str(self.out / "code-review.md"), filesystem["denyRead"])
            for peer in runner.SKILLS:
                if peer != skill:
                    self.assertIn(str(self.work / peer), filesystem["denyWrite"])
                    self.assertIn(str(self.work / "claude" / peer), filesystem["denyRead"])
                    self.assertIn(str(scratch / peer), filesystem["denyRead"])
                    self.assertIn(str(scratch / peer), filesystem["denyWrite"])
                    if peer != "code-review":
                        for suffix in ("md", "json", "stderr"):
                            self.assertIn(str(self.out / f"{peer}.{suffix}"), filesystem["denyRead"])
            for path in runner.shared_scratch():
                self.assertIn(str(path), filesystem["denyRead"])
                self.assertIn(str(path), filesystem["denyWrite"])

    def test_cargo_build_parallelism_accounts_for_concurrent_reviewers(self):
        for cpus in (None, 1, 2, 4, 8):
            with patch.object(os, "cpu_count", return_value=cpus):
                values = [runner.environment(self.run, self.work, skill, self.work / "scratch") for skill in runner.SKILLS]
            self.assertEqual(int(values[0]["CARGO_BUILD_JOBS"]), cpus or 1)
            self.assertEqual([int(value["CARGO_BUILD_JOBS"]) for value in values[1:]], [max(1, (cpus or 1) // 3)] * 3)


if __name__ == "__main__":
    unittest.main()
