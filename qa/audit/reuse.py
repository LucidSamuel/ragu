"""Select prior trusted audit artifacts and recover independently verified passes."""

import argparse
import json
import os
from pathlib import Path

import findings
import github
import runner


def source_run(api, check, run):
    prefix = github.scope(run)
    external = check.get("external_id", "")
    if not external.startswith(prefix):
        return None
    parts = external[len(prefix):].split(":")
    if len(parts) != 3:
        return None
    try:
        pr, run_id, attempt = map(github.number, parts)
    except ValueError:
        return None
    if run_id == run.get("run_id") and attempt >= run.get("attempt", 0):
        return None
    metadata = api.call(f"/repos/{github.REPOSITORY}/actions/runs/{run_id}")
    if (metadata.get("id") != run_id or type(metadata.get("run_attempt")) is not int or metadata["run_attempt"] < attempt
            or metadata.get("event") != "issue_comment" or metadata.get("head_branch") != "main"
            or metadata.get("head_sha") != run["configuration"]
            or metadata.get("path") != ".github/workflows/audit.yml"
            or metadata.get("repository", {}).get("full_name") != github.REPOSITORY
            or metadata.get("head_repository", {}).get("full_name") != github.REPOSITORY):
        return None
    return {"run_id": run_id, "attempt": attempt, "check_id": check["id"], "pr": pr,
            "status": metadata["status"], "conclusion": metadata.get("conclusion"),
            "live_attempt": metadata["run_attempt"]}


def active(api, run):
    """Coalesce duplicate requests only after authorization and live API checks."""
    for check in github.checks(api, run["head"], os.environ["RAGU_AUDIT_APP_ID"]):
        if check.get("status") != "in_progress":
            continue
        source = source_run(api, check, run)
        if (not source or source["pr"] != run["pr"] or source["status"] == "completed"
                or source["attempt"] != source["live_attempt"]):
            continue
        try:
            trigger = json.loads(check.get("output", {}).get("text", "{}"))
            original = {"pr": run["pr"], "comment_id": github.number(trigger["comment_id"])}
        except (ValueError, KeyError, TypeError):
            continue
        try:
            github.command_present(api, original)
        except github.CancelledReview:
            continue
        return source
    return None


def plan(api, run):
    values = github.checks(api, run["head"], os.environ["RAGU_AUDIT_APP_ID"])
    # Prefer a completed successful invocation, then the latest partial run.
    values.sort(key=lambda item: (item.get("conclusion") == "success", item["id"]), reverse=True)
    eligible = [item for item in values if item.get("external_id", "").startswith(github.scope(run))]
    for check in eligible[:10]:
        source = source_run(api, check, run)
        if source is None:
            continue
        if (check.get("status") != "completed" and source["status"] != "completed"
                and source["attempt"] == source["live_attempt"]):
            continue
        suffix = f"{source['run_id']}-{source['attempt']}"
        archives = list(api.pages(f"/repos/{github.REPOSITORY}/actions/runs/{source['run_id']}/artifacts", "artifacts"))
        archives = [item for item in archives if not item.get("expired")]
        bulk = [item for item in archives if item["name"] == f"ragu-audit-reports-{suffix}"]
        individual = [item for item in archives if item["name"] in {
            f"ragu-audit-{role}-{suffix}" for role in runner.SKILLS}]
        selected = bulk or individual
        if selected:
            return {"current": run, "source": source,
                    "artifact_ids": [github.number(item["id"]) for item in selected]}
    return {"current": run, "source": None, "artifact_ids": []}


def regular(path, limit=9 * 1024 * 1024):
    if path.is_symlink() or not path.is_file() or path.stat().st_size > limit:
        raise ValueError("invalid reusable artifact file")
    return path.read_bytes()


def restore(run, out, cached):
    """Rebind verified native reports to this invocation; never execute artifacts."""
    try:
        selection = json.loads(regular(cached.parent / "reuse-plan.json", 65536))
        if selection["current"] != run:
            raise ValueError("reuse selection belongs to another invocation")
        source = selection["source"]
        if source is None:
            return [], False
        original = json.loads(regular(cached / "receipt.json", 65536))
        old = original["run"]
        if (runner.reuse_key(old) != runner.reuse_key(run)
                or any(old[key] != source[key] for key in ("run_id", "attempt", "check_id", "pr"))
                or old["app_id"] != run["app_id"]
                or old["external_id"] != github.scope(old) + f"{old['pr']}:{old['run_id']}:{old['attempt']}"
                or old["url"] != f"https://github.com/{github.REPOSITORY}/actions/runs/{old['run_id']}"):
            raise ValueError("reuse snapshot, settings, or provenance differ")
        for name in (*runner.SKILLS, runner.RECONCILER):
            for suffix in ("json", "md"):
                path = cached / f"{name}.{suffix}"
                if path.exists() or path.is_symlink():
                    regular(path)
        for name in ("reuse-receipt.json", "reconciliation-receipt.json", "reuse-reconciliation-receipt.json"):
            path = cached / name
            if path.exists() or path.is_symlink():
                regular(path, 65536)
        verified = runner.verify(old, cached, partial=True)
        phases = [{**phase, "duration_seconds": 0, "reused_from": runner.reuse_origin(old)}
                  for phase in verified["phases"]]
        if not phases:
            return [], False
        payloads = {f"{phase['skill']}.{suffix}": regular(cached / f"{phase['skill']}.{suffix}")
                    for phase in phases for suffix in ("md", "json")}
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        print("Prior reports were unavailable or could not be verified; reviewing afresh", flush=True)
        return [], False

    # All bytes were verified before writing. Writes preserve precreated inodes
    # so peer read-deny mounts remain effective when sessions start later.
    runner.write_json(out / "reuse-receipt.json", original)
    for name, value in payloads.items():
        (out / name).write_bytes(value)
    receipt = runner.read_json(out / "receipt.json")
    receipt["phases"] = phases
    runner.write_json(out / "receipt.json", receipt)
    runner.verify(run, out, partial=True)
    print(f"Reused {len(phases)}/4 verified reviews from {old['url']}", flush=True)

    if len(phases) == len(runner.SKILLS):
        try:
            _, groups = runner.verify_reconciliation(old, cached)
            bundle = runner.candidates(run, out)
            old_record = runner.read_json(cached / "reconciliation-receipt.json")
            runner.write_json(out / "findings.json", bundle)
            record = {"run": run, "input_sha256": findings.fingerprint(bundle)}
            if groups:
                result = runner.read_json(cached / "reconcile.json")
                runner.write_json(out / "reconcile.json", result)
                (out / "reconcile.md").write_text(findings.render_reconciliation(result["structured_output"], bundle))
                runner.write_json(out / "reuse-reconciliation-receipt.json", old_record)
                record.update(state="completed", sha256=runner.digest(out / "reconcile.md"),
                              result_sha256=runner.digest(out / "reconcile.json"),
                              duration_seconds=0, reused_from=runner.reuse_origin(old))
            else:
                # Empty original findings need no reconciliation model call.
                if bundle["findings"]:
                    raise ValueError("nonempty findings require the reconciliation result")
                record["state"] = "empty"
            runner.write_json(out / "reconciliation-receipt.json", record)
            runner.verify_reconciliation(run, out)
            return phases, True
        except (OSError, ValueError, KeyError, TypeError, AttributeError):
            print("Prior reconciliation unavailable; refining the reused reviews", flush=True)
    return phases, False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--plan", type=Path, required=True)
    args = parser.parse_args()
    run = runner.read_json(args.run)
    github.validate_identity(run)
    selection = plan(github.GitHub(), run)
    args.plan.parent.mkdir(parents=True, exist_ok=True)
    runner.write_json(args.plan, selection)
    github.output(source_run=selection["source"]["run_id"] if selection["source"] else "",
                  artifact_ids=",".join(map(str, selection["artifact_ids"])))


if __name__ == "__main__":
    main()
