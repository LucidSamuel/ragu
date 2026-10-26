"""Run a bounded, independent core-review pair without changing bot settings."""

import argparse
from decimal import Decimal, InvalidOperation
import os
from pathlib import Path
import re

import github
import runner


def budget(value):
    try:
        amount = Decimal(value)
    except (InvalidOperation, TypeError, ValueError):
        raise ValueError("evaluation budget must be between $1 and $25") from None
    if not amount.is_finite() or not 1 <= amount <= 25:
        raise ValueError("evaluation budget must be between $1 and $25")
    return amount


def compare(root, private, work, out, head, base, limit):
    """Keep the pair on one snapshot, fresh contexts, and one estimated budget."""
    head, base = github.sha(head), github.sha(base)
    if not re.fullmatch(r"claude-[a-z0-9.-]{1,100}", os.environ["RAGU_AUDIT_MODEL"]):
        raise ValueError("evaluation requires an explicit Claude model ID")
    remaining = budget(str(limit))
    out.mkdir(parents=True, exist_ok=False)
    records = []
    for effort in ("high", "xhigh"):
        if remaining <= 0:
            break
        run = {"purpose": "effort-evaluation", "repository": github.REPOSITORY,
               "configuration": github.sha(os.environ["GITHUB_WORKFLOW_SHA"]),
               "head": head, "base": base, "model": os.environ["RAGU_AUDIT_MODEL"], "effort": effort,
               "reconcile_model": runner.RECONCILE_MODEL, "reconcile_effort": runner.RECONCILE_EFFORT,
               "evaluation_budget_usd": str(remaining)}
        reports = out / effort
        completed = False
        try:
            runner.review(root, run, work / effort, reports, private, core_only=True)
            receipt = runner.verify(run, reports, partial=True)
            completed = [phase["skill"] for phase in receipt["phases"]] == [runner.SKILLS[0]]
        except (OSError, ValueError, KeyError, TypeError):
            print(f"{effort}: evaluation incomplete; see its reports", flush=True)
        cost = None
        try:
            result = runner.read_json(reports / "code-review.json")
            value = result.get("total_cost_usd")
            if type(value) in (int, float):
                amount = Decimal(str(value))
                if amount.is_finite() and amount >= 0:
                    cost = amount
        except (OSError, ValueError, TypeError, InvalidOperation):
            pass
        record = {"effort": effort, "complete": completed, "estimated_cost_usd": str(cost) if cost is not None else None}
        records.append(record)
        runner.write_json(out / "comparison.json", {"head": head, "base": base, "budget_usd": str(limit), "passes": records})
        lines = ["# Effort comparison", "", f"Head: `{head}` · Base: `{base}`", "",
                 "| Effort | Core review | Estimated API cost |", "| --- | --- | ---: |"]
        lines += [f"| {item['effort']} | {'Completed' if item['complete'] else 'Incomplete'} | "
                  + (f"${Decimal(item['estimated_cost_usd']):.2f}" if item['estimated_cost_usd'] is not None else "Unknown") + " |" for item in records]
        lines += ["", "Compare the original code-review reports against independently confirmed defects and false claims. "
                  "This single core-review pair does not establish quality for the three specialists or justify changing production effort.", "",
                  "Each session receives only the remaining estimated budget. In-flight requests can overshoot, "
                  "and CLI estimates can differ from Anthropic billing. Missing cost telemetry stops the comparison.", ""]
        (out / "comparison.md").write_text("\n".join(lines))
        if cost is None or not completed:
            break
        remaining -= cost
    if len(records) != 2 or not all(item["complete"] for item in records):
        raise ValueError("effort comparison incomplete; see preserved reports")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("root", "private", "work", "out"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--head", type=github.sha, required=True)
    parser.add_argument("--base", type=github.sha, required=True)
    parser.add_argument("--max-cost-usd", type=budget, default=Decimal("10"))
    args = parser.parse_args()
    if os.environ["GITHUB_REPOSITORY"] != github.REPOSITORY or os.environ["GITHUB_REF"] != "refs/heads/main":
        raise ValueError("evaluations require the trusted Ragu main workflow")
    api = github.GitHub()
    for login in {os.environ["GITHUB_ACTOR"], os.environ["GITHUB_TRIGGERING_ACTOR"]}:
        if not github.can_request(api, login):
            raise ValueError("evaluation requires live repository write permission")
    compare(args.root.resolve(), args.private.resolve(), args.work.resolve(), args.out.resolve(),
            args.head, args.base, args.max_cost_usd)


if __name__ == "__main__":
    main()
