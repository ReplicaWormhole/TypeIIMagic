#!/usr/bin/env python3
"""Inspect and continue the preserved TypeIIMagic workflow. Python 3.11+, stdlib only."""

from __future__ import annotations
import argparse
import collections
import fcntl
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "typeii_supervisor", ROOT / "workflow/aristotle_autopilot.py"
)
engine = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(engine)


def summary():
    state = engine.read_state()
    jobs = []
    for project in engine.expanded_projects(engine.read_config()):
        lane = state.get("projects", {}).get(project["id"], {})
        missing = engine.missing_dependencies(project, state)
        status = (
            "disabled"
            if not project.get("enabled", True)
            else "halted"
            if lane.get("halted")
            else "active"
            if lane.get("active") or lane.get("pending_submission")
            else "complete"
            if lane.get("next_index", 0) >= len(project["queue"])
            else "waiting"
            if missing
            else "ready"
        )
        jobs.append(
            {
                "id": project["id"],
                "package": project.get("package_id", project["id"]),
                "status": status,
                "missing_dependencies": missing,
                "reason": lane.get("halt_reason"),
                "next_index": lane.get("next_index", 0),
            }
        )
    outcomes = [
        x for v in state.get("projects", {}).values() for x in v.get("completed", [])
    ]
    return {
        "state_source": "runtime" if engine.STATE.exists() else "imported snapshot",
        "outcomes": dict(collections.Counter(x.get("decision") for x in outcomes)),
        "jobs": jobs,
    }


def status(as_json=False):
    data = summary()
    if as_json:
        print(json.dumps(data, indent=2))
        return
    print("TypeIIMagic — " + data["state_source"])
    print(
        "Recorded decisions: "
        + ", ".join(f"{n} {kind}" for kind, n in data["outcomes"].items())
    )
    print(
        "Configured queues: "
        + ", ".join(
            f"{n} {kind}"
            for kind, n in collections.Counter(
                x["status"] for x in data["jobs"]
            ).items()
        )
    )
    for job in data["jobs"]:
        if job["status"] in {"halted", "waiting", "ready", "active"}:
            print(
                f"{job['package']}: {job['status']}"
                + (
                    f"; needs {', '.join(job['missing_dependencies'])}"
                    if job["missing_dependencies"]
                    else ""
                )
            )
            if job["reason"]:
                print("  " + job["reason"])


def check(snapshot=False):
    manifest = json.loads((ROOT / "history/files.json").read_text())
    errors = []
    changed = []
    for entry in manifest["files"]:
        p = ROOT / entry["path"]
        if (
            not p.is_file()
            or hashlib.sha256(p.read_bytes()).hexdigest() != entry["export_sha256"]
        ):
            if entry["path"].startswith("history/") or snapshot:
                errors.append("changed or missing imported record: " + entry["path"])
            else:
                changed.append(entry["path"])
    archives = json.loads((ROOT / "history/archives.json").read_text())
    for entry in archives:
        p = ROOT / entry["export_archive"]
        if (
            not p.is_file()
            or hashlib.sha256(p.read_bytes()).hexdigest()
            != entry["export_archive_sha256"]
        ):
            errors.append(
                "changed or missing return archive: " + entry["export_archive"]
            )
    jobs = engine.expanded_projects(engine.read_config())
    ids = {x.get("package_id") for x in jobs if x.get("package_id")}
    pending = {
        x["package_id"]: set(x.get("depends_on", []))
        for x in jobs
        if x.get("package_id")
    }
    while pending:
        ready = {k for k, v in pending.items() if not v.intersection(pending)}
        if not ready:
            errors.append("dependency cycle")
            break
        for k in ready:
            del pending[k]
    for project in jobs:
        for dep in project.get("depends_on", []):
            if dep not in ids:
                errors.append("unknown dependency: " + dep)
        for packet in project["queue"]:
            if not (Path(project["task_root"]) / packet).is_file():
                errors.append("missing packet: " + packet)
    if errors:
        raise ValueError("\n".join(errors))
    if changed:
        print(
            f"Working copy differs from the imported snapshot in {len(changed)} files; historical records are intact."
        )
    print(
        f"Verified {len(manifest['files'])} imported text records, {len(archives)} return archives, packets and dependency graph."
    )


def resume(package, note, execute):
    if not execute:
        raise ValueError(
            "resume requires --execute and a review note; historical halts are preserved by default"
        )
    jobs = [
        x
        for x in engine.expanded_projects(engine.read_config())
        if x.get("package_id") == package or x["id"] == package
    ]
    if len(jobs) != 1:
        raise ValueError("name exactly one configured package")
    job = jobs[0]
    if not job.get("enabled", True):
        raise ValueError("package is disabled; reconcile the plan before enabling it")
    if not note.strip():
        raise ValueError("review note is required")
    engine.RUNTIME.mkdir(parents=True, exist_ok=True)
    with engine.LOCK.open("a") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError(
                "the supervisor is running; stop it before resuming a packet"
            )
        state = engine.read_state()
        lane = state["projects"].get(job["id"])
        if not lane or not lane.get("halted"):
            raise ValueError("only halted packets can be explicitly resumed")
        # Never discard a task whose remote status or closeout remains unresolved.
        if lane.get("active") or lane.get("pending_submission"):
            raise ValueError(
                "this halt retains an active or ambiguous submission; reconcile that exact task first"
            )
        state.setdefault("resume_events", []).append(
            {
                "package": package,
                "at": engine.stamp(),
                "review_note": note,
                "previous_halt": lane.get("halt_reason"),
            }
        )
        lane["halted"] = False
        lane.pop("halt_reason", None)
        lane.pop("closeout", None)
        lane["next_index"] = 0
        engine.write_state(state)
    print(
        f"{package} is eligible for a reviewed retry. Original decisions remain in history and completed records. No remote task was submitted."
    )


def verify():
    targets = {
        "finite_fibers": ["FiniteFiber"],
        "stabilizer": ["Formalization"]
        + [
            f"AristotleCandidates.{p.stem}"
            for p in sorted(
                (ROOT / "lean/stabilizer/AristotleCandidates").glob("*.lean")
            )
        ],
    }
    for project, names in targets.items():
        base = ROOT / "lean" / project
        subprocess.run(["lake", "build", *names], cwd=base, check=True)
        audit = (
            "tests/AxiomAudit.lean"
            if project == "finite_fibers"
            else "tests/TypeIIMagicAudit.lean"
        )
        result = subprocess.run(
            ["lake", "env", "lean", audit],
            cwd=base,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        print(result.stdout)
        if result.returncode or "sorryAx" in result.stdout:
            raise ValueError(f"{project}: build/axiom audit failed")
        # The audit files must explicitly list all nonstandard axioms, if any.
        import re

        for match in re.finditer(r"depends on axioms:\s*\[([^]]*)\]", result.stdout):
            axioms = {x.strip() for x in match.group(1).split(",") if x.strip()}
            if not axioms <= {"propext", "Classical.choice", "Quot.sound"}:
                raise ValueError(f"{project}: unexpected axioms: {axioms}")
    print(
        "Lean builds and selected theorem axiom audits passed. This does not discharge their explicit mathematical hypotheses."
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    s = sub.add_parser("status")
    s.add_argument("--json", action="store_true")
    c = sub.add_parser("check")
    c.add_argument("--snapshot", action="store_true")
    sub.add_parser("verify")
    sub.add_parser("history")
    for command in ["once", "watch"]:
        p = sub.add_parser(command)
        p.add_argument("--execute", action="store_true")
        p.add_argument("--max-cycles", type=int, default=0)
    p = sub.add_parser("resume")
    p.add_argument("package")
    p.add_argument("--review-note", required=True)
    p.add_argument("--execute", action="store_true")
    args = parser.parse_args()
    try:
        if args.command == "status":
            status(args.json)
        elif args.command == "check":
            check(args.snapshot)
        elif args.command == "verify":
            verify()
        elif args.command == "history":
            for event in json.loads((ROOT / "history/timeline.json").read_text()):
                print(
                    f"{event['at']}  {event['package']:12} {event['decision']:8} {event.get('final', '')}"
                )
        elif args.command == "resume":
            resume(args.package, args.review_note, args.execute)
        elif args.command in {"once", "watch"}:
            if not args.execute:
                raise ValueError(
                    "use status for offline inspection, or add --execute to continue the real loop"
                )
            check()
            cmd = [
                sys.executable,
                str(ROOT / "workflow/aristotle_autopilot.py"),
                "--" + args.command,
                "--execute",
            ]
            if args.max_cycles:
                cmd += ["--max-cycles", str(args.max_cycles)]
            return subprocess.call(cmd, cwd=ROOT)
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
