#!/usr/bin/env python3
"""Dependency-gated supervisor for prepared Aristotle formalization packets.

The supervisor owns eligibility, submission, and polling. Codex owns one
terminal result's download, review, integration, and verification. A packet is
eligible only after every declared predecessor has an accepted `advance`
decision. This permits independent foundation packets to run remotely in
parallel without allowing dependent work to outrun local semantic review.
"""

from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import tomllib


HERE = Path(__file__).resolve().parent
CONFIG = HERE / "autopilot.toml"
STATE = HERE / "state.json"
LOG_DIR = HERE / "logs"
LOCK = HERE / "autopilot.lock"
AUTH = Path.home() / ".codex/skills/aristotle-cli/scripts/aristotle-auth.sh"
CODEX_BIN = Path(os.environ.get("AUTOPILOT_CODEX_BIN", shutil.which("codex") or ""))
DEFAULT_TELEGRAM_SENDER = Path("<original-home>/.local/bin/tg-send")
UUID = re.compile(r"[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}")
TASK_STATUSES = (
    "QUEUED",
    "RUNNING",
    "IN_PROGRESS",
    "COMPLETE",
    "FAILED",
    "BLOCKED",
    "OUT_OF_BUDGET",
    "CANCELLED",
    "CANCELED",
)
TERMINAL = {"COMPLETE", "FAILED", "BLOCKED", "OUT_OF_BUDGET", "CANCELLED", "CANCELED"}


def stamp() -> str:
    return dt.datetime.now(dt.UTC).strftime("%Y%m%dT%H%M%SZ")


def read_config() -> dict:
    with CONFIG.open("rb") as handle:
        return tomllib.load(handle)


def read_state() -> dict:
    if not STATE.exists():
        return {"projects": {}}
    return json.loads(STATE.read_text())


def write_state(state: dict) -> None:
    HERE.mkdir(parents=True, exist_ok=True)
    temporary = STATE.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n")
    temporary.replace(STATE)


def run(cmd: list[str], *, cwd: Path | None = None, input_text: str | None = None, timeout: int | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, input=input_text, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout, check=False)


def log_output(name: str, output: str) -> Path:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    path = LOG_DIR / f"{stamp()}-{name}.log"
    path.write_text(output)
    return path


def telegram_message(project: dict, package_id: str | None, reason: str) -> str:
    """Keep mobile alerts short while retaining the actionable local location."""
    package = package_id or project.get("id", "unknown packet")
    lane = project.get("plan_lane", project.get("id", "unknown lane"))
    compact_reason = " ".join(reason.split())
    if len(compact_reason) > 900:
        compact_reason = compact_reason[:897] + "..."
    return (
        f"Aristotle autopilot needs review: {package} (Lane {lane}).\n"
        f"Reason: {compact_reason}\n"
        "The local supervisor has paused this packet and its dependents."
    )


def send_telegram_alert(config: dict, state: dict, project: dict, lane: dict, reason: str) -> None:
    """Send one Telegram alert per halt reason; notification failure is nonfatal."""
    notifications = config.get("notifications", {})
    if not notifications.get("telegram_enabled", False):
        return
    package_id = (lane.get("active") or {}).get("package_id") or project.get("package_id")
    key = f"{package_id}:{reason}"
    if lane.get("last_telegram_alert") == key:
        return
    sender = Path(notifications.get("telegram_sender", DEFAULT_TELEGRAM_SENDER))
    if not sender.is_file() or not os.access(sender, os.X_OK):
        print(f"[{project['id']}] Telegram sender unavailable: {sender}", file=sys.stderr)
        return
    result = run([str(sender), "--text", telegram_message(project, package_id, reason)])
    log_path = log_output(f"{project['id']}-telegram", result.stdout)
    if result.returncode:
        print(f"[{project['id']}] Telegram alert failed; see {log_path}", file=sys.stderr)
        return
    lane["last_telegram_alert"] = key
    write_state(state)
    print(f"[{project['id']}] Telegram alert sent")


def packet_path(project: dict, index: int) -> Path:
    return Path(project["task_root"]) / project["queue"][index]


def expanded_projects(config: dict) -> list[dict]:
    """Expand a plan-aware program into the existing one-packet lane model."""
    expanded: list[dict] = []
    for project in config.get("project", []):
        jobs = project.get("job")
        if not jobs:
            expanded.append(project)
            continue
        shared = {key: value for key, value in project.items() if key != "job"}
        program_id = shared["id"]
        for job in jobs:
            package_id = job["package_id"]
            expanded.append({
                **shared,
                **job,
                "id": f"{program_id}_{package_id.lower()}",
                "program_id": program_id,
                "queue": [job["packet"]],
            })
    return expanded


def accepted_packages(state: dict) -> set[str]:
    accepted: set[str] = set()
    for lane in state.get("projects", {}).values():
        for result in lane.get("completed", []):
            if result.get("decision") != "advance":
                continue
            package_id = result.get("package_id")
            if package_id is None and result.get("packet"):
                package_id = Path(result["packet"]).name.split("-", 1)[0]
            if package_id:
                accepted.add(package_id)
    return accepted


def missing_dependencies(project: dict, state: dict) -> list[str]:
    accepted = accepted_packages(state)
    return [dependency for dependency in project.get("depends_on", []) if dependency not in accepted]


def status_for(project_id: str, task_id: str) -> tuple[str | None, str, Path]:
    result = run([str(AUTH), "tasks", project_id, "--limit", "20"])
    path = log_output(f"{project_id[:8]}-tasks", result.stdout)
    if result.returncode:
        raise RuntimeError(f"Aristotle tasks failed; see {path}")
    lines = result.stdout.splitlines()
    for index, line in enumerate(lines):
        if not line.startswith(task_id):
            continue
        block_lines = [line]
        for follow in lines[index + 1 : index + 20]:
            if UUID.match(follow):
                break
            block_lines.append(follow)
        block = "\n".join(block_lines)
        matches = re.findall(r"\b(" + "|".join(TASK_STATUSES) + r")\b", block)
        return (matches[-1] if matches else None), result.stdout, path
    return None, result.stdout, path


def latest_task(project_id: str) -> str:
    result = run([str(AUTH), "tasks", project_id, "--limit", "1"])
    path = log_output(f"{project_id[:8]}-new-task", result.stdout)
    if result.returncode:
        raise RuntimeError(f"Could not list newly submitted task; see {path}")
    match = UUID.search(result.stdout)
    if not match:
        raise RuntimeError(f"No task UUID found after submission; see {path}")
    return match.group(0)


def submission_stage(project: dict) -> Path:
    """Build an upload-only Lean project snapshot with canonical paper context."""
    project_root = Path(project["root"])
    paper_root = Path(project["paper_root"])
    if not (project_root / "lakefile.lean").exists():
        raise RuntimeError(f"Lean project is missing lakefile.lean: {project_root}")
    if not (paper_root / "main.tex").exists():
        raise RuntimeError(f"Canonical manuscript entry point is missing: {paper_root / 'main.tex'}")
    stage = Path(tempfile.mkdtemp(prefix=f"aristotle-{project['id']}-"))
    ignored = shutil.ignore_patterns(".git", ".lake", "aristotle_responses", "__pycache__", "*.olean", "*.ilean", "*.trace", "*.ir")
    shutil.copytree(project_root, stage, dirs_exist_ok=True, ignore=ignored)
    manuscript_dir = stage / "manuscript"
    manuscript_dir.mkdir()
    shutil.copy2(paper_root / "main.tex", manuscript_dir / "main.tex")
    for bibliography in paper_root.glob("*.bib"):
        shutil.copy2(bibliography, manuscript_dir / bibliography.name)
    shutil.copy2(HERE / "AUTONOMY_POLICY.md", stage / "AUTONOMY_POLICY.md")
    (stage / "ARISTOTLE_SOURCE_CONTEXT.md").write_text(
        "# Canonical manuscript context\n\n"
        "The canonical manuscript entry point and its bibliography files are\n"
        "included under `manuscript/`.\n"
        f"Read `{project['paper_entry']}` for the canonical source text.\n"
        "Read `AUTONOMY_POLICY.md`, `AGENTS.md`, `PLAN.md`, and\n"
        "`work/TWO-LANE-FORMALIZATION-DECISION.md` before beginning. Verify the\n"
        "packet's lane, predecessors, permitted gate, and forbidden downstream\n"
        "claims against those files. The packet names a milestone,\n"
        "but permits necessary local theory and a different proof route. Do not\n"
        "silently strengthen claims or add unstated analytic hypotheses.\n"
    )
    return stage


def submit(project: dict, packet: Path, state: dict, lane: dict, queue_index: int) -> tuple[str, str, Path]:
    prompt = (
        (HERE / "AUTONOMY_POLICY.md").read_text()
        + "\n\n# Active-plan requirement\n\n"
        + "Read `AGENTS.md`, `PLAN.md`, and `work/TWO-LANE-FORMALIZATION-DECISION.md`. "
        + "Obey the packet's Plan alignment section. Use only integrated predecessors, "
        + "and do not state any forbidden downstream claim.\n\n# Current packet\n\n"
        + packet.read_text()
    )
    stage = submission_stage(project)
    try:
        result = run([str(AUTH), "submit", prompt, "--project-dir", str(stage)])
    finally:
        shutil.rmtree(stage, ignore_errors=True)
    path = log_output(f"{project['id']}-{packet.stem}-submit", result.stdout)
    if result.returncode:
        raise RuntimeError(f"Aristotle submit failed; see {path}")
    project_match = re.search(r"Project created:\s*(" + UUID.pattern + r")", result.stdout)
    if not project_match:
        raise RuntimeError(f"Submission did not report a project UUID; see {path}")
    project_id = project_match.group(1)
    lane["pending_submission"] = {
        "queue_index": queue_index,
        "packet": str(packet),
        "project_id": project_id,
        "submit_log": str(path),
        "package_id": project.get("package_id"),
    }
    lane["next_index"] = queue_index + 1
    write_state(state)
    task_id = latest_task(project_id)
    lane.pop("pending_submission", None)
    return project_id, task_id, path


def response_paths(project: dict, active: dict) -> tuple[Path, Path]:
    """Return retry-safe raw archive and quarantine paths for one exact task."""
    response_root = Path(project["root"]) / "aristotle_responses"
    packet_stem = Path(active["packet"]).stem
    task_tag = f"{active['project_id'][:8]}-{active['task_id'][:8]}"
    archive = response_root / f"{packet_stem}-{task_tag}.tar.gz"
    quarantine = response_root / f"{packet_stem}-{task_tag}-quarantine"
    return archive, quarantine


def download_response(project: dict, active: dict) -> tuple[Path, Path]:
    """Download the exact terminal task once, without reusing package-level caches."""
    archive, quarantine = response_paths(project, active)
    archive.parent.mkdir(parents=True, exist_ok=True)
    if archive.is_file() and archive.stat().st_size > 0 and tarfile.is_tarfile(archive):
        return archive, quarantine
    if archive.exists():
        archive.unlink()
    result = run([
        str(AUTH),
        "download",
        active["project_id"],
        "--destination",
        str(archive),
    ])
    log_path = log_output(f"{active['project_id'][:8]}-{active['task_id'][:8]}-download", result.stdout)
    if (result.returncode or not archive.is_file() or archive.stat().st_size == 0
        or not tarfile.is_tarfile(archive)):
        raise RuntimeError(f"Aristotle download failed; see {log_path}")
    return archive, quarantine


def render_closeout(project: dict, active: dict, status: str, task_log: Path, task_output: str,
    response_archive: Path, quarantine_dir: Path) -> str:
    template = (HERE / "codex_closeout_prompt.md").read_text()
    values = {
        "LANE": project.get("plan_lane", project["id"]),
        "PROJECT_ROOT": project["root"],
        "PACKET_PATH": str(packet_path(project, active["queue_index"])),
        "PROJECT_ID": active["project_id"],
        "TASK_ID": active["task_id"],
        "TASK_STATUS": status,
        "TASK_LOG": str(task_log),
        "TASK_OUTPUT": task_output.rstrip(),
        "RESPONSE_ARCHIVE": str(response_archive),
        "QUARANTINE_DIR": str(quarantine_dir),
    }
    for key, value in values.items():
        template = template.replace("{{" + key + "}}", value)
    return template


def invoke_codex(project: dict, active: dict, status: str, task_log: Path, task_output: str, lane: dict, state: dict, timeout: int) -> tuple[int, Path, Path]:
    response_archive, quarantine_dir = download_response(project, active)
    prompt = render_closeout(
        project,
        active,
        status,
        task_log,
        task_output,
        response_archive,
        quarantine_dir,
    )
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    prefix = f"{stamp()}-{project['id']}-{active['task_id'][:8]}"
    prompt_path = LOG_DIR / f"{prefix}-prompt.md"
    json_path = LOG_DIR / f"{prefix}-codex.jsonl"
    final_path = LOG_DIR / f"{prefix}-codex-final.md"
    prompt_path.write_text(prompt)
    lane["closeout"] = {
        "task_id": active["task_id"],
        "status": status,
        "prompt": str(prompt_path),
        "final": str(final_path),
        "json": str(json_path),
        "started_at": stamp(),
    }
    write_state(state)
    cmd = [str(CODEX_BIN), "exec", "--cd", project["root"], "--sandbox", "danger-full-access", "--json", "--output-last-message", str(final_path), "-"]
    result = run(cmd, input_text=prompt, timeout=None if timeout == 0 else timeout)
    json_path.write_text(result.stdout)
    lane["closeout"]["exit_code"] = result.returncode
    lane["closeout"]["finished_at"] = stamp()
    write_state(state)
    return result.returncode, final_path, prompt_path


def closeout_decision(final_path: Path) -> str | None:
    if not final_path.exists():
        return None
    text = final_path.read_text()
    accepted = "AUTOPILOT_ACCEPTED: yes" in text
    match = re.findall(r"AUTOPILOT_DECISION:\s*(advance|halt)", text)
    if accepted and match:
        return match[-1]
    return None


def process_project(project: dict, state: dict, config: dict, *, dry_run: bool, no_codex: bool, timeout: int) -> bool:
    if not project.get("enabled", True):
        print(f"[{project['id']}] disabled by plan configuration")
        return False
    lane = state.setdefault("projects", {}).setdefault(project["id"], {"next_index": 0, "active": None, "completed": [], "halted": False})
    if lane.get("halted"):
        print(f"[{project['id']}] halted; inspect state and review before resuming")
        return False

    active = lane.get("active")
    pending = lane.get("pending_submission")
    if active is None and pending:
        try:
            task_id = latest_task(pending["project_id"])
        except Exception:
            print(f"[{project['id']}] submission pending; task listing failed, will retry")
            return False
        active = {
            "queue_index": pending["queue_index"],
            "packet": pending["packet"],
            "project_id": pending["project_id"],
            "task_id": task_id,
            "submitted_at": pending.get("submitted_at", stamp()),
            "submit_log": pending["submit_log"],
            "package_id": pending.get("package_id"),
        }
        lane["active"] = active
        lane.pop("pending_submission", None)
        write_state(state)
        print(f"[{project['id']}] recovered submitted task: project={active['project_id']}, task={task_id}")
    if active:
        status, output, task_log = status_for(active["project_id"], active["task_id"])
        print(f"[{project['id']}] {active['task_id']}: {status or 'UNKNOWN'}")
        if status not in TERMINAL:
            return False
        if dry_run or no_codex:
            print(f"[{project['id']}] would close out terminal task {active['task_id']}")
            return True
        prior_closeout = lane.get("closeout")
        if prior_closeout and prior_closeout.get("task_id") == active["task_id"]:
            final_path = Path(prior_closeout["final"])
            prompt_path = Path(prior_closeout["prompt"])
            decision = closeout_decision(final_path)
            if decision is None:
                lane["halted"] = True
                lane["halt_reason"] = f"Codex closeout was interrupted without a machine-readable decision; inspect {prompt_path} and {final_path} before resuming"
                write_state(state)
                send_telegram_alert(config, state, project, lane, lane["halt_reason"])
                print(f"[{project['id']}] interrupted Codex closeout; lane halted for review")
                return True
            code = int(prior_closeout.get("exit_code", 0))
        else:
            code, final_path, prompt_path = invoke_codex(project, active, status, task_log, output, lane, state, timeout)
            decision = closeout_decision(final_path)
        print(f"[{project['id']}] Codex exit={code}, decision={decision or 'INVALID'}")
        if code != 0 or decision is None:
            lane["halted"] = True
            lane["halt_reason"] = f"Codex closeout failed or lacked machine-readable acceptance; prompt={prompt_path} final={final_path}"
            write_state(state)
            send_telegram_alert(config, state, project, lane, lane["halt_reason"])
            return True
        lane["completed"].append({**active, "status": status, "decision": decision, "closed_at": stamp(), "final": str(final_path)})
        lane["active"] = None
        lane.pop("closeout", None)
        if decision == "halt":
            lane["halted"] = True
            lane["halt_reason"] = f"Codex recorded a genuine partial/blocked result; final={final_path}"
            write_state(state)
            send_telegram_alert(config, state, project, lane, lane["halt_reason"])
            return True
        write_state(state)

    index = lane["next_index"]
    if index >= len(project["queue"]):
        print(f"[{project['id']}] queue complete")
        return False
    packet = packet_path(project, index)
    if not packet.exists():
        raise RuntimeError(f"Prepared packet is missing: {packet}")
    missing = missing_dependencies(project, state)
    if missing:
        print(f"[{project['id']}] waiting for accepted predecessors: {', '.join(missing)}")
        return False
    if dry_run or no_codex:
        print(f"[{project['id']}] next packet: {packet}")
        return True
    project_id, task_id, submit_log = submit(project, packet, state, lane, index)
    lane["active"] = {"queue_index": index, "packet": str(packet), "project_id": project_id, "task_id": task_id, "submitted_at": stamp(), "submit_log": str(submit_log), "package_id": project.get("package_id")}
    lane["next_index"] = index + 1
    write_state(state)
    print(f"[{project['id']}] submitted {packet.name}: project={project_id}, task={task_id}")
    return True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--once", action="store_true", help="run one poll cycle")
    parser.add_argument("--watch", action="store_true", help="poll until stopped")
    parser.add_argument("--dry-run", action="store_true", help="inspect queues without network submission or Codex")
    parser.add_argument("--no-codex", action="store_true", help="do not invoke Codex; useful only for diagnostics")
    parser.add_argument("--poll-seconds", type=int, default=None)
    parser.add_argument("--max-cycles", type=int, default=0)
    args = parser.parse_args()
    if args.once and args.watch:
        parser.error("choose --once or --watch")
    if not args.once and not args.watch:
        args.once = True
    if not AUTH.exists():
        print(f"missing Aristotle auth wrapper: {AUTH}", file=sys.stderr)
        return 2
    if not CODEX_BIN.is_file() or not os.access(CODEX_BIN, os.X_OK):
        print(f"missing Codex executable: {CODEX_BIN}", file=sys.stderr)
        return 2

    config = read_config()
    state = read_state()
    poll = args.poll_seconds or int(config.get("poll_seconds", 600))
    timeout = int(config.get("codex_timeout_seconds", 0))
    HERE.mkdir(parents=True, exist_ok=True)
    with LOCK.open("w") as lock_handle:
        try:
            fcntl.flock(lock_handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("another autopilot instance already holds the lock", file=sys.stderr)
            return 3
        cycle = 0
        while True:
            cycle += 1
            try:
                for project in expanded_projects(config):
                    process_project(project, state, config, dry_run=args.dry_run, no_codex=args.no_codex, timeout=timeout)
            except Exception as exc:  # long-running supervisor: preserve state and continue polling
                print(f"autopilot error: {exc}", file=sys.stderr)
                write_state(state)
                notification_state = state.setdefault("notification_state", {})
                send_telegram_alert(
                    config,
                    state,
                    {"id": "supervisor", "plan_lane": "system"},
                    notification_state,
                    f"Supervisor error: {exc}",
                )
                if args.once:
                    return 1
            if args.once or (args.max_cycles and cycle >= args.max_cycles):
                return 0
            time.sleep(poll)


if __name__ == "__main__":
    raise SystemExit(main())
