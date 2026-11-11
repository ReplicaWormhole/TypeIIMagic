#!/usr/bin/env python3
"""Poll Aristotle and invoke Codex once a tracked task finishes.

This script is intentionally an orchestrator, not a formalizer.  Aristotle is
still responsible for focused Lean proving tasks.  When an Aristotle task in
`MANIFEST.toml` reaches a terminal status, this script starts one noninteractive
Codex run with a bounded prompt that asks Codex to download/integrate the
result, update bookkeeping, choose the next target, and submit it to Aristotle.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib


ROOT = Path(__file__).resolve().parents[1]
AUTH_WRAPPER = Path.home() / ".codex/skills/aristotle-cli/scripts/aristotle-auth.sh"
DEFAULT_PROMPT_TEMPLATE = ROOT / "aristotle/orchestrator/codex_orchestration_prompt.md"
STATE_FILE = ROOT / "aristotle/orchestrator/loop_state.json"
LOG_DIR = ROOT / "aristotle/logs"

ACTIVE_STATUSES = {
    "sent_to_aristotle_queued",
    "sent_to_aristotle_in_progress",
    "sent_to_aristotle_running",
}
TERMINAL_TASK_STATUSES = {"COMPLETE", "FAILED", "CANCELLED", "CANCELED", "BLOCKED"}
TASK_STATUSES = (
    "QUEUED",
    "RUNNING",
    "IN_PROGRESS",
    "COMPLETE",
    "FAILED",
    "CANCELLED",
    "CANCELED",
    "BLOCKED",
)
TASK_ID_RE = re.compile(r"^[0-9a-fA-F-]{36}\b")
TASK_STATUS_RE = re.compile(r"\b(" + "|".join(TASK_STATUSES) + r")\b")
TARGET_ID_RE = re.compile(r"\b([A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*-\d{3})\b")
BLOCKER_OUTPUT_PATTERNS = (
    ("blocked", re.compile(r"\bblocked\b", re.IGNORECASE)),
    (
        "missing prerequisite",
        re.compile(r"\bmissing (?:mathematical )?prerequisites?\b", re.IGNORECASE),
    ),
    ("missing lemma", re.compile(r"\bmissing lemmas?\b", re.IGNORECASE)),
    ("failed to synthesize", re.compile(r"\bfailed to synthesize\b", re.IGNORECASE)),
    ("unknown constant", re.compile(r"\bunknown constant\b", re.IGNORECASE)),
    ("unsolved goals", re.compile(r"\bunsolved goals?\b", re.IGNORECASE)),
)
NEGATED_BLOCKER_LINE_RE = re.compile(
    r"\b(?:no|without|none)\b.{0,40}\b(?:"
    r"blocked|missing prerequisites?|missing lemmas?|failed to synthesize|"
    r"unknown constants?|unsolved goals?"
    r")\b",
    re.IGNORECASE,
)


def timestamp() -> str:
    return dt.datetime.now(dt.UTC).strftime("%Y%m%dT%H%M%SZ")


def load_manifest() -> dict:
    with (ROOT / "MANIFEST.toml").open("rb") as handle:
        return tomllib.load(handle)


def load_state() -> dict:
    if not STATE_FILE.exists():
        return {"handled_tasks": {}}
    return json.loads(STATE_FILE.read_text())


def save_state(state: dict) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    tmp = STATE_FILE.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n")
    tmp.replace(STATE_FILE)


def find_active_packet(manifest: dict) -> dict | None:
    packets = manifest.get("aristotle_packet", [])
    for packet in reversed(packets):
        if packet.get("status") in ACTIVE_STATUSES and packet.get("project") and packet.get("task"):
            return packet
    return None


def is_smoke_packet(packet: dict) -> bool:
    text = " ".join(
        str(packet.get(key, ""))
        for key in ("id", "kind", "source", "goal", "packet")
    ).lower()
    return "smoke" in text or "toy" in text


def target_by_id(manifest: dict) -> dict[str, dict]:
    return {target.get("id", ""): target for target in manifest.get("target", [])}


def parse_target_id(packet: dict, packet_text: str) -> str | None:
    explicit = packet.get("target_id")
    if isinstance(explicit, str) and explicit:
        return explicit

    target_line = re.search(r"(?mi)^target_id:\s*([A-Za-z0-9_-]+)\s*$", packet_text)
    if target_line:
        return target_line.group(1)

    heading = re.search(r"(?m)^#\s*Target:\s*(\S+)", packet_text)
    if heading:
        return heading.group(1)

    packet_id = packet.get("id")
    if isinstance(packet_id, str):
        match = TARGET_ID_RE.search(packet_id)
        if match:
            return match.group(1)
    return None


def current_blueprint_gate(packet: dict, manifest: dict, *, mode: str) -> tuple[str, str]:
    """Validate that an active packet is tied to the current manifest blueprint.

    The gate is deliberately conservative.  Smoke-test packets are exempt, but
    every real formalization packet must identify a manifest target, cite that
    target's current blueprint path, and not predate the blueprint file.
    """

    lines: list[str] = ["Current-blueprint extraction gate:"]
    if mode == "off":
        lines.append("- Status: SKIPPED (--blueprint-gate-mode off).")
        return "SKIPPED", "\n".join(lines)

    if is_smoke_packet(packet):
        lines.append("- Status: PASS (smoke-test packet; blueprint gate does not apply).")
        return "PASS", "\n".join(lines)

    errors: list[str] = []
    warnings: list[str] = []

    packet_rel = packet.get("packet", "")
    packet_path = ROOT / packet_rel if packet_rel else None
    packet_text = ""
    if packet_path is None:
        errors.append("packet path is missing from MANIFEST.toml")
    elif not packet_path.exists():
        errors.append(f"packet file does not exist: {packet_rel}")
    else:
        packet_text = packet_path.read_text()

    target_id = parse_target_id(packet, packet_text)
    lines.append(f"- Packet: {packet_rel or '<missing>'}")
    lines.append(f"- Parsed target ID: {target_id or '<missing>'}")
    if not target_id:
        errors.append("could not parse a target ID from packet metadata or packet text")

    target = target_by_id(manifest).get(target_id or "")
    if target is None:
        errors.append(f"target {target_id or '<missing>'} is not present in MANIFEST.toml")
    else:
        tex_rel = target.get("tex", "")
        lean_rel = target.get("lean", "")
        lines.append(f"- Manifest target status: {target.get('status', '<missing>')}")
        lines.append(f"- Manifest blueprint: {tex_rel or '<missing>'}")
        lines.append(f"- Manifest Lean path: {lean_rel or '<missing>'}")

        tex_path = ROOT / tex_rel if tex_rel else None
        if tex_path is None:
            errors.append(f"target {target_id} has no tex path in MANIFEST.toml")
        elif not tex_path.exists():
            errors.append(f"manifest blueprint does not exist: {tex_rel}")
        else:
            tex_text = tex_path.read_text()
            if target_id and target_id not in tex_text:
                errors.append(f"blueprint {tex_rel} does not mention target ID {target_id}")
            if packet_text and tex_rel not in packet_text:
                errors.append(f"packet does not cite current manifest blueprint path {tex_rel}")
            if lean_rel and packet_text and lean_rel not in packet_text:
                warnings.append(f"packet does not mention manifest Lean path {lean_rel}")
            if packet_path is not None and packet_path.exists():
                packet_mtime = packet_path.stat().st_mtime
                tex_mtime = tex_path.stat().st_mtime
                manifest_mtime = (ROOT / "MANIFEST.toml").stat().st_mtime
                if packet_mtime + 1 < tex_mtime:
                    errors.append(
                        "packet is older than its blueprint; regenerate or review the packet "
                        f"against {tex_rel} before using it"
                    )
                if packet_mtime + 1 < manifest_mtime:
                    warnings.append(
                        "packet is older than MANIFEST.toml; confirm target status/dependencies "
                        "before submitting follow-up work"
                    )

    status = "FAIL" if errors else "WARN" if warnings else "PASS"
    if status == "FAIL" and mode == "warn":
        status = "WARN"
        warnings.extend(f"strict-mode failure downgraded by --blueprint-gate-mode warn: {e}" for e in errors)
        errors = []

    lines.append(f"- Status: {status}")
    for error in errors:
        lines.append(f"- ERROR: {error}")
    for warning in warnings:
        lines.append(f"- WARNING: {warning}")
    return status, "\n".join(lines)


def blocker_repair_scan(task_status_value: str, task_output: str) -> tuple[str, str]:
    """Detect Aristotle results that must enter the blocker repair protocol."""

    lines: list[str] = ["Blocker auto-repair supervisor scan:"]
    reasons: list[str] = []

    if task_status_value != "COMPLETE":
        reasons.append(f"terminal task status is {task_status_value}")

    output_lines = task_output.splitlines()
    for label, pattern in BLOCKER_OUTPUT_PATTERNS:
        if any(pattern.search(line) and not NEGATED_BLOCKER_LINE_RE.search(line) for line in output_lines):
            reasons.append(f"task output mentions {label}")

    status = "REQUIRED" if reasons else "NOT_REQUIRED"
    lines.append(f"- Status: {status}")
    for reason in reasons:
        lines.append(f"- Trigger: {reason}")
    if status == "REQUIRED":
        lines.append(
            "- Required action: run the blocker auto-repair gate before choosing "
            "or submitting any follow-up Aristotle packet."
        )
    else:
        lines.append("- No blocker trigger was detected by the supervisor scan.")

    return status, "\n".join(lines)


def run_command(
    cmd: list[str],
    *,
    stdin: str | None = None,
    log: Path | None = None,
    timeout_seconds: int | None = None,
) -> subprocess.CompletedProcess:
    try:
        result = subprocess.run(
            cmd,
            input=stdin,
            text=True,
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode(errors="replace")
        stdout += f"\n[TIMEOUT] Command exceeded {timeout_seconds} seconds.\n"
        result = subprocess.CompletedProcess(cmd, 124, stdout)
    if log is not None:
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_text(result.stdout)
    return result


def task_status(project: str, task: str) -> tuple[str | None, Path, str]:
    log_path = LOG_DIR / f"orchestrator-{timestamp()}-{project[:8]}-tasks.log"
    result = run_command([str(AUTH_WRAPPER), "tasks", project], log=log_path)
    if result.returncode != 0:
        raise RuntimeError(f"aristotle tasks failed; see {log_path}")
    lines = result.stdout.splitlines()
    for index, line in enumerate(lines):
        if not line.startswith(f"{task} "):
            continue

        row_lines = [line]
        for follow in lines[index + 1 : index + 20]:
            if TASK_ID_RE.match(follow):
                break
            row_lines.append(follow)

        matches = list(TASK_STATUS_RE.finditer("\n".join(row_lines)))
        if matches:
            return matches[-1].group(1), log_path, result.stdout
    return None, log_path, result.stdout


def render_prompt(
    packet: dict,
    task_status_value: str,
    task_log: Path,
    task_output: str,
    *,
    prompt_template: Path,
    user_goal: str,
    gate_report: str,
    blocker_report: str,
) -> str:
    template = prompt_template.read_text()
    replacements = {
        "PACKET_ID": packet.get("id", ""),
        "PACKET_PATH": packet.get("packet", ""),
        "PROJECT_ID": packet.get("project", ""),
        "TASK_ID": packet.get("task", ""),
        "TASK_STATUS": task_status_value,
        "TASK_LOG": str(task_log.relative_to(ROOT)),
        "USER_GOAL": user_goal,
        "TASK_OUTPUT": task_output.rstrip(),
        "GATE_REPORT": gate_report.rstrip(),
        "BLOCKER_REPORT": blocker_report.rstrip(),
    }
    rendered = template
    for key, value in replacements.items():
        rendered = rendered.replace("{{" + key + "}}", value)
    return rendered


def invoke_codex(prompt: str, args: argparse.Namespace) -> tuple[int, Path, Path]:
    run_id = timestamp()
    json_log = LOG_DIR / f"orchestrator-{run_id}-codex.jsonl"
    last_message = LOG_DIR / f"orchestrator-{run_id}-codex-final.md"
    cmd = [
        "codex",
        "exec",
        "--cd",
        str(ROOT),
        "--sandbox",
        args.codex_sandbox,
        "--json",
        "--output-last-message",
        str(last_message),
    ]
    if args.codex_model:
        cmd.extend(["--model", args.codex_model])
    for extra in args.codex_arg:
        cmd.append(extra)
    cmd.append("-")

    timeout = None if args.codex_timeout_seconds == 0 else args.codex_timeout_seconds
    result = run_command(cmd, stdin=prompt, log=json_log, timeout_seconds=timeout)
    return result.returncode, json_log, last_message


def handle_once(args: argparse.Namespace) -> bool:
    manifest = load_manifest()
    packet = find_active_packet(manifest)
    if args.project and args.task:
        packet = {
            "id": args.packet_id or "manual-override",
            "packet": args.packet_path or "",
            "project": args.project,
            "task": args.task,
        }
    if packet is None:
        print("No active Aristotle packet found in MANIFEST.toml.")
        return False

    project = packet["project"]
    task = packet["task"]
    status, task_log, task_output = task_status(project, task)
    if status is None:
        print(f"Task {task} not found for project {project}; see {task_log}.")
        return False

    print(f"Aristotle task {task} in project {project}: {status}")
    if status not in TERMINAL_TASK_STATUSES:
        return False

    gate_status, gate_report = current_blueprint_gate(
        packet,
        manifest,
        mode=args.blueprint_gate_mode,
    )
    print(gate_report)
    if gate_status == "FAIL":
        print(
            "Current-blueprint gate failed; not invoking Codex. "
            "Regenerate/review the packet against the current blueprint, or rerun "
            "with --blueprint-gate-mode warn for a one-off manual integration."
        )
        return False

    blocker_repair_status, blocker_report = blocker_repair_scan(status, task_output)
    print(blocker_report)

    state = load_state()
    handled = state.setdefault("handled_tasks", {})
    handled_entry = handled.get(task)
    if handled_entry and handled_entry.get("codex_exit_code") == 0 and not args.force:
        print(f"Task {task} was already handled at {handled[task].get('handled_at')}.")
        return False

    prompt = render_prompt(
        packet,
        status,
        task_log,
        task_output,
        prompt_template=args.prompt_template,
        user_goal=args.user_goal,
        gate_report=gate_report,
        blocker_report=blocker_report,
    )
    prompt_log = LOG_DIR / f"orchestrator-{timestamp()}-{task[:8]}-prompt.md"
    prompt_log.write_text(prompt)

    if args.dry_run:
        print(f"Dry run: would invoke Codex with prompt {prompt_log}.")
        return True

    code, codex_log, last_message = invoke_codex(prompt, args)
    record = {
        "handled_at": timestamp(),
        "project": project,
        "status": status,
        "blocker_repair_status": blocker_repair_status,
        "packet_id": packet.get("id", ""),
        "prompt_log": str(prompt_log.relative_to(ROOT)),
        "codex_log": str(codex_log.relative_to(ROOT)),
        "codex_final": str(last_message.relative_to(ROOT)),
        "codex_exit_code": code,
    }
    if code == 0:
        handled[task] = record
    else:
        state.setdefault("failed_codex_runs", []).append(record)
    save_state(state)
    print(f"Codex exit code: {code}")
    print(f"Codex log: {codex_log.relative_to(ROOT)}")
    print(f"Codex final message: {last_message.relative_to(ROOT)}")
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--once", action="store_true", help="Poll once and exit.")
    parser.add_argument("--watch", action="store_true", help="Poll repeatedly.")
    parser.add_argument("--poll-seconds", type=int, default=300)
    parser.add_argument("--max-cycles", type=int, default=0, help="0 means unlimited in --watch mode.")
    parser.add_argument("--dry-run", action="store_true", help="Render prompt but do not invoke Codex.")
    parser.add_argument("--force", action="store_true", help="Allow handling a terminal task again.")
    parser.add_argument("--project", help="Override Aristotle project ID.")
    parser.add_argument("--task", help="Override Aristotle task ID.")
    parser.add_argument("--packet-id", help="Label for manual override mode.")
    parser.add_argument("--packet-path", help="Packet path for manual override mode.")
    parser.add_argument("--codex-model", help="Optional model passed to codex exec.")
    parser.add_argument("--codex-sandbox", default="danger-full-access", choices=["read-only", "workspace-write", "danger-full-access"])
    parser.add_argument(
        "--codex-timeout-seconds",
        type=int,
        default=0,
        help="Timeout for each Codex integration pass; 0 disables the timeout.",
    )
    parser.add_argument("--codex-arg", action="append", default=[], help="Extra argument passed to codex exec; repeatable.")
    parser.add_argument(
        "--blueprint-gate-mode",
        choices=["strict", "warn", "off"],
        default="strict",
        help=(
            "Validate that active formalization packets cite and postdate the "
            "current manifest blueprint. strict blocks failures; warn includes "
            "the report in the Codex prompt; off skips the gate."
        ),
    )
    parser.add_argument(
        "--prompt-template",
        type=Path,
        default=DEFAULT_PROMPT_TEMPLATE,
        help="Codex orchestration prompt template.",
    )
    parser.add_argument(
        "--user-goal",
        default=(
            "complete sorry-free formalization of the relationship between "
            "stabilizer systems and the resulting von Neumann algebra types in "
            "the canonical projection/local-code-subspace state"
        ),
        help="Goal string substituted into the Codex orchestration prompt.",
    )
    args = parser.parse_args()

    if not AUTH_WRAPPER.exists():
        print(f"Missing Aristotle auth wrapper: {AUTH_WRAPPER}", file=sys.stderr)
        return 2
    if not args.prompt_template.is_absolute():
        args.prompt_template = ROOT / args.prompt_template
    if not args.prompt_template.exists():
        print(f"Missing Codex prompt template: {args.prompt_template}", file=sys.stderr)
        return 2
    if args.watch and args.once:
        print("Use either --once or --watch, not both.", file=sys.stderr)
        return 2
    if not args.watch:
        args.once = True

    cycles = 0
    while True:
        cycles += 1
        try:
            handle_once(args)
        except Exception as exc:  # noqa: BLE001 - this is a long-running supervisor.
            print(f"orchestrator error: {exc}", file=sys.stderr)
            if args.once:
                return 1
        if args.once:
            return 0
        if args.max_cycles and cycles >= args.max_cycles:
            return 0
        time.sleep(args.poll_seconds)


if __name__ == "__main__":
    raise SystemExit(main())
