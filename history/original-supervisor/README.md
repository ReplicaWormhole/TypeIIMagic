# Dependency-gated Aristotle/Codex autopilot

This is the live replacement for the archived
`work/OLD/formalization/scripts/aristotle_codex_loop.py`. It coordinates the
finite-fiber project and the active two-lane P47--P61 plan in the standalone
stabilizer-hyperfinite project.

The work is deterministic, packet-driven, and dependency-gated:

- finite-fiber lane: FF15 (full-word multiplication), then FF16--FF23 through
  a concrete finite-range support corner and the final no-type-III
  central-summand theorem;
- stabilizer two-lane program: the approved `PLAN.md` graph P47--P59. P47,
  P48, P52, and P54 are the initial independent wave. Later packets are
  submitted only after all declared predecessors have been integrated and
  received an accepted Codex `advance` decision. Optional P60 and P61 are
  prepared but disabled pending separate approval.

Lane G contains a mandatory analytic chain P49A--P49C between the finite C-star
trace and P50: strong closedness of concrete von Neumann algebras, the analytic
double-commutant theorem, and Kaplansky unit-ball density. These packets must
produce actual proved theorems. The supervisor will not release P50 on the basis
of a supplied density interface.

The prior P37--P41 execution and P41 partial halt remain preserved in
`state.json`, logs, and project reviews. P42--P46 are historical drafts and are
not part of the live queue.

There is at most one active Aristotle task per packet job, so independent ready
packets may run remotely in parallel. Closeouts are still processed serially by
the supervisor. On a terminal result, the runner invokes one Codex closeout in
that project's directory. Codex must
download and quarantine the result, integrate only the allowed candidate,
verify it, and write a review. The runner advances only when Codex's final
message contains both:

```text
AUTOPILOT_ACCEPTED: yes
AUTOPILOT_DECISION: advance
```

Any failed, partial, blocked, malformed, or unverified closeout halts that packet
job and keeps all dependents ineligible; unrelated ready packets remain
independent. The runner never commits, pushes,
unpacks an archive over a project, or invents a task.

## Mobile alerts

When `[notifications] telegram_enabled = true` in `autopilot.toml`, the runner
sends one short Telegram message when a packet is halted by a failed, partial,
blocked, or unverified Codex closeout, and when the supervisor itself raises an
unexpected error. Repeated polling does not resend the same alert reason. The
sender is the local `<original-home>/.local/bin/tg-send`; its credentials remain in
`<original-home>/.config/codex-telegram.env` and are never copied into the project or
logs. Successful packets do not generate Telegram notifications.

For every submission it creates a temporary upload snapshot containing the
Lean project plus only the canonical `manuscript/main.tex` and bibliography
files. The snapshot is removed after upload and does not change either Lean
worktree.

`AUTONOMY_POLICY.md` is included with every upload. The full project snapshot
also contains `AGENTS.md`, `PLAN.md`, and the two-lane decision record. The
submission and closeout prompts explicitly require auditing the packet's lane,
predecessors, permitted gate, and forbidden downstream claims. The policy permits
Aristotle to develop missing project-local theory or use a different proof
route, provided it proves a recognizable form of the manuscript theorem and
records every new premise and remaining gap.

Inspect the prepared queues without network activity:

```bash
python3 work/aristotle_autopilot/aristotle_autopilot.py --once --dry-run
```

Start the overnight watcher from any directory:

```bash
python3 workflow/aristotle_autopilot.py --watch
```

Alternatively, install the supplied user-systemd units (without enabling them
yet) and then start the timer:

```bash
mkdir -p ~/.config/systemd/user
cp workflow/aristotle-autopilot.service ~/.config/systemd/user/
cp workflow/aristotle-autopilot.timer ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable --now aristotle-autopilot.timer
```

The timer is not installed or enabled by this repository change.

State and logs are kept under `work/aristotle_autopilot/`. The lock prevents a
cron invocation and a manually started watcher from submitting duplicate jobs.
The runner uses the Aristotle auth wrapper, so the API key is not printed and
does not depend on an interactive `.bashrc`.

Before enabling unattended execution, run one dry pass and then one real
`--once` pass while watching the two project worktrees. The first real pass
will submit FF15 and P37; it will not download or integrate anything until
those remote tasks reach a terminal state.
