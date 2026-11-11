# Aristotle-Codex Orchestrator

This folder contains the local supervisor for the Aristotle/Codex loop.

The loop is deliberately split:

- Aristotle performs focused long-running Lean formalization tasks.
- Codex performs one orchestration pass after an Aristotle task finishes:
  download, inspect, integrate, verify, document, choose the next target, and
  submit it back to Aristotle.

## Usage

Poll once, useful for cron or manual checks:

```bash
python3 scripts/aristotle_codex_loop.py --once
```

Run a long-lived watcher, useful in `tmux`:

```bash
python3 scripts/aristotle_codex_loop.py --watch --poll-seconds 600
```

The watcher is meant for long Aristotle runs.  It does not impose a timeout on
remote formalization work; it polls until the recorded Aristotle task reaches a
terminal status.  By default, `--codex-timeout-seconds 0` also leaves the local
Codex integration pass untimed.  Pass a positive value only when deliberately
debugging a bounded local run.

Dry-run the Codex prompt without invoking Codex:

```bash
python3 scripts/aristotle_codex_loop.py --once --dry-run
```

The default `--blueprint-gate-mode strict` blocks real formalization packets
that do not cite the current manifest blueprint path, are older than that
blueprint file, or cannot be tied to a `[[target]]` in `MANIFEST.toml`.
Use `--blueprint-gate-mode warn` only for a deliberate one-off integration of
an old completed Aristotle result; the generated Codex prompt will still carry
the gate report and must not use the stale packet as authority for follow-up
work.  `--blueprint-gate-mode off` is reserved for non-mathematical smoke tests
or local debugging.

Run the two-round toy smoke test lane:

```bash
python3 scripts/aristotle_codex_loop.py \
  --watch \
  --poll-seconds 60 \
  --prompt-template aristotle/orchestrator/smoke_test_prompt.md \
  --user-goal "two-round Aristotle/Codex smoke test on toy Nat lemmas"
```

The smoke test uses `TOY-ROUND-001` and `TOY-ROUND-002`.  Round 1 asks
Aristotle to create `Formalization/Test/LoopToy.lean` with `toy_zero_add`.
When round 1 completes, Codex should integrate it and submit round 2.  Round 2
adds `toy_zero_add_succ` using the first theorem.  When round 2 completes,
Codex should mark the smoke test complete and submit no further toy tasks.

The script reads the most recent active `[[aristotle_packet]]` in
`MANIFEST.toml` whose status is `sent_to_aristotle_queued`,
`sent_to_aristotle_in_progress`, or `sent_to_aristotle_running`.

When the corresponding Aristotle task becomes `COMPLETE`, `FAILED`,
`CANCELLED`/`CANCELED`, or `BLOCKED`, the script first runs the
current-blueprint extraction gate.  If the gate passes, it writes a prompt log
under `aristotle/logs/` and invokes:

```bash
codex exec --cd . --sandbox danger-full-access --json
```

Codex then performs exactly one orchestration pass and exits.  The supervisor
records handled task IDs in `aristotle/orchestrator/loop_state.json`, so a
restart does not re-handle the same Aristotle result unless `--force` is used.

The Codex handoff prompt requires a second, round-trip sync gate.  After a
result is downloaded, Codex must compare returned Lean declarations against the
current blueprint and manifest target.  If Aristotle exposes a changed theorem
shape, missing hypothesis, new mathematical helper, or weakened target, Codex
must update the blueprint/manifest first or record the result as partial or
blocked before any new packet is submitted.

If Aristotle fails or returns a blocked/missing-lemma report, Codex must run a
blocker auto-repair loop before advancing.  The loop classifies the blocker,
records the exact failed theorem shapes and missing prerequisites, runs
writer/reviewer roles for blueprint repair, Lean extraction, source grounding,
Lean feasibility, and manifest/dependency consistency, and repeats repairs
until the affected reviewers approve.  If the obstruction is genuine, Codex
records it explicitly instead of silently narrowing the target.

The supervisor treats `BLOCKED` as a terminal task status and includes a
blocker-repair scan in the generated Codex prompt.  A `REQUIRED` scan result
means the next Codex pass must repair or explicitly record the obstruction
before submitting any follow-up packet.

## Requirements

- `codex` must be installed and logged in.
- Aristotle authentication must work through
  `~/.codex/skills/aristotle-cli/scripts/aristotle-auth.sh`.
- The repository should already contain a submitted Aristotle packet recorded
  in `MANIFEST.toml`.

The loop does not commit or push by default.  It leaves Codex's integration
artifacts in the working tree unless the triggering prompt explicitly asks for
a commit.
