# TypeIIMagic

This repository contains a partial Lean formalization of the stabilizer-system
results discussed in Sections II.A–C of
[Infinite magic and the emergence of the continuum](https://arxiv.org/abs/2610.20790).
It preserves both the formalization and the development record of the
Codex–Aristotle workflow that produced it.

## Project status

As of November 2026, Aristotle
[no longer supports Lean-only projects](https://aristotle.harmonic.fun/docs/overview).
Consequently, this project's automated formalization workflow is discontinued
in its current form.

The existing Lean development can still be built and checked locally.
The orchestration code and saved state are preserved, but continuing the
automated workflow would require adapting it to another supported backend.
The continuation instructions below document the historical workflow.

## How the formalization was developed

The paper's proofs served as a mathematical blueprint from which Codex
prepared formalization packages for Aristotle. These packages are preserved in
[`lean/finite_fibers/aristotle_tasks/`](lean/finite_fibers/aristotle_tasks/)
and [`lean/stabilizer/aristotle_tasks/`](lean/stabilizer/aristotle_tasks/).

A Python supervisor,
[`workflow/aristotle_autopilot.py`](workflow/aristotle_autopilot.py),
was configured to poll Aristotle at five-minute intervals. When a task
finished, the supervisor downloaded its output and invoked Codex to review
the result, integrate acceptable changes, and run Lean builds and axiom checks.
Following an accepted review, the supervisor submitted the next prepared
package whose dependencies had been accepted. Partial or rejected results
halted the affected queue.

The repository retains the task packets, returned artifacts, prompts,
integration reviews, Codex traces, and supervisor state.
[`history/TIMELINE.md`](history/TIMELINE.md) provides a chronological entry
point into this record.

The formalization remains incomplete. Proved results, explicit assumptions,
partial results, and unresolved obligations are distinguished in
[`STATE.md`](STATE.md).

## Read the current state

Python 3.11 or newer is sufficient for inspection; no account or API call is needed.

```bash
python3 scripts/typeiimagic.py status
python3 scripts/typeiimagic.py history
python3 scripts/typeiimagic.py check --snapshot
```

The imported state records **36 `advance` and 4 `halt` decisions**. Those are
historical review decisions, not 36 independently re-established mathematical
results. The current configured queues contain 24 completed jobs, 5 disabled
jobs, 2 halted jobs and 2 waiting jobs.

- The finite-fiber sequence FF15–FF23 is recorded as accepted.
- P57C halted because the required completed vacuum-ITP identification was missing.
- P59B halted because the returned GNS bridge used `sorry`/`sorryAx`.
- P59R waits on both of those bridges; P59T waits on P59R.

See [STATE.md](STATE.md) for theorem locators and the exact mathematical boundary.

## See how it happened

Start with [the chronological decision record](history/TIMELINE.md). Each entry
links to the packet and original closeout. The underlying records are:

| Path | Contents |
| --- | --- |
| `lean/finite_fibers/` | The finite-Pauli, stabilizer, GNS, full-corner and central-summand Lean package |
| `lean/stabilizer/` | The actual standalone development, including the later corner trace, ultraweak-normality and two-lane work |
| `history/logs/` | Original submission/status logs, closeout prompts, final reviews and Codex JSONL traces, with local paths relocated |
| `history/returns/` | 56 text-only returned-source archives, kept separate from the live Lean worktrees |
| `history/archives.json` | Original archive hashes, exported archive hashes and member indexes |
| `history/investigations/` | Earlier blueprints, tasks, integration reviews and handoffs |
| `history/state.json` | The preserved supervisor state; never overwritten by continued runs |
| `history/original-supervisor/` | The previous supervisor and configuration before the portability changes |
| `workflow/` | That supervisor adapted to this repository layout |
| `sources/manuscript/` | The source manuscript snapshot and bibliographies, supplied as context to new uploads |

The original source revisions and uncommitted state are recorded in
[history/source-revisions.json](history/source-revisions.json). Importing the
existing uncommitted work does not fabricate historical Git commits. File hashes
and path-relocation records are in [history/files.json](history/files.json).
No original credentials, dependency caches, Git internals or live notification
configuration are required by the export.

## Build and check the mathematics

Both Lean projects pin Lean/mathlib 4.28.0, with the original Lake manifests.
After installing `elan`, prepare the dependencies in each project:

```bash
(cd lean/finite_fibers && lake exe cache get)
(cd lean/stabilizer && lake exe cache get)
python3 scripts/typeiimagic.py verify
```

`verify` builds both exported developments and checks the existing finite-fiber
axiom audit plus selected later corner/weight theorems. It rejects `sorryAx` or
unexpected axioms in those audits. It does not prove that the mathematical
hypotheses of a conditional theorem hold in an additional physical model.

```bash
python3 -m unittest discover -s tests -v
```

The workflow tests run the actual supervisor state machine with external commands
mocked. They do not consume Aristotle credits or invoke Codex.

## Continue the same loop

Install the Aristotle CLI and Codex CLI, authenticate them locally, and supply
`ARISTOTLE_API_KEY` in your environment. Alternatively set `ARISTOTLE_BIN` to an
absolute path to your existing authenticated wrapper. Set `CODEX_BIN` if Codex
is not on `PATH`. Credentials belong outside this repository.

```bash
# Inspection is offline and does not create live state.
python3 workflow/aristotle_autopilot.py --once --dry-run

# Continue from the imported state, with a five-minute polling interval.
python3 scripts/typeiimagic.py watch --execute
```

The loop reads `history/state.json` until it first needs to persist a transition;
subsequent state and logs go to ignored `.typeiimagic/`. It does not reset old
results or resubmit completed packets. Ready independent packets may run in
parallel; Codex closeouts are serial. No system service is installed by cloning
or inspecting this repository.

**The imported loop is halted on real proof obligations.** Starting the watcher
preserves those halts. After reviewing/repairing a halted packet and reconciling
its source locators, explicitly re-enable that retry:

```bash
python3 scripts/typeiimagic.py resume P57C \
  --review-note "Describe the reviewed repair and its source alignment here" --execute
python3 scripts/typeiimagic.py once --execute
```

`resume` records the note, retains earlier outcomes, and refuses ambiguous active
submissions. It does not submit a task itself. P59B can be resumed in the same
way. A clone cannot resume another person's private remote task without access
to the original Aristotle account; the returned artifacts and decisions remain
inspectable offline.

The retained Codex closeout contract requires scoped integration, local Lean
checks, an axiom audit, a review, and explicit `AUTOPILOT_ACCEPTED` /
`AUTOPILOT_DECISION` markers. Its default sandbox is now `workspace-write`;
`CODEX_SANDBOX` can explicitly override it. The watcher performs real remote work
only when `--execute` is supplied.

See [PORTABILITY.md](PORTABILITY.md) for the small differences from the original
runner, including the offline dry-run fix. No new mathematical proof is claimed
by this repository extraction. No license has been selected in this snapshot.
