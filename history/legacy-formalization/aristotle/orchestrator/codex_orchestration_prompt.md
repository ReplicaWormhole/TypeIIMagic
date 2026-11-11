# Aristotle Completion Orchestration

This Codex invocation was started by `scripts/aristotle_codex_loop.py` because
an Aristotle task reached a terminal state.

## User Goal

{{USER_GOAL}}

Codex is the orchestration model here, not the main Lean prover.  Aristotle
does the focused long-running formalization work.  Your job is to perform one
bounded orchestration step, then stop.

## Completed Aristotle Task

- Packet ID: `{{PACKET_ID}}`
- Packet path: `{{PACKET_PATH}}`
- Project ID: `{{PROJECT_ID}}`
- Task ID: `{{TASK_ID}}`
- Terminal status: `{{TASK_STATUS}}`
- Task log: `{{TASK_LOG}}`

Task output:

```text
{{TASK_OUTPUT}}
```

## Gate Report

The supervisor ran the current-blueprint extraction gate before starting this
Codex pass.

```text
{{GATE_REPORT}}
```

## Blocker Repair Supervisor Scan

The supervisor scanned the terminal Aristotle status and task output for
blocked or missing-prerequisite signals.

```text
{{BLOCKER_REPORT}}
```

## Required Actions

1. Start by checking `git status --short` and reading the local policy files
   relevant to this repository.
2. Inspect the completed Aristotle task via the Aristotle CLI.  Download its
   result archive under `aristotle/responses/` if it has not already been
   downloaded.
3. Inspect the returned diff/artifacts.  Integrate only useful source files and
   raw response records.  Do not overwrite local bookkeeping with stale files
   from the returned archive.
4. Verify locally.  Use at least:
   - `lake build Formalization` when Lean files changed;
   - manifest parse check via Python `tomllib` when `MANIFEST.toml` changed;
   - placeholder scan for `sorry`, `admit`, `axiom`, and `implemented_by`;
   - focused axiom checks for important new proved declarations when practical.
5. Run the round-trip sync gate before updating target status:
   - compare each returned Lean declaration, theorem statement, helper
     definition, and dependency against the current manifest target and its
     `blueprints/*.tex` source;
   - if Aristotle strengthened, weakened, renamed, split, or added mathematical
     content, update the blueprint first so the TeX statement/proof sketch is a
     faithful informal image of the integrated Lean, or mark the Lean result
     `partial`/`blocked` and do not treat it as synced;
   - if a helper is purely implementation plumbing, record it as such in the
     review instead of promoting it to mathematical blueprint content;
   - if a new missing prerequisite is discovered, add or update the manifest
     blocker and the blueprint dependency text before submitting follow-up work.
6. If the blocker supervisor scan says `REQUIRED`, or if Aristotle failed,
   returned `blocked`, or exposed missing mathematical prerequisites, run the
   blocker auto-repair loop before choosing a new target:
   - classify the blocker as blueprint gap, Lean/API gap, source-locator gap,
     dependency-order gap, or genuine mathematical obstruction;
   - create or update a blocker note under `agents/` or `reviews/` with the
     exact returned theorem shapes, error text, missing lemmas, and affected
     blueprint/manifest targets;
   - spawn or otherwise run independent writer/reviewer passes when the
     available runtime supports agents.  At minimum use separate roles:
     Blueprint Repair Writer, Lean Extraction Writer, Source-Grounding
     Reviewer, Lean-Feasibility Reviewer, and Manifest/Dependency Reviewer;
   - the writers may edit blueprints, manifest status/dependencies, and packet
     plans, but may not silently weaken the user-level theorem scope;
   - reviewers must return `APPROVED` or `REVISE`.  If any reviewer returns
     `REVISE`, fix the confirmed issue and rerun the affected reviewers;
   - do not submit a follow-up Aristotle packet until every affected reviewer
     has returned `APPROVED`, or until the blocker is explicitly recorded as a
     genuine mathematical/API obstruction with no honest repair available in
     this orchestration pass.
7. Update `MANIFEST.toml`, `PROGRESS.md`, and add a review under `reviews/`.
   Clearly distinguish proved, checked partial, blocked, and merely submitted
   statuses.  The review must contain a `Blueprint/Lean sync gate` section with
   a PASS/PARTIAL/BLOCKED verdict and the exact blueprint files checked or
   changed.  If the blocker auto-repair loop ran, the review must also contain
   a `Blocker auto-repair gate` section listing writer/reviewer roles, verdicts,
   files changed, and any unresolved obstruction.
8. Before preparing the next packet, run the current-blueprint extraction gate
   manually:
   - choose a target ID from `MANIFEST.toml`;
   - read its current `tex` blueprint file;
   - extract the source locator, statement, proof sketch, dependencies, and
     intended Lean path from that current file;
   - ensure the packet cites the exact manifest `tex` path and contains no
     mathematical content absent from the blueprint;
   - if the blueprint is incomplete or stale, update and review it before
     submitting to Aristotle.
9. Choose the next smallest Aristotle target that advances the user goal.
   Prepare exactly one focused packet under `aristotle/packets/` and submit it
   to Aristotle with the authenticated wrapper only after the extraction gate
   passes.
10. Record the new Aristotle project/task IDs and logs in `MANIFEST.toml` and
   `PROGRESS.md`.
11. Stop after one orchestration cycle.  Do not keep polling inside Codex.

## Constraints

- Do not attempt the whole formalization inside Codex.
- Do not introduce Lean axioms, final `sorry`, `admit`, or `implemented_by`.
- Do not silently weaken source-backed theorem statements.
- Do not submit a follow-up Aristotle packet if the packet is older than the
  current blueprint, fails to cite the manifest blueprint path, or contains
  theorem/definition content not present in the blueprint.
- Do not mark a target `lean_checked`, `proved`, or equivalent unless the
  round-trip sync gate passed or the review explicitly records the remaining
  blueprint/Lean mismatch as partial or blocked.
- Do not skip the blocker auto-repair loop merely because Aristotle returned a
  missing-lemma list.  Missing prerequisites should be turned into reviewed
  blueprint/manifest repairs or explicitly recorded as genuine obstructions.
- Do not push to remotes.
- Do not delete or modify unrelated dirty work, including `../scaffold/`.
- Commit only if the user explicitly requested committing in the current
  triggering context; otherwise leave the changes documented but uncommitted.
