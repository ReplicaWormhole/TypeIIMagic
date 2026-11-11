# TypeIIMagic

## Purpose and scope

Preserve and continue the existing stabilizer/operator-algebra formalization and
its actual Aristotle–Codex development record. Artifacts: Lean code, mathematics,
source-backed history and workflow code. `STATE.md` is the current scope guide.

## Paths

- `lean/finite_fibers/`, `lean/stabilizer/`: live Lean worktrees. Read each local
  AGENTS.md before edits; every theorem retains its explicit hypotheses.
- `workflow/`: adapted original supervisor. `history/original-supervisor/`
  preserves the earlier version.
- `history/`: imported immutable record. Add new records separately; never rewrite
  an old failed/partial result as accepted.
- `sources/manuscript/`: export-time manuscript context. Source locators in older
  packets must be checked against the appropriate historical snapshot.
- `.typeiimagic/`: ignored runtime state/logs. Preserve ambiguous submissions.

## Commands

- Offline status: `python3 scripts/typeiimagic.py status`.
- Historical provenance: `python3 scripts/typeiimagic.py check --snapshot`.
- After intentional live edits: `python3 scripts/typeiimagic.py check`.
- Focused workflow tests: `python3 -m unittest discover -s tests -v`.
- Lean builds and theorem axiom audits: `python3 scripts/typeiimagic.py verify`.
- Read-only queue inspection: `python3 workflow/aristotle_autopilot.py --dry-run`.
- Real remote continuation: `python3 scripts/typeiimagic.py watch --execute`.

Do not run remote continuation merely to test the runner. A halted task requires
review and an explicit resume. Do not reset completed tasks or duplicate an
ambiguous remote submission. Do not install/enable a system timer implicitly.

## Mathematical contract

Separate a state on `q M q` from a trace/weight on all of `M`, finite-region
results from infinite-lattice realization, and central-summand finite-projection
criteria from direct-integral/fiberwise classifications. No new axioms, `sorry`,
`admit`, `opaque`, `unsafe` or proof surrogates in accepted work. Compile success
does not establish the intended physical hypotheses. Retain failed candidates
in history, not in an accepted dependency chain.

## Closeout

Run relevant tests and narrow Lean checks; audit theorem axioms. Review the diff
and public export for source provenance, credentials, unrelated changes and
claim inflation. Keep credentials, caches and runtime logs out of Git. Use a
focused local commit after verified edits; no automatic push or publication.
