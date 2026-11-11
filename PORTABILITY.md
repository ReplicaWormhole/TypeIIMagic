# Portability changes to the existing loop

The execution algorithm in `workflow/aristotle_autopilot.py` is copied from the
original supervisor preserved under `history/original-supervisor/`. Submission,
remote status parsing, dependency eligibility, exact-task response naming,
Codex closeout and acceptance/halting logic are retained.

The adaptations are:

1. Repository-relative project/source/packet paths are resolved at runtime.
2. Imported `history/state.json` is read without resetting the queue. New state,
   locks and logs live under ignored `.typeiimagic/`.
3. `ARISTOTLE_BIN` and `CODEX_BIN` replace machine-specific executable paths.
   Original Telegram notifications are disabled; no sender is installed.
4. `--dry-run` is genuinely offline. The original implementation could query
   Aristotle before reaching its dry-run branch and could write state on error.
5. Actual execution requires `--execute`. Codex defaults to `workspace-write`
   rather than the original unrestricted sandbox; an explicit `CODEX_SANDBOX`
   setting remains available for an intentionally configured environment.
6. Codex runs from the repository root, with the specific Lean project named
   in its closeout prompt. This keeps repository-relative source paths valid.
   Upload-only copies of local source policies use `manuscript/`, matching the
   uploaded manuscript layout; originals remain in the provenance record.
7. A small inspection/continuation CLI adds state summaries, chronological
   navigation, provenance checks, build/axiom checks, and explicit reviewed retry
   of a halted packet. Retrying preserves previous outcomes and is protected by
   the supervisor lock. It refuses unresolved active or pending submissions.

`check --snapshot` attests all imported working files against the initial export.
Ordinary `check` permits intentional changes to live sources/packets while still
verifying immutable history and archived returns. Commit source/packet changes
before further remote submissions if you want them recorded in Git history.

All imported text records have an original SHA-256 and an exported SHA-256.
Machine paths are relocated and Markdown navigation adjusted. Returned archives
are text-only exports of the actual original source snapshots; their original
archive hashes, exported hashes and full original member indexes are retained.
No claim is made that the exported tarballs are byte-identical to their originals.

The original tests are retained as historical artifacts. Three original tests
fail against the later original configuration (fixed package-list/initial-wave
expectations and a case-sensitive lane-text expectation). The new tests exercise
the retained state machine and portability behavior without altering those old
records. The mathematical developments are not changed to make tests pass.
