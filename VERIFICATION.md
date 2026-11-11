# Extraction verification — 2026-11-11

- 152 imported live Lean source files are byte-identical to their originals.
  Mathematics was not rewritten during extraction.
- `python3 scripts/typeiimagic.py verify` passed both exported builds:
  3,212 Lake jobs for the finite-fiber project and 8,132 for the standalone
  development. Existing pinned dependency/build caches were reused locally;
  this was not a clean network installation of mathlib.
- The existing finite-fiber audit and the added later corner/weight audit emitted
  191 theorem axiom reports. The audited theorems contain only `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx` was reported.
- `python3 -m unittest discover -s tests -v` passed 14 tests. They exercise the
  retained advance/halt state machine, dependency gating, saved-state relocation,
  offline dry-run, explicit execution opt-in, reviewed retry and upload context.
  Aristotle/Codex execution is mocked in these tests.
- `python3 scripts/typeiimagic.py check --snapshot` verified 1,355 imported text
  records, 56 indexed returned-source archives, configured packets and the
  dependency graph. Primary README/state/timeline navigation links were checked.
- `ruff check scripts tests` and the focused staged whitespace check passed
  for the new CLI, tests, adapted workflow and root documentation. Historical
  imports retain their original whitespace, including old diff-check warnings.
- Credential-pattern scans of exported text found no literal API keys,
  GitHub tokens, JWTs or long literal credential assignments. Returned archives
  contain the scanned text-only exports, not Git internals or caches.
- The locally installed command help was checked with Aristotle CLI 2.1.0 and
  Codex CLI 0.167.0. No authenticated status request, proof submission or Codex
  closeout was run as part of this extraction.

## Adversarial review

The review checked that imported Lean proofs were unchanged, the actual historical
packets/results/reviews were retained, halts were not converted to accepted
results, ambiguous submissions cannot be reset by the retry command, dry-run is
offline, and the original workspace and service configuration were untouched.
Portability changes are listed separately in `PORTABILITY.md`.

No blocking issue remains in the tested local extraction. Runtime compatibility
with authenticated remote services is not verified. Historical acceptance is not
an independent mathematical audit of all manuscript-specific hypotheses, and
P57C/P59B remain blocked at their recorded obligations. No measurable
fiber-decomposition/type-classification result is claimed by the export.
