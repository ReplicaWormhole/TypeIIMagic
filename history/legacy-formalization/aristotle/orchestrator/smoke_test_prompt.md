# Two-Round Aristotle/Codex Smoke Test

This Codex invocation was started by `scripts/aristotle_codex_loop.py` for a
toy two-round orchestration test.  This is not part of the stabilizer/type
formalization, except as a test of the automation.

## Smoke-Test Goal

{{USER_GOAL}}

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

## Required Actions

1. Check `git status --short` and preserve unrelated dirty work.
2. Download the completed Aristotle project under
   `aristotle/responses/smoke/` if not already downloaded.
3. Inspect the returned archive and integrate only the toy files and raw
   response records relevant to the smoke test.
4. Verify locally with:
   - `lake build Formalization`;
   - manifest parse via Python `tomllib`;
   - placeholder scan for `sorry`, `admit`, `axiom`, and `implemented_by`;
   - focused axiom checks for new toy declarations when practical.
5. Update `MANIFEST.toml`, `PROGRESS.md`, and add or update a smoke-test review
   under `reviews/`.

## Two-Round Logic

If the completed packet is `TOY-ROUND-001`:

- Integrate Aristotle's first-round result.
- Confirm that `Formalization.Test.LoopToy.toy_zero_add` is present and builds.
- Submit exactly one next Aristotle packet:
  `aristotle/packets/TOY-ROUND-002.md`.
- Record the new project/task IDs in `MANIFEST.toml` and `PROGRESS.md`.
- Stop.  Do not attempt the second theorem locally.

If the completed packet is `TOY-ROUND-002`:

- Integrate Aristotle's second-round result.
- Confirm that both
  `Formalization.Test.LoopToy.toy_zero_add` and
  `Formalization.Test.LoopToy.toy_zero_add_succ` are present and build.
- Mark the smoke test complete in `MANIFEST.toml` and `PROGRESS.md`.
- Stop.  Do not submit any further Aristotle tasks.

## Constraints

- This is a smoke test.  Do not submit or edit real stabilizer, GNS,
  operator-algebra, or type-classification targets.
- No axioms.
- No final `sorry`, `admit`, or `implemented_by`.
- Do not push to remotes.
- Do not delete unrelated dirty work, including `../scaffold/`.
