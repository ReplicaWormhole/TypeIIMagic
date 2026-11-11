# Aristotle Batch-Packet Loop Goal

Date: 2026-06-25

## Goal

After the currently running Aristotle task finishes, update the
Aristotle/Codex loop so future submissions use larger coherent packets and
route local orchestration work through appropriately cheap agents instead of
always using one large Codex pass.

The new policy should reduce total wall-clock overhead and local token use
while preserving the blueprint-first contract, per-target sync review, and
honest partial/blocked status tracking.

## Current Baseline

Latest committed checkpoint:

```text
5971902 Record Aristotle formalization progress
```

The local watcher has been stopped.  The active remote Aristotle task is still
running:

```text
packet:  aristotle/packets/PAULI-002-TRACE-INCLUDE-2026-06-25.md
project: 573f8f45-0c9f-44cf-8291-d38036466997
task:    9ff89387-5831-424c-b24e-9e7241a0fc47
status:  IN_PROGRESS as of aristotle/logs/orchestrator-20260625T051900Z-573f8f45-tasks.log
```

Do not restart the old watcher before implementing the batch-packet and
token-efficient routing policy.
When this task reaches a terminal status, integrate it under the existing
round-trip sync and review rules, then resume with the new setup.

## Rationale

The current loop is target-driven:

- it watches the most recent active `[[aristotle_packet]]` in `MANIFEST.toml`;
- after terminal status, Codex integrates the result;
- Codex then chooses the next smallest target and submits exactly one focused
  packet.

This is safe but may waste time because each small task pays fixed overhead:
submission, queueing, remote setup, polling, download, local integration,
verification, review, ledger update, and next submission.

Aristotle appears able to handle larger prompts.  The desired change is not to
submit whole blueprint files blindly, but to submit medium-sized coherent
batches.

There is also a separate local-token problem: every terminal Aristotle event
currently invokes a broad Codex orchestration prompt that asks one strong agent
to inspect the task, integrate, verify, review, choose the next target, prepare
the next packet, submit it, and update ledgers.  Standard-theory green-path
cases should not need that much context or model strength.

## Token-Efficient Routing Policy

Split the local loop into deterministic routing plus three agent tiers.

### Deterministic supervisor

No model should be used for work that Python can do reliably:

- poll Aristotle and classify task status;
- parse `MANIFEST.toml`;
- parse packet target IDs, including multi-target packets;
- run the current-blueprint freshness gate;
- run the blocker keyword scan;
- build a compact task summary from logs instead of injecting full logs into
  every prompt;
- select the prompt template and model tier;
- construct the next candidate batch from manifest metadata when the queue is
  unambiguous;
- record prompt size and routing decision under `aristotle/logs/`.

### Fast green-path agent

Use the cheapest reliable Codex model for routine completion cases where all
of the following hold:

- Aristotle status is `COMPLETE`;
- the current-blueprint gate passes for every target in the packet;
- the blocker scan is `NOT_REQUIRED`;
- Aristotle returned declarations for the requested target IDs;
- returned theorem shapes appear to match the packet and blueprint IDs;
- no new source locator, theorem weakening, or mathematical dependency choice
  is required;
- the next candidate batch is already determined by the supervisor.

The fast agent may save raw responses, integrate mechanical Lean/documentation
changes, update `MANIFEST.toml` and `PROGRESS.md`, and instantiate the next
packet from a template.  It must not make new mathematical strategy decisions.

### Standard integration agent

Use a mid-tier model when the result is still ordinary but needs local Lean
judgment:

- import/name/docstring adjustments;
- small implementation-plumbing helpers;
- local build failures that look mechanical;
- packet drafting where the target batch is known but the exact Lean context
  needs summarizing.

The standard agent may repair integration details but must escalate before
changing theorem scope, adding blueprint mathematics, or reordering major
dependencies.

### Strong repair/strategy agent

Use the current strong Codex-style orchestration only for red-path cases:

- Aristotle status is `FAILED`, `BLOCKED`, `CANCELLED`, or partial;
- blocker scan is `REQUIRED`;
- Lean still fails after simple integration repair;
- Aristotle changed, weakened, split, or renamed a theorem shape;
- source locators or blueprint content are missing;
- the next target choice is mathematically nontrivial;
- the target touches GNS, represented von Neumann algebras, or type
  classification;
- an adversarial blocker-repair loop is required.

Only this tier should receive the full blocker-repair prompt.

## Prompt And Context Budget

Do not pass full logs or broad repository instructions to every agent.  The
supervisor should produce a compact prompt containing:

- packet ID, target IDs, project ID, task ID, and terminal status;
- paths to full logs and archives;
- a short extracted task-output summary;
- the current-blueprint gate report;
- the blocker scan report;
- the routing decision and permitted actions for that tier;
- explicit file paths the agent should inspect.

Full Aristotle output should remain available on disk, but should be read only
when the selected tier needs it.

## Batch Packet Policy

Replace "next smallest target" with "next smallest coherent batch".

A coherent batch should normally satisfy all of the following:

- 2--5 closely coupled target IDs;
- same blueprint file when practical;
- same Lean file or nearby module boundary when practical;
- dependencies form a short local chain rather than unrelated branches;
- every target has a current blueprint environment or explicitly quoted
  supporting environment;
- every target has a desired Lean declaration or acceptable fallback shape;
- no cross-layer jumps such as Pauli + GNS + type theory in one batch.

The packet should still forbid:

- Lean axioms;
- final `sorry`, `admit`, or `implemented_by`;
- silent theorem weakening;
- touching unrelated target layers.

## Packet Format Change

Update the packet convention from a single `# Target:` to either:

```text
# Targets: PAULI-002, QL-001
```

or an explicit metadata block:

```text
target_ids:
- PAULI-002
- QL-001
```

Each batch packet should include:

- blueprint path for every target;
- exact blueprint excerpt for every target or supporting environment;
- source locator for every target;
- informal proof sketch or definition-only note for every target;
- current Lean context;
- desired Lean declaration shape for every target;
- expected response table with per-target status:
  `proved | partial | blocked`.

The Aristotle response should be treated as target-wise, not all-or-nothing.
If one target blocks, integrate checked proved pieces and record the blocked
piece precisely.

## Required Code And Policy Updates

Update these files:

```text
aristotle/orchestrator/codex_orchestration_prompt.md
aristotle/orchestrator/README.md
COMMUNICATION.md
scripts/aristotle_codex_loop.py
```

Add these orchestration files:

```text
aristotle/orchestrator/model_policy.toml
aristotle/orchestrator/green_path_prompt.md
aristotle/orchestrator/standard_integrate_prompt.md
aristotle/orchestrator/repair_prompt.md
```

Required behavior changes:

1. The Codex handoff prompt must tell Codex to choose the next smallest coherent
   batch, not the next smallest single target.
2. The prompt must require per-target round-trip sync verdicts.
3. The prompt must require follow-up batches to contain only remaining partial
   or blocked prerequisites, not already integrated proved statements.
4. The current-blueprint gate must accept multiple target IDs.
5. The gate must validate that every target ID exists in `MANIFEST.toml`.
6. The gate must validate that every target cites the exact current manifest
   `tex` path.
7. The gate must validate that packet mtime is newer than every cited
   blueprint file.
8. The gate must fail if any target ID is absent from its cited blueprint.
9. The generated Codex prompt must show the full multi-target gate report.
10. The loop must classify each terminal Aristotle result as
    `green`, `standard`, or `repair`.
11. The loop must choose the Codex model and prompt template from
    `model_policy.toml`, with CLI overrides still available for manual runs.
12. The green-path prompt must be narrow and must forbid mathematical strategy
    decisions.
13. The standard prompt must allow Lean integration repairs but require
    escalation for theorem-shape or blueprint/source changes.
14. The repair prompt must retain the existing blocker auto-repair rules and
    strong-agent review expectations.
15. The loop must log the routing decision, selected prompt, selected model,
    and approximate prompt size under `aristotle/logs/`.
16. The supervisor should avoid injecting full task logs into green-path
    prompts; it should provide paths and compact excerpts instead.

Do not weaken the strict gate.  Generalize it from single-target to
multi-target validation.

Do not make weak agents responsible for mathematical scope decisions.  Their
contract is to execute prepared, checked transitions; strong agents remain the
fallback for ambiguity.

## First Batches After Current Task

After `PAULI-002-TRACE-INCLUDE` completes:

1. If `traceCoeff_include` is proved or a usable checked version is integrated,
   submit a blueprint-007 local-net batch:

   ```text
   QL-001, QL-002
   ```

   Scope: local-net/quasilocal algebra interface and finite-local inclusions.

2. If `traceCoeff_include` blocks, submit a PAULI repair batch:

   ```text
   PAULI-002 missing API lemmas + traceCoeff_include
   ```

   Scope: only the missing finite matrix/tensor trace facts needed for the
   coefficient-inclusion lemma.

3. Once Pauli/quasilocal basics are stable, submit a state batch:

   ```text
   STATE-002, STATE-003, STATE-004
   ```

   Scope: finite projection-code state, compatible local states, and
   quasilocal extension/restriction facts.

Avoid batching GNS, represented von Neumann algebras, and type-classification
targets until the Pauli/quasilocal/state layer is stable.

## Verification For The Policy Change

Before restarting the loop:

```bash
python3 -m py_compile scripts/aristotle_codex_loop.py
python3 scripts/aristotle_codex_loop.py --help
python3 -c 'import tomllib; tomllib.load(open("MANIFEST.toml","rb")); print("MANIFEST.toml ok")'
```

Also run at least one dry-run gate check on a synthetic or real multi-target
batch packet before submitting it to Aristotle.  The dry-run should exercise at
least one green-path routing case and one repair-path routing case.  Record the
selected tier, selected prompt, selected model, and prompt-size estimate in the
log and in `PROGRESS.md`, then add a review under `reviews/`.

## Resume Checklist

1. Poll current Aristotle task:

   ```bash
   <original-home>/.codex/skills/aristotle-cli/scripts/aristotle-auth.sh tasks 573f8f45-0c9f-44cf-8291-d38036466997
   ```

2. If complete, download and integrate the result for
   `PAULI-002-TRACE-INCLUDE`.
3. Run local Lean verification and round-trip sync review.
4. Implement the batch-packet and token-efficient routing policy above.
5. Dry-run the new multi-target gate and routing classifier.
6. Submit exactly one coherent batch packet.
7. Restart the watcher only after the new packet is recorded in
   `MANIFEST.toml`.
