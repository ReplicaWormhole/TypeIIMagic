# Wait Handoff: Global Blueprint-Suite Aristotle Run

Date: 2026-06-22

## Current State

All completed formalization blueprints were submitted to Aristotle as one
explicitly approved global project run.

Aristotle project:

```text
588bebdf-9fc8-4828-a058-6874e367efa8
```

Packet:

```text
aristotle/packets/GLOBAL-BLUEPRINT-SUITE-2026-06-22.md
```

Submission log:

```text
aristotle/logs/2026-06-22-global-blueprint-suite-submit.log
```

Last checked status:

```text
RUNNING
```

It is fine to close the computer.  The Aristotle job is remote; the local
machine only needs to be reopened later to poll and download results.

## Important Warning

The submit command printed:

```text
WARNING: Your Lean toolchain version (leanprover/lean4:v4.29.1) does not match Aristotle's.
Aristotle works best with Lean Toolchain leanprover/lean4:v4.28.0
```

Treat any returned Lean archive as untrusted until it builds locally with the
project's `lean-toolchain`.

## What Was Sent

The full `formalization/` Lean project was uploaded with:

- `AGENTS.md`, `README.md`, `COMMUNICATION.md`, `PROGRESS.md`,
  `MANIFEST.toml`;
- source ledger `blueprints/000-source-ledger.tex`;
- blueprints `001` through `013`;
- current Lean files under `Formalization/`;
- the global packet asking Aristotle to formalize as much as possible in
  dependency order and return either a compiling patch/archive or a
  target-by-target blocker list.

## When Resuming

From the repository root:

```bash
cd formalization
<original-home>/.codex/skills/aristotle-cli/scripts/aristotle-auth.sh list --limit 5
```

If project `588bebdf-9fc8-4828-a058-6874e367efa8` is still `RUNNING`, wait and
poll again later.

If it is complete or idle with downloadable results, download to a temp archive:

```bash
<original-home>/.codex/skills/aristotle-cli/scripts/aristotle-auth.sh download 588bebdf-9fc8-4828-a058-6874e367efa8 --destination /tmp/aristotle-global-blueprint-suite-result.tar.gz
```

Then inspect before applying:

```bash
mkdir -p /tmp/aristotle-global-blueprint-suite-result
tar -tzf /tmp/aristotle-global-blueprint-suite-result.tar.gz | sed -n '1,120p'
tar -xzf /tmp/aristotle-global-blueprint-suite-result.tar.gz -C /tmp/aristotle-global-blueprint-suite-result
```

Expected review steps:

1. Read Aristotle's status, target lists, missing lemmas, and changed Lean
   files.
2. Do not overwrite local work blindly.  Diff returned files against the
   current checkout.
3. Integrate only source-traceable Lean changes that respect the blueprint
   statements.
4. Run:

```bash
lake build
```

5. Save raw Aristotle output under `aristotle/responses/`.
6. Update `MANIFEST.toml`, `PROGRESS.md`, and add a review under `reviews/`.

## Current Local Verification Before Waiting

Before this handoff, local `lake build` succeeded and the manifest parsed.
The new global packet and submission log were added after the global submit.

## Scope Reminder

The final classification target remains scoped to canonical stabilizer
projection states on finite or countably infinite regions.  Do not accept a
returned theorem that silently generalizes to arbitrary logical states, gLU
normal forms, or geometrically local Clifford implementations.
