# AGENTS.md

Local instructions for agents working under `formalization/`.

## Purpose

This folder is for a source-backed Lean formalization of the stabilizer-system
and von Neumann algebra type-restriction project.  The immediate goal is to
define the systems, states, Hilbert spaces, concrete represented algebras, and
only then prove type restrictions.

Every Lean definition, theorem, and proof target must first appear in an
explicit natural-language TeX note in `blueprints/`.  These blueprint files are
not scratch prompts: they are the informal source of truth for formalization and
must contain the relevant definitions, theorem statements, assumptions, proof
sketches or proofs, and textbook or lecture-note locators.

## Start Of Work

- Check `git status --short` from the repository root.
- Read this file, `README.md`, `PROGRESS.md`, and `COMMUNICATION.md`.
- Check `MANIFEST.toml` before creating a new target ID.
- Treat all existing blueprint, packet, response, and Lean files as user work.
  Do not overwrite or reflow them without a specific reason.

## Artifact Rules

- `blueprints/`: authoritative informal TeX notes.  A Lean target may not be
  created until its blueprint note exists and contains the relevant informal
  definitions/theorems/proofs.
- `aristotle/packets/`: single-target requests extracted from existing
  blueprint notes.  Packets are not independent mathematical sources.
- `aristotle/responses/`: raw Aristotle outputs.  Do not edit raw responses;
  integrate by copying into Lean files with review.
- `aristotle/logs/`: command logs and blocked-target notes.
- `Formalization/`: Lean source files.
- `agents/`: handoffs and per-agent notes.
- `reviews/`: adversarial or human review reports.

## Blueprint-First Contract

No new Lean declaration, theorem, or proof attempt may be introduced unless an
existing `blueprints/*.tex` file already contains its informal counterpart.
Before editing Lean, check the manifest entry and the blueprint note.  If the
informal note is missing, incomplete, or lacks source locators, update the
blueprint first and stop before formalizing if the mathematical content is not
settled.

Each blueprint note must include, for every target it supports:

- stable ID, e.g. `GNS-001`;
- source locator with book/notes, section/theorem/equation if available, and
  PDF page when known;
- all definitions needed by the target;
- natural-language theorem/lemma statement when applicable;
- assumptions and conventions before they are used;
- proof sketch or complete informal proof, or explicit declaration that the
  target is a definition only;
- intended Lean target name.

Blueprint mathematical content should be written directly in ordinary TeX math
environments.  The optional environment title should begin with the intended
Lean-facing name, or a stable formalization name if the Lean name is not fixed
yet.  If the statement is source-backed, append the source locator in the same
environment title.  If the statement is project-local or newly defined in the
blueprint, keep the same environment style but omit the source locator.

Use this general shape for both sourced and unsourced work:

```tex
\begin{definition}[LeanNameOrFormalName, optional source locator]
...
\end{definition}

\begin{proposition}[LeanNameOrFormalName, optional source locator]
...
\end{proposition}

\begin{proof}
...
\end{proof}
```

For sourced content, the body of the environment should contain the actual
definition, theorem, lemma, proposition, construction, or remark, not merely the
name of a reference.  For theorem-like environments (`lemma`, `proposition`,
`theorem`, `corollary`), include a following `proof` environment with a proof or
proof sketch.  For definition-only targets, no proof is required unless a
well-formedness argument is part of the blueprint.  Do not use separate
`Takesaki Source Fact` or analogous source-fact blocks as the future blueprint
style; source locators belong in the environment title when the statement is
source-backed.  Target bookkeeping such as stable IDs, intended Lean paths,
dependencies, and status may still be recorded with the local macros used by
the blueprint, but those macros are not a substitute for the environment-title
style.

Each Lean declaration derived from a blueprint should include a docstring with:

- blueprint ID;
- blueprint file path;
- source locator;
- whether it is proved, scaffolded, or blocked.

Do not introduce new mathematical content directly in Lean.  Update the
blueprint note first, then extract a packet or edit Lean from that note.

## Aristotle Workflow

Use one packet per target ID.  Packets must cite the blueprint note path and
contain an extract of the source locator, natural-language statement/proof,
existing dependencies, desired Lean declaration, allowed imports, and
constraints:

- no axioms;
- no `sorry` in final integrated Lean;
- no weakening of the theorem statement without recording the change in the
  blueprint and manifest;
- if blocked, return a minimal missing-lemma list.

Raw responses remain in `aristotle/responses/`.  Integrated Lean code must be
checked independently with Lean/Lake before marking the target proved.

## Lean Scope

Use mathlib when possible.  Prefer concrete von Neumann algebras
`VonNeumannAlgebra H`, i.e. subalgebras of bounded operators on a Hilbert space,
for the operator-algebra layer.

The infinite-system dependency chain is:

```text
stabilizer system
-> quasi-local C*-algebra or local-net abstraction
-> state omega
-> GNS Hilbert space H_omega
-> representation pi_omega : A -> B(H_omega)
-> region von Neumann algebra pi_omega(A_region)''
-> type restriction theorem
```

Do not skip the GNS/representation layer for infinite systems.

## Progress Documentation

After substantive work, update `PROGRESS.md` and `MANIFEST.toml`.

Record:

- target IDs touched;
- files changed;
- Aristotle packets sent and responses received;
- Lean commands run and results;
- blockers and missing lemmas;
- source locators still missing.

## Verification

Preferred checks, from narrow to broad:

```bash
lake env lean Formalization/<file>.lean
lake build
```

If Lake or mathlib dependencies are not available, record that explicitly in
`PROGRESS.md` rather than presenting the Lean as verified.
