# Manuscript-Only Context Policy

## Source authority

For manuscript-facing statements, the sole mathematical source is
`sources/manuscript/main.tex`.
The local summary and locator record is `SOURCE-CONTRACT.md`. Do not modify
the manuscript from this project.

Every claim described as coming from the manuscript must identify an exact
line range in `main.tex`. Repository history, earlier chat context, and other
artifacts are not substitute sources.

## Context firewall

Do not introduce, assume, or attribute to the manuscript any gLU,
refinement, layer-coherence, or finite-coordinate construction unless it is
present in the cited manuscript lines or is explicitly introduced as a new
auxiliary assumption. A Lean file compiling does not make its unstated
physical or operator-algebraic hypotheses part of the manuscript.

Classify each item as one of:

1. **manuscript-derived**: exact source locator and no stronger conclusion;
2. **auxiliary assumption**: explicitly labelled and used only conditionally;
3. **Lean infrastructure**: reusable formal mathematics that makes no source
   claim; or
4. **legacy exploratory work**: retained for reference but unavailable as
   support for a manuscript-derived assertion.

`CONTEXT-LEDGER.md` records the current legacy items.

## Current formalization boundary

The target discussed in the manuscript is the short-range regional-algebra
statement at `main.tex:1740-1752`; its proposed proof is at
`main.tex:1891-2004`. Keep separate the asserted algebraic identification,
the product-state/GNS steps, the unformalized operator-algebraic completion and
spatial tensor-product steps, and the trace conclusion. A tracial state is
appropriate only for the finite pure-sector case. The infinite pure-sector
target instead calls for a faithful normal semifinite trace/weight when the
required hypotheses and von Neumann infrastructure are supplied.

## Aristotle task packets

Every new task under `aristotle_tasks/` must begin with exactly one context
declaration:

- `Source basis: main.tex:<line range>` for a manuscript-facing task; or
- `Infrastructure only:` for reusable Lean material that makes no manuscript
  claim.

It must then list every auxiliary assumption, state its exact Lean target, and
say whether its conclusion is conditional. A task may not cite a legacy
artifact as its source basis. Use `aristotle_tasks/TEMPLATE.md` for new
packets.

## Active two-lane plan execution

The active Codex/Aristotle execution plan is `PLAN.md`, with the approval
record in `work/TWO-LANE-FORMALIZATION-DECISION.md`. Before starting any new
package in the P47--P61 program, read both files and the closeout/audit record
for every declared predecessor.

Every future packet must include a `Plan alignment` section containing:

1. the exact package identifier and its lane: `G` (general finite-corner and
   central type-III exclusion), `H` (explicit local-hyperbolic tensor-factor
   model), `shared`, or `reconnection`;
2. the predecessor packages that have already been integrated, or `none` for
   a foundation package;
3. the exact gate this package is permitted to discharge; and
4. downstream claims it is forbidden to make.

The Aristotle prompt must explicitly instruct the worker to read the active
plan and respect this section. A package may use only integrated, compiled
predecessors; a finished remote job is not a dependency until it has passed
the local semantic audit. Do not infer a theorem from a later package, and do
not submit a dependent packet before its listed prerequisites are integrated.

For Lane G, the required conclusion is a nonzero finite **projection** in
every nonzero central summand; a finite-dimensional subalgebra is not enough.
For Lane H, do not call the local algebra a factor until the spatial tensor
factorization and factorhood of both factors are proved. Neither lane may
claim a global trace/weight unless it constructs or explicitly assumes one.

## Verification and reporting

Report Lean compilation separately from mathematical validation. For each
manuscript-facing milestone, state which source clauses are represented, which
assumptions remain external, and which analytic/von Neumann-algebraic claims
are not yet formalized in the pinned Mathlib version.
