# Remaining Blueprint Suite Goal

Date: 2026-06-22

## Goal

Complete the remaining source-backed TeX blueprint suite needed before further
Lean extraction for the canonical stabilizer projection-state von Neumann
algebra type classification.

The goal is to turn the remaining `planned_in_master_blueprint` and
`blueprint_draft` targets in `MANIFEST.toml` into dedicated prerequisite
blueprint notes, each with enough mathematical content to support later
Aristotle packets or direct Lean formalization.  This goal does not authorize
new Lean declarations, Aristotle submissions, or theorem weakening.

## Current Baseline

Already complete or separately covered:

- `SYS-001`: algebraic stabilizer system over `F2`;
- `STATE-001`: canonical stabilizer coefficient rule;
- `PAULI-002`: finite Pauli algebra basis and normalized trace coefficients;
- `QL-001`: quasi-local qubit algebra or local-net interface;
- `blueprints/006-full-type-classification-dependency-plan.tex`: manifest-level
  dependency plan for the full classification.

Known partial source-locator gaps from the manifest/master plan:

- `STATE-003`: exact C*-inductive-limit state extension locator;
- `VN-002`: center/factor definition locator;
- `PROJ-001`: projection-comparison/Murray-von Neumann locator details.

Authoritative operator-algebra sources:

- `../sources/takesaki_1.pdf`
- `../sources/Takesaki_II.pdf`
- `../sources/Takesaki_III.pdf`

Operator-algebra blueprint targets must be based on Takesaki wherever Takesaki
contains the needed definition, theorem, proposition, corollary, lemma, or
remark.  Other operator-algebra sources may be used only as supplements,
cross-checks, or fallback sources for facts not located in Takesaki.

The stabilizer-system definitions and stabilizer-side algebraic reductions may
remain project-local, using Gottesman, project proof note 004, and direct
finite-dimensional arguments as appropriate.

## Takesaki Traceability Rule

For every operator-algebraic `definition`, `theorem`, `lemma`, `proposition`,
`corollary`, `remark`, or analogous math environment in a blueprint:

- the statement should be a faithful verbatim transcript from the relevant
  Takesaki source statement, except for explicitly marked notation adaptation
  needed to match the project and Lean target;
- the environment heading or first source line must point back to the precise
  Takesaki statement, e.g.
  `[cf. Proposition X.Y.Z in \cite{TakesakiI}, PDF p.~N]`;
- the note must include the Takesaki volume, numbered statement, section when
  available, PDF page, and intended citation key;
- if a statement combines Takesaki with project-specific stabilizer notation,
  the Takesaki transcript and the project specialization must be separated in
  the prose;
- if a needed operator-algebra statement cannot be found in Takesaki, the
  blueprint must mark the target as source-blocked or explicitly record the
  fallback source and why Takesaki is insufficient;
- no operator-algebra target may be marked `blueprint_note_complete` until each
  load-bearing math environment has this Takesaki trace.

Acceptable TeX patterns include:

```tex
\begin{theorem}[ID: TYPE-ALT-001; cf. Theorem X.Y.Z in \cite{TakesakiII}, PDF p.~N]
...
\end{theorem}
```

or, when the environment title must stay short:

```tex
\begin{definition}[ID: VN-002]
...
\source{Verbatim source statement: cf. Definition X.Y.Z in \cite{TakesakiI},
PDF p.~N.}
\end{definition}
```

## Required Blueprint Blocks

### 1. Stabilizer and Local-State Foundations

Promote or complete:

- `PAULI-001`
- `QL-002`
- `STATE-002`
- `STATE-003`
- `STATE-004`

Required content:

- finite-support Pauli labels and binary symplectic commutation, with the
  concrete-matrix connection needed by later finite algebra targets;
- region algebras and finite-support label restriction;
- finite-local positivity and consistency of the canonical stabilizer
  projection state;
- quasi-local state extension from compatible finite-local states;
- region restriction and crossing-stabilizer invisibility.

Before marking this block complete, resolve the `STATE-003` source-locator gap
for the C*-inductive-limit state extension.

### 2. Internal Stabilizer Reduction

Promote:

- `SYMP-001`
- `SYMP-002`
- `PROD-001`

Required content:

- countable symplectic Gram-Schmidt basis adapted to an isotropic stabilizer
  subspace;
- induced Pauli algebra isomorphism from an adapted symplectic basis;
- product form of canonical projection states into fixed pure modes and
  tracial defect modes.

This block must explicitly separate algebraic symplectic equivalence from
geometrically local Clifford or gLU equivalence.

### 3. Hilbert, GNS, and Represented-Region Layer

Promote or complete:

- `HILB-001`
- `GNS-001`
- `GNS-002`
- `GNS-003`
- `VN-001`
- `VN-003`

Required content:

- Hilbert-space interfaces used by GNS and product-state constructions;
- mathlib-backed GNS wrapper plan around `PositiveLinearMap.GNS` and
  `PositiveLinearMap.gnsStarAlgHom`;
- GNS unitary equivalence under state transport by star isomorphism;
- product-state GNS identification for the stabilizer product form;
- represented region von Neumann algebras as concrete `VonNeumannAlgebra H`;
- bicommutants and represented region algebras under unitary equivalence.

This block must keep the GNS/representation layer explicit.  Infinite-region
von Neumann algebras may not be introduced directly without a Hilbert space and
representation.

Operator-algebraic statements in this block should be traced first to Takesaki,
especially the GNS construction/representation statements and bicommutant or
represented von Neumann algebra facts.  Mathlib identifiers are implementation
targets, not substitutes for Takesaki source statements.

### 4. Project-Local Von Neumann Type Theory

Promote:

- `VN-002`
- `PROJ-001`
- `TRACE-001`
- `TYPE-DEF-001`
- `TYPE-ALT-001`
- `MATRIX-001`

Required content:

- centers and factor predicates for concrete von Neumann algebras;
- Murray-von Neumann equivalence and the projection comparison facts actually
  needed by the stabilizer proof;
- finite, infinite, properly infinite, and semifinite projections;
- finite and semifinite trace interfaces adequate for the classification;
- type predicates for `I_n`, `I_infty`, `II_1`, `II_infty`, and `III`;
- recognition criteria for the relevant factor alternatives;
- finite matrix and `B(l2)` model factors.

Before marking this block complete, resolve the `VN-002` and `PROJ-001`
source-locator gaps.  The blueprint may rely on standard operator-algebra
theorems as sourced targets, but it must state exactly which theorem is needed
and what assumptions the later Lean target will carry.

This block is Takesaki-first.  Every operator-algebraic definition and theorem
in the block must be linked to the corresponding Takesaki definition,
proposition, theorem, corollary, lemma, or remark, using the Takesaki
traceability rule above.

### 5. Infinite Product and Tensor Type Calculus

Promote:

- `ITP-001`
- `ITP-PURE-001`
- `ITP-TRACE-001`
- `TENSOR-001`

Required content:

- infinite tensor product von Neumann algebra package for product states;
- pure-mode product factor recognition as type `I`;
- infinite tracial defect product as the hyperfinite `II_1` factor;
- tensor-product type calculus for pure and defect model factors.

This block must distinguish facts expected to become project-local Lean targets
from facts that will remain narrowly scoped sourced abstractions until Lean
support is available.

This block should use Takesaki as the primary source for infinite tensor
products and type-calculus facts when those facts are available there.  If a
specific infinite-product fact is not located in Takesaki, record that search
result and only then use a fallback source.

### 6. Final Classification Targets

Promote:

- `TYPE-001`
- `TYPE-002`

Required content:

- final canonical projection-state type matrix for finite or countably
  infinite regions;
- proof dependency trace from product form, represented region equivalence, and
  tensor type calculus;
- type III exclusion corollary;
- explicit caveat that the classification is for canonical projection states,
  not arbitrary logical ground states.

## Blueprint Completion Criteria

Each promoted blueprint target must include:

- stable target ID;
- source locator with book/notes, section/theorem/equation when available, and
  PDF page when known;
- for operator-algebraic targets, a Takesaki statement reference on every
  load-bearing math environment, using the pattern
  `[cf. Proposition/Theorem/Definition X.Y.Z in \cite{Takesaki...}, PDF p.~N]`;
- definitions before load-bearing use;
- assumptions and conventions before they are used;
- theorem/lemma/proposition statement when applicable;
- proof sketch or complete informal proof, or an explicit definition-only note;
- intended Lean declaration name and file path;
- dependency list;
- status marker;
- distinction between mathlib-backed infrastructure and project-local theory.

## Workflow Constraints

- Do not add new Lean declarations under this goal.
- Do not submit Aristotle packets under this goal.
- Do not weaken theorem statements silently.
- Do not mark a target `blueprint_note_complete` if its source locator is still
  intentionally partial.
- Do not mark an operator-algebraic target `blueprint_note_complete` unless
  every load-bearing math environment has a Takesaki trace or a documented
  source-blocked/fallback exception.
- After each substantive blueprint promotion, update `MANIFEST.toml`,
  `PROGRESS.md`, and run the relevant TeX/manifest checks.
- Run adversarial closeout review for each promoted blueprint block.

## Suggested Execution Order

1. `QL-002`, `STATE-002`, `STATE-003`, `STATE-004`.
2. `SYMP-001`, `SYMP-002`, `PROD-001`.
3. `HILB-001`, `GNS-001`, `GNS-002`, `GNS-003`, `VN-001`, `VN-003`.
4. `VN-002`, `PROJ-001`, `TRACE-001`, `TYPE-DEF-001`, `TYPE-ALT-001`,
   `MATRIX-001`.
5. `ITP-001`, `ITP-PURE-001`, `ITP-TRACE-001`, `TENSOR-001`.
6. `TYPE-001`, `TYPE-002`.

The first execution block should begin by resolving the `STATE-003`
C*-inductive-limit state extension locator, because the state-extension layer
feeds the GNS and represented-region layers.

## Non-Goals

- No gLU layer-coherence theorem work.
- No geometrically local Clifford normal-form theorem.
- No arbitrary logical-state classification theorem.
- No Lean proof implementation or API design beyond recording intended targets.
- No cleanup of the embedded `scaffold/` repository.
