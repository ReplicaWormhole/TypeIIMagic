# P49C — Kaplansky density and compressed-corner approximation

## Context declaration

- **Source basis:** `main.tex:1269-1315`.

## Plan alignment

- **Package and lane:** `P49C`; Lane `shared` analytic infrastructure used by G.
- **Predecessors:** `P49B`, integrated and locally audited before submission.
- **Gate discharged:** prove unit-ball Kaplansky density and the bounded
  compressed-corner approximation required for P50.
- **Forbidden downstream claims:** no assertion that `tau_q` is tracial, normal,
  or faithful; no finiteness/fullness or type-III conclusion; no Lane-H factor claim.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Create only `AristotleCandidates/KaplanskyDensity.lean`. For a represented
unital C-star algebra `A ⊆ B(H)` and `M = A''`, prove the bounded form of
Kaplansky density: the unit ball of `A` is strong-operator dense in the unit ball
of `M`. Include the scaled norm-bounded form and the self-adjoint/positive forms
needed by the proof if they are intermediate steps.

Then prove the manuscript-facing analytic corollary: for a projection `q ∈ M`,
every `qxq ∈ qMq` admits a uniformly norm-bounded net `q a_i q`, with `a_i ∈ A`,
converging strongly to `qxq`. Prove the corresponding jointly indexed bounded
product convergence used to pass cyclicity from `qAq` to `qMq`.

## Auxiliary assumptions

Only explicit representation, unitality, and C-star hypotheses may remain.
Kaplansky density and the compressed approximation must be proved, not supplied
as structure fields or axioms. Develop missing functional-calculus/topological
support locally when Mathlib lacks it.

## Files and imports

Create only `AristotleCandidates/KaplanskyDensity.lean`. Import P49B and existing
C-star/operator infrastructure. Do not import P50 or later packages.

## Acceptance criteria

- `lake build AristotleCandidates.KaplanskyDensity` succeeds.
- Unit-ball density, scaled bounded density, compressed-corner approximation,
  and bounded product convergence are actual proved declarations.
- No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or supplied density interface.
- If the core theorem remains unproved, halt with the precise missing lemma
  graph; do not advance a conditional substitute.
