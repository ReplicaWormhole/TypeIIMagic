# P49A — strong-operator closed concrete von Neumann algebras

## Context declaration

- **Infrastructure only:** reusable strong-operator topology and closure theory
  for concrete operator algebras; this packet makes no manuscript claim.

## Plan alignment

- **Package and lane:** `P49A`; Lane `shared` analytic infrastructure.
- **Predecessors:** `P48`, integrated and locally audited before submission.
- **Gate discharged:** prove commutants and Mathlib concrete von Neumann
  algebras are closed under strong-operator limits.
- **Forbidden downstream claims:** no equality of a star algebra's strong
  closure with its bicommutant, no Kaplansky density, no corner trace, no
  faithfulness, finiteness, fullness, or type classification.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Create only `AristotleCandidates/StrongOperatorClosedVonNeumann.lean`. Reuse or
develop a project-local strong-operator convergence/closure API for
`H →L[ℂ] H`. Prove:

1. a net converges strongly exactly when it converges pointwise in norm;
2. the commutant of an arbitrary operator set is strongly closed;
3. any `M : VonNeumannAlgebra H`, using Mathlib's defining equality
   `M = M''`, is strongly closed;
4. a uniformly bounded strong limit is stable under left/right multiplication
   by a fixed bounded operator, with the joint bounded-product corollary needed
   later.

Package the results as reusable declarations, not only a lemma specialized to
the projection tower.

## Auxiliary assumptions

Only the standard complex Hilbert-space and completeness assumptions required
for bounded operators. The four core conclusions above must be proved; they may
not be supplied as fields or axioms.

## Files and imports

Create only `AristotleCandidates/StrongOperatorClosedVonNeumann.lean`. Reuse
`AristotleCandidates.BicommutantVonNeumannCore` and the strong-convergence
arguments in `AristotleCandidates.GeneralLatticeProjectionTower`. Do not import
P49B, P49C, P50, or any later package.

## Acceptance criteria

- `lake build AristotleCandidates.StrongOperatorClosedVonNeumann` succeeds.
- The four core conclusions are actual theorems with no `sorry`, `admit`, new
  axiom, `opaque`, `unsafe`, or supplied analytic interface.
- The response gives exact declaration names and reports their axioms.
- If the core gate cannot be proved, halt with the exact obstruction; do not
  advance a conditional substitute.
