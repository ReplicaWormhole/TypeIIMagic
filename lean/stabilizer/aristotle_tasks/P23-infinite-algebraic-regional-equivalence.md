# P23 — infinite algebraic regional equivalence interface

## Context declaration

- **Source basis:** `main.tex:1915-1924`

## Mathematical target

Create only `AristotleCandidates/InfiniteAlgebraicRegionalEquiv.lean`.

Formalize the algebraic, directed-limit version of the manuscript's proposed
map `alpha : P_I -> A_Gamma`. Do **not** construct the actual regional map.
Instead bundle the supplied data required for it:

- a directed system of finite source Pauli/star algebras;
- a directed system of finite target regional/star algebras;
- supplied finite-stage complex star-algebra equivalences; and
- their exact compatibility with every connecting map.

Using `algebraicLimitStarAlgEquiv`, define the induced infinite algebraic
star-algebra equivalence `alpha`, prove its finite-stage formula and uniqueness
from those formulas, and provide inverse-stage formulas. If useful, expose a
constructor from finite Pauli-word basis/phase data via
`phaseCorrectedStarAlgEquivOfBasis`, but keep all cocycle and basis hypotheses
explicit.

## Auxiliary assumptions

- both directed systems and their complex star-algebra structures;
- finite-stage star equivalences or the full word-basis/cocycle data required
  to construct them; and
- exact coherence with all connecting maps.

The result must state clearly that these assumptions are not obtained merely
from the manuscript's adapted symplectic basis or finite support condition.

## Boundary

This is the infinite **algebraic direct-limit** step only. It must not claim a
C-star completion, continuity, normality, a spatial tensor product, a von
Neumann bicommutant, quasi-equivalence, hyperfiniteness, factor type, or a
trace/weight theorem. Do not use gLU, refinement, or layer-coherence.

## Files and imports

Use `Formalization.AlgebraicLimitStarHom`,
`Formalization.PhaseCorrectedWordBasisEquiv`, and their dependencies. Do not
modify existing files.

## Acceptance criteria

- `lake build AristotleCandidates.InfiniteAlgebraicRegionalEquiv` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The output calls the induced map `alpha` only as an explicitly supplied,
  algebraic direct-limit equivalence and enumerates the missing analytic steps.
