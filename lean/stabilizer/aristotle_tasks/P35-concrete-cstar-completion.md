# P35 — concrete C*-completion from an operator representation

## Context declaration

Infrastructure only: reusable Lean infrastructure; no manuscript claim.

## Mathematical target

Create only `AristotleCandidates/ConcreteCStarCompletion.lean`.

Use the pinned Mathlib APIs for `StarAlgHom`, bounded operators
`H →L[ℂ] H`, `StarSubalgebra.range`, and `StarSubalgebra.topologicalClosure`.
Given a normed complex *-algebra `A` satisfying the C*-identity and an
explicit isometric complex star-algebra homomorphism
`rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)` into bounded operators on a Hilbert space,
construct the closed operator-algebra range as a genuine `CStarAlgebra`.

Define the canonical embedding of `A` into that closed range and prove:

1. it is a complex star-algebra homomorphism;
2. it is isometric and injective;
3. its range is dense in the constructed closed range;
4. the construction is minimal among closed star-subalgebras containing the
   operator range; and
5. two such constructions are uniquely equivalent when they agree on the
   embedded dense source.

If a requested theorem is unavailable, narrow the target to the strongest
compiling construction supported by the APIs; do not introduce `sorry`,
`admit`, or axioms. Do not merely repackage an arbitrary ambient C*-algebra:
the ambient algebra must be the closed range inside bounded operators.

## Boundary

No von Neumann algebra, bicommutant, GNS state identity, tensor product,
factor classification, trace/weight, gLU, or refinement claim.

## Acceptance criteria

- `lake build AristotleCandidates.ConcreteCStarCompletion` succeeds.
- no `sorry`/`admit`/user-declared axiom.
- any supplied representation/isometry hypotheses are explicit in the Lean
  structure and the result is clearly conditional on them.
