# P37 — operator representation of the algebraic quasi-local limit

## Context declaration

Infrastructure only: reusable Lean infrastructure; no manuscript claim.

## Mathematical target

Create only `AristotleCandidates/AlgebraicLimitOperatorRepresentation.lean`.

For a directed family of complex star algebras `A i` with compatible connecting
`StarAlgHom`s, and a fixed Hilbert space `H`, suppose we are given compatible
stage representations

`rho i : A i →⋆ₐ[ℂ] (H →L[ℂ] H)`.

Construct the induced complex star-algebra homomorphism from the algebraic
direct limit `DirectLimit A f` into bounded operators. Prove the finite-stage
formula and independence of representatives. If each stage representation is
injective and the connecting maps are injective, prove injectivity of the
induced limit representation whenever this follows from the direct-limit API.

Package the concrete dyadic specialization for
`StabilizerHyperfinite.QubitTensorPower` and
`qubitTensorPowerMap` as a conditional structure, but do not invent an
infinite tensor-product Hilbert space. The Hilbert space and compatible stage
representations must remain explicit supplied data.

If injectivity of the limit map requires an additional finite-stage separation
hypothesis, state that hypothesis explicitly and prove the strongest result
available. Do not use `sorry`, `admit`, or axioms.

## Boundary

No C*-completion, norm on the algebraic limit, von Neumann closure,
bicommutant theorem, GNS state identity, tensor-product factor classification,
trace/weight, gLU, or refinement claim.

## Acceptance criteria

- `lake build AristotleCandidates.AlgebraicLimitOperatorRepresentation`
  succeeds.
- no `sorry`/`admit`/user-declared axiom.
- all representation and compatibility assumptions are explicit and the
  resulting theorem is clearly conditional on them.
