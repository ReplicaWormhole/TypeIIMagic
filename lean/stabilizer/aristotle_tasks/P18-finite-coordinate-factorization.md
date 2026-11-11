# P18 — finite coordinate factorization interface

## Context declaration

- **Source basis:** `main.tex:1740-1752`

## Mathematical target

Create only `AristotleCandidates/FiniteCoordinateFactorization.lean`.

Develop a finite algebraic interface for the finite analogue of the asserted
type-I/core split. The target is a conditional theorem transporting the
already-checked product tracial functional through a supplied complex
star-algebra equivalence from a finite pure matrix factor tensored with a
finite core matrix factor. Reuse `TensorMatrixEquiv`, `FiniteTensorTrace`,
`MatrixOverTrace`, and `TraceTransport` where appropriate.

The theorem should expose the elementary-tensor trace formula and distinguish
the supplied finite factorization from any claim about an infinite spatial von
Neumann tensor product.

## Auxiliary assumptions

- finite index types for the pure and core matrix factors;
- a supplied complex star-algebra equivalence from the finite product model to
  the target algebra; and
- any nonemptiness assumptions required by the normalized matrix trace.

The result is conditional on the supplied equivalence. Do not introduce gLU,
refinement, hyperfiniteness, GNS, normality, or an infinite tensor product.

## Files and imports

Use only existing finite algebraic modules and Mathlib. Do not modify existing
files.

## Acceptance criteria

- `lake build AristotleCandidates.FiniteCoordinateFactorization` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The output names the finite factorization hypothesis and does not claim the
  manuscript's von Neumann theorem.
