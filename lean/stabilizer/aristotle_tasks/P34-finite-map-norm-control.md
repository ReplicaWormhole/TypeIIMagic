# P34 — norm control for coherent finite maps

## Context declaration

- **Source basis:** `main.tex:1915-1924`

## Mathematical target

Create only `AristotleCandidates/FiniteCoordinateMapNormControl.lean`.

For supplied finite-dimensional C-star realizations of the P29 finite
coordinate star-equivalences, prove the maps are isometric and continuous and
that their inclusion squares preserve the corresponding norm estimates. Package
the exact dense-subalgebra estimate needed to extend the coherent algebraic
alpha to completions.

## Auxiliary assumptions

- supplied finite C-star structures on source and target stages;
- supplied P29 finite star-equivalences; and
- supplied compatibility with the stage embeddings.

No completion is constructed here.

## Boundary

No GNS, normality, spatial tensor product, factor type, trace/weight, or gLU/
refinement claim.

## Acceptance criteria

- `lake build AristotleCandidates.FiniteCoordinateMapNormControl` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
