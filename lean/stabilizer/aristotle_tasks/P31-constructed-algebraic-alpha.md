# P31 — constructed algebraic alpha from finite coordinate data

## Context declaration

- **Source basis:** `main.tex:1671-1679, 1915-1924`

## Mathematical target

Create only `AristotleCandidates/ConstructedAlgebraicAlpha.lean`.

Combine P29 and P30 with P23. Define a directed-system package whose stage
equivalences are constructed by P29 and whose required coherence is proved by
P30. Use it to construct P23's algebraic direct-limit `alpha`, with its
finite-stage Pauli-word formula.

The resulting theorem must not take a finite-stage `StarAlgEquiv` or its
whole-stage coherence as an independent input; it may take the underlying
finite word/basis/cocycle and inclusion-compatibility data as inputs.

## Boundary

This remains algebraic. Do not claim C-star completion, continuity, GNS,
normality, spatial tensor product, or von Neumann factor classification.

## Acceptance criteria

- `lake build AristotleCandidates.ConstructedAlgebraicAlpha` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- State clearly which finite coordinate/cocycle/inclusion data remain supplied.
