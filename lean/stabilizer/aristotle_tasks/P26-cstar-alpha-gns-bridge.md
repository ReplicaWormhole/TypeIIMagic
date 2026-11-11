# P26 — C-star alpha state compatibility to GNS bridge

## Context declaration

- **Source basis:** `main.tex:1921-1958`

## Mathematical target

Create only `AristotleCandidates/CStarAlphaGNSBridge.lean`.

Combine P25 `CStarCompletionData` with P19 `CStarGNSBridge.Data`. Given
supplied positive unital continuous source and target states satisfying exact
compatibility along P25's `alphaCStar`, construct/package the P19 GNS bridge.
Expose the GNS unitary, intertwining formula, and algebraic centralizer
transport, with a finite-stage formula inherited from P25/P24 where possible.

## Boundary

All C-star completions, alpha extension, and states are supplied. Do not claim
normality, quasi-equivalence, spatial tensor product, von Neumann closure,
hyperfiniteness, factor type, or trace/weight. No gLU/refinement assumptions.

## Acceptance criteria

- `lake build AristotleCandidates.CStarAlphaGNSBridge` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
