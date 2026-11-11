# P56 — regional/product-state identity

## Context declaration

- **Source basis:** `main.tex:1915-1969`.

## Plan alignment

- **Package and lane:** `P56`; Lane `H`.
- **Predecessors:** `P55`, integrated and locally audited before submission.
- **Gate discharged:** prove equality of the regional stabilizer state pulled
  back by alpha with the pure/mixed product state.
- **Forbidden downstream claims:** no GNS tensor splitting, von Neumann spatial
  tensor product, factorhood, or trace/weight classification.

## Mathematical target

Create only `AristotleCandidates/RegionalProductStateIdentity.lean`. Prove the
state identity first on finite Pauli-word basis elements using the stabilizer
membership criterion and phase calibration, then extend it to the concrete
C-star algebra by density and continuity. State every equality with the exact
P55 alpha.

## Auxiliary assumptions

List any regional-state continuity, density, stabilizer-character, or finite-word
expectation premise not already integrated.

## Files and imports

Create only `AristotleCandidates/RegionalProductStateIdentity.lean`; import P55
and the checked pure/mixed product-state modules.

## Acceptance criteria

`lake build AristotleCandidates.RegionalProductStateIdentity` succeeds without
forbidden declarations. Report the finite-word lemma and the final continuous
state equality separately.
