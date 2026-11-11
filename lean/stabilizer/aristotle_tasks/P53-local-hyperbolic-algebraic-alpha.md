# P53 — algebraic alpha from local-hyperbolic coordinates

## Context declaration

- **Source basis:** `main.tex:1898-1944`.

## Plan alignment

- **Package and lane:** `P53`; Lane `H`.
- **Predecessors:** `P52`, integrated and locally audited before submission.
- **Gate discharged:** construct phase-calibrated finite-stage star equivalences
  and their coherent algebraic direct-limit star equivalence `alpha`.
- **Forbidden downstream claims:** no C-star completion, state identity, GNS
  tensor split, factorhood, or trace/weight theorem.

## Mathematical target

Create only `AristotleCandidates/LocalHyperbolicAlgebraicAlpha.lean`. Instantiate
the existing cocycle, word-basis, coherence, and algebraic-limit theorems using
the concrete P52 coordinate data. Construct rather than assume the finite-stage
maps, phase calibration, commuting squares, and global algebraic `StarAlgEquiv`.

## Auxiliary assumptions

Expose any word-basis, phase-character extension, or finite-stage bijectivity
premise not derived from P52.

## Files and imports

Create only `AristotleCandidates/LocalHyperbolicAlgebraicAlpha.lean`; import
P52 and the checked phase/coherence/direct-limit modules.

## Acceptance criteria

`lake build AristotleCandidates.LocalHyperbolicAlgebraicAlpha` succeeds without
forbidden declarations. Report whether any stage equivalence remains supplied.
