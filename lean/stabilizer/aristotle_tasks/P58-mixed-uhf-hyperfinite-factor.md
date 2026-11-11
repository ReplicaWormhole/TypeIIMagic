# P58 — mixed UHF factor classification

## Context declaration

- **Source basis:** `main.tex:1945-1967`.

## Plan alignment

- **Package and lane:** `P58`; Lane `H`.
- **Predecessors:** `P54`, integrated and locally audited before submission.
- **Gate discharged:** prove the finite mixed matrix and infinite mixed
  hyperfinite-II1 alternatives under explicit project-local definitions.
- **Forbidden downstream claims:** no regional alpha transport, no pure-sector
  classification, no spatial product factorhood, and no final trace/weight theorem.

## Mathematical target

Create only `AristotleCandidates/MixedUHFHyperfiniteFactor.lean`. For the mixed
coordinates in the P54 dyadic representation, prove the finite case is a matrix
factor with normalized trace. For an infinite mixed subsystem, construct the
increasing matrix approximation and the strongest checked factor/finite-trace
statement available; state any analytic factoriality or hyperfinite-II1
classification bridge as an explicit conditional interface rather than a label
mistaken for a proof.

## Auxiliary assumptions

List every weak closure, factoriality, normality, faithfulness, or classification
premise explicitly.

## Files and imports

Create only `AristotleCandidates/MixedUHFHyperfiniteFactor.lean`; import P54 and
the existing dyadic trace and bicommutant modules.

## Acceptance criteria

`lake build AristotleCandidates.MixedUHFHyperfiniteFactor` succeeds without
forbidden declarations. The response distinguishes matrix approximation,
factorhood, hyperfiniteness, and II1 classification.
