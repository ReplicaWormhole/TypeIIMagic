# P57 — product GNS tensor factorization

## Context declaration

- **Source basis:** `main.tex:1945-1985`.

## Plan alignment

- **Package and lane:** `P57`; Lane `H`.
- **Predecessors:** `P54`, `P56R`, and `P57A`, all integrated and locally
  audited before submission. P56 is a preserved partial artifact and is not a
  predecessor.
- **Gate discharged:** construct the pure/mixed product GNS Hilbert-space split
  and the spatial represented-algebra identification.
- **Forbidden downstream claims:** no mixed-factor classification, no assertion
  that both factors are factors, no final regional factorhood, and no trace/weight dichotomy.

## Mathematical target

Create only `AristotleCandidates/ProductGNSTensorFactorization.lean`. Construct
the canonical GNS unitary associated with the product state, prove its
intertwining identity on a dense finite-word subspace and by continuity, and
identify the represented algebra with the spatial pure/mixed tensor product in
the strongest form supported by pinned Mathlib. If a spatial von Neumann tensor
product API is absent, stop at the strongest proved local theorem and document
the exact missing API. Do not replace it by a named interface, axiom, or
completion assumption.

## Auxiliary assumptions

List every Hilbert tensor-product, density, normal extension, bicommutant, or
spatial-closure premise explicitly.

## Files and imports

Create only `AristotleCandidates/ProductGNSTensorFactorization.lean`; import
P54, P56R's recovered state declarations, P57A's locally ported ITP core, and
the checked GNS/bicommutant transport modules.

## Acceptance criteria

`lake build AristotleCandidates.ProductGNSTensorFactorization` succeeds without
forbidden declarations. Separate constructed GNS facts from supplied spatial
von Neumann closure facts.
