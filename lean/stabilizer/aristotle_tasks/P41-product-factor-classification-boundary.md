# P41 — product GNS factor and trace/type classification boundary

## Context declaration

- **Source basis:** `main.tex:1945-1967`

## Mathematical target

Create only `AristotleCandidates/ProductFactorClassificationBoundary.lean`.
Formalize the strongest conditional product-representation theorem supported by
the existing pure/mixed finite-stage state construction: supplied product-GNS
factorization, supplied mixed-sector factor model, and supplied spatial tensor
identification imply the stated type-I times finite-type-I or hyperfinite-II1
conclusion. Encode separately the finite-pure normalized-trace case and the
infinite-pure faithful normal semifinite trace/weight case.

## Boundary

Do not assert that Mathlib presently constructs infinite tensor products,
hyperfinite II1 factors, normal traces, or their classification. Make each
missing analytic theorem a named assumption/interface and do not call the
infinite-pure trace a state.

## Acceptance criteria

`lake build AristotleCandidates.ProductFactorClassificationBoundary` succeeds,
with no user axiom and with the finite/infinite pure-sector distinction visible
in every conclusion.
