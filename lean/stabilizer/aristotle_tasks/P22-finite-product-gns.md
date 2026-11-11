# P22 — finite pure/mixed product GNS interface

## Context declaration

- **Source basis:** `main.tex:1927-1953`

## Mathematical target

Create only `AristotleCandidates/FiniteProductGNS.lean`.

Develop a finite-dimensional, explicitly scoped GNS interface for the existing
pure/mixed qubit product state. Reuse P21 if available only when it is present
in the submitted snapshot; otherwise work independently from Mathlib GNS. A
useful result is a finite-stage GNS datum and finite-stage representation for a
supplied pure/mixed pattern, together with its defining state/inner-product
formula on represented algebra elements.

Do not attempt an infinite tensor-product decomposition. A useful partial
result that compiles and identifies the exact pinned-Mathlib obstruction to
assembling the finite states is preferable to adding assumptions or axioms.

## Auxiliary assumptions

Any positivity/order/C-star assumptions required by Mathlib must be explicit.
Do not add a regional identification, gLU/refinement hypothesis, normality,
spatial tensor product, or factor classification.

## Files and imports

Use only concrete finite qubit-state modules and Mathlib GNS APIs. Do not
modify existing files.

## Acceptance criteria

- `lake build AristotleCandidates.FiniteProductGNS` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The final comments distinguish checked finite GNS data from the open
infinite product-GNS decomposition.
