# P17 — finite stabilizer product-state identification

## Context declaration

- **Source basis:** `main.tex:1671-1679, 1927-1931`

## Mathematical target

Create only `AristotleCandidates/FiniteStabilizerProductState.lean`.

Formalize a finite, explicitly conditional bridge between the selected-Z
stabilizer description and the finite pure/mixed qubit product state. Reuse
the existing theorems
`finiteQubitPauliSelectedZ_iff_mem_coordinateStabilizerSubmodule` and
`qubitPureMixedState_finiteQubitPauliWord_eq_selectedZIndicator`.

The useful result should say: whenever a supplied finite stabilizer-word
realization identifies its stabilizer words with the selected-Z labels, its
finite product-state expectation on every supplied Pauli basis word equals the
selected-Z/stabilizer indicator. State the data and this identification
hypothesis explicitly; do not attempt to construct them from short-range
order.

## Auxiliary assumptions

- A finite qubit stage and its supplied adapted coordinate basis.
- A supplied map from source Pauli basis words to finite qubit Pauli labels.
- A supplied hypothesis that source stabilizer membership is exactly the
  selected-Z condition under that map.

The conclusion must be conditional on these assumptions. Do not introduce
gLU, refinement, layer-coherence, C-star completion, GNS, or von Neumann
claims.

## Files and imports

Use the smallest relevant imports from `Formalization.FiniteQubitPauliSelection`,
`Formalization.FinitePureMixedQubitState`, and
`Formalization.AdaptedStabilizerSubspace`. Do not modify existing files.

## Acceptance criteria

- `lake build AristotleCandidates.FiniteStabilizerProductState` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The response lists the exact supplied hypotheses and explicitly says that it
  does not construct the regional realization.
