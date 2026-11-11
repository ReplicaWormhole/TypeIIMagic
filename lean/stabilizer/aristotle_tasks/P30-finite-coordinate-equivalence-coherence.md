# P30 — coherence of constructed finite coordinate equivalences

## Context declaration

- **Source basis:** `main.tex:1671-1679, 1915-1920`

## Mathematical target

Create only `AristotleCandidates/FiniteCoordinateEquivCoherence.lean`.

For a directed family of finite coordinate systems whose stage equivalences are
constructed by P29, prove whole-stage commuting squares from explicit
compatibility on the chosen finite Pauli-word bases. Reuse
`starAlgEquiv_commutes_of_basis` or the relevant existing basis-extensionality
theorem. The conclusion must be the exact coherence required by P23.

## Auxiliary assumptions

- finite source/target connecting star maps;
- finite Pauli-word bases at each stage;
- explicit inclusion compatibility of labels, phases, and word images.

Do not assume coherence as a bare field and do not use gLU/refinement/C-star or
von Neumann claims.

## Acceptance criteria

- `lake build AristotleCandidates.FiniteCoordinateEquivCoherence` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The final theorem exposes its Pauli-basis coherence hypotheses.
