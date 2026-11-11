# P29 — finite adapted-coordinate Pauli star equivalence

## Context declaration

- **Source basis:** `main.tex:1671-1679, 1915-1920`

## Mathematical target

Create only `AristotleCandidates/FiniteAdaptedCoordinateStarEquiv.lean`.

Starting from explicit finite adapted-coordinate data, a source/target
Pauli-word basis, an additive label map, and an explicit phase correction,
construct the finite-stage star-algebra equivalence using
`phaseCorrectedStarAlgEquivOfBasis`. Package the exact multiplier and
involution equations as finite-coordinate hypotheses and prove its formula on
each Pauli word.

The equivalence must be constructed from the supplied word/basis/cocycle data,
not supplied as a `StarAlgEquiv` field.

## Auxiliary assumptions

- finite adapted coordinate data and finite Pauli-word bases;
- explicit label map and phase;
- multiplier/involution compatibility; and
- the specified linear basis map and its word-image formula.

Do not infer phase coherence from symplecticity alone, and do not use
gLU/refinement/C-star/von Neumann hypotheses.

## Acceptance criteria

- `lake build AristotleCandidates.FiniteAdaptedCoordinateStarEquiv` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The resulting finite-stage equivalence has an explicit Pauli-word formula.
