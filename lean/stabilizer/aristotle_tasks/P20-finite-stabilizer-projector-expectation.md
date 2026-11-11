# P20 — finite stabilizer projector expectation

## Context declaration

- **Source basis:** `main.tex:1927-1944`

## Mathematical target

Create only `AristotleCandidates/FiniteStabilizerProjectorExpectation.lean`.

Formalize the finite Pauli-basis verification pattern used by the manuscript:
a finite group-average stabilizer projector/density functional has expectation
one on supplied stabilizer basis words and zero on supplied non-stabilizer
basis words, provided the required trace-orthogonality hypotheses are supplied
explicitly. Reuse `FiniteStabilizerProjector`, `FiniteStabilizerDimension`, and
P17 where useful.

The useful theorem may bundle a supplied finite word family, stabilizer
predicate, group representation, and trace-orthogonality assumption. Its
conclusion must identify the resulting finite functional with the stabilizer
indicator on that word family.

## Auxiliary assumptions

- a finite-dimensional matrix/qubit-stage algebra and a finite stabilizer
  group representation;
- a supplied source word family and stabilizer predicate; and
- explicit trace-orthogonality/normalization hypotheses relating the group
  average to that word family.

Do not infer these assumptions from short-range order. Do not introduce gLU,
refinement, C-star completion, GNS, or von Neumann conclusions.

## Files and imports

Use only existing finite projector, finite density, and finite product-state
modules plus Mathlib. Do not modify existing files.

## Acceptance criteria

- `lake build AristotleCandidates.FiniteStabilizerProjectorExpectation` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The output clearly labels the trace-orthogonality realization as supplied.
