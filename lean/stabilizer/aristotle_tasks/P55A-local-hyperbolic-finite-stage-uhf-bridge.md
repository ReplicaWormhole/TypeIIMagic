# P55A — finite-stage local-hyperbolic Pauli-to-dyadic bridge

## Context declaration

- **Infrastructure only:** construct the finite-dimensional bridge that was
  missing between P53's coordinate Pauli stages and the standard dyadic matrix
  stages. No completed manuscript claim is asserted here.

## Plan alignment

- **Package and lane:** `P55A`; Lane `H`.
- **Predecessors:** `P53`, integrated and locally audited before submission.
- **Gate discharged:** construct the finite-stage Pauli-to-dyadic star
  equivalences and prove their norm and generator formulas.
- **Forbidden downstream claims:** no direct-limit equivalence, C-star
  completion, regional alpha, state identity, GNS tensor split, factor
  classification, or trace/weight conclusion.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Create only
`AristotleCandidates/LocalHyperbolicFiniteStageUHFBridge.lean`.

For `A : LocalHyperbolicAlpha.AlphaData L I`, a stage `n`, a natural number
`k`, and an explicit enumeration `e : A.Coord n ≃ Fin k`, construct a complex
`StarAlgEquiv`

`A.sourceStageUHFEquiv n e :
  LocalHyperbolicAlpha.pauliAlgebra (A.sourceForm n) ≃⋆ₐ[ℂ]
    QubitTensorPower k`.

The equivalence must be built from the explicit P53 Pauli-word basis and an
explicit enumeration parameter; the star equivalence itself may not be
supplied as a structure field. Also export a default specialization at
`k = Nat.card (A.Coord n)` using a constructed finite enumeration. Define the
standard finite-qubit `X` and `Z` words in the
recursive `QubitTensorPower` model and prove the images of the P53 coordinate
`Z` and `X` generators, including every convention-dependent fourth-root
phase. Prove multiplication, star preservation, bijectivity, and the induced
norm/isometry statements. If an equivalent indexing of the dyadic matrix
stage is technically required, construct and prove the exact equivalence to
`QubitTensorPower (Nat.card (A.Coord n))` in this file.

## Auxiliary assumptions

No finite-stage star equivalence, norm equality, word basis, or matrix-unit
identification may be assumed. Classical choice of an enumeration of a finite
type is allowed and must appear only as constructed data. If the recursive
left-versus-right tensor convention introduces a permutation or phase, expose
and prove it rather than strengthening the theorem silently.

## Files and imports

Create only
`AristotleCandidates/LocalHyperbolicFiniteStageUHFBridge.lean`; import P53,
`Formalization.DyadicTensorTower`, and the checked finite-coordinate norm
control modules as needed. Do not edit predecessor modules.

## Acceptance criteria

- `lake build AristotleCandidates.LocalHyperbolicFiniteStageUHFBridge` passes.
- No `sorry`, `admit`, new axiom, or supplied stage equivalence is introduced.
- The response prints the exact generator formulas and convention-dependent
  phases, the exact verification command, and all remaining assumptions.
- No direct-limit or downstream Lane-H conclusion is claimed.
