import Formalization.CoherentPhaseQubitState

/-!
# Regional finite-stage witness data

This module adds no new mathematics.  It packages, as a *transparent record of
input data*, exactly the finite-stage hypotheses consumed by the already
checked theorem
`StabilizerHyperfinite.exists_stabilizerState_of_adaptedCoordinateStages`
in `Formalization/CoherentPhaseQubitState.lean`, and re-derives that theorem's
conclusion from the packaged record.

The record `StabilizerHyperfinite.RegionalStageWitness` carries

* the pure-coordinate Boolean pattern `pure`;
* the finite-stage source bases `sourceBasis` and the source-label embeddings
  `sourceLabelMap`;
* the finite-qubit target Pauli labels `targetLabelMap` and the coherent
  phases `phase`;
* the finite-stage star-algebra equivalences `e` onto the concrete qubit
  tensor powers;
* the three coherence clauses `h_source`, `h_phase`, `h_labels` together with
  the finite basis-word identification `h_word`;
* the adapted-coordinate data `coordinateData` and the actual selected-Z
  membership equivalence `h_membership`, which identifies the regional
  stabilizer words.

Nothing here constructs these data from a bare adapted Hamel basis: every
field is an assumption that a regional (gLU) construction must still supply.
No axiom, `sorry`, `admit`, or unproved instance is introduced; the wrapper
theorem is a direct application of the existing checked theorem.

Build this module directly with

```
lake build AristotleCandidates.RegionalWitness
```
-/

namespace StabilizerHyperfinite

universe uV uC

variable {A : ℕ → Type*}
variable [∀ n, Semiring (A n)] [∀ n, StarRing (A n)] [∀ n, Algebra ℂ (A n)]
variable {f : ∀ n m : ℕ, n ≤ m → A n →⋆ₐ[ℂ] A m}
variable [DirectedSystem A (f · · ·)]

/-- All finite-stage input data required by
`exists_stabilizerState_of_adaptedCoordinateStages`, bundled as one record.

`V n` indexes the source Pauli-word basis at stage `n`, and `C n` is the
`PauliBit`-module in which the adapted coordinates of stage `n` live.  Every
field is *supplied data or a supplied identity*: the record does not build a
coordinate system out of a bare adapted Hamel basis. -/
structure RegionalStageWitness
    (A : ℕ → Type*) [∀ n, Semiring (A n)] [∀ n, StarRing (A n)]
    [∀ n, Algebra ℂ (A n)]
    (f : ∀ n m : ℕ, n ≤ m → A n →⋆ₐ[ℂ] A m)
    (V : ℕ → Type uV) (C : ℕ → Type uC)
    [∀ n, AddCommGroup (C n)] [∀ n, Module PauliBit (C n)] where
  /-- The pure/mixed coordinate pattern selecting the vector state at the
  marked coordinates. -/
  pure : ℕ → Bool
  /-- The regional stabilizer predicate on finite-stage source labels. -/
  isStabilizer : ∀ n, V n → Prop
  /-- Decidability of the regional stabilizer predicate. -/
  decIsStabilizer : ∀ n, DecidablePred (isStabilizer n)
  /-- The adapted Pauli coordinate basis supplied at each finite stage. -/
  coordinateData : ∀ n, AdaptedPauliCoordinateBasis (I := Fin n) (V := C n)
  /-- The finite-stage source Pauli-word bases. -/
  sourceBasis : ∀ n, Module.Basis (V n) ℂ (A n)
  /-- The source-label embeddings along the directed system. -/
  sourceLabelMap : ∀ n m, n ≤ m → V n → V m
  /-- The finite-qubit Pauli label attached to each source basis word. -/
  targetLabelMap : ∀ n, V n → FiniteQubitPauliLabel n
  /-- The coherent phase attached to each source basis word. -/
  phase : ∀ n, V n → ℂ
  /-- The finite-stage star-algebra equivalences onto the qubit tensor
  powers. -/
  e : ∀ n, A n ≃⋆ₐ[ℂ] QubitTensorPower n
  /-- Coherence clause: the directed system moves basis words to basis
  words. -/
  h_source : ∀ n m (h : n ≤ m) v,
    f n m h (sourceBasis n v) = sourceBasis m (sourceLabelMap n m h v)
  /-- Coherence clause: the phases are stable under enlarging the stage. -/
  h_phase : ∀ n m (h : n ≤ m) v,
    phase m (sourceLabelMap n m h v) = phase n v
  /-- Coherence clause: the target labels are stable under enlarging the
  stage. -/
  h_labels : ∀ n m (h : n ≤ m) v,
    targetLabelMap m (sourceLabelMap n m h v) =
      finiteQubitPauliLabelMap n m h (targetLabelMap n v)
  /-- Finite basis-word identification: each source basis word is sent to the
  phase times the concrete finite Pauli word. -/
  h_word : ∀ n v,
    e n (sourceBasis n v) =
      phase n v • finiteQubitPauliBasis n (targetLabelMap n v)
  /-- The actual regional identification: the adapted-coordinate image of the
  target label lies in the selected-Z stabilizer submodule exactly when the
  source word is a regional stabilizer word. -/
  h_membership : ∀ n v,
    (coordinateData n).coordinateLabelEquiv
        (finiteQubitPauliCoordinateLabel n (targetLabelMap n v)) ∈
      coordinateStabilizerSubmodule (coordinateData n)
        (finiteQubitPureCoordinates pure n) ↔
      isStabilizer n v

attribute [instance] RegionalStageWitness.decIsStabilizer

/-- **Regional finite-stage witness wrapper.**  Given the packaged
finite-stage input data, the algebraic directed limit carries an algebraic
state whose value on every source basis word is the phase-calibrated
stabilizer expectation

`omega ([sourceBasis n v]) = if isStabilizer n v then phase n v else 0`.

The proof is exactly an application of the existing checked theorem
`exists_stabilizerState_of_adaptedCoordinateStages`; no clause is weakened or
replaced. -/
theorem exists_stabilizerState_of_regionalStageWitness
    {V : ℕ → Type uV} {C : ℕ → Type uC}
    [∀ n, AddCommGroup (C n)] [∀ n, Module PauliBit (C n)]
    (W : RegionalStageWitness A f V C) :
    ∃ omega : DirectLimit A f →ₗ[ℂ] ℂ,
      IsAlgebraicState omega ∧
        ∀ n v, omega (DirectLimit.Module.of ℂ ℕ A f n (W.sourceBasis n v)) =
          if W.isStabilizer n v then W.phase n v else 0 :=
  exists_stabilizerState_of_adaptedCoordinateStages
    W.pure W.isStabilizer W.coordinateData W.sourceBasis W.sourceLabelMap
    W.targetLabelMap W.phase W.e W.h_source W.h_phase W.h_labels W.h_word
    W.h_membership

end StabilizerHyperfinite
