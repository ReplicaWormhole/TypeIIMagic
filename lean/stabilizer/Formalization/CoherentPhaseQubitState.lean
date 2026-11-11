import Formalization.CoherentBasisEquiv
import Formalization.PureCoordinateNotTracial
import Formalization.FiniteQubitPauliSelection

/-!
# A coherent phase-corrected coordinate system induces the regional state

This module turns finite Pauli-word coherence into the precise algebraic state
formula needed by the short-range stabilizer argument.  The theorem is
conditional on concrete finite-stage coordinate equivalences, but it derives
their direct-limit compatibility from finite basis-word checks.
-/

namespace StabilizerHyperfinite

variable {A : ℕ → Type*}
variable [∀ n, Semiring (A n)] [∀ n, StarRing (A n)] [∀ n, Algebra ℂ (A n)]
variable {f : ∀ n m : ℕ, n ≤ m → A n →⋆ₐ[ℂ] A m}
variable [DirectedSystem A (f · · ·)]

omit [DirectedSystem A (fun n m h => f n m h)] in
/-- Phase-corrected coordinate data that are coherent on source basis words
make the finite-stage coordinate equivalences commute on all elements. -/
theorem coherentPhaseQubitStages_compatible
    {V : ℕ → Type*}
    (sourceBasis : ∀ n, Module.Basis (V n) ℂ (A n))
    (sourceLabelMap : ∀ n m, n ≤ m → V n → V m)
    (targetLabelMap : ∀ n, V n → FiniteQubitPauliLabel n)
    (phase : ∀ n, V n → ℂ)
    (e : ∀ n, A n ≃⋆ₐ[ℂ] QubitTensorPower n)
    (h_source : ∀ n m (h : n ≤ m) v,
      f n m h (sourceBasis n v) = sourceBasis m (sourceLabelMap n m h v))
    (h_phase : ∀ n m (h : n ≤ m) v,
      phase m (sourceLabelMap n m h v) = phase n v)
    (h_labels : ∀ n m (h : n ≤ m) v,
      targetLabelMap m (sourceLabelMap n m h v) =
        finiteQubitPauliLabelMap n m h (targetLabelMap n v))
    (h_word : ∀ n v,
      e n (sourceBasis n v) =
        phase n v • finiteQubitPauliBasis n (targetLabelMap n v)) :
    ∀ n m (h : n ≤ m) x,
      e m (f n m h x) = qubitTensorPowerMap n m h (e n x) := by
  have h_target : ∀ n m (h : n ≤ m) v,
      qubitTensorPowerMap n m h
        (phase n v • finiteQubitPauliBasis n (targetLabelMap n v)) =
        phase m (sourceLabelMap n m h v) •
          finiteQubitPauliBasis m (targetLabelMap m (sourceLabelMap n m h v)) := by
    intro n m h v
    rw [map_smul, qubitTensorPowerMap_finiteQubitPauliBasis, h_phase, h_labels]
  intro n m h x
  exact starAlgEquiv_commutes_of_source_basis
    (sourceBasis n) (sourceBasis m) (sourceLabelMap n m h)
    (fun v => phase n v • finiteQubitPauliBasis n (targetLabelMap n v))
    (fun v => phase m v • finiteQubitPauliBasis m (targetLabelMap m v))
    (f n m h) (qubitTensorPowerMap n m h) (e n) (e m)
    (h_source n m h) (h_word n) (h_word m) (h_target n m h) x

/-- The coherent phase-corrected coordinate equivalences induce a star-algebra
equivalence from the source algebraic direct limit to the algebraic qubit UHF
direct limit. -/
noncomputable def coherentPhaseQubitLimitStarAlgEquiv
    {V : ℕ → Type*}
    (sourceBasis : ∀ n, Module.Basis (V n) ℂ (A n))
    (sourceLabelMap : ∀ n m, n ≤ m → V n → V m)
    (targetLabelMap : ∀ n, V n → FiniteQubitPauliLabel n)
    (phase : ∀ n, V n → ℂ)
    (e : ∀ n, A n ≃⋆ₐ[ℂ] QubitTensorPower n)
    (h_source : ∀ n m (h : n ≤ m) v,
      f n m h (sourceBasis n v) = sourceBasis m (sourceLabelMap n m h v))
    (h_phase : ∀ n m (h : n ≤ m) v,
      phase m (sourceLabelMap n m h v) = phase n v)
    (h_labels : ∀ n m (h : n ≤ m) v,
      targetLabelMap m (sourceLabelMap n m h v) =
        finiteQubitPauliLabelMap n m h (targetLabelMap n v))
    (h_word : ∀ n v,
      e n (sourceBasis n v) =
        phase n v • finiteQubitPauliBasis n (targetLabelMap n v)) :
    DirectLimit A f ≃⋆ₐ[ℂ] QubitUHFAlgebra :=
  algebraicLimitStarAlgEquiv e
    (coherentPhaseQubitStages_compatible sourceBasis sourceLabelMap
      targetLabelMap phase e h_source h_phase h_labels h_word)

/-- A coherent phase-corrected finite-coordinate system determines an
algebraic direct-limit state, with its value on every source Pauli basis word
given by the phase times the canonical pure/mixed selection indicator. -/
theorem exists_pureMixedState_of_coherentPhaseQubitStages
    {V : ℕ → Type*}
    (pure : ℕ → Bool)
    (sourceBasis : ∀ n, Module.Basis (V n) ℂ (A n))
    (sourceLabelMap : ∀ n m, n ≤ m → V n → V m)
    (targetLabelMap : ∀ n, V n → FiniteQubitPauliLabel n)
    (phase : ∀ n, V n → ℂ)
    (e : ∀ n, A n ≃⋆ₐ[ℂ] QubitTensorPower n)
    (h_source : ∀ n m (h : n ≤ m) v,
      f n m h (sourceBasis n v) = sourceBasis m (sourceLabelMap n m h v))
    (h_phase : ∀ n m (h : n ≤ m) v,
      phase m (sourceLabelMap n m h v) = phase n v)
    (h_labels : ∀ n m (h : n ≤ m) v,
      targetLabelMap m (sourceLabelMap n m h v) =
        finiteQubitPauliLabelMap n m h (targetLabelMap n v))
    (h_word : ∀ n v,
      e n (sourceBasis n v) =
        phase n v • finiteQubitPauliBasis n (targetLabelMap n v)) :
    ∃ omega : DirectLimit A f →ₗ[ℂ] ℂ,
      IsAlgebraicState omega ∧
        ∀ n v, omega (DirectLimit.Module.of ℂ ℕ A f n (sourceBasis n v)) =
          phase n v * qubitPureMixedPauliIndicator pure n (targetLabelMap n v) := by
  have eCompatible := coherentPhaseQubitStages_compatible
    sourceBasis sourceLabelMap targetLabelMap phase e h_source h_phase h_labels h_word
  obtain ⟨omega, h_omega, h_of⟩ :=
    exists_pureMixedState_of_coherentQubitStages pure e eCompatible
  refine ⟨omega, h_omega, ?_⟩
  intro n v
  rw [h_of, h_word, map_smul, finiteQubitPauliBasis_apply,
    qubitPureMixedState_finiteQubitPauliWord_eq_indicator]
  rfl

/-- In the finite coordinate ordering, the coherent pure/mixed state has the
exact selected-Z stabilizer expectation rule on every source basis word. -/
theorem exists_pureMixedState_of_coherentPhaseQubitStages_selectedZ
    {V : ℕ → Type*}
    (pure : ℕ → Bool)
    (sourceBasis : ∀ n, Module.Basis (V n) ℂ (A n))
    (sourceLabelMap : ∀ n m, n ≤ m → V n → V m)
    (targetLabelMap : ∀ n, V n → FiniteQubitPauliLabel n)
    (phase : ∀ n, V n → ℂ)
    (e : ∀ n, A n ≃⋆ₐ[ℂ] QubitTensorPower n)
    (h_source : ∀ n m (h : n ≤ m) v,
      f n m h (sourceBasis n v) = sourceBasis m (sourceLabelMap n m h v))
    (h_phase : ∀ n m (h : n ≤ m) v,
      phase m (sourceLabelMap n m h v) = phase n v)
    (h_labels : ∀ n m (h : n ≤ m) v,
      targetLabelMap m (sourceLabelMap n m h v) =
        finiteQubitPauliLabelMap n m h (targetLabelMap n v))
    (h_word : ∀ n v,
      e n (sourceBasis n v) =
        phase n v • finiteQubitPauliBasis n (targetLabelMap n v)) :
    ∃ omega : DirectLimit A f →ₗ[ℂ] ℂ,
      IsAlgebraicState omega ∧
        ∀ n v, omega (DirectLimit.Module.of ℂ ℕ A f n (sourceBasis n v)) =
          phase n v *
            finiteQubitPauliSelectedZIndicator pure n (targetLabelMap n v) := by
  obtain ⟨omega, h_state, h_word_value⟩ :=
    exists_pureMixedState_of_coherentPhaseQubitStages pure sourceBasis
      sourceLabelMap targetLabelMap phase e h_source h_phase h_labels h_word
  refine ⟨omega, h_state, ?_⟩
  intro n v
  rw [h_word_value, qubitPureMixedPauliIndicator_eq_selectedZIndicator]

/-- If the supplied finite coordinate data identify the selected-Z labels
with the actual finite-stage stabilizer words, then the coherent product state
has exactly the phase-calibrated stabilizer expectation formula on source basis
words.  The `h_selection` premise is the finite regional identification that
must be proved from gLU/refinement data in the intended application. -/
theorem exists_stabilizerState_of_coherentPhaseQubitStages
    {V : ℕ → Type*}
    (pure : ℕ → Bool)
    (isStabilizer : ∀ n, V n → Prop)
    [∀ n, DecidablePred (isStabilizer n)]
    (sourceBasis : ∀ n, Module.Basis (V n) ℂ (A n))
    (sourceLabelMap : ∀ n m, n ≤ m → V n → V m)
    (targetLabelMap : ∀ n, V n → FiniteQubitPauliLabel n)
    (phase : ∀ n, V n → ℂ)
    (e : ∀ n, A n ≃⋆ₐ[ℂ] QubitTensorPower n)
    (h_source : ∀ n m (h : n ≤ m) v,
      f n m h (sourceBasis n v) = sourceBasis m (sourceLabelMap n m h v))
    (h_phase : ∀ n m (h : n ≤ m) v,
      phase m (sourceLabelMap n m h v) = phase n v)
    (h_labels : ∀ n m (h : n ≤ m) v,
      targetLabelMap m (sourceLabelMap n m h v) =
        finiteQubitPauliLabelMap n m h (targetLabelMap n v))
    (h_word : ∀ n v,
      e n (sourceBasis n v) =
        phase n v • finiteQubitPauliBasis n (targetLabelMap n v))
    (h_selection : ∀ n v,
      finiteQubitPauliSelectedZ pure n (targetLabelMap n v) ↔
        isStabilizer n v) :
    ∃ omega : DirectLimit A f →ₗ[ℂ] ℂ,
      IsAlgebraicState omega ∧
        ∀ n v, omega (DirectLimit.Module.of ℂ ℕ A f n (sourceBasis n v)) =
          if isStabilizer n v then phase n v else 0 := by
  obtain ⟨omega, h_state, h_word_value⟩ :=
    exists_pureMixedState_of_coherentPhaseQubitStages_selectedZ pure sourceBasis
      sourceLabelMap targetLabelMap phase e h_source h_phase h_labels h_word
  refine ⟨omega, h_state, ?_⟩
  intro n v
  rw [h_word_value]
  by_cases h_stabilizer : isStabilizer n v
  · have h_selected : finiteQubitPauliSelectedZ pure n (targetLabelMap n v) :=
      (h_selection n v).mpr h_stabilizer
    simp [finiteQubitPauliSelectedZIndicator, h_selected, h_stabilizer]
  · have h_selected : ¬finiteQubitPauliSelectedZ pure n (targetLabelMap n v) := by
      intro h_selected
      exact h_stabilizer ((h_selection n v).mp h_selected)
    simp [finiteQubitPauliSelectedZIndicator, h_selected, h_stabilizer]

/-- The preceding phase-calibrated stabilizer state formula can be stated directly
with the selected-Z stabilizer submodule of an adapted coordinate basis.  This
is the exact finite-stage regional identification required of the gLU data. -/
theorem exists_stabilizerState_of_adaptedCoordinateStages
    {V C : ℕ → Type*}
    [∀ n, AddCommGroup (C n)] [∀ n, Module PauliBit (C n)]
    (pure : ℕ → Bool)
    (isStabilizer : ∀ n, V n → Prop)
    [∀ n, DecidablePred (isStabilizer n)]
    (coordinateData : ∀ n,
      AdaptedPauliCoordinateBasis (I := Fin n) (V := C n))
    (sourceBasis : ∀ n, Module.Basis (V n) ℂ (A n))
    (sourceLabelMap : ∀ n m, n ≤ m → V n → V m)
    (targetLabelMap : ∀ n, V n → FiniteQubitPauliLabel n)
    (phase : ∀ n, V n → ℂ)
    (e : ∀ n, A n ≃⋆ₐ[ℂ] QubitTensorPower n)
    (h_source : ∀ n m (h : n ≤ m) v,
      f n m h (sourceBasis n v) = sourceBasis m (sourceLabelMap n m h v))
    (h_phase : ∀ n m (h : n ≤ m) v,
      phase m (sourceLabelMap n m h v) = phase n v)
    (h_labels : ∀ n m (h : n ≤ m) v,
      targetLabelMap m (sourceLabelMap n m h v) =
        finiteQubitPauliLabelMap n m h (targetLabelMap n v))
    (h_word : ∀ n v,
      e n (sourceBasis n v) =
        phase n v • finiteQubitPauliBasis n (targetLabelMap n v))
    (h_membership : ∀ n v,
      (coordinateData n).coordinateLabelEquiv
          (finiteQubitPauliCoordinateLabel n (targetLabelMap n v)) ∈
        coordinateStabilizerSubmodule (coordinateData n)
          (finiteQubitPureCoordinates pure n) ↔
        isStabilizer n v) :
    ∃ omega : DirectLimit A f →ₗ[ℂ] ℂ,
      IsAlgebraicState omega ∧
        ∀ n v, omega (DirectLimit.Module.of ℂ ℕ A f n (sourceBasis n v)) =
          if isStabilizer n v then phase n v else 0 := by
  have h_selection : ∀ n v,
      finiteQubitPauliSelectedZ pure n (targetLabelMap n v) ↔
        isStabilizer n v := by
    intro n v
    exact (finiteQubitPauliSelectedZ_iff_mem_coordinateStabilizerSubmodule n
      (coordinateData n) pure (targetLabelMap n v)).trans (h_membership n v)
  exact exists_stabilizerState_of_coherentPhaseQubitStages pure isStabilizer
    sourceBasis sourceLabelMap targetLabelMap phase e h_source h_phase h_labels
    h_word h_selection

/-- The all-mixed coordinate specialization pulls the algebraic UHF trace
back to a tracial state on the source direct limit. -/
theorem coherentPhaseQubitAllMixed_isAlgebraicTracialState
    {V : ℕ → Type*}
    (sourceBasis : ∀ n, Module.Basis (V n) ℂ (A n))
    (sourceLabelMap : ∀ n m, n ≤ m → V n → V m)
    (targetLabelMap : ∀ n, V n → FiniteQubitPauliLabel n)
    (phase : ∀ n, V n → ℂ)
    (e : ∀ n, A n ≃⋆ₐ[ℂ] QubitTensorPower n)
    (h_source : ∀ n m (h : n ≤ m) v,
      f n m h (sourceBasis n v) = sourceBasis m (sourceLabelMap n m h v))
    (h_phase : ∀ n m (h : n ≤ m) v,
      phase m (sourceLabelMap n m h v) = phase n v)
    (h_labels : ∀ n m (h : n ≤ m) v,
      targetLabelMap m (sourceLabelMap n m h v) =
        finiteQubitPauliLabelMap n m h (targetLabelMap n v))
    (h_word : ∀ n v,
      e n (sourceBasis n v) =
        phase n v • finiteQubitPauliBasis n (targetLabelMap n v)) :
    IsAlgebraicTracialState
      (pullback
        (coherentPhaseQubitLimitStarAlgEquiv sourceBasis sourceLabelMap
          targetLabelMap phase e h_source h_phase h_labels h_word)
        qubitUHFTrace) := by
  exact isAlgebraicTracialState_pullback
    (coherentPhaseQubitLimitStarAlgEquiv sourceBasis sourceLabelMap
      targetLabelMap phase e h_source h_phase h_labels h_word)
    qubitUHFTrace qubitUHFTrace_isAlgebraicTracialState

/-- Under coherent phase-corrected coordinates, the pulled-back pure/mixed
product state is tracial exactly in the all-mixed case. -/
theorem coherentPhaseQubitState_isAlgebraicTracialState_iff
    {V : ℕ → Type*}
    (pure : ℕ → Bool)
    (sourceBasis : ∀ n, Module.Basis (V n) ℂ (A n))
    (sourceLabelMap : ∀ n m, n ≤ m → V n → V m)
    (targetLabelMap : ∀ n, V n → FiniteQubitPauliLabel n)
    (phase : ∀ n, V n → ℂ)
    (e : ∀ n, A n ≃⋆ₐ[ℂ] QubitTensorPower n)
    (h_source : ∀ n m (h : n ≤ m) v,
      f n m h (sourceBasis n v) = sourceBasis m (sourceLabelMap n m h v))
    (h_phase : ∀ n m (h : n ≤ m) v,
      phase m (sourceLabelMap n m h v) = phase n v)
    (h_labels : ∀ n m (h : n ≤ m) v,
      targetLabelMap m (sourceLabelMap n m h v) =
        finiteQubitPauliLabelMap n m h (targetLabelMap n v))
    (h_word : ∀ n v,
      e n (sourceBasis n v) =
        phase n v • finiteQubitPauliBasis n (targetLabelMap n v)) :
    IsAlgebraicTracialState
      (pullback
        (coherentPhaseQubitLimitStarAlgEquiv sourceBasis sourceLabelMap
          targetLabelMap phase e h_source h_phase h_labels h_word)
        (qubitPureMixedUHFState pure)) ↔
      ∀ n, pure n = false := by
  exact (isAlgebraicTracialState_pullback_iff
    (coherentPhaseQubitLimitStarAlgEquiv sourceBasis sourceLabelMap
      targetLabelMap phase e h_source h_phase h_labels h_word)
    (qubitPureMixedUHFState pure)).trans
      (qubitPureMixedUHFState_isAlgebraicTracialState_iff pure)

end StabilizerHyperfinite
