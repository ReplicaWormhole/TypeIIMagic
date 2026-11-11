import Formalization.FinitePureMixedQubitState

/-!
# A pure coordinate obstructs traciality

The pure/mixed product state is tracial exactly in its all-mixed sector.  This
module proves the obstruction direction at an arbitrary finite coordinate and
then lifts it to the algebraic UHF direct limit.
-/

namespace StabilizerHyperfinite

/-- If the qubit adjoined at stage `n + 1` is pure, the finite product state
cannot be cyclic. -/
theorem qubitPureMixedState_succ_not_isUnitalTracial
    (pure : ℕ → Bool) (n : ℕ) (h_pure : pure n = true) :
    ¬ IsUnitalTracial (qubitPureMixedState pure (n + 1)) := by
  intro h
  let e01 : QubitTensorPower (n + 1) := !![(0 : QubitTensorPower n), 1; 0, 0]
  let e10 : QubitTensorPower (n + 1) := !![(0 : QubitTensorPower n), 0; 1, 0]
  have h_cyclic := h.cyclic e01 e10
  change (if pure n then qubitKetZeroStateOver (qubitPureMixedState pure n)
    else normalizedMatrixTraceOver (Fin 2) (qubitPureMixedState pure n))
      (e01 * e10) =
    (if pure n then qubitKetZeroStateOver (qubitPureMixedState pure n)
      else normalizedMatrixTraceOver (Fin 2) (qubitPureMixedState pure n))
      (e10 * e01) at h_cyclic
  rw [h_pure] at h_cyclic
  change qubitPureMixedState pure n ((e01 * e10) 0 0) =
    qubitPureMixedState pure n ((e10 * e01) 0 0) at h_cyclic
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h_cyclic
  norm_num [e01, e10] at h_cyclic
  have h_one := (qubitPureMixedState_isAlgebraicState pure n).map_one
  rw [h_one] at h_cyclic
  norm_num at h_cyclic

/-- A finite product state with a pure newly adjoined qubit is not an
algebraic tracial state. -/
theorem qubitPureMixedState_succ_not_isAlgebraicTracialState
    (pure : ℕ → Bool) (n : ℕ) (h_pure : pure n = true) :
    ¬ IsAlgebraicTracialState (qubitPureMixedState pure (n + 1)) := by
  intro h
  exact qubitPureMixedState_succ_not_isUnitalTracial pure n h_pure
    ⟨h.map_one, h.cyclic⟩

/-- If any coordinate of the algebraic UHF product state is pure, the induced
direct-limit state cannot be cyclic. -/
theorem qubitPureMixedUHFState_not_isUnitalTracial
    (pure : ℕ → Bool) (h_pure : ∃ n, pure n = true) :
    ¬ IsUnitalTracial (qubitPureMixedUHFState pure) := by
  rcases h_pure with ⟨n, h_pure⟩
  intro h
  let e01 : QubitTensorPower (n + 1) := !![(0 : QubitTensorPower n), 1; 0, 0]
  let e10 : QubitTensorPower (n + 1) := !![(0 : QubitTensorPower n), 0; 1, 0]
  let iota := algebraicLimitStageStarAlgHom (A := QubitTensorPower)
    (f := qubitTensorPowerMap) (n + 1)
  have h_cyclic := h.cyclic
    (iota e01) (iota e10)
  have h_e01 : iota e01 * iota e10 = iota (e01 * e10) :=
    (iota.map_mul e01 e10).symm
  have h_e10 : iota e10 * iota e01 = iota (e10 * e01) :=
    (iota.map_mul e10 e01).symm
  rw [h_e01, h_e10] at h_cyclic
  simp only [iota, algebraicLimitStageStarAlgHom_apply] at h_cyclic
  rw [qubitPureMixedUHFState_of, qubitPureMixedUHFState_of] at h_cyclic
  change qubitPureMixedState pure (n + 1) (e01 * e10) =
    qubitPureMixedState pure (n + 1) (e10 * e01) at h_cyclic
  change (if pure n then qubitKetZeroStateOver (qubitPureMixedState pure n)
    else normalizedMatrixTraceOver (Fin 2) (qubitPureMixedState pure n))
      (e01 * e10) =
    (if pure n then qubitKetZeroStateOver (qubitPureMixedState pure n)
      else normalizedMatrixTraceOver (Fin 2) (qubitPureMixedState pure n))
      (e10 * e01) at h_cyclic
  rw [h_pure] at h_cyclic
  change qubitPureMixedState pure n ((e01 * e10) 0 0) =
    qubitPureMixedState pure n ((e10 * e01) 0 0) at h_cyclic
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h_cyclic
  norm_num [e01, e10] at h_cyclic
  have h_one := (qubitPureMixedState_isAlgebraicState pure n).map_one
  rw [h_one] at h_cyclic
  norm_num at h_cyclic

/-- In particular, a pure coordinate prevents the UHF product state from
being an algebraic tracial state. -/
theorem qubitPureMixedUHFState_not_isAlgebraicTracialState
    (pure : ℕ → Bool) (h_pure : ∃ n, pure n = true) :
    ¬ IsAlgebraicTracialState (qubitPureMixedUHFState pure) := by
  intro h
  exact qubitPureMixedUHFState_not_isUnitalTracial pure h_pure
    ⟨h.map_one, h.cyclic⟩

/-- The algebraic UHF product state is tracial exactly when every coordinate
is maximally mixed. -/
theorem qubitPureMixedUHFState_isAlgebraicTracialState_iff
    (pure : ℕ → Bool) :
    IsAlgebraicTracialState (qubitPureMixedUHFState pure) ↔
      ∀ n, pure n = false := by
  constructor
  · intro h n
    by_contra h_not_false
    exact qubitPureMixedUHFState_not_isAlgebraicTracialState pure
      ⟨n, Bool.eq_true_of_not_eq_false h_not_false⟩ h
  · intro h_all_mixed
    have h_pure : pure = fun _ => false := funext h_all_mixed
    rw [h_pure, qubitPureMixedUHFState_allMixed]
    exact qubitUHFTrace_isAlgebraicTracialState

end StabilizerHyperfinite
