import Formalization.FiniteQubitPauliSelection

/-!
# Conditional finite stabilizer product-state identification

**Context declaration.** Source basis: `main.tex:1671-1679, 1927-1931`.

This file records a finite, *explicitly conditional* bridge between a supplied
selected-Z stabilizer description and the finite pure/mixed qubit product
state of `Formalization.FinitePureMixedQubitState`.

All of the following are **supplied data / auxiliary assumptions**; none of
them is constructed here:

* a finite qubit stage `n` together with a supplied adapted coordinate basis
  `data : AdaptedPauliCoordinateBasis (I := Fin n) (V := V)`;
* a supplied pure/mixed coordinate pattern `pure : ℕ → Bool`;
* a supplied type `W` of source Pauli basis words together with a supplied map
  `label : W → FiniteQubitPauliLabel n` into finite qubit Pauli labels;
* a supplied source stabilizer predicate `isStabilizer : W → Prop`; and
* a supplied identification hypothesis saying that source stabilizer
  membership holds exactly when the image label lies in the selected-Z
  stabilizer submodule `coordinateStabilizerSubmodule data
  (finiteQubitPureCoordinates pure n)`.

The conclusion — that the finite product-state expectation of every supplied
Pauli basis word equals the stabilizer indicator — is conditional on exactly
these assumptions.  **No regional realization is constructed here**: the
adapted basis, the word map, and the identification hypothesis are all
hypotheses, not outputs.  Nothing about gLU circuits, refinement,
layer-coherence, C⋆ completion, GNS representations, or von Neumann algebras
is asserted or used.

The two reused inputs are
`StabilizerHyperfinite.finiteQubitPauliSelectedZ_iff_mem_coordinateStabilizerSubmodule`
and
`StabilizerHyperfinite.qubitPureMixedState_finiteQubitPauliWord_eq_selectedZIndicator`.
-/

namespace AristotleCandidates

open StabilizerHyperfinite

section FiniteStabilizerProductState

variable {V W : Type*} [AddCommGroup V] [Module PauliBit V]

/-- The complex indicator of a supplied source stabilizer predicate. -/
noncomputable def stabilizerWordIndicator (isStabilizer : W → Prop) (w : W) : ℂ := by
  classical
  exact if isStabilizer w then 1 else 0

/-- A **supplied** finite stabilizer-word realization on the qubit stage `n`.

It bundles the auxiliary data and the single identification hypothesis; it is
never constructed in this file. -/
structure FiniteStabilizerWordRealization (n : ℕ)
    (data : AdaptedPauliCoordinateBasis (I := Fin n) (V := V))
    (pure : ℕ → Bool) (W : Type*) where
  /-- The supplied map from source Pauli basis words to finite qubit labels. -/
  label : W → FiniteQubitPauliLabel n
  /-- The supplied source stabilizer predicate. -/
  isStabilizer : W → Prop
  /-- The supplied identification hypothesis: source stabilizer membership is
  exactly membership of the image coordinate label in the selected-Z
  stabilizer submodule. -/
  isStabilizer_iff : ∀ w : W, isStabilizer w ↔
    data.coordinateLabelEquiv (finiteQubitPauliCoordinateLabel n (label w)) ∈
      coordinateStabilizerSubmodule data (finiteQubitPureCoordinates pure n)

namespace FiniteStabilizerWordRealization

variable {n : ℕ} {data : AdaptedPauliCoordinateBasis (I := Fin n) (V := V)}
  {pure : ℕ → Bool}

/-- Under the supplied identification hypothesis, source stabilizer membership
is exactly the concrete selected-Z condition on the associated finite qubit
Pauli label. -/
theorem isStabilizer_iff_selectedZ
    (realization : FiniteStabilizerWordRealization n data pure W) (w : W) :
    realization.isStabilizer w ↔
      finiteQubitPauliSelectedZ pure n (realization.label w) :=
  (realization.isStabilizer_iff w).trans
    (finiteQubitPauliSelectedZ_iff_mem_coordinateStabilizerSubmodule n data pure
      (realization.label w)).symm

/-- Under the supplied identification hypothesis, the selected-Z indicator of a
source word's label is its stabilizer indicator. -/
theorem selectedZIndicator_label_eq_stabilizerWordIndicator
    (realization : FiniteStabilizerWordRealization n data pure W) (w : W) :
    finiteQubitPauliSelectedZIndicator pure n (realization.label w) =
      stabilizerWordIndicator realization.isStabilizer w := by
  classical
  simp only [finiteQubitPauliSelectedZIndicator, stabilizerWordIndicator]
  by_cases h : realization.isStabilizer w
  · rw [if_pos h, if_pos ((realization.isStabilizer_iff_selectedZ w).mp h)]
  · rw [if_neg h, if_neg (fun hz => h ((realization.isStabilizer_iff_selectedZ w).mpr hz))]

/-- **Conditional finite stabilizer product-state identification.**  Given the
supplied adapted coordinate basis, word map and identification hypothesis, the
finite pure/mixed product-state expectation of every supplied Pauli basis word
equals the selected-Z indicator of its finite qubit label. -/
theorem qubitPureMixedState_label_eq_selectedZIndicator
    (realization : FiniteStabilizerWordRealization n data pure W) (w : W) :
    qubitPureMixedState pure n (finiteQubitPauliWord n (realization.label w)) =
      finiteQubitPauliSelectedZIndicator pure n (realization.label w) :=
  qubitPureMixedState_finiteQubitPauliWord_eq_selectedZIndicator pure n
    (realization.label w)

/-- **Main conditional statement.**  The finite product-state expectation of
every supplied Pauli basis word is `1` on source stabilizer words and `0`
otherwise. -/
theorem qubitPureMixedState_label_eq_stabilizerWordIndicator
    (realization : FiniteStabilizerWordRealization n data pure W) (w : W) :
    qubitPureMixedState pure n (finiteQubitPauliWord n (realization.label w)) =
      stabilizerWordIndicator realization.isStabilizer w := by
  rw [realization.qubitPureMixedState_label_eq_selectedZIndicator w,
    realization.selectedZIndicator_label_eq_stabilizerWordIndicator w]

/-- The expectation is exactly `1` on a supplied stabilizer word. -/
theorem qubitPureMixedState_label_eq_one
    (realization : FiniteStabilizerWordRealization n data pure W) {w : W}
    (hw : realization.isStabilizer w) :
    qubitPureMixedState pure n (finiteQubitPauliWord n (realization.label w)) = 1 := by
  classical
  rw [realization.qubitPureMixedState_label_eq_stabilizerWordIndicator w,
    stabilizerWordIndicator, if_pos hw]

/-- The expectation vanishes on every supplied non-stabilizer word. -/
theorem qubitPureMixedState_label_eq_zero
    (realization : FiniteStabilizerWordRealization n data pure W) {w : W}
    (hw : ¬ realization.isStabilizer w) :
    qubitPureMixedState pure n (finiteQubitPauliWord n (realization.label w)) = 0 := by
  classical
  rw [realization.qubitPureMixedState_label_eq_stabilizerWordIndicator w,
    stabilizerWordIndicator, if_neg hw]

end FiniteStabilizerWordRealization

/-- Unbundled form of the conditional identification: the data and the
identification hypothesis are passed as explicit arguments. -/
theorem qubitPureMixedState_eq_stabilizerWordIndicator_of_identification
    {n : ℕ} (data : AdaptedPauliCoordinateBasis (I := Fin n) (V := V))
    (pure : ℕ → Bool) (label : W → FiniteQubitPauliLabel n)
    (isStabilizer : W → Prop)
    (identification : ∀ w : W, isStabilizer w ↔
      data.coordinateLabelEquiv (finiteQubitPauliCoordinateLabel n (label w)) ∈
        coordinateStabilizerSubmodule data (finiteQubitPureCoordinates pure n))
    (w : W) :
    qubitPureMixedState pure n (finiteQubitPauliWord n (label w)) =
      stabilizerWordIndicator isStabilizer w :=
  FiniteStabilizerWordRealization.qubitPureMixedState_label_eq_stabilizerWordIndicator
    { label := label, isStabilizer := isStabilizer, isStabilizer_iff := identification } w

end FiniteStabilizerProductState

end AristotleCandidates
