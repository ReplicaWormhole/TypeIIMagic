import Formalization.FinitePureMixedQubitState
import Formalization.AdaptedStabilizerSubspace

/-!
# Finite qubit Pauli selection in coordinate form

The recursive labels of the finite qubit tower can be read as a finite list of
X/Z coordinates.  In these coordinates the pure/mixed product state has the
same selection rule as a selected-Z stabilizer subspace: a pure coordinate
forbids its X exponent, while a mixed coordinate permits only the identity.
-/

namespace StabilizerHyperfinite

/-- Read the label attached to a finite qubit coordinate.  The newest qubit
at stage `n + 1` is coordinate zero, matching the recursive tensor order. -/
def finiteQubitPauliLabelAt : (n : ℕ) →
    FiniteQubitPauliLabel n → Fin n → SingleQubitLabel
  | 0, _, i => Fin.elim0 i
  | n + 1, v, i =>
      Fin.cases v.1 (fun j => finiteQubitPauliLabelAt n v.2 j) i

/-- The pure/mixed assignment at a finite coordinate, in the same ordering as
`finiteQubitPauliLabelAt`. -/
def finiteQubitPureAt (pure : ℕ → Bool) : (n : ℕ) → Fin n → Bool
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases (pure n) (finiteQubitPureAt pure n) i

/-- The pure finite coordinates, viewed as the selected Z-coordinate index
set for the abstract adapted-coordinate construction. -/
def finiteQubitPureCoordinates (pure : ℕ → Bool) (n : ℕ) : Set (Fin n) :=
  {i | finiteQubitPureAt pure n i}

/-- Interpret a binary finite-index exponent as an element of the Pauli-bit
field used by the adapted-coordinate formalization. -/
def pauliBitOfFinTwo (bit : Fin 2) : PauliBit := bit.val

/-- Convert an ordered finite-qubit word label into the finitely supported
Z/X coordinate label used by `AdaptedStabilizerSubspace`: the left summand is
the Z exponent and the right summand is the X exponent. -/
noncomputable def finiteQubitPauliCoordinateLabel (n : ℕ)
    (v : FiniteQubitPauliLabel n) : PauliCoordinateLabels (Fin n) :=
  Finsupp.equivFunOnFinite.symm fun index =>
    match index with
    | Sum.inl i => pauliBitOfFinTwo (finiteQubitPauliLabelAt n v i).2
    | Sum.inr i => pauliBitOfFinTwo (finiteQubitPauliLabelAt n v i).1

/-- A binary exponent is zero as a Pauli bit exactly when it is the zero
finite index. -/
theorem pauliBitOfFinTwo_eq_zero_iff (bit : Fin 2) :
    pauliBitOfFinTwo bit = 0 ↔ bit = 0 := by
  fin_cases bit <;> norm_num [pauliBitOfFinTwo]

/-- The finite coordinate label records the Z exponent on the left summand. -/
theorem finiteQubitPauliCoordinateLabel_inl (n : ℕ)
    (v : FiniteQubitPauliLabel n) (i : Fin n) :
    finiteQubitPauliCoordinateLabel n v (Sum.inl i) =
      pauliBitOfFinTwo (finiteQubitPauliLabelAt n v i).2 := by
  rfl

/-- The finite coordinate label records the X exponent on the right summand. -/
theorem finiteQubitPauliCoordinateLabel_inr (n : ℕ)
    (v : FiniteQubitPauliLabel n) (i : Fin n) :
    finiteQubitPauliCoordinateLabel n v (Sum.inr i) =
      pauliBitOfFinTwo (finiteQubitPauliLabelAt n v i).1 := by
  rfl

/-- The selected-Z condition on a finite qubit Pauli label.  A selected
coordinate is pure and hence may carry only a Z exponent; an unselected
coordinate is mixed and hence must carry the identity label. -/
def finiteQubitPauliSelectedZ (pure : ℕ → Bool) (n : ℕ)
    (v : FiniteQubitPauliLabel n) : Prop :=
  ∀ i, if finiteQubitPureAt pure n i
    then (finiteQubitPauliLabelAt n v i).1 = 0
    else finiteQubitPauliLabelAt n v i = 0

/-- The indicator of the selected-Z condition on a finite qubit Pauli label. -/
noncomputable def finiteQubitPauliSelectedZIndicator (pure : ℕ → Bool) (n : ℕ)
    (v : FiniteQubitPauliLabel n) : ℂ := by
  classical
  exact if finiteQubitPauliSelectedZ pure n v then 1 else 0

/-- The recursive pure/mixed Pauli selection rule is exactly the selected-Z
coordinate rule: pure coordinates kill X exponents and mixed coordinates kill
both X and Z exponents. -/
theorem qubitPureMixedPauliAllowed_iff_coordinateSelection
    (pure : ℕ → Bool) (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedPauliAllowed pure n v ↔
      finiteQubitPauliSelectedZ pure n v := by
  change qubitPureMixedPauliAllowed pure n v ↔
    ∀ i, if finiteQubitPureAt pure n i
      then (finiteQubitPauliLabelAt n v i).1 = 0
      else finiteQubitPauliLabelAt n v i = 0
  induction n with
  | zero => simp [qubitPureMixedPauliAllowed, finiteQubitPureAt]
  | succ n ih =>
    rcases v with ⟨head, tail⟩
    simp [qubitPureMixedPauliAllowed, finiteQubitPureAt,
      finiteQubitPauliLabelAt, Fin.forall_fin_succ, ih]

/-- The concrete selected-Z predicate is exactly support containment in the
selected Z-coordinate set of the abstract adapted-coordinate label space. -/
theorem finiteQubitPauliSelectedZ_iff_coordinateSupport
    (pure : ℕ → Bool) (n : ℕ) (v : FiniteQubitPauliLabel n) :
    finiteQubitPauliSelectedZ pure n v ↔
      ((finiteQubitPauliCoordinateLabel n v).support : Set (Sum (Fin n) (Fin n))) ⊆
        Sum.inl '' finiteQubitPureCoordinates pure n := by
  rw [coordinateSupport_subset_selectedZ_iff]
  constructor
  · intro h
    constructor
    · intro i
      rw [finiteQubitPauliCoordinateLabel_inr]
      apply (pauliBitOfFinTwo_eq_zero_iff _).mpr
      by_cases h_pure : finiteQubitPureAt pure n i
      · simpa [finiteQubitPauliSelectedZ, h_pure] using h i
      · have h_zero : finiteQubitPauliLabelAt n v i = 0 := by
          simpa [finiteQubitPauliSelectedZ, h_pure] using h i
        exact congrArg Prod.fst h_zero
    · intro i h_unselected
      rw [finiteQubitPauliCoordinateLabel_inl]
      apply (pauliBitOfFinTwo_eq_zero_iff _).mpr
      by_cases h_pure : finiteQubitPureAt pure n i
      · exact (h_unselected h_pure).elim
      · have h_zero : finiteQubitPauliLabelAt n v i = 0 := by
          simpa [finiteQubitPauliSelectedZ, h_pure] using h i
        exact congrArg Prod.snd h_zero
  · intro h i
    by_cases h_pure : finiteQubitPureAt pure n i
    · rw [if_pos h_pure]
      apply (pauliBitOfFinTwo_eq_zero_iff _).mp
      rw [← finiteQubitPauliCoordinateLabel_inr]
      exact h.1 i
    · rw [if_neg h_pure]
      apply Prod.ext
      · change (finiteQubitPauliLabelAt n v i).1 = 0
        apply (pauliBitOfFinTwo_eq_zero_iff _).mp
        rw [← finiteQubitPauliCoordinateLabel_inr]
        exact h.1 i
      · change (finiteQubitPauliLabelAt n v i).2 = 0
        apply (pauliBitOfFinTwo_eq_zero_iff _).mp
        rw [← finiteQubitPauliCoordinateLabel_inl]
        apply h.2 i
        exact h_pure

/-- After choosing an adapted coordinate basis, the finite pure/mixed Pauli
selection rule is literal membership in the selected-Z stabilizer submodule. -/
theorem finiteQubitPauliSelectedZ_iff_mem_coordinateStabilizerSubmodule
    {V : Type*} [AddCommGroup V] [Module PauliBit V]
    (n : ℕ) (data : AdaptedPauliCoordinateBasis (I := Fin n) (V := V))
    (pure : ℕ → Bool) (v : FiniteQubitPauliLabel n) :
    finiteQubitPauliSelectedZ pure n v ↔
      data.coordinateLabelEquiv (finiteQubitPauliCoordinateLabel n v) ∈
        coordinateStabilizerSubmodule data (finiteQubitPureCoordinates pure n) := by
  exact (finiteQubitPauliSelectedZ_iff_coordinateSupport pure n v).trans
    (coordinateLabelEquiv_mem_coordinateStabilizerSubmodule_iff data
      (finiteQubitPureCoordinates pure n)
      (finiteQubitPauliCoordinateLabel n v)).symm

/-- The existing pure/mixed Pauli indicator is the selected-Z stabilizer
indicator in finite coordinates. -/
theorem qubitPureMixedPauliIndicator_eq_selectedZIndicator
    (pure : ℕ → Bool) (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedPauliIndicator pure n v =
      finiteQubitPauliSelectedZIndicator pure n v := by
  simp only [qubitPureMixedPauliIndicator, finiteQubitPauliSelectedZIndicator]
  rw [qubitPureMixedPauliAllowed_iff_coordinateSelection]

/-- The finite pure/mixed density-state expectation is one precisely on the
selected-Z stabilizer labels and vanishes on every other finite Pauli label. -/
theorem qubitPureMixedState_finiteQubitPauliWord_eq_selectedZIndicator
    (pure : ℕ → Bool) (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitPureMixedState pure n (finiteQubitPauliWord n v) =
      finiteQubitPauliSelectedZIndicator pure n v := by
  rw [qubitPureMixedState_finiteQubitPauliWord_eq_indicator,
    qubitPureMixedPauliIndicator_eq_selectedZIndicator]

end StabilizerHyperfinite
