import FiniteFiber.FiniteRegionQubitAlgebra

/-!
# Phase-free finite-region Pauli matrices

For a finite region `F : Finset Site` and a Hermitian one-qubit Pauli label at
every site of `F`, this file constructs the literal tensor-product matrix on
the computational basis `finiteRegionBasis F = (↥F → Fin 2)` by the
coordinate-free formula

`P_F(a)(x, y) = ∏ i : ↥F, PauliLabel.matrix (a i) (x i) (y i)`.

It proves that the all-identity string is the matrix identity, that every such
string is self-adjoint, and that the checked local inclusion
`finiteRegionEmbed F F' hFF'` sends `P_F(a)` to `P_{F'}` of the labels padded
by the identity on `F' \ F`.

This is deliberately **not** a representation of the normal-form Pauli group:
no multiplication, closure, homomorphism, support, coherence, colimit, state,
or GNS statement is made here.
-/

namespace FiniteFiber

open scoped BigOperators Kronecker

variable {Site : Type*} [DecidableEq Site]

/--
The finite-region phase-free Pauli matrix: the literal tensor product over the
sites of `F` of the one-qubit Hermitian Pauli matrices, written in the
computational basis of the region.
-/
noncomputable def finiteRegionPauliMatrix
    (F : Finset Site) (a : ↥F → PauliLabel) :
    finiteRegionQubitAlgebra F :=
  fun x y => ∏ i : ↥F, PauliLabel.matrix (a i) (x i) (y i)

/-- Labels on `F` padded by the identity label on the complement `F' \ F`. -/
noncomputable def finiteRegionPadLabels
    (F F' : Finset Site) (a : ↥F → PauliLabel) :
    ↥F' → PauliLabel :=
  fun x => if hx : x.val ∈ F then a ⟨x.val, hx⟩ else PauliLabel.I

/--
An entrywise product of one-qubit identity entries is the identity entry of the
product basis.
-/
private theorem prod_one_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w z : ι → Fin 2) :
    (∏ i : ι, (1 : Matrix (Fin 2) (Fin 2) ℂ) (w i) (z i)) =
      (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) w z := by
  classical
  by_cases hwz : w = z
  · subst hwz
    simp
  · obtain ⟨i, hi⟩ : ∃ i, w i ≠ z i := by
      by_contra hcon
      exact hwz (funext fun i => not_not.mp (fun h => hcon ⟨i, h⟩))
    have hzero : (1 : Matrix (Fin 2) (Fin 2) ℂ) (w i) (z i) = 0 :=
      Matrix.one_apply_ne hi
    rw [Matrix.one_apply_ne hwz, Finset.prod_eq_zero (Finset.mem_univ i) hzero]

/-- The all-identity finite-region Pauli string is the identity matrix. -/
theorem finiteRegionPauliMatrix_all_I (F : Finset Site) :
    finiteRegionPauliMatrix F (fun _ => PauliLabel.I) = 1 := by
  classical
  funext x y
  simp only [finiteRegionPauliMatrix, PauliLabel.matrix_I_eq_one]
  exact prod_one_apply x y

omit [DecidableEq Site] in
/-- Every finite-region phase-free Pauli matrix is self-adjoint. -/
theorem finiteRegionPauliMatrix_isSelfAdjoint
    (F : Finset Site) (a : ↥F → PauliLabel) :
    IsSelfAdjoint (finiteRegionPauliMatrix F a) := by
  classical
  have hone : ∀ (b : PauliLabel) (i j : Fin 2),
      star (PauliLabel.matrix b j i) = PauliLabel.matrix b i j := by
    intro b i j
    have hb : Matrix.conjTranspose (PauliLabel.matrix b) = PauliLabel.matrix b := by
      simpa [Matrix.star_eq_conjTranspose] using PauliLabel.matrix_isSelfAdjoint b
    calc star (PauliLabel.matrix b j i)
        = Matrix.conjTranspose (PauliLabel.matrix b) i j := by
          simp [Matrix.conjTranspose_apply]
      _ = PauliLabel.matrix b i j := by rw [hb]
  show star (finiteRegionPauliMatrix F a) = finiteRegionPauliMatrix F a
  rw [Matrix.star_eq_conjTranspose]
  funext x y
  simp only [Matrix.conjTranspose_apply, finiteRegionPauliMatrix, star_prod]
  exact Finset.prod_congr rfl fun i _ => hone (a i) (x i) (y i)

/-- The sites of `F'` split as the sites of `F` together with those of `F' \ F`. -/
private def regionSumEquiv (F F' : Finset Site) (hFF' : F ⊆ F') :
    (↥F ⊕ ↥(F' \ F)) ≃ ↥F' where
  toFun := Sum.elim (fun i => ⟨i.val, hFF' i.property⟩)
    (fun i => ⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩)
  invFun := fun x =>
    if hx : x.val ∈ F then Sum.inl ⟨x.val, hx⟩
    else Sum.inr ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩
  left_inv := by
    rintro (i | i)
    · simp [i.property]
    · simp [(Finset.mem_sdiff.mp i.property).2]
  right_inv := by
    intro x
    by_cases hx : x.val ∈ F <;> simp [hx]

/-- The padding theorem: the local inclusion pads the labels by the identity. -/
theorem finiteRegionEmbed_pauliMatrix
    (F F' : Finset Site) (hFF' : F ⊆ F')
    (a : ↥F → PauliLabel) :
    finiteRegionEmbed F F' hFF' (finiteRegionPauliMatrix F a) =
      finiteRegionPauliMatrix F' (finiteRegionPadLabels F F' a) := by
  classical
  rw [finiteRegionEmbed_apply]
  funext u v
  rw [Matrix.reindex_apply]
  simp only [Equiv.symm_symm, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    finiteRegionPauliMatrix]
  -- split the product over `F'` along `F ⊕ (F' \ F)`
  have hsplit :
      (∏ i : ↥F', PauliLabel.matrix (finiteRegionPadLabels F F' a i) (u i) (v i)) =
        (∏ i : ↥F, PauliLabel.matrix (finiteRegionPadLabels F F' a
            ((regionSumEquiv F F' hFF') (Sum.inl i)))
            (u ((regionSumEquiv F F' hFF') (Sum.inl i)))
            (v ((regionSumEquiv F F' hFF') (Sum.inl i)))) *
        (∏ i : ↥(F' \ F), PauliLabel.matrix (finiteRegionPadLabels F F' a
            ((regionSumEquiv F F' hFF') (Sum.inr i)))
            (u ((regionSumEquiv F F' hFF') (Sum.inr i)))
            (v ((regionSumEquiv F F' hFF') (Sum.inr i)))) := by
    have h1 :
        (∏ i : ↥F', PauliLabel.matrix (finiteRegionPadLabels F F' a i) (u i) (v i)) =
          ∏ j : ↥F ⊕ ↥(F' \ F),
            PauliLabel.matrix (finiteRegionPadLabels F F' a
              ((regionSumEquiv F F' hFF') j))
              (u ((regionSumEquiv F F' hFF') j)) (v ((regionSumEquiv F F' hFF') j)) :=
      (Fintype.prod_equiv (regionSumEquiv F F' hFF') _ _ (fun _ => rfl)).symm
    rw [h1, Fintype.prod_sum_type]
  rw [hsplit]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have : finiteRegionPadLabels F F' a ((regionSumEquiv F F' hFF') (Sum.inl i)) = a i := by
      simp [finiteRegionPadLabels, regionSumEquiv, i.property]
    rw [this]
    rfl
  · have hfac : ∀ i : ↥(F' \ F),
        PauliLabel.matrix (finiteRegionPadLabels F F' a
            ((regionSumEquiv F F' hFF') (Sum.inr i)))
            (u ((regionSumEquiv F F' hFF') (Sum.inr i)))
            (v ((regionSumEquiv F F' hFF') (Sum.inr i))) =
          (1 : Matrix (Fin 2) (Fin 2) ℂ)
            (u ⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩)
            (v ⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩) := by
      intro i
      have hi : i.val ∉ F := (Finset.mem_sdiff.mp i.property).2
      simp [finiteRegionPadLabels, regionSumEquiv, hi, PauliLabel.matrix_I_eq_one]
    rw [Finset.prod_congr rfl fun i _ => hfac i, prod_one_apply]
    rfl

end FiniteFiber
