import FiniteFiber.FiniteRegionPauliMatrices
import FiniteFiber.OneSitePauliNormalForm

/-!
# Finite-region phased Pauli matrices in the `X^x Z^z` normal form

For a finite region `F : Finset Site` and a projective label `p i` at every
site `i ∈ F`, this file builds the **raw** finite-region normal-form matrix as
the entrywise product over the region of the one-site raw matrices
`normalFormOneSiteMatrix (p i) = X^{x_i} Z^{z_i}` (in that factor order), and
the summed `ZMod 4` correction

`c_F(p) = ∑ i : ↥F, normalFormHermitianCorrection (p i)`.

The main theorem is the exact matrix identity

`rawMatrix_F(p) = i ^ c_F(p) • P_F(ofProjectiveCoordinates ∘ p)`,

where `P_F` is the phase-free Hermitian finite-region Pauli matrix of
`FiniteFiber.finiteRegionPauliMatrix`.  Two corollaries are proved: the
all-zero label string gives the identity matrix, and the local inclusion
`finiteRegionEmbed F F' hFF'` sends the raw matrix on `F` to the raw matrix on
`F'` of the labels padded by the zero projective label on `F' \ F`.

The one-site convention is fixed by the imported file and is kept here: the
factor order is `X^x * Z^z`, so the correction at the label `(1, 1)` is `3`,
i.e. `X * Z = -i * Y`.

Nothing else is claimed: there is no multiplicativity statement for
`FullPauliWord`, no cocycle compatibility, no support or locality statement,
no colimit, no state, and no GNS construction.
-/

namespace FiniteFiber

open scoped BigOperators

/-! ### Multiplicativity of the fourth-root-of-unity phase factor -/

private theorem I_pow_mod_four (n : ℕ) : Complex.I ^ (n % 4) = Complex.I ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 4]
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

/-- The phase factor `i ^ k` turns addition in `ZMod 4` into multiplication. -/
theorem zmod4PhaseFactor_add (a b : ZMod 4) :
    zmod4PhaseFactor (a + b) = zmod4PhaseFactor a * zmod4PhaseFactor b := by
  simp only [zmod4PhaseFactor, ZMod.val_add, I_pow_mod_four, pow_add]

/-- The phase factor of the zero exponent is `1`. -/
@[simp] theorem zmod4PhaseFactor_zero : zmod4PhaseFactor 0 = 1 := by
  simp [zmod4PhaseFactor]

/-- The phase factor of a finite sum of exponents is the product of the factors. -/
theorem zmod4PhaseFactor_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 4) :
    zmod4PhaseFactor (∑ i ∈ s, f i) = ∏ i ∈ s, zmod4PhaseFactor (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, zmod4PhaseFactor_add, ih]

/-! ### The finite-region raw normal-form matrix -/

variable {Site : Type*} [DecidableEq Site]

/--
The raw finite-region normal-form matrix: the entrywise product over the sites
of `F` of the raw one-site matrices `X^{x_i} Z^{z_i}`.
-/
noncomputable def finiteRegionNormalFormMatrix
    (F : Finset Site) (p : ↥F → ProjectivePauliLabel) :
    finiteRegionQubitAlgebra F :=
  fun x y => ∏ i : ↥F, normalFormOneSiteMatrix (p i) (x i) (y i)

/-- The summed `ZMod 4` correction of a finite-region label function. -/
def finiteRegionNormalFormCorrection
    (F : Finset Site) (p : ↥F → ProjectivePauliLabel) : ZMod 4 :=
  ∑ i : ↥F, normalFormHermitianCorrection (p i)

omit [DecidableEq Site] in
/--
The finite-region normalization: the raw normal-form matrix equals the scalar
`i ^ c_F(p)` times the phase-free Hermitian finite-region Pauli matrix of the
canonical representatives.
-/
theorem finiteRegionNormalFormMatrix_eq_phase_smul_pauliMatrix
    (F : Finset Site) (p : ↥F → ProjectivePauliLabel) :
    finiteRegionNormalFormMatrix F p =
      zmod4PhaseFactor (finiteRegionNormalFormCorrection F p) •
        finiteRegionPauliMatrix F
          (fun i => PauliLabel.ofProjectiveCoordinates (p i)) := by
  classical
  funext x y
  simp only [finiteRegionNormalFormMatrix, finiteRegionNormalFormCorrection,
    Matrix.smul_apply, finiteRegionPauliMatrix, smul_eq_mul,
    zmod4PhaseFactor_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [normalFormOneSiteMatrix_eq_phase_smul_hermitian (p i)]
  simp [Matrix.smul_apply]

omit [DecidableEq Site] in
/-- The all-zero label string has zero summed correction. -/
@[simp] theorem finiteRegionNormalFormCorrection_zero (F : Finset Site) :
    finiteRegionNormalFormCorrection F (fun _ => 0) = 0 := by
  have h : (0 : ProjectivePauliLabel) ≠ (1, 1) := by decide
  simp [finiteRegionNormalFormCorrection, normalFormHermitianCorrection, h]

/-- The raw normal-form matrix of the all-zero label string is the identity. -/
theorem finiteRegionNormalFormMatrix_zero (F : Finset Site) :
    finiteRegionNormalFormMatrix F (fun _ => 0) = 1 := by
  classical
  have hI : (fun i : ↥F => PauliLabel.ofProjectiveCoordinates
      ((fun _ : ↥F => (0 : ProjectivePauliLabel)) i)) = fun _ => PauliLabel.I := by
    funext i
    exact (PauliLabel.ofProjectiveCoordinates_eq_I_iff _).mpr rfl
  rw [finiteRegionNormalFormMatrix_eq_phase_smul_pauliMatrix,
    finiteRegionNormalFormCorrection_zero, zmod4PhaseFactor_zero, hI,
    finiteRegionPauliMatrix_all_I, one_smul]

/-! ### Identity padding along a finite inclusion -/

/-- Projective labels on `F` padded by the zero label on the complement `F' \ F`. -/
noncomputable def finiteRegionPadProjectiveLabels
    (F F' : Finset Site) (p : ↥F → ProjectivePauliLabel) :
    ↥F' → ProjectivePauliLabel :=
  fun x => if hx : x.val ∈ F then p ⟨x.val, hx⟩ else 0

/-- The sites of `F'` split as the sites of `F` together with those of `F' \ F`. -/
private def phasedRegionSumEquiv (F F' : Finset Site) (hFF' : F ⊆ F') :
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

/-- Padding by the zero label does not change the summed correction. -/
theorem finiteRegionNormalFormCorrection_pad
    (F F' : Finset Site) (hFF' : F ⊆ F') (p : ↥F → ProjectivePauliLabel) :
    finiteRegionNormalFormCorrection F' (finiteRegionPadProjectiveLabels F F' p) =
      finiteRegionNormalFormCorrection F p := by
  classical
  simp only [finiteRegionNormalFormCorrection]
  rw [← Fintype.sum_equiv (phasedRegionSumEquiv F F' hFF')
      (fun j => normalFormHermitianCorrection
        (finiteRegionPadProjectiveLabels F F' p (phasedRegionSumEquiv F F' hFF' j)))
      (fun i => normalFormHermitianCorrection
        (finiteRegionPadProjectiveLabels F F' p i)) (fun _ => rfl),
    Fintype.sum_sum_type]
  have hleft : ∀ i : ↥F,
      normalFormHermitianCorrection (finiteRegionPadProjectiveLabels F F' p
        (phasedRegionSumEquiv F F' hFF' (Sum.inl i))) =
        normalFormHermitianCorrection (p i) := by
    intro i
    simp [finiteRegionPadProjectiveLabels, phasedRegionSumEquiv, i.property]
  have hright : ∀ i : ↥(F' \ F),
      normalFormHermitianCorrection (finiteRegionPadProjectiveLabels F F' p
        (phasedRegionSumEquiv F F' hFF' (Sum.inr i))) = 0 := by
    intro i
    have hi : i.val ∉ F := (Finset.mem_sdiff.mp i.property).2
    have h : (0 : ProjectivePauliLabel) ≠ (1, 1) := by decide
    simp [finiteRegionPadProjectiveLabels, phasedRegionSumEquiv, hi,
      normalFormHermitianCorrection, h]
  rw [Finset.sum_congr rfl fun i _ => hleft i,
    Finset.sum_congr rfl fun i _ => hright i]
  simp

/-- Padding commutes with the choice of Hermitian representatives. -/
theorem ofProjectiveCoordinates_pad
    (F F' : Finset Site) (p : ↥F → ProjectivePauliLabel) :
    (fun i : ↥F' => PauliLabel.ofProjectiveCoordinates
        (finiteRegionPadProjectiveLabels F F' p i)) =
      finiteRegionPadLabels F F' (fun i => PauliLabel.ofProjectiveCoordinates (p i)) := by
  classical
  funext i
  by_cases hi : i.val ∈ F
  · simp [finiteRegionPadProjectiveLabels, finiteRegionPadLabels, hi]
  · simp [finiteRegionPadProjectiveLabels, finiteRegionPadLabels, hi,
      (PauliLabel.ofProjectiveCoordinates_eq_I_iff (0 : ProjectivePauliLabel)).mpr rfl]

/--
Identity padding: the local inclusion sends the raw normal-form matrix on `F`
to the raw normal-form matrix on `F'` of the labels padded by the zero
projective label on `F' \ F`.
-/
theorem finiteRegionEmbed_normalFormMatrix
    (F F' : Finset Site) (hFF' : F ⊆ F') (p : ↥F → ProjectivePauliLabel) :
    finiteRegionEmbed F F' hFF' (finiteRegionNormalFormMatrix F p) =
      finiteRegionNormalFormMatrix F' (finiteRegionPadProjectiveLabels F F' p) := by
  classical
  rw [finiteRegionNormalFormMatrix_eq_phase_smul_pauliMatrix,
    finiteRegionNormalFormMatrix_eq_phase_smul_pauliMatrix,
    finiteRegionNormalFormCorrection_pad F F' hFF' p,
    map_smul, ofProjectiveCoordinates_pad F F' p,
    finiteRegionEmbed_pauliMatrix F F' hFF']

end FiniteFiber

