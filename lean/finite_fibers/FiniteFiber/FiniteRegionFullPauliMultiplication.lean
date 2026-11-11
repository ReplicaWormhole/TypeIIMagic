import FiniteFiber.FiniteRegionPhasedPauliMatrices
import FiniteFiber.FiniteRegionEmbeddingCoherence

/-!
# Finite-region multiplicativity of the full-Pauli normal form

This file supplies the finite-region operator-level bridge which
`FiniteFiber.FullPauliLattice` and `FiniteFiber.FiniteRegionPhasedPauliMatrices`
deliberately left open: the raw normal-form matrices of a finite region
multiply exactly as the algebraic normal form `FullPauliWord Site` does, with
the phase correction given by the *existing* cocycle `FullPauliWord.cocycle`.

The development is in three steps.

* One site: `normalFormOneSiteMatrix_mul` proves
  `X^{x₁} Z^{z₁} · X^{x₂} Z^{z₂} = (-1)^{z₁ x₂} X^{x₁+x₂} Z^{z₁+z₂}`,
  the single anticommutation input, with the sign written through the
  existing embedding `FullPauliWord.phaseEmbed`.
* Finite region, projective labels: `finiteRegionNormalFormMatrix_mul` uses the
  tensor factorization `finiteRegionTensorMatrix_mul` of a product of
  entrywise-product matrices to get
  `raw_F(p) · raw_F(q) = i ^ c_F(p,q) • raw_F(p+q)` with the summed sign
  `finiteRegionNormalFormCocycle`.
* Full words: `fullPauliRegionMatrix` attaches the scalar `zmod4PhaseFactor`
  of the central `ZMod 4` phase, and `fullPauliRegionMatrix_mul` is the exact
  identity `matrix (a * b) = matrix a * matrix b` for words supported in `F`.
  The identity word maps to `1` and the central word
  `FullPauliWord.negativeIdentity` maps to `(-1) • 1`.

The convention is the one already fixed by `OneSitePauliNormalForm`: the factor
order is `X` then `Z`, so the `(1,1)` one-site raw matrix is `-i · Y` and its
Hermitian correction is `3 : ZMod 4`.  The cocycle is *not* redefined here: the
region-level sign is proved equal to `FullPauliWord.cocycle` in
`cocycle_eq_finiteRegionNormalFormCocycle`.

Nothing else is claimed: no quasilocal completion, no state, no GNS
construction, and no infinite finite-projection theorem.
-/

namespace FiniteFiber

open scoped BigOperators

/-! ### Two scalar computations -/

/-- The defining formula of the sign embedding `ZMod 2 → ZMod 4`. -/
theorem phaseEmbed_apply (c : ZMod 2) :
    FullPauliWord.phaseEmbed c = if c = 0 then 0 else 2 := rfl

/-- The phase factor of the sign exponent `2` is `-1`. -/
@[simp] theorem zmod4PhaseFactor_two : zmod4PhaseFactor (2 : ZMod 4) = -1 := by
  have hval : (2 : ZMod 4).val = 2 := rfl
  rw [zmod4PhaseFactor, hval, pow_two, Complex.I_mul_I]

/-- The phase factor attached to a binary sign exponent is `±1`. -/
theorem zmod4PhaseFactor_phaseEmbed (c : ZMod 2) :
    zmod4PhaseFactor (FullPauliWord.phaseEmbed c) = if c = 0 then 1 else -1 := by
  by_cases hc : c = 0
  · rw [phaseEmbed_apply, if_pos hc, if_pos hc, zmod4PhaseFactor_zero]
  · rw [phaseEmbed_apply, if_neg hc, if_neg hc, zmod4PhaseFactor_two]

/-! ### The one-site multiplication relation -/

set_option maxHeartbeats 1000000 in
/--
**The one-site relation.**  With the convention `X` then `Z`, the raw
normal-form matrices satisfy

`X^{x₁} Z^{z₁} · X^{x₂} Z^{z₂} = (-1)^{z₁ x₂} · X^{x₁+x₂} Z^{z₁+z₂}`,

the sign being the `ZMod 2` product `z₁ x₂` transported by the existing
embedding `FullPauliWord.phaseEmbed`.
-/
theorem normalFormOneSiteMatrix_mul (p q : ProjectivePauliLabel) :
    normalFormOneSiteMatrix p * normalFormOneSiteMatrix q =
      zmod4PhaseFactor (FullPauliWord.phaseEmbed (p.2 * q.1)) •
        normalFormOneSiteMatrix (p + q) := by
  obtain ⟨x₁, z₁⟩ := p
  obtain ⟨x₂, z₂⟩ := q
  fin_cases x₁ <;> fin_cases z₁ <;> fin_cases x₂ <;> fin_cases z₂ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num +decide [normalFormOneSiteMatrix, zmod4PhaseFactor_phaseEmbed,
          PauliLabel.matrix, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_fin_two, Prod.ext_iff]

/-! ### Multiplication of finite-region tensor matrices -/

variable {Site : Type*} [DecidableEq Site]

/--
The finite-region matrix built entrywise from one-site matrices, i.e. the
tensor product `⨂ i ∈ F, A i` written in the computational basis.
-/
noncomputable def finiteRegionTensorMatrix
    (F : Finset Site) (A : ↥F → Matrix (Fin 2) (Fin 2) ℂ) :
    finiteRegionQubitAlgebra F :=
  fun x y => ∏ i : ↥F, A i (x i) (y i)

/--
**The finite tensor/product factorization.**  A product of finite-region
tensor matrices is the tensor matrix of the sitewise products.
-/
theorem finiteRegionTensorMatrix_mul
    (F : Finset Site) (A B : ↥F → Matrix (Fin 2) (Fin 2) ℂ) :
    finiteRegionTensorMatrix F A * finiteRegionTensorMatrix F B =
      finiteRegionTensorMatrix F (fun i => A i * B i) := by
  classical
  funext x z
  rw [Matrix.mul_apply]
  simp only [finiteRegionTensorMatrix]
  have hentry : ∀ i : ↥F,
      (A i * B i) (x i) (z i) = ∑ t : Fin 2, A i (x i) t * B i t (z i) := by
    intro i
    rw [Matrix.mul_apply]
  rw [Finset.prod_congr rfl fun i _ => hentry i]
  rw [Finset.prod_univ_sum (fun _ : ↥F => (Finset.univ : Finset (Fin 2)))
    (fun i t => A i (x i) t * B i t (z i))]
  rw [Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun y _ => (Finset.prod_mul_distrib).symm

/-! ### Multiplication of finite-region projective normal-form matrices -/

/--
The summed finite-region sign exponent of two projective label functions: the
`ZMod 4` exponent recording, site by site, the `Z`-past-`X` crossings.
-/
noncomputable def finiteRegionNormalFormCocycle
    (F : Finset Site) (p q : ↥F → ProjectivePauliLabel) : ZMod 4 :=
  ∑ i : ↥F, FullPauliWord.phaseEmbed ((p i).2 * (q i).1)

omit [DecidableEq Site] in
/-- The raw normal-form matrix is the tensor matrix of the one-site raw matrices. -/
theorem finiteRegionNormalFormMatrix_eq_tensor
    (F : Finset Site) (p : ↥F → ProjectivePauliLabel) :
    finiteRegionNormalFormMatrix F p =
      finiteRegionTensorMatrix F (fun i => normalFormOneSiteMatrix (p i)) := rfl

/--
**Finite-region projective multiplication.**  The raw normal-form matrices of
a finite region multiply with the summed sign exponent
`finiteRegionNormalFormCocycle`.
-/
theorem finiteRegionNormalFormMatrix_mul
    (F : Finset Site) (p q : ↥F → ProjectivePauliLabel) :
    finiteRegionNormalFormMatrix F p * finiteRegionNormalFormMatrix F q =
      zmod4PhaseFactor (finiteRegionNormalFormCocycle F p q) •
        finiteRegionNormalFormMatrix F (p + q) := by
  classical
  rw [finiteRegionNormalFormMatrix_eq_tensor, finiteRegionNormalFormMatrix_eq_tensor,
    finiteRegionTensorMatrix_mul]
  funext x y
  simp only [finiteRegionTensorMatrix, finiteRegionNormalFormMatrix,
    finiteRegionNormalFormCocycle, Matrix.smul_apply, smul_eq_mul,
    zmod4PhaseFactor_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [normalFormOneSiteMatrix_mul (p i) (q i)]
  simp [Matrix.smul_apply]

/-! ### The region sign exponent is the existing cocycle -/

omit [DecidableEq Site] in
/-- The `X` coordinate of a projective word is its sitewise first component. -/
theorem xCoordinate_apply (w : ProjectivePauliWord Site) (i : Site) :
    FullPauliWord.xCoordinate w i = (w i).1 := rfl

omit [DecidableEq Site] in
/-- The `Z` coordinate of a projective word is its sitewise second component. -/
theorem zCoordinate_apply (w : ProjectivePauliWord Site) (i : Site) :
    FullPauliWord.zCoordinate w i = (w i).2 := rfl

omit [DecidableEq Site] in
/--
For a left argument supported in the finite region `F`, the binary dot product
is the plain sum of pointwise products over `F`.
-/
theorem binaryDot_eq_sum_of_support_subset
    (F : Finset Site) (u v : Site →₀ ZMod 2) (hu : u.support ⊆ F) :
    FullPauliWord.binaryDot u v = ∑ i ∈ F, u i * v i := by
  classical
  have hsum : FullPauliWord.binaryDot u v = u.sum (fun i c => c * v i) := rfl
  rw [hsum, Finsupp.sum_of_support_subset u hu (fun i c => c * v i)
    (fun i _ => by simp)]

/-- The projective label of a full Pauli word restricted to a finite region. -/
noncomputable def restrictLabel (F : Finset Site) (w : ProjectivePauliWord Site) :
    ↥F → ProjectivePauliLabel := fun i => w i.val

omit [DecidableEq Site] in
/-- Restriction to a region turns the sum of words into the pointwise sum. -/
theorem restrictLabel_add (F : Finset Site) (u v : ProjectivePauliWord Site) :
    restrictLabel F (u + v) = restrictLabel F u + restrictLabel F v := rfl

omit [DecidableEq Site] in
/--
**The region sign exponent is the manuscript cocycle.**  For a left word whose
support lies in `F`, the summed finite-region exponent of the restricted
labels equals the already existing `FullPauliWord.cocycle`.
-/
theorem cocycle_eq_finiteRegionNormalFormCocycle
    (F : Finset Site) (u v : ProjectivePauliWord Site) (hu : u.support ⊆ F) :
    FullPauliWord.cocycle u v =
      finiteRegionNormalFormCocycle F (restrictLabel F u) (restrictLabel F v) := by
  classical
  have hsupp : (FullPauliWord.zCoordinate u).support ⊆ F := by
    intro i hi
    apply hu
    rw [Finsupp.mem_support_iff] at hi ⊢
    intro h
    exact hi (by rw [zCoordinate_apply, h]; rfl)
  rw [FullPauliWord.cocycle,
    binaryDot_eq_sum_of_support_subset F _ _ hsupp]
  rw [map_sum]
  have hcoe : finiteRegionNormalFormCocycle F (restrictLabel F u) (restrictLabel F v) =
      ∑ i ∈ F, FullPauliWord.phaseEmbed ((u i).2 * (v i).1) :=
    Finset.sum_coe_sort F (fun i => FullPauliWord.phaseEmbed ((u i).2 * (v i).1))
  rw [hcoe]
  exact Finset.sum_congr rfl fun i _ => by
    rw [zCoordinate_apply, xCoordinate_apply]

/-! ### The full-word finite-region matrix -/

/--
The finite-region matrix of a full Pauli word `i^phase X^x Z^z`: the scalar
phase factor `i ^ phase` times the raw normal-form matrix of the restricted
projective label.
-/
noncomputable def fullPauliRegionMatrix
    (F : Finset Site) (a : FullPauliWord Site) : finiteRegionQubitAlgebra F :=
  zmod4PhaseFactor a.phase • finiteRegionNormalFormMatrix F (restrictLabel F a.label)

/--
**The finite-region full-Pauli multiplication theorem.**  For a word `a`
supported in the finite region `F` and an arbitrary word `b`, the finite-region
matrices multiply exactly:

`matrix (a * b) = matrix a * matrix b`,

the phase correction being precisely `FullPauliWord.cocycle a.label b.label`.
Only the support hypothesis on the *left* factor is needed, since the cocycle
sums the `Z` coordinate of `a` against the `X` coordinate of `b`; in
particular the identity holds for any two words supported in `F`.
-/
theorem fullPauliRegionMatrix_mul
    (F : Finset Site) (a b : FullPauliWord Site) (ha : a.label.support ⊆ F) :
    fullPauliRegionMatrix F (a * b) =
      fullPauliRegionMatrix F a * fullPauliRegionMatrix F b := by
  classical
  have hphase : (a * b).phase =
      a.phase + b.phase + FullPauliWord.cocycle a.label b.label := rfl
  have hlabel : (a * b).label = a.label + b.label := rfl
  rw [fullPauliRegionMatrix, fullPauliRegionMatrix, fullPauliRegionMatrix,
    hphase, hlabel, restrictLabel_add, Matrix.smul_mul, Matrix.mul_smul,
    finiteRegionNormalFormMatrix_mul, smul_smul, smul_smul,
    zmod4PhaseFactor_add, zmod4PhaseFactor_add,
    cocycle_eq_finiteRegionNormalFormCocycle F a.label b.label ha]

/-- The identity full Pauli word is represented by the identity matrix. -/
theorem fullPauliRegionMatrix_one (F : Finset Site) :
    fullPauliRegionMatrix F (1 : FullPauliWord Site) = 1 := by
  have hphase : (1 : FullPauliWord Site).phase = 0 := rfl
  have hlabel : restrictLabel F (1 : FullPauliWord Site).label = fun _ => 0 := rfl
  rw [fullPauliRegionMatrix, hphase, hlabel, zmod4PhaseFactor_zero, one_smul,
    finiteRegionNormalFormMatrix_zero]

/-- The central word `-1` is represented by the scalar `-1` times the identity. -/
theorem fullPauliRegionMatrix_negativeIdentity (F : Finset Site) :
    fullPauliRegionMatrix F (FullPauliWord.negativeIdentity (Site := Site)) =
      (-1 : ℂ) • 1 := by
  have hphase : (FullPauliWord.negativeIdentity (Site := Site)).phase = 2 := rfl
  have hlabel :
      restrictLabel F (FullPauliWord.negativeIdentity (Site := Site)).label =
        fun _ => 0 := rfl
  rw [fullPauliRegionMatrix, hphase, hlabel, zmod4PhaseFactor_two,
    finiteRegionNormalFormMatrix_zero]

end FiniteFiber
