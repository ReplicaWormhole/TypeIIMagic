import FiniteFiber.FullPauliStabilizerDensity
import FiniteFiber.FiniteRegionEmbeddingCoherence

/-!
# A coherent directed system of actual local full-Pauli algebras

This file packages the checked finite-region data of
`FiniteFiber.FullPauliSupportLocality`, `FiniteFiber.FullPauliStabilizerDensity`
and `FiniteFiber.FiniteRegionEmbeddingCoherence` into a **directed system**
indexed by the finite regions `F : Finset Site`, ordered by inclusion, and
proves the exact finite-stage restriction formula together with its composition
law.

## The finite data

* **Local algebras.**  The finite complex matrix algebra
  `finiteRegionQubitAlgebra F` on the computational basis `↥F → Fin 2`.
* **Local inclusions.**  The identity padding `A ↦ A ⊗ 1` given by
  `finiteRegionEmbed F F' hFF'`, written `localInclusion hFF'` for the
  order-indexed form.  The instance
  `finiteRegionQubitAlgebraDirectedSystem` records that these satisfy the
  identity and composition laws of a `DirectedSystem`.
* **Actual full-Pauli images.**  The finite-region matrix
  `fullPauliRegionMatrix F a` of an algebraic full-Pauli word.  For a word
  supported in `F` these images are coherent across the system
  (`localInclusion_fullPauliRegionMatrix`).
* **Finite restrictions.**  The partial trace `finiteRegionPartialTrace F F' hFF'`
  over the discarded sites `F' \ F`, in the literal bit coordinates supplied by
  `regionExtend`.
* **Finite stabilizer densities.**  For a `FullPauliStabilizerSystem` (a
  subgroup of `FullPauliWord Site` whose elements are involutive and which
  excludes the central word `-1`), the local group `G_{S,F} = G_S ∩ A_F` and
  its density `ρ_F = 2^{-|F|} ∑_{g ∈ G_{S,F}} g`, taken from the already
  checked finite-density layer.

## What is proved

* `finiteRegionPartialTrace_finiteRegionEmbed`: tracing out `F' \ F` undoes the
  identity padding up to the factor `2^{|F' \ F|}`.
* `trace_finiteRegionPartialTrace` and
  `finiteRegionPartialTrace_mul_finiteRegionEmbed`: the partial trace preserves
  the trace and is a module map for the local inclusion.
* `finiteRegionPartialTrace_trans` / `finiteRegionPartialTrace_comp`: **the
  composition law** of the finite restrictions, `Tr_{F' \ F} ∘ Tr_{F'' \ F'} =
  Tr_{F'' \ F}`.
* `finiteRegionPartialTrace_fullPauliRegionMatrix_dichotomy`: the manuscript's
  surviving-term dichotomy — a full-Pauli word survives the partial trace
  exactly when it is already supported in the smaller region, and is then
  rescaled by `2^{|F' \ F|}`; otherwise its partial trace is `0`.
* `FullPauliStabilizerSystem.finiteRegionPartialTrace_regionDensity`: the
  manuscript's compatibility relation `ρ_F = Tr_{F' \ F}(ρ_{F'})` for the actual
  finite stabilizer densities.
* `FullPauliStabilizerSystem.localState_localInclusion`: **the exact
  finite-stage restriction formula** `ω_{F'}(A ⊗ 1_{F' \ F}) = ω_F(A)` for the
  finite local states `ω_F(A) = Tr(ρ_F A)`, with
  `localState_localInclusion_trans` and
  `finiteRegionPartialTrace_regionDensity_trans` its composition law.
* `FullPauliStabilizerSystem.localState_fullPauliRegionMatrix`: each finite
  local state is the stabilizer state of its region.
* `zWordSystem`: the hypotheses are non-vacuous.

## What is *not* claimed

This is finite/direct-limit data only.  No algebraic direct limit of the system
is formed here, and nothing below is called a C-star algebra or a quasilocal
algebra; no positivity, norm or completion statement is made on any quotient or
colimit; no global state on an infinite system is constructed, and there is no
GNS representation, no von Neumann algebra and no normality statement.  The
finite local states are honest positive normalized functionals of *finite*
matrix algebras only (positivity enters through
`FullPauliStabilizerSystem.regionDensity_posSemidef`).
-/

namespace FiniteFiber

open scoped BigOperators ComplexOrder
open scoped FiniteFiber.FiniteRegionQubitMatrix

variable {Site : Type*} [DecidableEq Site]

/-! ### Assembling a bit configuration from a subregion and its complement -/

/--
The bit configuration on `F'` assembled from a configuration `u` on the
subregion `F` and a configuration `w` on the complementary sites `F' \ F`.
-/
def regionExtend (F F' : Finset Site) (u : finiteRegionBasis F)
    (w : finiteRegionBasis (F' \ F)) : finiteRegionBasis F' :=
  fun x =>
    if hx : x.val ∈ F then u ⟨x.val, hx⟩
    else w ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩

@[simp] theorem regionExtend_of_mem (F F' : Finset Site) (u : finiteRegionBasis F)
    (w : finiteRegionBasis (F' \ F)) (x : ↥F') (hx : x.val ∈ F) :
    regionExtend F F' u w x = u ⟨x.val, hx⟩ := dif_pos hx

theorem regionExtend_of_not_mem (F F' : Finset Site) (u : finiteRegionBasis F)
    (w : finiteRegionBasis (F' \ F)) (x : ↥F') (hx : x.val ∉ F) :
    regionExtend F F' u w x =
      w ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩ := dif_neg hx

/-- Assembling is the inverse of the canonical coordinate split. -/
theorem finiteRegionSplitEquiv_symm_apply (F F' : Finset Site) (hFF' : F ⊆ F')
    (u : finiteRegionBasis F) (w : finiteRegionBasis (F' \ F)) :
    (finiteRegionSplitEquiv F F' hFF').symm (u, w) = regionExtend F F' u w := rfl

/-- Restricting an assembled configuration to the subregion returns its first part. -/
@[simp] theorem finiteRegionRestrict_regionExtend (F F' : Finset Site) (hFF' : F ⊆ F')
    (u : finiteRegionBasis F) (w : finiteRegionBasis (F' \ F)) :
    finiteRegionRestrict F F' hFF' (regionExtend F F' u w) = u := by
  funext y
  exact dif_pos y.property

/-- Every sum over the configurations of `F'` splits as an iterated sum. -/
theorem sum_finiteRegionBasis_split {M : Type*} [AddCommMonoid M]
    (F F' : Finset Site) (hFF' : F ⊆ F') (f : finiteRegionBasis F' → M) :
    ∑ x : finiteRegionBasis F', f x =
      ∑ u : finiteRegionBasis F, ∑ w : finiteRegionBasis (F' \ F),
        f (regionExtend F F' u w) := by
  classical
  rw [← (finiteRegionSplitEquiv F F' hFF').symm.sum_comp f, Fintype.sum_prod_type]
  simp only [finiteRegionSplitEquiv_symm_apply]

/-- Two assembled configurations agree outside `F` exactly when their outer parts agree. -/
theorem regionExtend_agree_iff (F F' : Finset Site)
    (u u' : finiteRegionBasis F) (w w' : finiteRegionBasis (F' \ F)) :
    (∀ x : ↥F', x.val ∉ F →
        regionExtend F F' u w x = regionExtend F F' u' w' x) ↔ w = w' := by
  constructor
  · intro h
    funext y
    have hy : y.val ∉ F := (Finset.mem_sdiff.mp y.property).2
    have hy' : y.val ∈ F' := (Finset.mem_sdiff.mp y.property).1
    have := h ⟨y.val, hy'⟩ hy
    rw [regionExtend_of_not_mem F F' u w ⟨y.val, hy'⟩ hy,
      regionExtend_of_not_mem F F' u' w' ⟨y.val, hy'⟩ hy] at this
    simpa using this
  · rintro rfl x hx
    rw [regionExtend_of_not_mem F F' u w x hx, regionExtend_of_not_mem F F' u' w x hx]

/-- The sites of `F'` split into the sites of `F` and those of `F' \ F`. -/
def regionSumEquiv (F F' : Finset Site) (hFF' : F ⊆ F') :
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

/-- A product over the sites of `F'` splits into the `F` part and the `F' \ F` part. -/
theorem prod_finiteRegion_split (F F' : Finset Site) (hFF' : F ⊆ F') (h : ↥F' → ℂ) :
    ∏ i : ↥F', h i =
      (∏ i : ↥F, h ⟨i.val, hFF' i.property⟩) *
        ∏ j : ↥(F' \ F), h ⟨j.val, (Finset.mem_sdiff.mp j.property).1⟩ := by
  classical
  rw [← Fintype.prod_equiv (regionSumEquiv F F' hFF')
      (fun j => h (regionSumEquiv F F' hFF' j)) h (fun _ => rfl),
    Fintype.prod_sum_type]
  rfl

/-! ### The finite-region partial trace -/

/--
The partial trace over the complementary sites `F' \ F` of a matrix on the
finite region `F'`, for a finite inclusion `F ⊆ F'`.
-/
noncomputable def finiteRegionPartialTrace (F F' : Finset Site) (hFF' : F ⊆ F') :
    finiteRegionQubitAlgebra F' →ₗ[ℂ] finiteRegionQubitAlgebra F where
  toFun A := fun u v => ∑ w : finiteRegionBasis (F' \ F),
    A ((finiteRegionSplitEquiv F F' hFF').symm (u, w))
      ((finiteRegionSplitEquiv F F' hFF').symm (v, w))
  map_add' A B := by
    ext u v
    simp [Finset.sum_add_distrib]
  map_smul' c A := by
    ext u v
    change (∑ w : finiteRegionBasis (F' \ F), c * _) = c * ∑ w : finiteRegionBasis (F' \ F), _
    rw [Finset.mul_sum]

/-- The entrywise formula for the finite-region partial trace. -/
theorem finiteRegionPartialTrace_apply (F F' : Finset Site) (hFF' : F ⊆ F')
    (A : finiteRegionQubitAlgebra F') (u v : finiteRegionBasis F) :
    finiteRegionPartialTrace F F' hFF' A u v =
      ∑ w : finiteRegionBasis (F' \ F),
        A (regionExtend F F' u w) (regionExtend F F' v w) := rfl

/--
**Partial trace of an identity padding.**  Tracing out `F' \ F` undoes the
local inclusion `A ↦ A ⊗ 1` up to the dimension `2 ^ |F' \ F|` of the
discarded factor.
-/
theorem finiteRegionPartialTrace_finiteRegionEmbed (F F' : Finset Site) (hFF' : F ⊆ F')
    (A : finiteRegionQubitAlgebra F) :
    finiteRegionPartialTrace F F' hFF' (finiteRegionEmbed F F' hFF' A) =
      ((2 : ℂ) ^ (F' \ F).card) • A := by
  classical
  ext u v
  rw [finiteRegionPartialTrace_apply]
  have h : ∀ w : finiteRegionBasis (F' \ F),
      finiteRegionEmbed F F' hFF' A (regionExtend F F' u w) (regionExtend F F' v w) =
        A u v := by
    intro w
    have hagree : ∀ x : ↥F', x.val ∉ F →
        regionExtend F F' u w x = regionExtend F F' v w x :=
      (regionExtend_agree_iff F F' u v w w).mpr rfl
    rw [finiteRegionEmbed_apply_entry F F' hFF' A, if_pos hagree,
      finiteRegionRestrict_regionExtend, finiteRegionRestrict_regionExtend]
  rw [Finset.sum_congr rfl (fun w _ => h w), Finset.sum_const, Finset.card_univ,
    card_finiteRegionBasis]
  simp

/-- The finite-region partial trace preserves the ordinary trace. -/
theorem trace_finiteRegionPartialTrace (F F' : Finset Site) (hFF' : F ⊆ F')
    (A : finiteRegionQubitAlgebra F') :
    (finiteRegionPartialTrace F F' hFF' A).trace = A.trace := by
  classical
  simp only [Matrix.trace, Matrix.diag]
  rw [sum_finiteRegionBasis_split F F' hFF' (fun x => A x x)]
  exact Finset.sum_congr rfl fun u _ => rfl

/--
**The module property of the finite-region partial trace.**  Tracing out
`F' \ F` is a module map for the local inclusion: an identity-padded right
factor can be pulled out of the partial trace.
-/
theorem finiteRegionPartialTrace_mul_finiteRegionEmbed
    (F F' : Finset Site) (hFF' : F ⊆ F')
    (B : finiteRegionQubitAlgebra F') (A : finiteRegionQubitAlgebra F) :
    finiteRegionPartialTrace F F' hFF' (B * finiteRegionEmbed F F' hFF' A) =
      finiteRegionPartialTrace F F' hFF' B * A := by
  classical
  ext u v
  rw [finiteRegionPartialTrace_apply]
  have hentry : ∀ w : finiteRegionBasis (F' \ F),
      (B * finiteRegionEmbed F F' hFF' A) (regionExtend F F' u w)
          (regionExtend F F' v w) =
        ∑ u' : finiteRegionBasis F,
          B (regionExtend F F' u w) (regionExtend F F' u' w) * A u' v := by
    intro w
    rw [Matrix.mul_apply, sum_finiteRegionBasis_split F F' hFF']
    refine Finset.sum_congr rfl fun u' _ => ?_
    have hterm : ∀ w' : finiteRegionBasis (F' \ F),
        B (regionExtend F F' u w) (regionExtend F F' u' w') *
            finiteRegionEmbed F F' hFF' A (regionExtend F F' u' w')
              (regionExtend F F' v w) =
          if w' = w then
            B (regionExtend F F' u w) (regionExtend F F' u' w) * A u' v else 0 := by
      intro w'
      rw [finiteRegionEmbed_apply_entry F F' hFF' A]
      by_cases hw : w' = w
      · subst hw
        rw [if_pos ((regionExtend_agree_iff F F' u' v w' w').mpr rfl), if_pos rfl,
          finiteRegionRestrict_regionExtend, finiteRegionRestrict_regionExtend]
      · rw [if_neg (fun hcon => hw ((regionExtend_agree_iff F F' u' v w' w).mp hcon)),
          if_neg hw, mul_zero]
    rw [Finset.sum_congr rfl (fun w' _ => hterm w'), Finset.sum_ite_eq' Finset.univ w,
      if_pos (Finset.mem_univ w)]
  rw [Finset.sum_congr rfl (fun w _ => hentry w), Finset.sum_comm, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun u' _ => ?_
  rw [finiteRegionPartialTrace_apply, Finset.sum_mul]

/-! ### The composition law of the finite-region partial traces -/

/--
For `F ⊆ F' ⊆ F''` the complementary configurations of the two successive
inclusions assemble into the complementary configurations of the composed
inclusion.
-/
def regionComplementEquiv (F F' F'' : Finset Site) (hFF' : F ⊆ F') (hF'F'' : F' ⊆ F'') :
    finiteRegionBasis (F' \ F) × finiteRegionBasis (F'' \ F') ≃
      finiteRegionBasis (F'' \ F) where
  toFun p := fun x =>
    if hx : x.val ∈ F' then
      p.1 ⟨x.val, Finset.mem_sdiff.mpr ⟨hx, (Finset.mem_sdiff.mp x.property).2⟩⟩
    else
      p.2 ⟨x.val, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp x.property).1, hx⟩⟩
  invFun w :=
    (fun y => w ⟨y.val, Finset.mem_sdiff.mpr
        ⟨hF'F'' (Finset.mem_sdiff.mp y.property).1, (Finset.mem_sdiff.mp y.property).2⟩⟩,
      fun y => w ⟨y.val, Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp y.property).1,
          fun hcon => (Finset.mem_sdiff.mp y.property).2 (hFF' hcon)⟩⟩)
  left_inv := by
    rintro ⟨w₁, w₂⟩
    refine Prod.ext (funext fun y => ?_) (funext fun y => ?_)
    · exact dif_pos (Finset.mem_sdiff.mp y.property).1
    · exact dif_neg (Finset.mem_sdiff.mp y.property).2
  right_inv := by
    intro w
    funext x
    by_cases hx : x.val ∈ F' <;> simp [hx]

/-- Assembling in two steps is assembling in one step. -/
theorem regionExtend_regionExtend (F F' F'' : Finset Site)
    (hFF' : F ⊆ F') (hF'F'' : F' ⊆ F'') (u : finiteRegionBasis F)
    (w₁ : finiteRegionBasis (F' \ F)) (w₂ : finiteRegionBasis (F'' \ F')) :
    regionExtend F' F'' (regionExtend F F' u w₁) w₂ =
      regionExtend F F'' u (regionComplementEquiv F F' F'' hFF' hF'F'' (w₁, w₂)) := by
  funext x
  by_cases hxF' : x.val ∈ F'
  · rw [regionExtend_of_mem F' F'' _ w₂ x hxF']
    by_cases hxF : x.val ∈ F
    · rw [regionExtend_of_mem F F' u w₁ ⟨x.val, hxF'⟩ hxF,
        regionExtend_of_mem F F'' u _ x hxF]
    · rw [regionExtend_of_not_mem F F' u w₁ ⟨x.val, hxF'⟩ hxF,
        regionExtend_of_not_mem F F'' u _ x hxF]
      simp [regionComplementEquiv, hxF']
  · have hxF : x.val ∉ F := fun hcon => hxF' (hFF' hcon)
    rw [regionExtend_of_not_mem F' F'' _ w₂ x hxF',
      regionExtend_of_not_mem F F'' u _ x hxF]
    simp [regionComplementEquiv, hxF']

/--
**The composition law of the finite-region restrictions.**  For finite regions
`F ⊆ F' ⊆ F''`, tracing out `F'' \ F'` and then `F' \ F` is exactly tracing
out `F'' \ F`.
-/
theorem finiteRegionPartialTrace_trans (F F' F'' : Finset Site)
    (hFF' : F ⊆ F') (hF'F'' : F' ⊆ F'') (A : finiteRegionQubitAlgebra F'') :
    finiteRegionPartialTrace F F' hFF'
        (finiteRegionPartialTrace F' F'' hF'F'' A) =
      finiteRegionPartialTrace F F'' (hFF'.trans hF'F'') A := by
  classical
  ext u v
  rw [finiteRegionPartialTrace_apply, finiteRegionPartialTrace_apply]
  have hstep : ∀ w₁ : finiteRegionBasis (F' \ F),
      finiteRegionPartialTrace F' F'' hF'F'' A (regionExtend F F' u w₁)
          (regionExtend F F' v w₁) =
        ∑ w₂ : finiteRegionBasis (F'' \ F'),
          A (regionExtend F F'' u (regionComplementEquiv F F' F'' hFF' hF'F'' (w₁, w₂)))
            (regionExtend F F'' v
              (regionComplementEquiv F F' F'' hFF' hF'F'' (w₁, w₂))) := by
    intro w₁
    rw [finiteRegionPartialTrace_apply]
    exact Finset.sum_congr rfl fun w₂ _ => by
      rw [regionExtend_regionExtend F F' F'' hFF' hF'F'' u w₁ w₂,
        regionExtend_regionExtend F F' F'' hFF' hF'F'' v w₁ w₂]
  rw [Finset.sum_congr rfl (fun w₁ _ => hstep w₁),
    ← Fintype.sum_equiv (regionComplementEquiv F F' F'' hFF' hF'F'')
      (fun p => A (regionExtend F F'' u (regionComplementEquiv F F' F'' hFF' hF'F'' p))
        (regionExtend F F'' v (regionComplementEquiv F F' F'' hFF' hF'F'' p)))
      (fun w => A (regionExtend F F'' u w) (regionExtend F F'' v w)) (fun _ => rfl),
    Fintype.sum_prod_type]

/-- The composition law as an equality of linear maps. -/
theorem finiteRegionPartialTrace_comp (F F' F'' : Finset Site)
    (hFF' : F ⊆ F') (hF'F'' : F' ⊆ F'') :
    (finiteRegionPartialTrace F F' hFF').comp
        (finiteRegionPartialTrace F' F'' hF'F'') =
      finiteRegionPartialTrace F F'' (hFF'.trans hF'F'') :=
  LinearMap.ext fun A => finiteRegionPartialTrace_trans F F' F'' hFF' hF'F'' A

/-! ### Partial traces of finite-region full-Pauli matrices -/

/-- Every nontrivial one-site normal-form matrix is traceless. -/
theorem sum_diag_normalFormOneSiteMatrix_eq_zero (p : ProjectivePauliLabel) (hp : p ≠ 0) :
    ∑ b : Fin 2, normalFormOneSiteMatrix p b b = 0 := by
  obtain ⟨x, z⟩ := p
  fin_cases x <;> fin_cases z
  · exact absurd (by decide) hp
  all_goals
    · norm_num [Fin.sum_univ_two, normalFormOneSiteMatrix, PauliLabel.matrix,
        Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_fin_two]

/--
**Vanishing of nonlocal full-Pauli words under restriction.**  If a full Pauli
word carries a nontrivial label at a site of `F' \ F`, then its finite-region
matrix on `F'` is annihilated by the partial trace over `F' \ F`.
-/
theorem finiteRegionPartialTrace_fullPauliRegionMatrix_eq_zero
    (F F' : Finset Site) (hFF' : F ⊆ F') (a : FullPauliWord Site)
    (s : Site) (hsF' : s ∈ F') (hsF : s ∉ F) (hlabel : a.label s ≠ 0) :
    finiteRegionPartialTrace F F' hFF' (fullPauliRegionMatrix F' a) = 0 := by
  classical
  ext u v
  rw [finiteRegionPartialTrace_apply, Matrix.zero_apply]
  have hterm : ∀ w : finiteRegionBasis (F' \ F),
      fullPauliRegionMatrix F' a (regionExtend F F' u w) (regionExtend F F' v w) =
        zmod4PhaseFactor a.phase *
            (∏ i : ↥F, normalFormOneSiteMatrix (a.label i.val) (u i) (v i)) *
          ∏ j : ↥(F' \ F), normalFormOneSiteMatrix (a.label j.val) (w j) (w j) := by
    intro w
    rw [fullPauliRegionMatrix_apply, prod_finiteRegion_split F F' hFF', ← mul_assoc]
    congr 1
    · congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [regionExtend_of_mem F F' u w ⟨i.val, hFF' i.property⟩ i.property,
        regionExtend_of_mem F F' v w ⟨i.val, hFF' i.property⟩ i.property]
    · refine Finset.prod_congr rfl fun j _ => ?_
      have hj : j.val ∉ F := (Finset.mem_sdiff.mp j.property).2
      rw [regionExtend_of_not_mem F F' u w ⟨j.val, (Finset.mem_sdiff.mp j.property).1⟩ hj,
        regionExtend_of_not_mem F F' v w ⟨j.val, (Finset.mem_sdiff.mp j.property).1⟩ hj]
  have hsum : (∑ w : finiteRegionBasis (F' \ F),
        ∏ j : ↥(F' \ F), normalFormOneSiteMatrix (a.label j.val) (w j) (w j)) =
      ∏ j : ↥(F' \ F), ∑ b : Fin 2, normalFormOneSiteMatrix (a.label j.val) b b := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have hzero : (∏ j : ↥(F' \ F),
      ∑ b : Fin 2, normalFormOneSiteMatrix (a.label j.val) b b) = 0 :=
    Finset.prod_eq_zero
      (Finset.mem_univ (⟨s, Finset.mem_sdiff.mpr ⟨hsF', hsF⟩⟩ : ↥(F' \ F)))
      (sum_diag_normalFormOneSiteMatrix_eq_zero _ hlabel)
  rw [Finset.sum_congr rfl (fun w _ => hterm w), ← Finset.mul_sum, hsum, hzero, mul_zero]

/--
**Restriction of a locally supported full-Pauli word.**  If the label support
of `a` lies in `F`, tracing out `F' \ F` returns its finite-region matrix on
`F`, rescaled by the dimension of the discarded factor.
-/
theorem finiteRegionPartialTrace_fullPauliRegionMatrix_of_supportedIn
    (F F' : Finset Site) (hFF' : F ⊆ F') (a : FullPauliWord Site)
    (ha : a.SupportedIn F) :
    finiteRegionPartialTrace F F' hFF' (fullPauliRegionMatrix F' a) =
      ((2 : ℂ) ^ (F' \ F).card) • fullPauliRegionMatrix F a := by
  rw [← finiteRegionEmbed_fullPauliRegionMatrix F F' hFF' a ha,
    finiteRegionPartialTrace_finiteRegionEmbed]

/--
**The manuscript's surviving-term dichotomy.**  For a word supported in `F'`,
the partial trace over `F' \ F` of its finite-region matrix is nonzero exactly
for the words already supported in `F`, and then it is the rescaled
finite-region matrix on `F`.
-/
theorem finiteRegionPartialTrace_fullPauliRegionMatrix_dichotomy
    (F F' : Finset Site) (hFF' : F ⊆ F') (a : FullPauliWord Site)
    (hsupp : a.SupportedIn F') :
    (a.SupportedIn F ∧ finiteRegionPartialTrace F F' hFF' (fullPauliRegionMatrix F' a) =
        ((2 : ℂ) ^ (F' \ F).card) • fullPauliRegionMatrix F a) ∨
      (¬ a.SupportedIn F ∧
        finiteRegionPartialTrace F F' hFF' (fullPauliRegionMatrix F' a) = 0) := by
  classical
  by_cases ha : a.SupportedIn F
  · exact Or.inl ⟨ha,
      finiteRegionPartialTrace_fullPauliRegionMatrix_of_supportedIn F F' hFF' a ha⟩
  · obtain ⟨s, hs, hsF⟩ := Finset.not_subset.mp ha
    exact Or.inr ⟨ha, finiteRegionPartialTrace_fullPauliRegionMatrix_eq_zero F F' hFF' a s
      (hsupp hs) hsF (Finsupp.mem_support_iff.mp hs)⟩

/-! ### The directed system of finite local matrix algebras -/

/--
The local inclusion of the directed system of finite-region matrix algebras,
indexed by the inclusion order of finite regions.
-/
noncomputable def localInclusion ⦃F F' : Finset Site⦄ (hFF' : F ≤ F')
    (A : finiteRegionQubitAlgebra F) : finiteRegionQubitAlgebra F' :=
  finiteRegionEmbed F F' hFF' A

theorem localInclusion_eq (F F' : Finset Site) (hFF' : F ⊆ F')
    (A : finiteRegionQubitAlgebra F) :
    localInclusion hFF' A = finiteRegionEmbed F F' hFF' A := rfl

/--
**The coherent directed system of finite local matrix algebras.**  The finite
regions of `Site`, ordered by inclusion, index the local matrix algebras, and
the identity-padding inclusions satisfy the identity and composition laws of a
directed system.
-/
instance finiteRegionQubitAlgebraDirectedSystem :
    DirectedSystem (fun F : Finset Site => finiteRegionQubitAlgebra F)
      (fun _ _ h A => localInclusion h A) where
  map_self := fun {F} A => finiteRegionEmbed_self F A
  map_map := fun {k j i} hij hjk A => finiteRegionEmbed_trans i j k hij hjk A

/--
The actual full-Pauli image of a word is a coherent element of the directed
system: on every finite region containing its support the local inclusions
carry its finite-region matrix to the finite-region matrix on the larger
region.
-/
theorem localInclusion_fullPauliRegionMatrix (F F' : Finset Site) (hFF' : F ⊆ F')
    (a : FullPauliWord Site) (ha : a.SupportedIn F) :
    localInclusion hFF' (fullPauliRegionMatrix F a) = fullPauliRegionMatrix F' a :=
  finiteRegionEmbed_fullPauliRegionMatrix F F' hFF' a ha

/-- Every local stabilizer fixes the local stabilizer density. -/
theorem FullPauliRegionStabilizer.fullPauliRegionMatrix_mul_regionDensity
    (D : FullPauliRegionStabilizer Site) (g : D.group) :
    fullPauliRegionMatrix D.region (g : FullPauliWord Site) * D.regionDensity =
      D.regionDensity := by
  rw [D.regionDensity_eq_trace_normalized_regionProjector, Matrix.mul_smul,
    D.fullPauliRegionMatrix_mul_regionProjector g]

/-! ### A global consistent stabilizer system and its finite local data -/

/--
A **consistent stabilizer system**: a subgroup of the algebraic full-Pauli
group all of whose elements are involutive (algebraic Hermiticity) and which
does not contain the central word `-1`.  No countability, lattice structure,
exhaustion or short-range-order input is assumed.
-/
structure FullPauliStabilizerSystem (Site : Type*) [DecidableEq Site] where
  /-- The global stabilizer subgroup. -/
  group : Subgroup (FullPauliWord Site)
  /-- Every stabilizer squares to the identity word. -/
  involutive : ∀ g ∈ group, g * g = 1
  /-- Consistency: the central word `-1` is not a stabilizer. -/
  consistent : FullPauliWord.negativeIdentity (Site := Site) ∉ group

namespace FullPauliStabilizerSystem

variable (S : FullPauliStabilizerSystem Site)

/-- The explicitly finite local stabilizer subgroup and its finite-region data. -/
noncomputable def regionStabilizer (F : Finset Site) : FullPauliRegionStabilizer Site :=
  FullPauliRegionStabilizer.ofGlobalStabilizer S.group F S.involutive S.consistent

@[simp] theorem regionStabilizer_region (F : Finset Site) :
    (S.regionStabilizer F).region = F := rfl

theorem mem_regionStabilizer_group_iff (F : Finset Site) (a : FullPauliWord Site) :
    a ∈ (S.regionStabilizer F).group ↔ a ∈ S.group ∧ a.label.support ⊆ F :=
  mem_localStabilizerSubgroup_iff S.group F a

/-- The local stabilizer groups increase along the inclusion of finite regions. -/
theorem regionStabilizer_group_mono (F F' : Finset Site) (hFF' : F ⊆ F') :
    (S.regionStabilizer F).group ≤ (S.regionStabilizer F').group := by
  intro a ha
  obtain ⟨haS, hasupp⟩ := (S.mem_regionStabilizer_group_iff F a).mp ha
  exact (S.mem_regionStabilizer_group_iff F' a).mpr ⟨haS, hasupp.trans hFF'⟩

/-- The finite local stabilizer density `ρ_F = 2^{-|F|} ∑_{g ∈ G_{S,F}} g`. -/
noncomputable def regionDensity (F : Finset Site) : finiteRegionQubitAlgebra F :=
  (S.regionStabilizer F).regionDensity

/-- The finite local density is positive semidefinite. -/
theorem regionDensity_posSemidef (F : Finset Site) : (S.regionDensity F).PosSemidef :=
  (S.regionStabilizer F).regionDensity_posSemidef

/-- The finite local density has trace one. -/
theorem regionDensity_trace (F : Finset Site) : (S.regionDensity F).trace = 1 :=
  (S.regionStabilizer F).regionDensity_trace

/--
**Compatibility of the finite stabilizer densities.**  For finite regions
`F ⊆ F'`, tracing out `F' \ F` in the local density of `F'` gives exactly the
local density of `F`.  This is the manuscript's relation
`ρ_F = Tr_{F' \ F}(ρ_{F'})`.
-/
theorem finiteRegionPartialTrace_regionDensity (F F' : Finset Site) (hFF' : F ⊆ F') :
    finiteRegionPartialTrace F F' hFF' (S.regionDensity F') = S.regionDensity F := by
  classical
  have hle := S.regionStabilizer_group_mono F F' hFF'
  have hsum : finiteRegionPartialTrace F F' hFF' ((S.regionStabilizer F').regionSum) =
      ((2 : ℂ) ^ (F' \ F).card) • (S.regionStabilizer F).regionSum := by
    rw [FullPauliRegionStabilizer.regionSum, map_sum,
      FullPauliRegionStabilizer.regionSum, Finset.smul_sum]
    refine (Finset.sum_of_injOn
      (fun g : ↥(S.regionStabilizer F).group =>
        (⟨g.val, hle g.property⟩ : ↥(S.regionStabilizer F').group))
      (by
        intro g _ h _ hgh
        have hval : (g : FullPauliWord Site) = (h : FullPauliWord Site) := by
          simpa using congrArg
            (fun x : ↥(S.regionStabilizer F').group => (x : FullPauliWord Site)) hgh
        exact Subtype.ext hval)
      (fun g _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_ ?_).symm
    · intro h _ hnotmem
      have hsupp : ¬ ((h : FullPauliWord Site).label.support ⊆ F) := by
        intro hcon
        refine hnotmem ⟨⟨h.val, (S.mem_regionStabilizer_group_iff F h.val).mpr
          ⟨((S.mem_regionStabilizer_group_iff F' h.val).mp h.property).1, hcon⟩⟩,
          Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
      obtain ⟨s, hs, hsF⟩ := Finset.not_subset.mp hsupp
      exact finiteRegionPartialTrace_fullPauliRegionMatrix_eq_zero F F' hFF' _ s
        (((S.mem_regionStabilizer_group_iff F' h.val).mp h.property).2 hs) hsF
        (Finsupp.mem_support_iff.mp hs)
    · intro g _
      exact (finiteRegionPartialTrace_fullPauliRegionMatrix_of_supportedIn F F' hFF'
        (g : FullPauliWord Site)
        ((S.mem_regionStabilizer_group_iff F g.val).mp g.property).2).symm
  have hcard : ((2 : ℂ) ^ F'.card) = (2 : ℂ) ^ (F' \ F).card * (2 : ℂ) ^ F.card := by
    rw [← pow_add, Finset.card_sdiff_add_card_eq_card hFF']
  have h2 : ((2 : ℂ) ^ (F' \ F).card) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hscalar : ((2 : ℂ) ^ F'.card)⁻¹ * (2 : ℂ) ^ (F' \ F).card =
      ((2 : ℂ) ^ F.card)⁻¹ := by
    rw [hcard, mul_inv, mul_comm ((2 : ℂ) ^ (F' \ F).card)⁻¹, mul_assoc,
      inv_mul_cancel₀ h2, mul_one]
  rw [regionDensity, regionDensity, FullPauliRegionStabilizer.regionDensity,
    FullPauliRegionStabilizer.regionDensity, map_smul, hsum, smul_smul,
    regionStabilizer_region, hscalar]
  rfl

/-! ### The finite local states and the exact restriction formula -/

/-- The finite local state at a region: `ω_F(A) = Tr(ρ_F A)`. -/
noncomputable def localState (F : Finset Site) : finiteRegionQubitAlgebra F →ₗ[ℂ] ℂ where
  toFun A := ((S.regionDensity F) * A).trace
  map_add' A B := by rw [mul_add, Matrix.trace_add]
  map_smul' c A := by rw [Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul]

theorem localState_apply (F : Finset Site) (A : finiteRegionQubitAlgebra F) :
    S.localState F A = ((S.regionDensity F) * A).trace := rfl

/-- The finite local states are normalized. -/
@[simp] theorem localState_one (F : Finset Site) : S.localState F 1 = 1 := by
  rw [localState_apply, mul_one, S.regionDensity_trace]

/--
**The exact finite-stage restriction formula.**  For finite regions `F ⊆ F'`,
the finite local state of `F'` restricted along the identity-padding inclusion
is exactly the finite local state of `F`.
-/
theorem localState_localInclusion (F F' : Finset Site) (hFF' : F ⊆ F')
    (A : finiteRegionQubitAlgebra F) :
    S.localState F' (localInclusion hFF' A) = S.localState F A := by
  rw [localState_apply, localState_apply, localInclusion_eq,
    ← trace_finiteRegionPartialTrace F F' hFF',
    finiteRegionPartialTrace_mul_finiteRegionEmbed,
    S.finiteRegionPartialTrace_regionDensity F F' hFF']

/-- The restriction formula as an equality of linear functionals. -/
theorem localState_comp_localInclusion (F F' : Finset Site) (hFF' : F ⊆ F') :
    (S.localState F').comp (finiteRegionEmbed F F' hFF').toLinearMap = S.localState F :=
  LinearMap.ext fun A => S.localState_localInclusion F F' hFF' A

/--
**The composition law of the finite-stage restrictions.**  Restricting from
`F''` to `F'` and then to `F` is the restriction from `F''` to `F`, at the
level of the local inclusions, of the local densities and of the local states.
-/
theorem localState_localInclusion_trans (F F' F'' : Finset Site)
    (hFF' : F ⊆ F') (hF'F'' : F' ⊆ F'') (A : finiteRegionQubitAlgebra F) :
    S.localState F'' (localInclusion hF'F'' (localInclusion hFF' A)) = S.localState F A := by
  rw [S.localState_localInclusion F' F'' hF'F'', S.localState_localInclusion F F' hFF']

/-- The density form of the composition law. -/
theorem finiteRegionPartialTrace_regionDensity_trans (F F' F'' : Finset Site)
    (hFF' : F ⊆ F') (hF'F'' : F' ⊆ F'') :
    finiteRegionPartialTrace F F' hFF'
        (finiteRegionPartialTrace F' F'' hF'F'' (S.regionDensity F'')) =
      S.regionDensity F := by
  rw [S.finiteRegionPartialTrace_regionDensity F' F'' hF'F'',
    S.finiteRegionPartialTrace_regionDensity F F' hFF']

/--
The finite local state is the stabilizer state of its region: every local
stabilizer has expectation one.
-/
theorem localState_fullPauliRegionMatrix (F : Finset Site)
    (g : ↥(S.regionStabilizer F).group) :
    S.localState F (fullPauliRegionMatrix F (g : FullPauliWord Site)) = 1 := by
  have hmul : fullPauliRegionMatrix F (g : FullPauliWord Site) * S.regionDensity F =
      S.regionDensity F :=
    (S.regionStabilizer F).fullPauliRegionMatrix_mul_regionDensity g
  rw [localState_apply, Matrix.trace_mul_comm, hmul, S.regionDensity_trace]

end FullPauliStabilizerSystem

/-! ### Non-vacuity of the directed stabilizer system -/

/--
**Non-vacuity witness.**  A single one-site `Z` stabilizer generates a
consistent stabilizer system in the above sense, so all the compatibility and
restriction statements apply to it.
-/
noncomputable def zWordSystem (s : Site) : FullPauliStabilizerSystem Site where
  group := pairSubgroup (zWord s) (zWord_mul_self s)
  involutive := by
    intro g hg
    rcases (mem_pairSubgroup_iff (zWord s) (zWord_mul_self s) g).mp hg with rfl | rfl
    · exact one_mul 1
    · exact zWord_mul_self s
  consistent := by
    intro hmem
    rcases (mem_pairSubgroup_iff (zWord s) (zWord_mul_self s) _).mp hmem with h | h
    · exact FullPauliWord.negativeIdentity_ne_one h
    · exact zWord_ne_negativeIdentity s h.symm

/-- The one-site `Z` stabilizer belongs to the local group of every region containing it. -/
theorem zWord_mem_zWordSystem_regionStabilizer (s : Site) (F : Finset Site) (hs : s ∈ F) :
    zWord s ∈ ((zWordSystem s).regionStabilizer F).group :=
  ((zWordSystem s).mem_regionStabilizer_group_iff F (zWord s)).mpr
    ⟨(mem_pairSubgroup_iff (zWord s) (zWord_mul_self s) (zWord s)).mpr (Or.inr rfl),
      (zWord_support s).trans (Finset.singleton_subset_iff.mpr hs)⟩

/--
The local states of the one-site `Z` system are nontrivial: the stabilizer has
expectation one in every finite region containing its site.
-/
theorem zWordSystem_localState_zWord (s : Site) (F : Finset Site) (hs : s ∈ F) :
    (zWordSystem s).localState F (fullPauliRegionMatrix F (zWord s)) = 1 :=
  (zWordSystem s).localState_fullPauliRegionMatrix F
    ⟨zWord s, zWord_mem_zWordSystem_regionStabilizer s F hs⟩

end FiniteFiber
