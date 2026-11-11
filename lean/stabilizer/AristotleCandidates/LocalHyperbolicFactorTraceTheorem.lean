import AristotleCandidates.ProductGNSTensorFactorization
import AristotleCandidates.MixedUHFHyperfiniteFactor

/-!
# P59 — local-hyperbolic factor and trace theorem

**Context declaration.** Source basis: `main.tex:1671-1679, 1970-2004`.
Package `P59`, Lane `H`.  Predecessors `P57` (`ProductGNSTensorFactorization`)
and `P58` (`MixedUHFHyperfiniteFactor`) are imported.

This module transports the P57 spatial product model to the regional
represented algebra, proves the factor (trivial-centre) conclusion from
explicitly named commutation premises, and separates the finite-pure tracial
**state** from the infinite-pure faithful normal semifinite **weight**.

## Results, by status

**(a) Checked infrastructure (no premise).**

* Sections 1–2: the two commuting amplification `⋆`-homomorphisms
  `lampHom : B(K₁) →⋆ₐ[ℂ] B(K₁ ⊗̂ K₂)` and `rampHom : B(K₂) →⋆ₐ[ℂ] B(K₁ ⊗̂ K₂)`, including the
  operator norm bounds `norm_lmapₗ_le`, `norm_rmapₗ_le` (pinned Mathlib has no Hilbert-space
  operator tensor product), injectivity, and the centre/transport lemmas
  `hasTrivialCenterSet_bicommutant`, `HasTrivialCenterSet.image`, `restrictStarAlgEquiv`.
* Section 3: `tensorOpC_eq_amp`, `pureFactorSet_eq`, `mixedFactorSet_eq`.
* Section 4: the finite-pure functional `finitePureTrace` with `finitePureTrace_one`,
  `finitePureTrace_positive`, `finitePureTrace_isFiniteVectorNormal`, the elementary-product
  formula `finitePureTrace_lamp_ramp`, traciality on elementary products
  `finitePureTrace_tracial_lamp_ramp`, and faithfulness from a separating family.
* Sections 5, 7, 8: transport of functionals and of `ℝ≥0∞`-valued weights along a unitary, plus
  the unconditional weight calculus (`vectorWeight_add`, `vectorWeight_smul`,
  `vectorWeight_star_mul_self`, `vectorWeight_one_eq_top`).
* Section 10: the **bundled spatial `⋆`-isomorphism** `spatialRegionalStarEquiv`.

**(b) Theorems in the manuscript's intended form (unconditional).**

* `spatialRegionalStarEquiv : spatialSubalgebra D ≃⋆ₐ[ℂ] regionalSubalgebra D`, together with
  `unitaryConj_image_spatial`: the regional represented algebra is *spatially* `⋆`-isomorphic to
  `B(K_pure) ⊗̄ R_mixed`.
* `regionalAlgebra_weight_one_eq_top`: in the infinite-pure case the transported weight takes
  the value `∞` on `1`, so it is provably **not** a state.

**(c) Conditional theorems, with their exact extra premises.**

* `spatialTensorAlgebra_hasTrivialCenter`, `regionalAlgebra_hasTrivialCenter`
  (premise `SpatialFactorPremises`: `pure_nontrivial`, `pure_commutant`, `mixed_factor`).
* `spatialTensorAlgebra_isNormalizedTracialState`,
  `regionalAlgebra_isNormalizedTracialState`
  (premise `FinitePureTracePremises`: `mixed_unit`, `tracial`, `separating`).
* `spatialTensorAlgebra_isFaithfulNormalSemifiniteWeight`,
  `regionalAlgebra_isFaithfulNormalSemifiniteWeight`
  (premise `InfinitePureWeightPremises`: `mixed_unit`, `separating`, `semifinite`, `tracial`).

**(d) Auxiliary assumptions used (all explicit Lean structure fields, never axioms).**

1. `SpatialFactorPremises.pure_commutant` — the commutation theorem for the pure type I factor,
   `(π₁(A₁) ⊗ 1)' = 1 ⊗ B(K_mixed)`; it packages irreducibility of the pure GNS representation
   together with the elementary commutation theorem.
2. `SpatialFactorPremises.mixed_factor` — factoriality of the mixed weak closure (supplied in the
   local-hyperbolic model by P58's `MixedWeakClosurePremises.factor`).
3. `SpatialFactorPremises.pure_nontrivial` — the pure GNS space is nonzero.
4. `FinitePureTracePremises.tracial` / `InfinitePureWeightPremises.tracial` — persistence of
   traciality from the elementary products (proved here) to the whole bicommutant; this needs
   σ-weak normality plus Kaplansky density, absent from pinned Mathlib.
5. `FinitePureTracePremises.separating` / `InfinitePureWeightPremises.separating` — the product
   vectors `eᵢ ⊗ Ω` are separating for the algebra.
6. `FinitePureTracePremises.mixed_unit` / `InfinitePureWeightPremises.mixed_unit` — `Ω` is a unit
   vector.
7. `InfinitePureWeightPremises.semifinite` — semifiniteness of the canonical trace-weight.

**(e) Source/Mathlib obstructions still open.**  Pinned Mathlib has no von Neumann spatial tensor
product, no commutation theorem `(M ⊗̄ N)' = M' ⊗̄ N'`, no Kaplansky density theorem, no σ-weak
topology API for normality, and no canonical semifinite trace on `B(H)`.  Items 1, 4 and 7 above
are exactly the places where those missing theories enter.

**Forbidden downstream claims are not made here**: no general-lattice central decomposition, no
claim that Lane H proves Lane G, and no global tracial *state* in the infinite-pure case (the
infinite-pure functional is `ℝ≥0∞`-valued and satisfies `W 1 = ∞`).
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace

namespace AristotleCandidates
namespace LocalHyperbolicFactorTrace

universe u

/-! ## 1. Amplifications on a Hilbert tensor product

Given two complex Hilbert spaces `K₁`, `K₂`, we construct the two commuting
amplification `⋆`-homomorphisms

* `lampHom : B(K₁) →⋆ₐ[ℂ] B(K₁ ⊗̂ K₂)`, `A ↦ A ⊗ 1`;
* `rampHom : B(K₂) →⋆ₐ[ℂ] B(K₁ ⊗̂ K₂)`, `B ↦ 1 ⊗ B`,

where `K₁ ⊗̂ K₂ = Completion (K₁ ⊗[ℂ] K₂)` is the Hilbert tensor product used
by P57.  Pinned Mathlib has no operator tensor product, so the required norm
bound `‖(A ⊗ 1) t‖ ≤ ‖A‖ ‖t‖` is proved here from scratch, using positivity of
`‖A‖² - A* A` and the fact that a nonnegative operator is a sum of elements
`star s * s`.

Everything in this section is **checked infrastructure**: no premise is
assumed. -/

section Amplification

variable {K₁ K₂ : Type u}
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]

/-- The algebraic operator `A ⊗ 1` on the algebraic tensor product. -/
noncomputable def lmapₗ (A : K₁ →L[ℂ] K₁) : (K₁ ⊗[ℂ] K₂) →ₗ[ℂ] (K₁ ⊗[ℂ] K₂) :=
  TensorProduct.map A.toLinearMap LinearMap.id

/-- The algebraic operator `1 ⊗ B` on the algebraic tensor product. -/
noncomputable def rmapₗ (B : K₂ →L[ℂ] K₂) : (K₁ ⊗[ℂ] K₂) →ₗ[ℂ] (K₁ ⊗[ℂ] K₂) :=
  TensorProduct.map LinearMap.id B.toLinearMap

omit [CompleteSpace K₁] [CompleteSpace K₂] in
@[simp] theorem lmapₗ_tmul (A : K₁ →L[ℂ] K₁) (x : K₁) (y : K₂) :
    lmapₗ A (x ⊗ₜ[ℂ] y) = (A x) ⊗ₜ[ℂ] y := rfl

omit [CompleteSpace K₁] [CompleteSpace K₂] in
@[simp] theorem rmapₗ_tmul (B : K₂ →L[ℂ] K₂) (x : K₁) (y : K₂) :
    rmapₗ (K₁ := K₁) B (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] (B y) := rfl

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem lmapₗ_one : lmapₗ (K₂ := K₂) (1 : K₁ →L[ℂ] K₁) = LinearMap.id := by
  refine TensorProduct.ext' fun x y => ?_
  simp

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem rmapₗ_one : rmapₗ (K₁ := K₁) (1 : K₂ →L[ℂ] K₂) = LinearMap.id := by
  refine TensorProduct.ext' fun x y => ?_
  simp

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem lmapₗ_comp (A A' : K₁ →L[ℂ] K₁) (t : K₁ ⊗[ℂ] K₂) :
    lmapₗ (A ∘L A') t = lmapₗ A (lmapₗ A' t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add t s ht hs => simp only [map_add, ht, hs]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem rmapₗ_comp (B B' : K₂ →L[ℂ] K₂) (t : K₁ ⊗[ℂ] K₂) :
    rmapₗ (B ∘L B') t = rmapₗ B (rmapₗ B' t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add t s ht hs => simp only [map_add, ht, hs]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem lmapₗ_rmapₗ_comm (A : K₁ →L[ℂ] K₁) (B : K₂ →L[ℂ] K₂) (t : K₁ ⊗[ℂ] K₂) :
    lmapₗ A (rmapₗ B t) = rmapₗ B (lmapₗ A t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add t s ht hs => simp only [map_add, ht, hs]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem lmapₗ_add (A A' : K₁ →L[ℂ] K₁) (t : K₁ ⊗[ℂ] K₂) :
    lmapₗ (A + A') t = lmapₗ A t + lmapₗ A' t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.add_tmul]
  | add t s ht hs =>
    simp only [map_add, ht, hs]
    abel

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem rmapₗ_add (B B' : K₂ →L[ℂ] K₂) (t : K₁ ⊗[ℂ] K₂) :
    rmapₗ (K₁ := K₁) (B + B') t = rmapₗ B t + rmapₗ B' t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.tmul_add]
  | add t s ht hs =>
    simp only [map_add, ht, hs]
    abel

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem lmapₗ_smul (c : ℂ) (A : K₁ →L[ℂ] K₁) (t : K₁ ⊗[ℂ] K₂) :
    lmapₗ (c • A) t = c • lmapₗ A t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add t s ht hs => simp only [map_add, ht, hs, smul_add]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem rmapₗ_smul (c : ℂ) (B : K₂ →L[ℂ] K₂) (t : K₁ ⊗[ℂ] K₂) :
    rmapₗ (K₁ := K₁) (c • B) t = c • rmapₗ B t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.tmul_smul]
  | add t s ht hs => simp only [map_add, ht, hs, smul_add]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem lmapₗ_rsmul (c : ℝ) (A : K₁ →L[ℂ] K₁) (t : K₁ ⊗[ℂ] K₂) :
    lmapₗ (c • A) t = (c : ℂ) • lmapₗ A t := by
  have : (c • A) = ((c : ℂ) • A) := by
    ext x; simp [Complex.coe_smul]
  rw [this, lmapₗ_smul]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem rmapₗ_rsmul (c : ℝ) (B : K₂ →L[ℂ] K₂) (t : K₁ ⊗[ℂ] K₂) :
    rmapₗ (K₁ := K₁) (c • B) t = (c : ℂ) • rmapₗ B t := by
  have : (c • B) = ((c : ℂ) • B) := by
    ext x; simp [Complex.coe_smul]
  rw [this, rmapₗ_smul]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem lmapₗ_sub (A A' : K₁ →L[ℂ] K₁) (t : K₁ ⊗[ℂ] K₂) :
    lmapₗ (A - A') t = lmapₗ A t - lmapₗ A' t := by
  have h : lmapₗ (K₂ := K₂) (A - A' + A') t = lmapₗ (A - A') t + lmapₗ A' t := lmapₗ_add _ _ t
  rw [sub_add_cancel] at h
  rw [h]
  abel

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem rmapₗ_sub (B B' : K₂ →L[ℂ] K₂) (t : K₁ ⊗[ℂ] K₂) :
    rmapₗ (K₁ := K₁) (B - B') t = rmapₗ B t - rmapₗ B' t := by
  have h : rmapₗ (K₁ := K₁) (B - B' + B') t = rmapₗ (B - B') t + rmapₗ B' t := rmapₗ_add _ _ t
  rw [sub_add_cancel] at h
  rw [h]
  abel

omit [CompleteSpace K₂] in
/-- The adjoint identity for `A ⊗ 1` on the algebraic tensor product. -/
theorem inner_lmapₗ (A : K₁ →L[ℂ] K₁) (t s : K₁ ⊗[ℂ] K₂) :
    ⟪lmapₗ A t, s⟫_ℂ = ⟪t, lmapₗ (ContinuousLinearMap.adjoint A) s⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
      show ⟪(A x) ⊗ₜ[ℂ] y, x' ⊗ₜ[ℂ] y'⟫_ℂ
        = ⟪x ⊗ₜ[ℂ] y, (ContinuousLinearMap.adjoint A x') ⊗ₜ[ℂ] y'⟫_ℂ
      rw [TensorProduct.inner_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.adjoint_inner_right]
    | add s₁ s₂ h1 h2 => rw [inner_add_right, h1, h2, map_add, inner_add_right]
  | add t₁ t₂ h1 h2 => rw [inner_add_left, ← h1, ← h2, map_add, inner_add_left]

omit [CompleteSpace K₁] in
/-- The adjoint identity for `1 ⊗ B` on the algebraic tensor product. -/
theorem inner_rmapₗ (B : K₂ →L[ℂ] K₂) (t s : K₁ ⊗[ℂ] K₂) :
    ⟪rmapₗ B t, s⟫_ℂ = ⟪t, rmapₗ (ContinuousLinearMap.adjoint B) s⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
      show ⟪x ⊗ₜ[ℂ] (B y), x' ⊗ₜ[ℂ] y'⟫_ℂ
        = ⟪x ⊗ₜ[ℂ] y, x' ⊗ₜ[ℂ] (ContinuousLinearMap.adjoint B y')⟫_ℂ
      rw [TensorProduct.inner_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.adjoint_inner_right]
    | add s₁ s₂ h1 h2 => rw [inner_add_right, h1, h2, map_add, inner_add_right]
  | add t₁ t₂ h1 h2 => rw [inner_add_left, ← h1, ← h2, map_add, inner_add_left]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
@[simp] theorem lmapₗ_zero (t : K₁ ⊗[ℂ] K₂) : lmapₗ (0 : K₁ →L[ℂ] K₁) t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add a b ha hb => simp [map_add, ha, hb]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
@[simp] theorem rmapₗ_zero (t : K₁ ⊗[ℂ] K₂) : rmapₗ (K₁ := K₁) (0 : K₂ →L[ℂ] K₂) t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add a b ha hb => simp [map_add, ha, hb]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
/-- The real part of `⟪x, x⟫` is `‖x‖²`. -/
theorem re_inner_self (x : K₁ ⊗[ℂ] K₂) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
  have h : ⟪x, x⟫_ℂ = ((‖x‖ : ℂ) ^ 2) := inner_self_eq_norm_sq_to_K x
  rw [h]; simp [← Complex.ofReal_pow]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
/-- The real part of `c * ⟪x, x⟫` for a real scalar `c`. -/
theorem re_inner_self_mul (c : ℝ) (x : K₁ ⊗[ℂ] K₂) :
    ((c : ℂ) * ⟪x, x⟫_ℂ).re = c * ‖x‖ ^ 2 := by
  have h : ⟪x, x⟫_ℂ = ((‖x‖ : ℂ) ^ 2) := inner_self_eq_norm_sq_to_K x
  rw [h]; simp [← Complex.ofReal_pow, ← Complex.ofReal_mul]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
/-- Inner products against the scaled identity in the first slot. -/
theorem inner_lmapₗ_rsmul_one (c : ℝ) (s t : K₁ ⊗[ℂ] K₂) :
    ⟪s, lmapₗ ((c : ℝ) • (1 : K₁ →L[ℂ] K₁)) t⟫_ℂ = (c : ℂ) * ⟪s, t⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
      show ⟪x' ⊗ₜ[ℂ] y', (((c : ℝ) • (1 : K₁ →L[ℂ] K₁)) x) ⊗ₜ[ℂ] y⟫_ℂ
        = (c : ℂ) * ⟪x' ⊗ₜ[ℂ] y', x ⊗ₜ[ℂ] y⟫_ℂ
      rw [TensorProduct.inner_tmul, TensorProduct.inner_tmul]
      have hx : (((c : ℝ) • (1 : K₁ →L[ℂ] K₁)) x) = (c : ℂ) • x := by
        simp [Complex.coe_smul]
      rw [hx, inner_smul_right]
      ring
    | add s₁ s₂ h1 h2 => rw [inner_add_left, h1, h2, inner_add_left, mul_add]
  | add t₁ t₂ h1 h2 => rw [map_add, inner_add_right, h1, h2, inner_add_right, mul_add]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
/-- Inner products against the scaled identity in the second slot. -/
theorem inner_rmapₗ_rsmul_one (c : ℝ) (s t : K₁ ⊗[ℂ] K₂) :
    ⟪s, rmapₗ (K₁ := K₁) ((c : ℝ) • (1 : K₂ →L[ℂ] K₂)) t⟫_ℂ = (c : ℂ) * ⟪s, t⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
      show ⟪x' ⊗ₜ[ℂ] y', x ⊗ₜ[ℂ] (((c : ℝ) • (1 : K₂ →L[ℂ] K₂)) y)⟫_ℂ
        = (c : ℂ) * ⟪x' ⊗ₜ[ℂ] y', x ⊗ₜ[ℂ] y⟫_ℂ
      rw [TensorProduct.inner_tmul, TensorProduct.inner_tmul]
      have hy : (((c : ℝ) • (1 : K₂ →L[ℂ] K₂)) y) = (c : ℂ) • y := by
        simp [Complex.coe_smul]
      rw [hy, inner_smul_right]
      ring
    | add s₁ s₂ h1 h2 => rw [inner_add_left, h1, h2, inner_add_left, mul_add]
  | add t₁ t₂ h1 h2 => rw [map_add, inner_add_right, h1, h2, inner_add_right, mul_add]

omit [CompleteSpace K₂] in
/-- Nonnegativity of `⟪t, (P ⊗ 1) t⟫` for a nonnegative operator `P`. -/
theorem re_inner_lmapₗ_nonneg {P : K₁ →L[ℂ] K₁} (hP : 0 ≤ P) (t : K₁ ⊗[ℂ] K₂) :
    0 ≤ (⟪t, lmapₗ P t⟫_ℂ).re := by
  rw [StarOrderedRing.nonneg_iff] at hP
  induction hP using AddSubmonoid.closure_induction with
  | mem P hP =>
    obtain ⟨s, rfl⟩ := hP
    have h : ⟪t, lmapₗ (K₂ := K₂) (star s * s) t⟫_ℂ = ⟪lmapₗ s t, lmapₗ s t⟫_ℂ := by
      rw [inner_lmapₗ]
      congr 1
      have : (star s * s) = (ContinuousLinearMap.adjoint s) ∘L s := by
        rw [ContinuousLinearMap.star_eq_adjoint]; rfl
      rw [this, lmapₗ_comp]
    rw [h, re_inner_self]
    positivity
  | zero => simp
  | add P Q _ _ hP hQ =>
    have hadd : ⟪t, lmapₗ (K₂ := K₂) (P + Q) t⟫_ℂ = ⟪t, lmapₗ P t⟫_ℂ + ⟪t, lmapₗ Q t⟫_ℂ := by
      rw [lmapₗ_add, inner_add_right]
    rw [hadd, Complex.add_re]
    exact add_nonneg hP hQ

omit [CompleteSpace K₁] in
/-- Nonnegativity of `⟪t, (1 ⊗ Q) t⟫` for a nonnegative operator `Q`. -/
theorem re_inner_rmapₗ_nonneg {Q : K₂ →L[ℂ] K₂} (hQ : 0 ≤ Q) (t : K₁ ⊗[ℂ] K₂) :
    0 ≤ (⟪t, rmapₗ Q t⟫_ℂ).re := by
  rw [StarOrderedRing.nonneg_iff] at hQ
  induction hQ using AddSubmonoid.closure_induction with
  | mem Q hQ =>
    obtain ⟨s, rfl⟩ := hQ
    have h : ⟪t, rmapₗ (K₁ := K₁) (star s * s) t⟫_ℂ = ⟪rmapₗ s t, rmapₗ s t⟫_ℂ := by
      rw [inner_rmapₗ]
      congr 1
      have : (star s * s) = (ContinuousLinearMap.adjoint s) ∘L s := by
        rw [ContinuousLinearMap.star_eq_adjoint]; rfl
      rw [this, rmapₗ_comp]
    rw [h, re_inner_self]
    positivity
  | zero => simp
  | add P Q _ _ hP hQ =>
    have hadd : ⟪t, rmapₗ (K₁ := K₁) (P + Q) t⟫_ℂ = ⟪t, rmapₗ P t⟫_ℂ + ⟪t, rmapₗ Q t⟫_ℂ := by
      rw [rmapₗ_add, inner_add_right]
    rw [hadd, Complex.add_re]
    exact add_nonneg hP hQ

/-- `‖A‖² - A*A` is a nonnegative operator. -/
theorem norm_sq_sub_adjoint_mul_self_nonneg (A : K₁ →L[ℂ] K₁) :
    (0 : K₁ →L[ℂ] K₁) ≤ (‖A‖ ^ 2 : ℝ) • (1 : K₁ →L[ℂ] K₁) - ContinuousLinearMap.adjoint A ∘L A := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff']
  refine ⟨?_, ?_⟩
  · refine IsSelfAdjoint.sub (IsSelfAdjoint.smul (IsSelfAdjoint.all _) (IsSelfAdjoint.one _)) ?_
    show star (ContinuousLinearMap.adjoint A ∘L A) = _
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  · intro x
    have h1 : ⟪((‖A‖ ^ 2 : ℝ) • (1 : K₁ →L[ℂ] K₁) - ContinuousLinearMap.adjoint A ∘L A) x, x⟫_ℂ
        = ((‖A‖ ^ 2 * ‖x‖ ^ 2 - ‖A x‖ ^ 2 : ℝ) : ℂ) := by
      simp [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    rw [h1, Complex.zero_le_real]
    nlinarith [A.le_opNorm x, norm_nonneg (A x), norm_nonneg x, norm_nonneg A]

omit [CompleteSpace K₂] in
/-- **The tensor norm bound for `A ⊗ 1`.** -/
theorem norm_lmapₗ_le (A : K₁ →L[ℂ] K₁) (t : K₁ ⊗[ℂ] K₂) : ‖lmapₗ A t‖ ≤ ‖A‖ * ‖t‖ := by
  set P : K₁ →L[ℂ] K₁ :=
    (‖A‖ ^ 2 : ℝ) • (1 : K₁ →L[ℂ] K₁) - ContinuousLinearMap.adjoint A ∘L A with hPdef
  have hP : (0 : K₁ →L[ℂ] K₁) ≤ P := norm_sq_sub_adjoint_mul_self_nonneg A
  have hsplit : ContinuousLinearMap.adjoint A ∘L A = (‖A‖ ^ 2 : ℝ) • (1 : K₁ →L[ℂ] K₁) - P := by
    rw [hPdef]; abel
  have key : ‖lmapₗ (K₂ := K₂) A t‖ ^ 2 = (‖A‖ ^ 2) * ‖t‖ ^ 2 - (⟪t, lmapₗ P t⟫_ℂ).re := by
    have h0 := inner_lmapₗ (K₂ := K₂) A t (lmapₗ A t)
    rw [← lmapₗ_comp] at h0
    have h1 : (‖lmapₗ (K₂ := K₂) A t‖ ^ 2 : ℝ)
        = (⟪t, lmapₗ (ContinuousLinearMap.adjoint A ∘L A) t⟫_ℂ).re := by
      rw [← h0, re_inner_self]
    rw [h1, hsplit, lmapₗ_sub, inner_sub_right, Complex.sub_re]
    congr 1
    rw [inner_lmapₗ_rsmul_one, re_inner_self_mul]
  have hnn : 0 ≤ (⟪t, lmapₗ (K₂ := K₂) P t⟫_ℂ).re := re_inner_lmapₗ_nonneg hP t
  have hle : ‖lmapₗ (K₂ := K₂) A t‖ ^ 2 ≤ (‖A‖ * ‖t‖) ^ 2 := by
    rw [key, mul_pow]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hle

omit [CompleteSpace K₁] in
/-- **The tensor norm bound for `1 ⊗ B`.** -/
theorem norm_rmapₗ_le (B : K₂ →L[ℂ] K₂) (t : K₁ ⊗[ℂ] K₂) : ‖rmapₗ B t‖ ≤ ‖B‖ * ‖t‖ := by
  set Q : K₂ →L[ℂ] K₂ :=
    (‖B‖ ^ 2 : ℝ) • (1 : K₂ →L[ℂ] K₂) - ContinuousLinearMap.adjoint B ∘L B with hQdef
  have hQ : (0 : K₂ →L[ℂ] K₂) ≤ Q := norm_sq_sub_adjoint_mul_self_nonneg B
  have hsplit : ContinuousLinearMap.adjoint B ∘L B = (‖B‖ ^ 2 : ℝ) • (1 : K₂ →L[ℂ] K₂) - Q := by
    rw [hQdef]; abel
  have key : ‖rmapₗ (K₁ := K₁) B t‖ ^ 2 = (‖B‖ ^ 2) * ‖t‖ ^ 2 - (⟪t, rmapₗ Q t⟫_ℂ).re := by
    have h0 := inner_rmapₗ (K₁ := K₁) B t (rmapₗ B t)
    rw [← rmapₗ_comp] at h0
    have h1 : (‖rmapₗ (K₁ := K₁) B t‖ ^ 2 : ℝ)
        = (⟪t, rmapₗ (ContinuousLinearMap.adjoint B ∘L B) t⟫_ℂ).re := by
      rw [← h0, re_inner_self]
    rw [h1, hsplit, rmapₗ_sub, inner_sub_right, Complex.sub_re]
    congr 1
    rw [inner_rmapₗ_rsmul_one, re_inner_self_mul]
  have hnn : 0 ≤ (⟪t, rmapₗ (K₁ := K₁) Q t⟫_ℂ).re := re_inner_rmapₗ_nonneg hQ t
  have hle : ‖rmapₗ (K₁ := K₁) B t‖ ^ 2 ≤ (‖B‖ * ‖t‖) ^ 2 := by
    rw [key, mul_pow]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hle

/-! ### 1.2 The amplification `⋆`-homomorphisms on the Hilbert tensor product -/

omit [CompleteSpace K₁] [CompleteSpace K₂] in
/-- Extensionality on the completion: two continuous linear maps out of a completion agree as
soon as they agree on the image of the dense subspace. -/
theorem completion_clm_ext {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (S T : Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Y)
    (h : ∀ t : K₁ ⊗[ℂ] K₂, S (t : Completion (K₁ ⊗[ℂ] K₂)) = T t) : S = T := by
  ext z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih t => exact h t

/-- The bounded operator `A ⊗ 1` on the algebraic tensor product. -/
noncomputable def lampPre (A : K₁ →L[ℂ] K₁) : (K₁ ⊗[ℂ] K₂) →L[ℂ] (K₁ ⊗[ℂ] K₂) :=
  (lmapₗ A).mkContinuous ‖A‖ (norm_lmapₗ_le A)

/-- The bounded operator `1 ⊗ B` on the algebraic tensor product. -/
noncomputable def rampPre (B : K₂ →L[ℂ] K₂) : (K₁ ⊗[ℂ] K₂) →L[ℂ] (K₁ ⊗[ℂ] K₂) :=
  (rmapₗ B).mkContinuous ‖B‖ (norm_rmapₗ_le B)

/-- **The left amplification** `A ↦ A ⊗ 1` on the Hilbert tensor product. -/
noncomputable def lamp (A : K₁ →L[ℂ] K₁) :
    Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂) :=
  (lampPre (K₂ := K₂) A).completion

/-- **The right amplification** `B ↦ 1 ⊗ B` on the Hilbert tensor product. -/
noncomputable def ramp (B : K₂ →L[ℂ] K₂) :
    Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂) :=
  (rampPre (K₁ := K₁) B).completion

omit [CompleteSpace K₂] in
@[simp] theorem lamp_coe (A : K₁ →L[ℂ] K₁) (t : K₁ ⊗[ℂ] K₂) :
    lamp A (t : Completion (K₁ ⊗[ℂ] K₂)) = ((lmapₗ A t : K₁ ⊗[ℂ] K₂) : Completion (K₁ ⊗[ℂ] K₂)) :=
  ContinuousLinearMap.completion_apply_coe _ _

omit [CompleteSpace K₁] in
@[simp] theorem ramp_coe (B : K₂ →L[ℂ] K₂) (t : K₁ ⊗[ℂ] K₂) :
    ramp (K₁ := K₁) B (t : Completion (K₁ ⊗[ℂ] K₂))
      = ((rmapₗ B t : K₁ ⊗[ℂ] K₂) : Completion (K₁ ⊗[ℂ] K₂)) :=
  ContinuousLinearMap.completion_apply_coe _ _

omit [CompleteSpace K₂] in
theorem lamp_one : lamp (K₂ := K₂) (1 : K₁ →L[ℂ] K₁) = 1 := by
  refine completion_clm_ext _ _ fun t => ?_
  rw [lamp_coe, lmapₗ_one]
  rfl

omit [CompleteSpace K₁] in
theorem ramp_one : ramp (K₁ := K₁) (1 : K₂ →L[ℂ] K₂) = 1 := by
  refine completion_clm_ext _ _ fun t => ?_
  rw [ramp_coe, rmapₗ_one]
  rfl

omit [CompleteSpace K₂] in
theorem lamp_mul (A A' : K₁ →L[ℂ] K₁) :
    lamp (K₂ := K₂) (A * A') = lamp A * lamp A' := by
  refine completion_clm_ext _ _ fun t => ?_
  show lamp (A * A') (t : Completion (K₁ ⊗[ℂ] K₂)) = lamp A (lamp A' (t : Completion _))
  rw [lamp_coe, lamp_coe, lamp_coe]
  congr 1
  exact lmapₗ_comp A A' t

omit [CompleteSpace K₁] in
theorem ramp_mul (B B' : K₂ →L[ℂ] K₂) :
    ramp (K₁ := K₁) (B * B') = ramp B * ramp B' := by
  refine completion_clm_ext _ _ fun t => ?_
  show ramp (K₁ := K₁) (B * B') (t : Completion (K₁ ⊗[ℂ] K₂))
    = ramp (K₁ := K₁) B (ramp B' (t : Completion _))
  rw [ramp_coe, ramp_coe, ramp_coe]
  congr 1
  exact rmapₗ_comp B B' t

omit [CompleteSpace K₂] in
theorem lamp_add (A A' : K₁ →L[ℂ] K₁) :
    lamp (K₂ := K₂) (A + A') = lamp A + lamp A' := by
  refine completion_clm_ext _ _ fun t => ?_
  show lamp (A + A') (t : Completion (K₁ ⊗[ℂ] K₂))
    = lamp A (t : Completion _) + lamp A' (t : Completion _)
  rw [lamp_coe, lamp_coe, lamp_coe, lmapₗ_add]
  exact Completion.coe_add _ _

omit [CompleteSpace K₁] in
theorem ramp_add (B B' : K₂ →L[ℂ] K₂) :
    ramp (K₁ := K₁) (B + B') = ramp B + ramp B' := by
  refine completion_clm_ext _ _ fun t => ?_
  show ramp (K₁ := K₁) (B + B') (t : Completion (K₁ ⊗[ℂ] K₂))
    = ramp (K₁ := K₁) B (t : Completion _) + ramp (K₁ := K₁) B' (t : Completion _)
  rw [ramp_coe, ramp_coe, ramp_coe, rmapₗ_add]
  exact Completion.coe_add _ _

omit [CompleteSpace K₂] in
theorem lamp_smul (c : ℂ) (A : K₁ →L[ℂ] K₁) :
    lamp (K₂ := K₂) (c • A) = c • lamp A := by
  refine completion_clm_ext _ _ fun t => ?_
  show lamp (c • A) (t : Completion (K₁ ⊗[ℂ] K₂)) = c • lamp A (t : Completion _)
  rw [lamp_coe, lamp_coe, lmapₗ_smul]
  exact Completion.coe_smul c _

omit [CompleteSpace K₁] in
theorem ramp_smul (c : ℂ) (B : K₂ →L[ℂ] K₂) :
    ramp (K₁ := K₁) (c • B) = c • ramp B := by
  refine completion_clm_ext _ _ fun t => ?_
  show ramp (K₁ := K₁) (c • B) (t : Completion (K₁ ⊗[ℂ] K₂)) = c • ramp (K₁ := K₁) B (t : Completion _)
  rw [ramp_coe, ramp_coe, rmapₗ_smul]
  exact Completion.coe_smul c _

omit [CompleteSpace K₂] in
theorem inner_lamp (A : K₁ →L[ℂ] K₁) (z w : Completion (K₁ ⊗[ℂ] K₂)) :
    ⟪lamp A z, w⟫_ℂ = ⟪z, lamp (ContinuousLinearMap.adjoint A) w⟫_ℂ := by
  induction z, w using Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq
      (Continuous.inner ((lamp A).continuous.comp continuous_fst) continuous_snd)
      (Continuous.inner continuous_fst
        ((lamp (ContinuousLinearMap.adjoint A)).continuous.comp continuous_snd))
  | ih t s =>
    rw [lamp_coe, lamp_coe, Completion.inner_coe, Completion.inner_coe]
    exact inner_lmapₗ A t s

omit [CompleteSpace K₁] in
theorem inner_ramp (B : K₂ →L[ℂ] K₂) (z w : Completion (K₁ ⊗[ℂ] K₂)) :
    ⟪ramp (K₁ := K₁) B z, w⟫_ℂ = ⟪z, ramp (K₁ := K₁) (ContinuousLinearMap.adjoint B) w⟫_ℂ := by
  induction z, w using Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq
      (Continuous.inner ((ramp (K₁ := K₁) B).continuous.comp continuous_fst) continuous_snd)
      (Continuous.inner continuous_fst
        ((ramp (K₁ := K₁) (ContinuousLinearMap.adjoint B)).continuous.comp continuous_snd))
  | ih t s =>
    rw [ramp_coe, ramp_coe, Completion.inner_coe, Completion.inner_coe]
    exact inner_rmapₗ B t s

omit [CompleteSpace K₂] in
theorem lamp_star (A : K₁ →L[ℂ] K₁) : star (lamp (K₂ := K₂) A) = lamp (star A) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun z w => ?_
  rw [ContinuousLinearMap.star_eq_adjoint]
  have h := inner_lamp (K₂ := K₂) (ContinuousLinearMap.adjoint A) z w
  rw [ContinuousLinearMap.adjoint_adjoint] at h
  exact h

omit [CompleteSpace K₁] in
theorem ramp_star (B : K₂ →L[ℂ] K₂) : star (ramp (K₁ := K₁) B) = ramp (star B) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun z w => ?_
  rw [ContinuousLinearMap.star_eq_adjoint]
  have h := inner_ramp (K₁ := K₁) (ContinuousLinearMap.adjoint B) z w
  rw [ContinuousLinearMap.adjoint_adjoint] at h
  exact h

/-- **The left amplification as a unital `⋆`-homomorphism** `B(K₁) →⋆ₐ B(K₁ ⊗̂ K₂)`. -/
noncomputable def lampHom :
    (K₁ →L[ℂ] K₁) →⋆ₐ[ℂ] (Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂)) where
  toFun := lamp
  map_one' := lamp_one
  map_mul' := lamp_mul
  map_zero' := by
    refine completion_clm_ext _ _ fun t => ?_
    rw [lamp_coe, lmapₗ_zero]
    rfl
  map_add' := lamp_add
  commutes' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, lamp_smul, lamp_one]
  map_star' := fun A => (lamp_star A).symm

/-- **The right amplification as a unital `⋆`-homomorphism** `B(K₂) →⋆ₐ B(K₁ ⊗̂ K₂)`. -/
noncomputable def rampHom :
    (K₂ →L[ℂ] K₂) →⋆ₐ[ℂ] (Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂)) where
  toFun := ramp
  map_one' := ramp_one
  map_mul' := ramp_mul
  map_zero' := by
    refine completion_clm_ext _ _ fun t => ?_
    rw [ramp_coe, rmapₗ_zero]
    rfl
  map_add' := ramp_add
  commutes' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ramp_smul, ramp_one]
  map_star' := fun B => (ramp_star B).symm

omit [CompleteSpace K₂] in
@[simp] theorem lampHom_apply (A : K₁ →L[ℂ] K₁) : lampHom (K₂ := K₂) A = lamp A := by
  rfl

omit [CompleteSpace K₁] in
@[simp] theorem rampHom_apply (B : K₂ →L[ℂ] K₂) : rampHom (K₁ := K₁) B = ramp B := by
  rfl

/-- **The two amplifications commute.** -/
theorem lamp_ramp_commute (A : K₁ →L[ℂ] K₁) (B : K₂ →L[ℂ] K₂) :
    lamp A * ramp (K₁ := K₁) B = ramp B * lamp A := by
  refine completion_clm_ext _ _ fun t => ?_
  show lamp A (ramp (K₁ := K₁) B (t : Completion (K₁ ⊗[ℂ] K₂)))
    = ramp (K₁ := K₁) B (lamp A (t : Completion _))
  rw [ramp_coe, lamp_coe, lamp_coe, ramp_coe]
  congr 1
  exact lmapₗ_rmapₗ_comm A B t

omit [CompleteSpace K₂] in
/-- **Injectivity of the left amplification** (given a nonzero second factor). -/
theorem lamp_injective (hK₂ : ∃ y : K₂, y ≠ 0) :
    Function.Injective (lamp (K₁ := K₁) (K₂ := K₂)) := by
  intro A A' h
  obtain ⟨y, hy⟩ := hK₂
  ext x
  have h1 : ((lmapₗ (K₂ := K₂) A (x ⊗ₜ[ℂ] y) : K₁ ⊗[ℂ] K₂) : Completion (K₁ ⊗[ℂ] K₂))
      = ((lmapₗ (K₂ := K₂) A' (x ⊗ₜ[ℂ] y) : K₁ ⊗[ℂ] K₂) : Completion (K₁ ⊗[ℂ] K₂)) := by
    rw [← lamp_coe, ← lamp_coe, h]
  have h2 : lmapₗ (K₂ := K₂) A (x ⊗ₜ[ℂ] y) = lmapₗ (K₂ := K₂) A' (x ⊗ₜ[ℂ] y) :=
    Completion.coe_injective _ h1
  rw [lmapₗ_tmul, lmapₗ_tmul] at h2
  have h3 : (A x - A' x) ⊗ₜ[ℂ] y = 0 := by
    rw [TensorProduct.sub_tmul, h2, sub_self]
  have h4 : ‖(A x - A' x) ⊗ₜ[ℂ] y‖ = 0 := by rw [h3, norm_zero]
  rw [TensorProduct.norm_tmul] at h4
  have h5 : ‖A x - A' x‖ = 0 := by
    rcases mul_eq_zero.mp h4 with h | h
    · exact h
    · exact absurd (norm_eq_zero.mp h) hy
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)

omit [CompleteSpace K₁] in
/-- **Injectivity of the right amplification** (given a nonzero first factor). -/
theorem ramp_injective (hK₁ : ∃ x : K₁, x ≠ 0) :
    Function.Injective (ramp (K₁ := K₁) (K₂ := K₂)) := by
  intro B B' h
  obtain ⟨x, hx⟩ := hK₁
  ext y
  have h1 : ((rmapₗ (K₁ := K₁) B (x ⊗ₜ[ℂ] y) : K₁ ⊗[ℂ] K₂) : Completion (K₁ ⊗[ℂ] K₂))
      = ((rmapₗ (K₁ := K₁) B' (x ⊗ₜ[ℂ] y) : K₁ ⊗[ℂ] K₂) : Completion (K₁ ⊗[ℂ] K₂)) := by
    rw [← ramp_coe, ← ramp_coe, h]
  have h2 : rmapₗ (K₁ := K₁) B (x ⊗ₜ[ℂ] y) = rmapₗ (K₁ := K₁) B' (x ⊗ₜ[ℂ] y) :=
    Completion.coe_injective _ h1
  rw [rmapₗ_tmul, rmapₗ_tmul] at h2
  have h3 : x ⊗ₜ[ℂ] (B y - B' y) = 0 := by
    rw [TensorProduct.tmul_sub, h2, sub_self]
  have h4 : ‖x ⊗ₜ[ℂ] (B y - B' y)‖ = 0 := by rw [h3, norm_zero]
  rw [TensorProduct.norm_tmul] at h4
  have h5 : ‖B y - B' y‖ = 0 := by
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd (norm_eq_zero.mp h) hx
    · exact h
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)

end Amplification

/-! ## 2. Centres, factors, and transport along a `⋆`-isomorphism

All results in this section are **checked infrastructure**; nothing is assumed. -/

section Center

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- **Project-local definition (trivial centre / factor, set form).**  A set of operators has
trivial centre when each of its elements that commutes with the whole set is a scalar.  For a
concrete von Neumann algebra this is exactly P58's `HasTrivialOperatorCenter`. -/
def HasTrivialCenterSet (S : Set (H →L[ℂ] H)) : Prop :=
  ∀ T ∈ S, (∀ y ∈ S, y * T = T * y) → ∃ c : ℂ, T = c • 1

theorem hasTrivialOperatorCenter_iff (M : VonNeumannAlgebra H) :
    StabilizerHyperfinite.HasTrivialOperatorCenter M ↔
      HasTrivialCenterSet (M : Set (H →L[ℂ] H)) := Iff.rfl

omit [CompleteSpace H] in
/-- **The centre of `S''` is the centre of `S'`.**  Hence a bicommutant is a factor as soon as
the commutant is one. -/
theorem hasTrivialCenterSet_bicommutant (S : Set (H →L[ℂ] H))
    (h : HasTrivialCenterSet S.centralizer) :
    HasTrivialCenterSet S.centralizer.centralizer := by
  intro T hTmem hTcomm
  have ha : T ∈ S.centralizer := fun y hy =>
    hTcomm y (Set.subset_centralizer_centralizer hy)
  exact h T ha hTmem

/-- **Transport of factoriality along a `⋆`-isomorphism of operator algebras.** -/
theorem HasTrivialCenterSet.image (e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H' →L[ℂ] H'))
    {S : Set (H →L[ℂ] H)} (h : HasTrivialCenterSet S) : HasTrivialCenterSet (e '' S) := by
  rintro _ ⟨x, hx, rfl⟩ hcomm
  have hxc : ∀ y ∈ S, y * x = x * y := by
    intro y hy
    have h1 : e y * e x = e x * e y := hcomm (e y) ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact e.injective h1
  obtain ⟨c, hc⟩ := h x hx hxc
  exact ⟨c, by rw [hc, map_smul, map_one]⟩

/-- Restriction of a `⋆`-isomorphism to a pair of matching `⋆`-subalgebras. -/
noncomputable def restrictStarAlgEquiv {A B : Type*}
    [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) (S : StarSubalgebra ℂ A) (T : StarSubalgebra ℂ B)
    (h : ∀ x : A, x ∈ S ↔ e x ∈ T) : S ≃⋆ₐ[ℂ] T :=
  StarAlgEquiv.ofBijective
    ((((e : A →⋆ₐ[ℂ] B)).comp S.subtype).codRestrict T (fun x => (h x).mp x.2))
    ⟨by
      intro x y hxy
      exact Subtype.ext (e.injective (congrArg Subtype.val hxy)),
     by
      rintro ⟨y, hy⟩
      refine ⟨⟨e.symm y, (h (e.symm y)).mpr ?_⟩, ?_⟩
      · rw [e.apply_symm_apply]; exact hy
      · exact Subtype.ext (by simp)⟩

@[simp] theorem restrictStarAlgEquiv_apply {A B : Type*}
    [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) (S : StarSubalgebra ℂ A) (T : StarSubalgebra ℂ B)
    (h : ∀ x : A, x ∈ S ↔ e x ∈ T) (x : S) :
    (restrictStarAlgEquiv e S T h x : B) = e (x : A) := rfl

end Center

/-! ## 3. The spatial product model of the regional algebra

We now specialize to the P57 product-GNS datum `D`.  Its Hilbert tensor product
`D.TensorGNS = Completion (K_pure ⊗ K_mixed)` carries the two amplifications of Section 1, and
P57's elementary tensor operators factor through them. -/

section Regional

open AristotleCandidates.ProductGNSTensor

variable (D : ProductGNSData.{u})

/-- The represented pure factor operator `π₁(a) ⊗ 1`. -/
noncomputable def pureAmp (a : D.Pure) : D.TensorGNS →L[ℂ] D.TensorGNS := lamp (D.pureRep a)

/-- The represented mixed factor operator `1 ⊗ π₂(b)`. -/
noncomputable def mixedAmp (b : D.Mixed) : D.TensorGNS →L[ℂ] D.TensorGNS := ramp (D.mixedRep b)

theorem tensorMapₗ_eq (a : D.Pure) (b : D.Mixed) (t : D.TensorPre) :
    D.tensorMapₗ a b t = lmapₗ (D.pureRep a) (rmapₗ (D.mixedRep b) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add t s ht hs => simp only [map_add, ht, hs]

/-- **P57's elementary tensor operator is the product of the two amplifications.** -/
theorem tensorOpC_eq_amp (a : D.Pure) (b : D.Mixed) :
    D.tensorOpC a b = pureAmp D a * mixedAmp D b := by
  refine completion_clm_ext _ _ fun t => ?_
  show D.tensorOpC a b (t : D.TensorGNS) = lamp (D.pureRep a) (ramp (D.mixedRep b) (t : D.TensorGNS))
  rw [ProductGNSData.tensorOpC_coe, ramp_coe, lamp_coe, tensorMapₗ_eq]

theorem pureFactorSet_eq : D.pureFactorSet = Set.range (pureAmp D) := by
  refine congrArg Set.range (funext fun a => ?_)
  rw [tensorOpC_eq_amp, mixedAmp, map_one, ramp_one, mul_one]

theorem mixedFactorSet_eq : D.mixedFactorSet = Set.range (mixedAmp D) := by
  refine congrArg Set.range (funext fun b => ?_)
  rw [tensorOpC_eq_amp, pureAmp, map_one, lamp_one, one_mul]

/-- The regional represented von Neumann algebra `π_ω̃(A_Γ)''` on the GNS space of the product
state. -/
def regionalAlgebra : Set (D.TotalGNS →L[ℂ] D.TotalGNS) :=
  (Set.range D.totalRep).centralizer.centralizer

/-- **The spatial identification (P57), restated for this packet.**  Conjugation by the product
GNS unitary carries the spatial tensor product `B_pure ⊗̄ R_mixed` onto the regional algebra. -/
theorem unitaryConj_image_spatial : D.unitaryConj '' D.spatialTensorAlgebra = regionalAlgebra D :=
  D.unitaryConj_image_spatialTensorAlgebra

/-! ### 3.1 The auxiliary commutation premises

The two fields below are the analytic inputs that neither P57 nor P58 provides and that pinned
Mathlib does not contain.  They are stated as explicit premises, never as axioms.

* `pure_commutant` is the *commutation theorem for the type I factor*: the commutant of the
  represented pure factor `π₁(A₁) ⊗ 1` consists exactly of the operators `1 ⊗ B`.  It contains
  both the irreducibility of the pure GNS representation (`π₁(A₁)'' = B(K_pure)`, true for a pure
  state) and the elementary commutation theorem `(B(K_pure) ⊗ 1)' = 1 ⊗ B(K_mixed)`.
* `mixed_factor` is the mixed-sector factoriality supplied, in the local-hyperbolic model, by
  P58's `MixedWeakClosurePremises.factor`.
* `pure_nontrivial` says the pure GNS space is nonzero; it holds whenever `pureState` is a state
  (i.e. `pureState 1 = 1`). -/
structure SpatialFactorPremises : Prop where
  /-- the pure GNS space is nonzero -/
  pure_nontrivial : ∃ x : D.PureGNS, x ≠ 0
  /-- commutation theorem for the pure type I factor -/
  pure_commutant :
    D.pureFactorSet.centralizer = Set.range (ramp (K₁ := D.PureGNS) (K₂ := D.MixedGNS))
  /-- the mixed represented algebra is a factor -/
  mixed_factor : HasTrivialCenterSet (Set.range D.mixedRep).centralizer.centralizer

/-- **Factoriality of the spatial tensor product.**  Under the two named commutation premises,
`B(K_pure) ⊗̄ R_mixed` has trivial centre. -/
theorem spatialTensorAlgebra_hasTrivialCenter (h : SpatialFactorPremises D) :
    HasTrivialCenterSet D.spatialTensorAlgebra := by
  classical
  set S : Set (D.TensorGNS →L[ℂ] D.TensorGNS) := D.pureFactorSet ∪ D.mixedFactorSet with hS
  have hramp_inj : Function.Injective (ramp (K₁ := D.PureGNS) (K₂ := D.MixedGNS)) :=
    ramp_injective h.pure_nontrivial
  intro T hTmem hTcomm
  -- `T` commutes with `S`, hence lies in `S'`
  have hTS : T ∈ S.centralizer := fun y hy =>
    hTcomm y (Set.subset_centralizer_centralizer hy)
  -- hence `T = 1 ⊗ b` for some `b`
  have hTpure : T ∈ D.pureFactorSet.centralizer := fun y hy => hTS y (Or.inl hy)
  obtain ⟨b, rfl⟩ : ∃ b, ramp b = T := by
    have := h.pure_commutant ▸ hTpure
    exact this
  -- `b` commutes with the represented mixed algebra
  have hbN' : b ∈ (Set.range D.mixedRep).centralizer := by
    rintro _ ⟨m, rfl⟩
    have h1 : mixedAmp D m * ramp b = ramp b * mixedAmp D m :=
      hTS _ (Or.inr (by rw [mixedFactorSet_eq]; exact ⟨m, rfl⟩))
    rw [mixedAmp, ← ramp_mul, ← ramp_mul] at h1
    exact hramp_inj h1
  -- every `1 ⊗ c` with `c` in the commutant lies in `S'`
  have hrampS : ∀ c ∈ (Set.range D.mixedRep).centralizer, ramp c ∈ S.centralizer := by
    intro c hc y hy
    rcases hy with hy | hy
    · rw [pureFactorSet_eq] at hy
      obtain ⟨a, rfl⟩ := hy
      exact (lamp_ramp_commute (D.pureRep a) c).symm ▸ rfl
    · rw [mixedFactorSet_eq] at hy
      obtain ⟨m, rfl⟩ := hy
      rw [mixedAmp, ← ramp_mul, ← ramp_mul, hc _ ⟨m, rfl⟩]
  -- so `b` also commutes with the whole commutant, i.e. `b ∈ N''`
  have hbN'' : b ∈ (Set.range D.mixedRep).centralizer.centralizer := by
    intro c hc
    have h1 : ramp c * ramp b = ramp b * ramp c := hTmem _ (hrampS c hc)
    rw [← ramp_mul, ← ramp_mul] at h1
    exact hramp_inj h1
  -- `b` is central in `N''`, hence scalar
  obtain ⟨c₀, hc₀⟩ := h.mixed_factor b hbN'' (fun y hy => (hy b hbN').symm)
  exact ⟨c₀, by rw [hc₀, ramp_smul, ramp_one]⟩

/-- **Factoriality of the regional algebra.**  Transporting the previous theorem through the
product GNS unitary: the regional represented von Neumann algebra is a factor. -/
theorem regionalAlgebra_hasTrivialCenter (h : SpatialFactorPremises D) :
    HasTrivialCenterSet (regionalAlgebra D) := by
  rw [← unitaryConj_image_spatial]
  exact (spatialTensorAlgebra_hasTrivialCenter D h).image D.unitaryConj

end Regional

/-! ## 4. Product vectors and the finite-pure normalized tracial state

For a *finite-dimensional* pure sector `K_pure` with orthonormal basis `e`, and a unit vector
`Ω` in the mixed sector, the functional

`φ(T) = (dim K_pure)⁻¹ ∑ᵢ ⟪eᵢ ⊗ Ω, T (eᵢ ⊗ Ω)⟫`

is the normalized `tr ⊗ τ`.  Unitality, positivity, normality (as a finite sum of vector
functionals) and traciality on elementary products are proved unconditionally; only faithfulness
uses a named separating-vector premise. -/

section ProductVectors

variable {K₁ K₂ : Type u}
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]

/-- The product vectors `vᵢ ⊗ Ω` in the Hilbert tensor product. -/
noncomputable def tvec {ι : Type*} (v : ι → K₁) (Ω : K₂) (i : ι) :
    Completion (K₁ ⊗[ℂ] K₂) := ((v i ⊗ₜ[ℂ] Ω : K₁ ⊗[ℂ] K₂) : Completion (K₁ ⊗[ℂ] K₂))

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem inner_tvec_self {ι : Type*} (v : ι → K₁) (Ω : K₂) (i : ι) :
    ⟪tvec v Ω i, tvec v Ω i⟫_ℂ = ⟪v i, v i⟫_ℂ * ⟪Ω, Ω⟫_ℂ := by
  rw [tvec, Completion.inner_coe, TensorProduct.inner_tmul]

theorem lamp_ramp_apply_tvec {ι : Type*} (v : ι → K₁) (Ω : K₂)
    (A : K₁ →L[ℂ] K₁) (B : K₂ →L[ℂ] K₂) (i : ι) :
    (lamp A * ramp B : Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂)) (tvec v Ω i)
      = ((A (v i) ⊗ₜ[ℂ] B Ω : K₁ ⊗[ℂ] K₂) : Completion (K₁ ⊗[ℂ] K₂)) := by
  show lamp A (ramp B (tvec v Ω i)) = _
  rw [tvec, ramp_coe, lamp_coe]
  rfl

theorem inner_tvec_lamp_ramp {ι : Type*} (v : ι → K₁) (Ω : K₂)
    (A : K₁ →L[ℂ] K₁) (B : K₂ →L[ℂ] K₂) (i : ι) :
    ⟪tvec v Ω i, (lamp A * ramp B : Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂))
        (tvec v Ω i)⟫_ℂ = ⟪v i, A (v i)⟫_ℂ * ⟪Ω, B Ω⟫_ℂ := by
  rw [lamp_ramp_apply_tvec, tvec, Completion.inner_coe, TensorProduct.inner_tmul]

/-- **Project-local definition (finitely-vector-normal functional).**  A functional given by a
finite sum of vector functionals; this is the concrete form of normality available here. -/
def IsFiniteVectorNormal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (phi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) : Prop :=
  ∃ (n : ℕ) (w : Fin n → H), ∀ T : H →L[ℂ] H, phi T = ∑ i, ⟪w i, T (w i)⟫_ℂ

/-- **Project-local definition (normalized tracial state on a set of operators).** -/
structure IsNormalizedTracialStateOn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : Set (H →L[ℂ] H)) (phi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) : Prop where
  /-- normality, in the finite-vector sense -/
  normal : IsFiniteVectorNormal phi
  /-- normalization -/
  unital : phi 1 = 1
  /-- positivity -/
  positive : ∀ T : H →L[ℂ] H, ∃ r : ℝ, 0 ≤ r ∧ phi (star T * T) = (r : ℂ)
  /-- traciality on `M` -/
  tracial : ∀ X ∈ M, ∀ Y ∈ M, phi (X * Y) = phi (Y * X)
  /-- faithfulness on `M` -/
  faithful : ∀ X ∈ M, phi (star X * X) = 0 → X = 0

end ProductVectors

section FinitePure

variable {K₁ K₂ : Type u}
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
  {ι : Type u} [Fintype ι] [Nonempty ι]

/-- **The normalized finite-pure functional** `(dim K_pure)⁻¹ · tr ⊗ ⟪Ω, · Ω⟫`. -/
noncomputable def finitePureTrace (e : OrthonormalBasis ι ℂ K₁) (Ω : K₂) :
    (Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂)) →ₗ[ℂ] ℂ where
  toFun T := (Fintype.card ι : ℂ)⁻¹ * ∑ i, ⟪tvec (⇑e) Ω i, T (tvec (⇑e) Ω i)⟫_ℂ
  map_add' T S := by
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Finset.sum_add_distrib]
    ring
  map_smul' c T := by
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right, ← Finset.mul_sum,
      RingHom.id_apply, smul_eq_mul]
    ring

omit [Nonempty ι] in
omit [CompleteSpace K₁] [CompleteSpace K₂] in
@[simp] theorem finitePureTrace_apply (e : OrthonormalBasis ι ℂ K₁) (Ω : K₂)
    (T : Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂)) :
    finitePureTrace e Ω T
      = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ⟪tvec (⇑e) Ω i, T (tvec (⇑e) Ω i)⟫_ℂ := rfl

theorem card_ne_zero : ((Fintype.card ι : ℂ)) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

omit [CompleteSpace K₁] [CompleteSpace K₂] in
/-- The finite-pure functional is normal in the finite-vector sense. -/
theorem finitePureTrace_isFiniteVectorNormal (e : OrthonormalBasis ι ℂ K₁) (Ω : K₂) :
    IsFiniteVectorNormal (finitePureTrace e Ω) := by
  classical
  obtain ⟨f⟩ := Fintype.truncEquivFin ι
  set c : ℂ := (((Real.sqrt (Fintype.card ι) : ℝ)) : ℂ)⁻¹ with hcdef
  have hcard : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc2 : (starRingEnd ℂ) c * c = ((Fintype.card ι : ℂ))⁻¹ := by
    have h1 : (starRingEnd ℂ) c = c := by
      rw [hcdef, map_inv₀, Complex.conj_ofReal]
    rw [h1, hcdef, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hcard.le]
    norm_num
  refine ⟨Fintype.card ι, fun j => c • tvec (⇑e) Ω (f.symm j), fun T => ?_⟩
  have hscal : ∀ j : Fin (Fintype.card ι),
      ⟪c • tvec (⇑e) Ω (f.symm j), T (c • tvec (⇑e) Ω (f.symm j))⟫_ℂ
        = ((Fintype.card ι : ℂ))⁻¹ * ⟪tvec (⇑e) Ω (f.symm j), T (tvec (⇑e) Ω (f.symm j))⟫_ℂ := by
    intro j
    rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hc2]
  rw [finitePureTrace_apply, Finset.mul_sum]
  rw [← Equiv.sum_comp f.symm
    (fun i => ((Fintype.card ι : ℂ))⁻¹ * ⟪tvec (⇑e) Ω i, T (tvec (⇑e) Ω i)⟫_ℂ)]
  exact (Finset.sum_congr rfl fun j _ => hscal j).symm

omit [CompleteSpace K₁] [CompleteSpace K₂] in
/-- **Unitality** of the finite-pure functional for a unit vector `Ω`. -/
theorem finitePureTrace_one (e : OrthonormalBasis ι ℂ K₁) {Ω : K₂} (hΩ : ‖Ω‖ = 1) :
    finitePureTrace e Ω 1 = 1 := by
  have hΩ2 : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  have hsum : ∑ _i : ι, ⟪Ω, Ω⟫_ℂ = (Fintype.card ι : ℂ) := by
    rw [Finset.sum_const, hΩ2, Finset.card_univ]
    simp
  rw [finitePureTrace_apply]
  have : ∀ i : ι, ⟪tvec (⇑e) Ω i, (1 : Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂))
      (tvec (⇑e) Ω i)⟫_ℂ = ⟪Ω, Ω⟫_ℂ := by
    intro i
    have he : ⟪e i, e i⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]; norm_num
    rw [ContinuousLinearMap.one_apply, inner_tvec_self, he, one_mul]
  rw [Finset.sum_congr rfl fun i _ => this i, hsum, inv_mul_cancel₀ card_ne_zero]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
/-- **Positivity** of the finite-pure functional. -/
theorem finitePureTrace_positive (e : OrthonormalBasis ι ℂ K₁) (Ω : K₂)
    (T : Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂)) :
    ∃ r : ℝ, 0 ≤ r ∧ finitePureTrace e Ω (star T * T) = (r : ℂ) := by
  refine ⟨(Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖T (tvec (⇑e) Ω i)‖ ^ 2, by positivity, ?_⟩
  rw [finitePureTrace_apply]
  have hterm : ∀ i : ι, ⟪tvec (⇑e) Ω i, (star T * T) (tvec (⇑e) Ω i)⟫_ℂ
      = ((‖T (tvec (⇑e) Ω i)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast
    norm_num
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  push_cast
  ring

omit [Nonempty ι] in
/-- **The elementary-product formula**: on `A ⊗ B` the functional is the normalized trace of `A`
times the mixed vector state of `B`. -/
theorem finitePureTrace_lamp_ramp (e : OrthonormalBasis ι ℂ K₁) (Ω : K₂)
    (A : K₁ →L[ℂ] K₁) (B : K₂ →L[ℂ] K₂) :
    finitePureTrace e Ω (lamp A * ramp B)
      = (Fintype.card ι : ℂ)⁻¹ * (LinearMap.trace ℂ K₁ (A : K₁ →ₗ[ℂ] K₁)) * ⟪Ω, B Ω⟫_ℂ := by
  rw [finitePureTrace_apply, LinearMap.trace_eq_sum_inner _ e]
  simp only [inner_tvec_lamp_ramp]
  rw [← Finset.sum_mul, mul_assoc]
  rfl

omit [Nonempty ι] in
/-- **Traciality on elementary products**, given traciality of the mixed vector state on the
pair `(B, B')`. -/
theorem finitePureTrace_tracial_lamp_ramp [FiniteDimensional ℂ K₁]
    (e : OrthonormalBasis ι ℂ K₁) (Ω : K₂)
    (A A' : K₁ →L[ℂ] K₁) (B B' : K₂ →L[ℂ] K₂)
    (hmix : ⟪Ω, (B * B') Ω⟫_ℂ = ⟪Ω, (B' * B) Ω⟫_ℂ) :
    finitePureTrace e Ω ((lamp A * ramp B) * (lamp A' * ramp B'))
      = finitePureTrace e Ω ((lamp A' * ramp B') * (lamp A * ramp B)) := by
  have hprod : ∀ (X X' : K₁ →L[ℂ] K₁) (Y Y' : K₂ →L[ℂ] K₂),
      (lamp X * ramp Y) * (lamp X' * ramp Y') = lamp (X * X') * ramp (Y * Y') := by
    intro X X' Y Y'
    rw [lamp_mul, ramp_mul]
    have h := lamp_ramp_commute X' Y
    calc lamp X * ramp Y * (lamp X' * ramp Y')
        = lamp X * (ramp Y * lamp X') * ramp Y' := by
          simp only [mul_assoc]
      _ = lamp X * (lamp X' * ramp Y) * ramp Y' := by rw [← h]
      _ = lamp X * lamp X' * (ramp Y * ramp Y') := by simp only [mul_assoc]
  rw [hprod, hprod, finitePureTrace_lamp_ramp, finitePureTrace_lamp_ramp, hmix]
  congr 2
  have : ((A * A' : K₁ →L[ℂ] K₁) : K₁ →ₗ[ℂ] K₁)
      = (A : K₁ →ₗ[ℂ] K₁) * (A' : K₁ →ₗ[ℂ] K₁) := rfl
  rw [this]
  have : ((A' * A : K₁ →L[ℂ] K₁) : K₁ →ₗ[ℂ] K₁)
      = (A' : K₁ →ₗ[ℂ] K₁) * (A : K₁ →ₗ[ℂ] K₁) := rfl
  rw [this, LinearMap.trace_mul_comm]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
/-- **Faithfulness** of the finite-pure functional on a set of operators for which the product
vectors are separating. -/
theorem finitePureTrace_faithful (e : OrthonormalBasis ι ℂ K₁) (Ω : K₂)
    {M : Set (Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂))}
    (hsep : ∀ T ∈ M, (∀ i, T (tvec (⇑e) Ω i) = 0) → T = 0)
    (T : Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂)) (hT : T ∈ M)
    (h0 : finitePureTrace e Ω (star T * T) = 0) : T = 0 := by
  refine hsep T hT fun i => ?_
  obtain ⟨r, hr0, hr⟩ := finitePureTrace_positive e Ω T
  have hterm : ∀ j : ι, ⟪tvec (⇑e) Ω j, (star T * T) (tvec (⇑e) Ω j)⟫_ℂ
      = ((‖T (tvec (⇑e) Ω j)‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast
    norm_num
  have hsum : ((∑ j, ‖T (tvec (⇑e) Ω j)‖ ^ 2 : ℝ) : ℂ) = 0 := by
    have h1 : (Fintype.card ι : ℂ)⁻¹ * ∑ j, ⟪tvec (⇑e) Ω j, (star T * T) (tvec (⇑e) Ω j)⟫_ℂ = 0 := h0
    rw [Finset.sum_congr rfl fun j _ => hterm j] at h1
    have h2 : ∑ j : ι, ((‖T (tvec (⇑e) Ω j)‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd (inv_eq_zero.mp h) card_ne_zero
      · exact h
    rw [← h2]
    push_cast
    ring
  have hsumR : (∑ j, ‖T (tvec (⇑e) Ω j)‖ ^ 2 : ℝ) = 0 := by
    exact_mod_cast hsum
  have hz : ‖T (tvec (⇑e) Ω i)‖ ^ 2 = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp hsumR i
      (Finset.mem_univ i)
    exact this
  have : ‖T (tvec (⇑e) Ω i)‖ = 0 := by nlinarith [norm_nonneg (T (tvec (⇑e) Ω i))]
  exact norm_eq_zero.mp this

end FinitePure


/-! ## 5. Transport of a normalized tracial state along a unitary

Conjugation by a unitary carries a normalized tracial state on a set of operators to a
normalized tracial state on the image set.  Unconditional. -/

section Transport

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- The functional transported along conjugation by a unitary `U`. -/
noncomputable def transportFunctional (U : H ≃ₗᵢ[ℂ] H') (phi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) :
    (H' →L[ℂ] H') →ₗ[ℂ] ℂ where
  toFun T := phi (U.conjStarAlgEquiv.symm T)
  map_add' T S := by simp only [map_add]
  map_smul' c T := by simp only [map_smul, RingHom.id_apply]

@[simp] theorem transportFunctional_apply (U : H ≃ₗᵢ[ℂ] H')
    (phi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (T : H' →L[ℂ] H') :
    transportFunctional U phi T = phi (U.conjStarAlgEquiv.symm T) := rfl

theorem IsFiniteVectorNormal.transport (U : H ≃ₗᵢ[ℂ] H')
    {phi : (H →L[ℂ] H) →ₗ[ℂ] ℂ} (h : IsFiniteVectorNormal phi) :
    IsFiniteVectorNormal (transportFunctional U phi) := by
  obtain ⟨n, w, hw⟩ := h
  refine ⟨n, fun i => U (w i), fun T => ?_⟩
  rw [transportFunctional_apply, hw]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : (U.conjStarAlgEquiv.symm T) (w i) = U.symm (T (U (w i))) := rfl
  rw [hz, ← U.inner_map_map (w i) (U.symm (T (U (w i)))), U.apply_symm_apply]

/-- **Transport of the normalized tracial state.** -/
theorem IsNormalizedTracialStateOn.transport (U : H ≃ₗᵢ[ℂ] H')
    {M : Set (H →L[ℂ] H)} {phi : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (h : IsNormalizedTracialStateOn M phi) :
    IsNormalizedTracialStateOn (U.conjStarAlgEquiv '' M) (transportFunctional U phi) where
  normal := h.normal.transport U
  unital := by rw [transportFunctional_apply, map_one]; exact h.unital
  positive := by
    intro T
    obtain ⟨r, hr0, hr⟩ := h.positive (U.conjStarAlgEquiv.symm T)
    exact ⟨r, hr0, by rw [transportFunctional_apply, map_mul, map_star]; exact hr⟩
  tracial := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
    simp only [transportFunctional_apply, ← map_mul, StarAlgEquiv.symm_apply_apply]
    exact h.tracial X hX Y hY
  faithful := by
    rintro _ ⟨X, hX, rfl⟩ h0
    have hstar : star (U.conjStarAlgEquiv X) = U.conjStarAlgEquiv (star X) :=
      (map_star U.conjStarAlgEquiv X).symm
    rw [transportFunctional_apply, hstar, ← map_mul, StarAlgEquiv.symm_apply_apply] at h0
    rw [h.faithful X hX h0, map_zero]

end Transport


/-! ## 6. The finite-pure case: a normalized tracial state on the regional algebra

Assembling Section 4 and Section 5.  The unconditional content is: normality (as a finite sum of
vector functionals), unitality, positivity, the elementary-product formula
`φ(A ⊗ B) = (dim K_pure)⁻¹ tr(A) ⟪Ω, B Ω⟫`, and traciality on elementary products.  Two analytic
inputs remain, and they are stated as explicit named premises (never as axioms):

* `tracial`, that traciality — proved here on the elementary products generating the algebra —
  persists on the whole weak closure.  This is the exact analogue of P58's
  `MixedWeakClosurePremises.tracial`; deducing it from the generator case requires normality of
  `φ` in the σ-weak sense together with a Kaplansky density argument, neither of which is
  available in pinned Mathlib.
* `separating`, that the product vectors `eᵢ ⊗ Ω` are separating for the algebra; this is the
  standard consequence of `Ω` being separating for the mixed factor. -/

section FinitePureRegional

open AristotleCandidates.ProductGNSTensor

variable (D : ProductGNSData.{u}) {ι : Type u} [Fintype ι] [Nonempty ι]

/-- **The auxiliary premises for the finite-pure trace.**  See the section docstring. -/
structure FinitePureTracePremises (e : OrthonormalBasis ι ℂ D.PureGNS) (Ω : D.MixedGNS) :
    Prop where
  /-- the mixed cyclic vector is a unit vector -/
  mixed_unit : ‖Ω‖ = 1
  /-- traciality persists from the elementary products to the whole spatial algebra -/
  tracial : ∀ X ∈ D.spatialTensorAlgebra, ∀ Y ∈ D.spatialTensorAlgebra,
    finitePureTrace e Ω (X * Y) = finitePureTrace e Ω (Y * X)
  /-- the product vectors are separating for the spatial algebra -/
  separating : ∀ T ∈ D.spatialTensorAlgebra, (∀ i, T (tvec (⇑e) Ω i) = 0) → T = 0

/-- **Finite-pure case, spatial form.**  The normalized functional
`(dim K_pure)⁻¹ · tr ⊗ ⟪Ω, · Ω⟫` is a normal, unital, positive, tracial and faithful state on
the spatial tensor product `B(K_pure) ⊗̄ R_mixed`. -/
theorem spatialTensorAlgebra_isNormalizedTracialState
    (e : OrthonormalBasis ι ℂ D.PureGNS) (Ω : D.MixedGNS)
    (h : FinitePureTracePremises D e Ω) :
    IsNormalizedTracialStateOn D.spatialTensorAlgebra (finitePureTrace e Ω) where
  normal := finitePureTrace_isFiniteVectorNormal e Ω
  unital := finitePureTrace_one e h.mixed_unit
  positive := finitePureTrace_positive e Ω
  tracial := h.tracial
  faithful := fun X hX h0 => finitePureTrace_faithful e Ω h.separating X hX h0

/-- **Finite-pure case, regional form.**  Transporting the previous theorem through the product
GNS unitary yields a normalized tracial state on the regional represented von Neumann algebra:
in the finite-pure case the local-hyperbolic algebra is a *finite* factor. -/
theorem regionalAlgebra_isNormalizedTracialState
    (e : OrthonormalBasis ι ℂ D.PureGNS) (Ω : D.MixedGNS)
    (h : FinitePureTracePremises D e Ω) :
    IsNormalizedTracialStateOn (regionalAlgebra D)
      (transportFunctional D.productGNSUnitary (finitePureTrace e Ω)) := by
  have hmain := (spatialTensorAlgebra_isNormalizedTracialState D e Ω h).transport
    D.productGNSUnitary
  have himg : D.productGNSUnitary.conjStarAlgEquiv '' D.spatialTensorAlgebra
      = regionalAlgebra D := unitaryConj_image_spatial D
  rwa [himg] at hmain

end FinitePureRegional


/-! ## 7. Weights defined by families of vectors

For the infinite-pure case the natural functional is an **unnormalizable weight**, taking values
in `ℝ≥0∞`.  We develop it for an arbitrary family of vectors: this is checked infrastructure,
with no premise. -/

section VectorWeight

variable {H H' : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- The `ℝ≥0∞`-valued weight `T ↦ ∑ⱼ ⟪vⱼ, T vⱼ⟫` attached to a family of vectors. -/
noncomputable def vectorWeight {J : Type u} (v : J → H) (T : H →L[ℂ] H) : ENNReal :=
  ∑' j, ENNReal.ofReal ((⟪v j, T (v j)⟫_ℂ).re)

theorem re_inner_nonneg_of_isPositive {T : H →L[ℂ] H} (hT : T.IsPositive) (x : H) :
    0 ≤ (⟪x, T x⟫_ℂ).re := by
  have h := (ContinuousLinearMap.isPositive_iff' T).mp hT |>.2 x
  have hre : (0 : ℝ) ≤ (⟪T x, x⟫_ℂ).re := by
    simpa using (Complex.le_def.mp h).1
  have hconj : ⟪x, T x⟫_ℂ = (starRingEnd ℂ) ⟪T x, x⟫_ℂ := (inner_conj_symm _ _).symm
  rw [hconj, Complex.conj_re]
  exact hre

/-- Additivity of the weight on positive operators. -/
theorem vectorWeight_add {J : Type u} (v : J → H) {S T : H →L[ℂ] H}
    (hS : S.IsPositive) (hT : T.IsPositive) :
    vectorWeight v (S + T) = vectorWeight v S + vectorWeight v T := by
  unfold vectorWeight
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun j => ?_
  rw [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re,
    ENNReal.ofReal_add (re_inner_nonneg_of_isPositive hS _) (re_inner_nonneg_of_isPositive hT _)]

omit [CompleteSpace H] in
/-- Positive homogeneity of the weight. -/
theorem vectorWeight_smul {J : Type u} (v : J → H) {c : ℝ} (hc : 0 ≤ c) (T : H →L[ℂ] H) :
    vectorWeight v ((c : ℂ) • T) = ENNReal.ofReal c * vectorWeight v T := by
  unfold vectorWeight
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, ENNReal.ofReal_mul hc]

/-- The weight of `T* T` is the sum of the squared norms `‖T vⱼ‖²`. -/
theorem vectorWeight_star_mul_self {J : Type u} (v : J → H) (T : H →L[ℂ] H) :
    vectorWeight v (star T * T) = ∑' j, ENNReal.ofReal (‖T (v j)‖ ^ 2) := by
  refine tsum_congr fun j => ?_
  congr 1
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- If the weight of `T* T` vanishes then `T` kills every vector of the family. -/
theorem vectorWeight_apply_eq_zero {J : Type u} (v : J → H) (T : H →L[ℂ] H)
    (h : vectorWeight v (star T * T) = 0) (j : J) : T (v j) = 0 := by
  rw [vectorWeight_star_mul_self] at h
  have hj : ENNReal.ofReal (‖T (v j)‖ ^ 2) = 0 := by
    have := ENNReal.tsum_eq_zero.mp h
    exact this j
  have h2 : ‖T (v j)‖ ^ 2 ≤ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using hj
  have : ‖T (v j)‖ = 0 := by nlinarith [norm_nonneg (T (v j))]
  exact norm_eq_zero.mp this

omit [CompleteSpace H] in
/-- The weight of the identity is the sum of the squared norms of the family. -/
theorem vectorWeight_one {J : Type u} (v : J → H) :
    vectorWeight v 1 = ∑' j, ENNReal.ofReal (‖v j‖ ^ 2) := by
  refine tsum_congr fun j => ?_
  congr 1
  rw [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
  norm_cast

omit [CompleteSpace H] in
/-- **The infinite-pure weight is not a state**: for an infinite family of unit vectors the
weight of the identity is `∞`. -/
theorem vectorWeight_one_eq_top {J : Type u} [Infinite J] (v : J → H)
    (hv : ∀ j, ‖v j‖ = 1) : vectorWeight v 1 = ⊤ := by
  rw [vectorWeight_one]
  have : ∀ j, ENNReal.ofReal (‖v j‖ ^ 2) = 1 := by
    intro j; rw [hv j]; norm_num
  rw [tsum_congr this]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- The weight transported along conjugation by a unitary. -/
noncomputable def transportWeight (U : H ≃ₗᵢ[ℂ] H') (W : (H →L[ℂ] H) → ENNReal)
    (T : H' →L[ℂ] H') : ENNReal := W (U.conjStarAlgEquiv.symm T)

theorem transportWeight_vectorWeight {J : Type u} (U : H ≃ₗᵢ[ℂ] H') (v : J → H) :
    transportWeight U (vectorWeight v) = vectorWeight (fun j => U (v j)) := by
  funext T
  refine tsum_congr fun j => ?_
  congr 2
  have hz : (U.conjStarAlgEquiv.symm T) (v j) = U.symm (T (U (v j))) := rfl
  rw [hz, ← U.inner_map_map (v j) (U.symm (T (U (v j)))), U.apply_symm_apply]

end VectorWeight


/-! ## 8. Faithful normal semifinite weights and their transport

`IsFaithfulNormalSemifiniteWeightOn M W` is the project-local notion used in the infinite-pure
case.  It is deliberately **not** a state: `W` takes values in `ℝ≥0∞`, is only additive and
positively homogeneous on the positive cone, and its value on `1` is allowed to be `∞` (and in
the intended infinite-pure model it *is* `∞`, see `vectorWeight_one_eq_top`). -/

section WeightStructure

variable {H H' : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- **Project-local definition (faithful normal semifinite trace-weight).** -/
structure IsFaithfulNormalSemifiniteWeightOn (M : Set (H →L[ℂ] H))
    (W : (H →L[ℂ] H) → ENNReal) : Prop where
  /-- normality, in the concrete form: `W` is a (possibly infinite) sum of vector functionals -/
  normal : ∃ (J : Type u) (v : J → H), W = vectorWeight v
  /-- additivity on the positive cone -/
  additive : ∀ S T : H →L[ℂ] H, S.IsPositive → T.IsPositive → W (S + T) = W S + W T
  /-- positive homogeneity -/
  homogeneous : ∀ c : ℝ, 0 ≤ c → ∀ T : H →L[ℂ] H, W ((c : ℂ) • T) = ENNReal.ofReal c * W T
  /-- faithfulness on `M` -/
  faithful : ∀ T ∈ M, W (star T * T) = 0 → T = 0
  /-- semifiniteness: every nonzero positive element of `M` dominates a nonzero positive element
  of `M` of finite weight -/
  semifinite : ∀ T ∈ M, T.IsPositive → T ≠ 0 →
    ∃ S ∈ M, S.IsPositive ∧ S ≠ 0 ∧ S ≤ T ∧ W S ≠ ⊤
  /-- traciality on `M` -/
  tracial : ∀ T ∈ M, W (star T * T) = W (T * star T)

theorem isPositive_conjStarAlgEquiv_symm (U : H ≃ₗᵢ[ℂ] H') {T : H' →L[ℂ] H'}
    (hT : T.IsPositive) : (U.conjStarAlgEquiv.symm T).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff'] at hT ⊢
  refine ⟨?_, fun x => ?_⟩
  · have hstar : star (U.conjStarAlgEquiv.symm T) = U.conjStarAlgEquiv.symm (star T) :=
      (map_star U.conjStarAlgEquiv.symm T).symm
    show star (U.conjStarAlgEquiv.symm T) = _
    rw [hstar, hT.1]
  · have hx : (U.conjStarAlgEquiv.symm T) x = U.symm (T (U x)) := rfl
    rw [hx, ← U.inner_map_map (U.symm (T (U x))) x, U.apply_symm_apply]
    exact hT.2 (U x)

theorem isPositive_conjStarAlgEquiv (U : H ≃ₗᵢ[ℂ] H') {T : H →L[ℂ] H}
    (hT : T.IsPositive) : (U.conjStarAlgEquiv T).IsPositive :=
  isPositive_conjStarAlgEquiv_symm U.symm hT

theorem le_conjStarAlgEquiv (U : H ≃ₗᵢ[ℂ] H') {S T : H →L[ℂ] H} (h : S ≤ T) :
    U.conjStarAlgEquiv S ≤ U.conjStarAlgEquiv T := by
  rw [← sub_nonneg] at h ⊢
  rw [← map_sub, ContinuousLinearMap.nonneg_iff_isPositive]
  exact isPositive_conjStarAlgEquiv U (ContinuousLinearMap.nonneg_iff_isPositive _ |>.mp h)

theorem le_conjStarAlgEquiv_symm (U : H ≃ₗᵢ[ℂ] H') {S T : H' →L[ℂ] H'} (h : S ≤ T) :
    U.conjStarAlgEquiv.symm S ≤ U.conjStarAlgEquiv.symm T :=
  le_conjStarAlgEquiv U.symm h

/-- **Transport of a faithful normal semifinite weight along a unitary.** -/
theorem IsFaithfulNormalSemifiniteWeightOn.transport (U : H ≃ₗᵢ[ℂ] H')
    {M : Set (H →L[ℂ] H)} {W : (H →L[ℂ] H) → ENNReal}
    (h : IsFaithfulNormalSemifiniteWeightOn M W) :
    IsFaithfulNormalSemifiniteWeightOn (U.conjStarAlgEquiv '' M) (transportWeight U W) where
  normal := by
    obtain ⟨J, v, rfl⟩ := h.normal
    exact ⟨J, fun j => U (v j), transportWeight_vectorWeight U v⟩
  additive := by
    intro S T hS hT
    show W (U.conjStarAlgEquiv.symm (S + T)) = W _ + W _
    rw [map_add]
    exact h.additive _ _ (isPositive_conjStarAlgEquiv_symm U hS)
      (isPositive_conjStarAlgEquiv_symm U hT)
  homogeneous := by
    intro c hc T
    show W (U.conjStarAlgEquiv.symm ((c : ℂ) • T)) = _
    rw [map_smul]
    exact h.homogeneous c hc _
  faithful := by
    rintro _ ⟨X, hX, rfl⟩ h0
    have hstar : star (U.conjStarAlgEquiv X) = U.conjStarAlgEquiv (star X) :=
      (map_star U.conjStarAlgEquiv X).symm
    have h1 : W (star X * X) = 0 := by
      have : transportWeight U W (star (U.conjStarAlgEquiv X) * U.conjStarAlgEquiv X)
          = W (star X * X) := by
        show W (U.conjStarAlgEquiv.symm _) = _
        rw [hstar, ← map_mul, StarAlgEquiv.symm_apply_apply]
      rw [← this]; exact h0
    rw [h.faithful X hX h1, map_zero]
  semifinite := by
    rintro _ ⟨X, hX, rfl⟩ hpos hne
    have hXpos : X.IsPositive := by
      have := isPositive_conjStarAlgEquiv_symm U hpos
      rwa [StarAlgEquiv.symm_apply_apply] at this
    have hXne : X ≠ 0 := fun h => hne (by rw [h, map_zero])
    obtain ⟨S, hSM, hSpos, hSne, hSle, hSfin⟩ := h.semifinite X hX hXpos hXne
    refine ⟨U.conjStarAlgEquiv S, ⟨S, hSM, rfl⟩, isPositive_conjStarAlgEquiv U hSpos,
      fun hz => hSne ?_, le_conjStarAlgEquiv U hSle, ?_⟩
    · have := congrArg U.conjStarAlgEquiv.symm hz
      rwa [StarAlgEquiv.symm_apply_apply, map_zero] at this
    · show W (U.conjStarAlgEquiv.symm (U.conjStarAlgEquiv S)) ≠ ⊤
      rwa [StarAlgEquiv.symm_apply_apply]
  tracial := by
    rintro _ ⟨X, hX, rfl⟩
    have hstar : star (U.conjStarAlgEquiv X) = U.conjStarAlgEquiv (star X) :=
      (map_star U.conjStarAlgEquiv X).symm
    show W (U.conjStarAlgEquiv.symm _) = W (U.conjStarAlgEquiv.symm _)
    rw [hstar, ← map_mul, ← map_mul, StarAlgEquiv.symm_apply_apply,
      StarAlgEquiv.symm_apply_apply]
    exact h.tracial X hX

end WeightStructure


/-! ## 9. The infinite-pure case: a faithful normal semifinite weight

When the pure sector is infinite-dimensional the type I factor `B(K_pure)` is infinite and no
tracial *state* exists.  The canonical operator trace of `B(K_pure)`, tensored with the mixed
vector trace, is the `ℝ≥0∞`-valued weight `vectorWeight (tvec e Ω)`.  It is **not** a state:
`W 1 = ∞` (`regionalAlgebra_weight_one_eq_top`).

Unconditional here: normality, additivity on the positive cone, positive homogeneity, the value
`∞` on the identity, faithfulness from a separating family, and the transport to the regional
algebra.  Two analytic inputs are named premises: semifiniteness and traciality of the weight on
the whole weak closure. -/

section InfinitePureWeight

variable {K₁ K₂ : Type u}
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
  {ι : Type u}

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem norm_tvec (v : ι → K₁) (Ω : K₂) (i : ι) : ‖tvec v Ω i‖ = ‖v i‖ * ‖Ω‖ := by
  rw [tvec, Completion.norm_coe, TensorProduct.norm_tmul]

/-- **The infinite-pure weight**: the canonical operator trace of `B(K_pure)` tensored with the
mixed vector state, realized as the vector weight of the product vectors `eᵢ ⊗ Ω`. -/
noncomputable def infinitePureWeight (v : ι → K₁) (Ω : K₂) :
    (Completion (K₁ ⊗[ℂ] K₂) →L[ℂ] Completion (K₁ ⊗[ℂ] K₂)) → ENNReal :=
  vectorWeight (tvec v Ω)

omit [CompleteSpace K₁] [CompleteSpace K₂] in
theorem infinitePureWeight_one_eq_top [Infinite ι] (e : HilbertBasis ι ℂ K₁) {Ω : K₂}
    (hΩ : ‖Ω‖ = 1) : infinitePureWeight (⇑e) Ω 1 = ⊤ :=
  vectorWeight_one_eq_top _ fun i => by
    rw [norm_tvec, hΩ, mul_one, e.orthonormal.1 i]

end InfinitePureWeight

section InfinitePureRegional

open AristotleCandidates.ProductGNSTensor

variable (D : ProductGNSData.{u}) {ι : Type u}

/-- **The auxiliary premises for the infinite-pure weight.**  Semifiniteness and traciality on
the weak closure are the two analytic inputs; they are stated as explicit named premises, never
as axioms. -/
structure InfinitePureWeightPremises (e : HilbertBasis ι ℂ D.PureGNS) (Ω : D.MixedGNS) :
    Prop where
  /-- the mixed cyclic vector is a unit vector -/
  mixed_unit : ‖Ω‖ = 1
  /-- the product vectors are separating for the spatial algebra -/
  separating : ∀ T ∈ D.spatialTensorAlgebra, (∀ i, T (tvec (⇑e) Ω i) = 0) → T = 0
  /-- semifiniteness of the weight on the spatial algebra -/
  semifinite : ∀ T ∈ D.spatialTensorAlgebra, T.IsPositive → T ≠ 0 →
    ∃ S ∈ D.spatialTensorAlgebra, S.IsPositive ∧ S ≠ 0 ∧ S ≤ T ∧
      infinitePureWeight (⇑e) Ω S ≠ ⊤
  /-- traciality of the weight on the spatial algebra -/
  tracial : ∀ T ∈ D.spatialTensorAlgebra,
    infinitePureWeight (⇑e) Ω (star T * T) = infinitePureWeight (⇑e) Ω (T * star T)

/-- **Infinite-pure case, spatial form.**  The weight `tr ⊗ ⟪Ω, · Ω⟫` is a faithful normal
semifinite trace-weight on `B(K_pure) ⊗̄ R_mixed`. -/
theorem spatialTensorAlgebra_isFaithfulNormalSemifiniteWeight
    (e : HilbertBasis ι ℂ D.PureGNS) (Ω : D.MixedGNS)
    (h : InfinitePureWeightPremises D e Ω) :
    IsFaithfulNormalSemifiniteWeightOn D.spatialTensorAlgebra
      (infinitePureWeight (⇑e) Ω) where
  normal := ⟨ι, tvec (⇑e) Ω, rfl⟩
  additive := fun _ _ hS hT => vectorWeight_add _ hS hT
  homogeneous := fun _ hc T => vectorWeight_smul _ hc T
  faithful := fun T hT h0 =>
    h.separating T hT fun i => vectorWeight_apply_eq_zero _ T h0 i
  semifinite := h.semifinite
  tracial := h.tracial

/-- **Infinite-pure case, regional form.**  Transport through the product GNS unitary: the
regional represented von Neumann algebra carries a faithful normal semifinite trace-weight. -/
theorem regionalAlgebra_isFaithfulNormalSemifiniteWeight
    (e : HilbertBasis ι ℂ D.PureGNS) (Ω : D.MixedGNS)
    (h : InfinitePureWeightPremises D e Ω) :
    IsFaithfulNormalSemifiniteWeightOn (regionalAlgebra D)
      (transportWeight D.productGNSUnitary (infinitePureWeight (⇑e) Ω)) := by
  have hmain := (spatialTensorAlgebra_isFaithfulNormalSemifiniteWeight D e Ω h).transport
    D.productGNSUnitary
  have himg : D.productGNSUnitary.conjStarAlgEquiv '' D.spatialTensorAlgebra
      = regionalAlgebra D := unitaryConj_image_spatial D
  rwa [himg] at hmain

/-- **The infinite-pure weight is not a state.**  Its value on the identity operator is `∞`,
both spatially and after transport to the regional algebra. -/
theorem regionalAlgebra_weight_one_eq_top [Infinite ι]
    (e : HilbertBasis ι ℂ D.PureGNS) (Ω : D.MixedGNS)
    (hΩ : ‖Ω‖ = 1) :
    transportWeight D.productGNSUnitary (infinitePureWeight (⇑e) Ω) 1 = ⊤ := by
  show infinitePureWeight (⇑e) Ω (D.productGNSUnitary.conjStarAlgEquiv.symm 1) = ⊤
  rw [map_one]
  exact infinitePureWeight_one_eq_top e hΩ

end InfinitePureRegional


/-! ## 10. The bundled spatial `⋆`-isomorphism

Section 3 identified the regional algebra with the spatial tensor product as *sets* of operators.
Here the identification is packaged as a `⋆`-algebra isomorphism of `⋆`-subalgebras

`B(K_pure) ⊗̄ R_mixed  ≃⋆ₐ[ℂ]  π_ω̃(A_Γ)''`,

implemented by conjugation with the product GNS unitary.  Unconditional. -/

section SpatialIso

open AristotleCandidates.ProductGNSTensor

variable (D : ProductGNSData.{u})

theorem star_generatorSet_subset :
    star (D.pureFactorSet ∪ D.mixedFactorSet) ⊆ D.pureFactorSet ∪ D.mixedFactorSet := by
  intro T hT
  have hT' : star T ∈ D.pureFactorSet ∪ D.mixedFactorSet := hT
  rcases hT' with h | h
  · rw [pureFactorSet_eq] at h
    obtain ⟨a, ha⟩ := h
    refine Or.inl ?_
    rw [pureFactorSet_eq]
    refine ⟨star a, ?_⟩
    have hstar : pureAmp D (star a) = star (pureAmp D a) := by
      rw [pureAmp, pureAmp, map_star, ← lamp_star]
    rw [hstar, ha]
    exact star_star T
  · rw [mixedFactorSet_eq] at h
    obtain ⟨b, hb⟩ := h
    refine Or.inr ?_
    rw [mixedFactorSet_eq]
    refine ⟨star b, ?_⟩
    have hstar : mixedAmp D (star b) = star (mixedAmp D b) := by
      rw [mixedAmp, mixedAmp, map_star, ← ramp_star]
    rw [hstar, hb]
    exact star_star T

theorem star_range_totalRep_subset :
    star (Set.range D.totalRep) ⊆ Set.range D.totalRep := by
  intro T hT
  obtain ⟨a, ha⟩ : ∃ a, D.totalRep a = star T := hT
  exact ⟨star a, by rw [map_star, ha, star_star]⟩

/-- The spatial tensor product `B(K_pure) ⊗̄ R_mixed`, packaged as a `⋆`-subalgebra. -/
noncomputable def spatialSubalgebra : StarSubalgebra ℂ (D.TensorGNS →L[ℂ] D.TensorGNS) :=
  StarSubalgebra.centralizer ℂ
    ((StarSubalgebra.centralizer ℂ (D.pureFactorSet ∪ D.mixedFactorSet) :
      StarSubalgebra ℂ (D.TensorGNS →L[ℂ] D.TensorGNS)) : Set (D.TensorGNS →L[ℂ] D.TensorGNS))

/-- The regional represented von Neumann algebra, packaged as a `⋆`-subalgebra. -/
noncomputable def regionalSubalgebra : StarSubalgebra ℂ (D.TotalGNS →L[ℂ] D.TotalGNS) :=
  StarSubalgebra.centralizer ℂ
    ((StarSubalgebra.centralizer ℂ (Set.range D.totalRep) :
      StarSubalgebra ℂ (D.TotalGNS →L[ℂ] D.TotalGNS)) : Set (D.TotalGNS →L[ℂ] D.TotalGNS))

@[simp] theorem coe_spatialSubalgebra :
    (spatialSubalgebra D : Set (D.TensorGNS →L[ℂ] D.TensorGNS)) = D.spatialTensorAlgebra := by
  rw [spatialSubalgebra, StarSubalgebra.coe_centralizer_centralizer,
    Set.union_eq_self_of_subset_right (star_generatorSet_subset D)]
  rfl

@[simp] theorem coe_regionalSubalgebra :
    (regionalSubalgebra D : Set (D.TotalGNS →L[ℂ] D.TotalGNS)) = regionalAlgebra D := by
  rw [regionalSubalgebra, StarSubalgebra.coe_centralizer_centralizer,
    Set.union_eq_self_of_subset_right (star_range_totalRep_subset D)]
  rfl

theorem mem_spatialSubalgebra_iff (T : D.TensorGNS →L[ℂ] D.TensorGNS) :
    T ∈ spatialSubalgebra D ↔ D.unitaryConj T ∈ regionalSubalgebra D := by
  have himg : D.unitaryConj '' D.spatialTensorAlgebra = regionalAlgebra D :=
    unitaryConj_image_spatial D
  constructor
  · intro hT
    have h1 : T ∈ D.spatialTensorAlgebra := by rwa [← SetLike.mem_coe, coe_spatialSubalgebra] at hT
    have : D.unitaryConj T ∈ regionalAlgebra D := himg ▸ ⟨T, h1, rfl⟩
    rwa [← SetLike.mem_coe, coe_regionalSubalgebra]
  · intro hT
    have h1 : D.unitaryConj T ∈ regionalAlgebra D := by
      rwa [← SetLike.mem_coe, coe_regionalSubalgebra] at hT
    rw [← himg] at h1
    obtain ⟨S, hS, hST⟩ := h1
    have : S = T := D.unitaryConj.injective hST
    rw [← SetLike.mem_coe, coe_spatialSubalgebra]
    exact this ▸ hS

/-- **The spatial `⋆`-isomorphism.**  Conjugation by the product GNS unitary is a
`⋆`-algebra isomorphism from the spatial tensor product `B(K_pure) ⊗̄ R_mixed` onto the regional
represented von Neumann algebra `π_ω̃(A_Γ)''`. -/
noncomputable def spatialRegionalStarEquiv :
    spatialSubalgebra D ≃⋆ₐ[ℂ] regionalSubalgebra D :=
  restrictStarAlgEquiv D.unitaryConj (spatialSubalgebra D) (regionalSubalgebra D)
    (mem_spatialSubalgebra_iff D)

@[simp] theorem spatialRegionalStarEquiv_apply (T : spatialSubalgebra D) :
    (spatialRegionalStarEquiv D T : D.TotalGNS →L[ℂ] D.TotalGNS)
      = D.unitaryConj (T : D.TensorGNS →L[ℂ] D.TensorGNS) := rfl

end SpatialIso

end LocalHyperbolicFactorTrace
end AristotleCandidates
