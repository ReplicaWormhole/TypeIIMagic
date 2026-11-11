import Mathlib
import AristotleCandidates.UHFReferenceRepresentation
import AristotleCandidates.RegionalProductStateIdentity
import AristotleCandidates.VacuumRestrictedInfiniteTensorProduct
import AristotleCandidates.GNSCommutantConjugation
import AristotleCandidates.BicommutantVonNeumannCore
import AristotleCandidates.VonNeumannBicommutantTheorem

/-!
# P57 — product GNS tensor factorization

**Context declaration.**  Source basis: `main.tex:1945-1985`.  Package `P57`, Lane `H`.
Predecessors `P54` (`UHFReferenceRepresentation`), `P56R` (`RegionalProductStateIdentity`) and
`P57A` (`VacuumRestrictedInfiniteTensorProduct`), together with the checked GNS/bicommutant
transport modules `GNSCommutantConjugation`, `BicommutantVonNeumannCore` and
`VonNeumannBicommutantTheorem`, are imported.

The manuscript step formalized here is the passage

* `H_ω̃ = K ⊗ K'` (the GNS Hilbert space of a product state splits as a Hilbert tensor product of
  the GNS spaces of the two factor states), and
* `π_ω̃(P_I)'' = (represented pure factor) ⊗̄ (represented mixed factor)` (the represented regional
  algebra is the spatial tensor product of the two represented factor algebras).

## Data and auxiliary assumptions

Everything is developed for the explicit bundle `ProductGNSData`, whose fields list *all*
auxiliary premises used anywhere in this file:

* two unital `⋆`-homomorphisms `pureEmb : Pure →⋆ₐ[ℂ] Total` and `mixedEmb : Mixed →⋆ₐ[ℂ] Total`
  of C⋆-algebras;
* positive linear functionals `pureState`, `mixedState`, `totalState`;
* `commuting` — the two embedded factors commute elementwise;
* `product` — `totalState (ι₁ a · ι₂ b) = pureState a · mixedState b`;
* `state_norm_le` — `totalState` is norm-decreasing (automatic for a state on a unital
  C⋆-algebra, but assumed here as an explicit premise rather than re-derived);
* `span_dense` — the linear span of the elementary products `ι₁ a · ι₂ b` is norm dense in
  `Total`.

No further hypothesis, interface, axiom, or completion assumption is introduced anywhere: there
are **no** `axiom`, `sorry`, `opaque`, `unsafe` or `implemented_by` declarations in this file, and
no supplied (unproved) spatial von Neumann closure facts.

## Classification of the results

**(1) Checked infrastructure constructed in this packet.**

* `clmExtend`, `extendOfBound`, `coeCLM`, `norm_clmExtend_le` — extension of bounded maps to
  completions (needed because `LinearMap.mkContinuous` does not elaborate directly out of
  `PositiveLinearMap.PreGNS` into operator-valued codomains).
* `prodElt`, `prodElt_mul`, `prodElt_star_mul`, `totalState_prodElt_inner`, `preInner_prodElt`,
  `norm_prodElt` — the algebra of elementary product elements and the factorization of the GNS
  inner product on them.
* `prodCLM`, `inner_prodCLM` — the bilinear product map `K_pure × K_mixed → H_ω̃`, with the
  exact inner-product factorization `⟪x ⊗ y, x' ⊗ y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫`.
* `tensorLiftₗ`, `norm_tensorLiftₗ`, `tensorLiftIsometry`, `tensorUnitaryCLM` — the induced
  isometry of the algebraic tensor product `TensorPre = K_pure ⊗[ℂ] K_mixed` and of its
  completion `TensorGNS`.
* `totalCoe`, `denseRange_tensorUnitaryCLM`, `surjective_tensorUnitaryCLM`.
* `tensorMapₗ`, `norm_tensorMapₗ_le`, `tensorOp`, `tensorOpC` — the elementary tensor operators
  `π₁(a) ⊗ π₂(b)`; their boundedness is *derived* from the intertwining identity and the
  isometry property, since pinned Mathlib has no general bound `‖T ⊗ S‖ ≤ ‖T‖ ‖S‖` on an
  algebraic tensor product of inner-product spaces.

**(2) Theorems recovered in the manuscript's intended form (for `ProductGNSData`).**

* `productGNSUnitary : TensorGNS ≃ₗᵢ[ℂ] TotalGNS` — the canonical GNS unitary
  `K_pure ⊗ K_mixed ≅ H_ω̃`; this is the manuscript's `H_ω̃ = K ⊗ K'`.
* `prodCLM_intertwine_coe` (intertwining on the dense subspace of classes of algebra elements,
  i.e. on finite words) and `prodCLM_intertwine`, `tensorUnitaryCLM_tensorOpC` (intertwining
  everywhere, by continuity).
* `unitaryConj_tensorOpC` — conjugation by the unitary maps `π₁(a) ⊗ π₂(b)` to
  `π_ω̃(ι₁ a · ι₂ b)`.
* `centralizer_representedProductSet` — the elementary product operators and the whole
  represented algebra have the same commutant.
* `bicommutant_elementary_eq_spatial` — the bicommutant of the elementary tensor operators equals
  `spatialTensorAlgebra`, the spatial von Neumann tensor product of the two represented factor
  algebras, defined as usual as `({π₁(a) ⊗ 1} ∪ {1 ⊗ π₂(b)})''`.
* `unitaryConj_image_spatialTensorAlgebra` — the manuscript's algebra identification:
  `U (M_pure ⊗̄ M_mixed) U⋆ = π_ω̃(Total)''`.

* `idPositive`, `trivialProductGNSData` and the resulting `Nonempty ProductGNSData` instance — a
  non-vacuity witness showing that the fields of `ProductGNSData` are jointly satisfiable (the
  witness is the trivial one on `ℂ`; it only certifies non-vacuity of the hypotheses).

**(3) Conditional statements.**  None beyond the explicit fields of `ProductGNSData` listed
above; in particular the density premise `span_dense` and the contractivity premise
`state_norm_le` are used and are stated as fields.

**(4) Source / Mathlib obstructions still open.**

* Pinned Mathlib has no von Neumann *spatial tensor product* `M ⊗̄ N` of two von Neumann algebras
  acting on Hilbert spaces `H`, `K`: there is no `VonNeumannAlgebra` tensor construction, no
  commutation theorem `(M ⊗̄ N)' = M' ⊗̄ N'`, and no `(M ⊗ 1)' = M' ⊗̄ B(K)`.  We therefore *define*
  the spatial tensor product concretely as the bicommutant
  `({π₁(a) ⊗ 1} ∪ {1 ⊗ π₂(b)})''` (`spatialTensorAlgebra`), which is the standard definition, and
  prove the identification for it.  What is *not* available is the further theory of that object
  (commutation theorem, slice maps, normal product extensions).
* Pinned Mathlib has no bound `‖T ⊗ S‖ ≤ ‖T‖ ‖S‖` for general bounded `T`, `S` on the algebraic
  tensor product of inner-product spaces (only `TensorProduct.mapIsometry` for isometries).  The
  boundedness needed here is obtained instead from the constructed intertwining identity.
* Pinned Mathlib has no inner product on `PiTensorProduct`, so an *infinite* tensor product of
  Hilbert spaces has to be built by hand; that is why the split here is stated for a two-factor
  product state, exactly as the manuscript's `K ⊗ K'`.

**Forbidden downstream claims are not made.**  Nothing here asserts that either factor is a
factor, no mixed-factor classification, no regional factorhood, and no trace or weight dichotomy;
`B(K)` is never claimed to be the represented pure factor (that would need irreducibility of the
pure-state representation, which is not part of this packet).
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open scoped InnerProductSpace ComplexOrder TensorProduct
open UniformSpace

namespace AristotleCandidates
namespace ProductGNSTensor

universe u

/-! ## 0. Two pieces of completion infrastructure -/

section Completions

variable {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Extension of a continuous linear map to the completion of its domain, when the codomain is
already complete. -/
noncomputable def clmExtend (f : X →L[ℂ] Y) : Completion X →L[ℂ] Y where
  toFun := Completion.extension f
  map_add' x y := by
    induction x, y using Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq (Completion.continuous_extension.comp continuous_add)
        (Continuous.add (Completion.continuous_extension.comp continuous_fst)
          (Completion.continuous_extension.comp continuous_snd))
    | ih a b =>
      rw [← Completion.coe_add, Completion.extension_coe f.uniformContinuous,
        Completion.extension_coe f.uniformContinuous, Completion.extension_coe f.uniformContinuous,
        map_add]
  map_smul' c x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (Completion.continuous_extension.comp (continuous_const_smul c))
        ((continuous_const_smul (c : ℂ)).comp Completion.continuous_extension)
    | ih a =>
      rw [← Completion.coe_smul, Completion.extension_coe f.uniformContinuous,
        Completion.extension_coe f.uniformContinuous, RingHom.id_apply, f.map_smul]
  cont := Completion.continuous_extension

@[simp] theorem clmExtend_coe (f : X →L[ℂ] Y) (a : X) : clmExtend f (a : Completion X) = f a :=
  Completion.extension_coe f.uniformContinuous a

/-- The canonical inclusion of a seminormed complex vector space into its completion, as a
continuous linear map. -/
noncomputable def coeCLM (X : Type*) [SeminormedAddCommGroup X] [NormedSpace ℂ X] :
    X →L[ℂ] Completion X where
  toFun x := (x : Completion X)
  map_add' x y := Completion.coe_add x y
  map_smul' r x := Completion.coe_smul r x
  cont := Completion.continuous_coe X

@[simp] theorem coeCLM_apply (X : Type*) [SeminormedAddCommGroup X] [NormedSpace ℂ X] (x : X) :
    coeCLM X x = (x : Completion X) := rfl

/-- Extension to the completion of a bounded additive and `ℂ`-homogeneous map into a complete
normed space.  This packaging avoids elaborating an intermediate `LinearMap` whose instance
path differs from the seminormed one on GNS pre-Hilbert type synonyms. -/
noncomputable def extendOfBound (f : X → Y) (C : ℝ) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (r : ℂ) (x : X), f (r • x) = r • f x) (hb : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Completion X →L[ℂ] Y :=
  clmExtend (LinearMap.mkContinuous
    { toFun := f, map_add' := hadd, map_smul' := hsmul } C hb)

@[simp] theorem extendOfBound_coe (f : X → Y) (C : ℝ) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (r : ℂ) (x : X), f (r • x) = r • f x) (hb : ∀ x, ‖f x‖ ≤ C * ‖x‖) (a : X) :
    extendOfBound f C hadd hsmul hb (a : Completion X) = f a :=
  clmExtend_coe _ _

theorem norm_clmExtend_le (f : X →L[ℂ] Y) (C : ℝ) (hC : ∀ a, ‖f a‖ ≤ C * ‖a‖) (x : Completion X) :
    ‖clmExtend f x‖ ≤ C * ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a => rw [clmExtend_coe, Completion.norm_coe]; exact hC a

end Completions

/-! ## 1. Product-state data -/

/-- The data of a product state: a total C⋆-algebra with two commuting unital C⋆-subalgebras
(presented as unital ⋆-homomorphisms `pureEmb`, `mixedEmb`), and a positive functional on the
total algebra which factorizes as a product of positive functionals on the two factors.

All auxiliary premises are explicit fields:

* `commuting` — the two embedded algebras commute elementwise;
* `product` — the state factorizes on products of the two factors;
* `state_norm_le` — the total functional is norm-decreasing (true for any state on a unital
  C⋆-algebra, assumed here rather than re-derived);
* `span_dense` — the linear span of the product elements is norm dense in the total algebra.
-/
structure ProductGNSData where
  /-- The "pure" tensor factor algebra. -/
  Pure : Type u
  /-- The "mixed" tensor factor algebra. -/
  Mixed : Type u
  /-- The total algebra. -/
  Total : Type u
  [pureCStar : CStarAlgebra Pure]
  [mixedCStar : CStarAlgebra Mixed]
  [totalCStar : CStarAlgebra Total]
  [pureOrder : PartialOrder Pure]
  [mixedOrder : PartialOrder Mixed]
  [totalOrder : PartialOrder Total]
  [pureStarOrdered : StarOrderedRing Pure]
  [mixedStarOrdered : StarOrderedRing Mixed]
  [totalStarOrdered : StarOrderedRing Total]
  /-- The embedding of the pure factor. -/
  pureEmb : Pure →⋆ₐ[ℂ] Total
  /-- The embedding of the mixed factor. -/
  mixedEmb : Mixed →⋆ₐ[ℂ] Total
  /-- The state of the pure factor. -/
  pureState : Pure →ₚ[ℂ] ℂ
  /-- The state of the mixed factor. -/
  mixedState : Mixed →ₚ[ℂ] ℂ
  /-- The total (product) state. -/
  totalState : Total →ₚ[ℂ] ℂ
  /-- The two embedded factors commute. -/
  commuting : ∀ (a : Pure) (b : Mixed), pureEmb a * mixedEmb b = mixedEmb b * pureEmb a
  /-- The total state is the product state. -/
  product : ∀ (a : Pure) (b : Mixed),
    totalState (pureEmb a * mixedEmb b) = pureState a * mixedState b
  /-- The total state is norm-decreasing. -/
  state_norm_le : ∀ x : Total, ‖totalState x‖ ≤ ‖x‖
  /-- The product elements span a dense subspace of the total algebra. -/
  span_dense :
    Dense ((Submodule.span ℂ (Set.range fun p : Pure × Mixed => pureEmb p.1 * mixedEmb p.2) :
      Submodule ℂ Total) : Set Total)

attribute [instance] ProductGNSData.pureCStar ProductGNSData.mixedCStar ProductGNSData.totalCStar
  ProductGNSData.pureOrder ProductGNSData.mixedOrder ProductGNSData.totalOrder
  ProductGNSData.pureStarOrdered ProductGNSData.mixedStarOrdered
  ProductGNSData.totalStarOrdered

namespace ProductGNSData

variable (D : ProductGNSData)

/-! ### 1.1 Elementary product elements -/

/-- The elementary product element `ι₁ a · ι₂ b` of the total algebra. -/
def prodElt (a : D.Pure) (b : D.Mixed) : D.Total := D.pureEmb a * D.mixedEmb b

theorem prodElt_star_mul (a c : D.Pure) (b d : D.Mixed) :
    star (D.prodElt a b) * D.prodElt c d = D.prodElt (star a * c) (star b * d) := by
  have h1 : star (D.prodElt a b) = D.mixedEmb (star b) * D.pureEmb (star a) := by
    simp [prodElt, star_mul, map_star]
  calc star (D.prodElt a b) * D.prodElt c d
      = D.mixedEmb (star b) * (D.pureEmb (star a) * D.pureEmb c) * D.mixedEmb d := by
        rw [h1, prodElt]; simp only [mul_assoc]
    _ = D.mixedEmb (star b) * D.pureEmb (star a * c) * D.mixedEmb d := by rw [map_mul]
    _ = D.pureEmb (star a * c) * D.mixedEmb (star b) * D.mixedEmb d := by
        rw [(D.commuting (star a * c) (star b)).symm]
    _ = D.prodElt (star a * c) (star b * d) := by
        rw [prodElt, map_mul D.mixedEmb, ← mul_assoc]

theorem prodElt_mul (a c : D.Pure) (b d : D.Mixed) :
    D.prodElt a b * D.prodElt c d = D.prodElt (a * c) (b * d) := by
  calc D.prodElt a b * D.prodElt c d
      = D.pureEmb a * (D.mixedEmb b * D.pureEmb c) * D.mixedEmb d := by
        simp only [prodElt, mul_assoc]
    _ = D.pureEmb a * (D.pureEmb c * D.mixedEmb b) * D.mixedEmb d := by
        rw [← D.commuting c b]
    _ = D.prodElt (a * c) (b * d) := by
        simp only [prodElt, map_mul, mul_assoc]

@[simp] theorem prodElt_one_one : D.prodElt 1 1 = 1 := by simp [prodElt]

theorem totalState_prodElt_inner (a c : D.Pure) (b d : D.Mixed) :
    D.totalState (star (D.prodElt a b) * D.prodElt c d)
      = D.pureState (star a * c) * D.mixedState (star b * d) := by
  rw [prodElt_star_mul, prodElt, D.product]

/-! ### 1.2 The three GNS spaces -/

/-- The GNS Hilbert space of the pure factor state. -/
abbrev PureGNS : Type _ := D.pureState.GNS

/-- The GNS Hilbert space of the mixed factor state. -/
abbrev MixedGNS : Type _ := D.mixedState.GNS

/-- The GNS Hilbert space of the total product state. -/
abbrev TotalGNS : Type _ := D.totalState.GNS

/-- The GNS representation of the pure factor. -/
noncomputable def pureRep : D.Pure →⋆ₐ[ℂ] (D.PureGNS →L[ℂ] D.PureGNS) :=
  D.pureState.gnsStarAlgHom

/-- The GNS representation of the mixed factor. -/
noncomputable def mixedRep : D.Mixed →⋆ₐ[ℂ] (D.MixedGNS →L[ℂ] D.MixedGNS) :=
  D.mixedState.gnsStarAlgHom

/-- The GNS representation of the total algebra. -/
noncomputable def totalRep : D.Total →⋆ₐ[ℂ] (D.TotalGNS →L[ℂ] D.TotalGNS) :=
  D.totalState.gnsStarAlgHom

/-! ### 1.3 The pre-GNS inner-product identity -/

theorem preInner_prodElt (a c : D.Pure) (b d : D.Mixed) :
    ⟪D.totalState.toPreGNS (D.prodElt a b), D.totalState.toPreGNS (D.prodElt c d)⟫_ℂ
      = ⟪D.pureState.toPreGNS a, D.pureState.toPreGNS c⟫_ℂ *
        ⟪D.mixedState.toPreGNS b, D.mixedState.toPreGNS d⟫_ℂ := by
  rw [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS]
  exact D.totalState_prodElt_inner a c b d

theorem norm_prodElt (a : D.Pure) (b : D.Mixed) :
    ‖D.totalState.toPreGNS (D.prodElt a b)‖
      = ‖D.pureState.toPreGNS a‖ * ‖D.mixedState.toPreGNS b‖ := by
  have h := D.preInner_prodElt a a b b
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hc : ((‖D.totalState.toPreGNS (D.prodElt a b)‖ ^ 2 : ℝ) : ℂ)
      = (((‖D.pureState.toPreGNS a‖ * ‖D.mixedState.toPreGNS b‖) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow]
    exact h
  have h' : (‖D.totalState.toPreGNS (D.prodElt a b)‖ : ℝ) ^ 2
      = (‖D.pureState.toPreGNS a‖ * ‖D.mixedState.toPreGNS b‖) ^ 2 := by
    exact_mod_cast hc
  have h1 : (0 : ℝ) ≤ ‖D.totalState.toPreGNS (D.prodElt a b)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖D.pureState.toPreGNS a‖ * ‖D.mixedState.toPreGNS b‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [h', h1, h2]

/-! ## 2. The product bilinear map on the two factor GNS spaces -/

/-- For a fixed pure-factor element, the pre-GNS level map `b ↦ ι₁ a · ι₂ b`. -/
noncomputable def preProdₗ (a : D.Pure) : D.mixedState.PreGNS →ₗ[ℂ] D.totalState.PreGNS where
  toFun b := D.totalState.toPreGNS (D.prodElt a (D.mixedState.ofPreGNS b))
  map_add' x y := by
    simp [prodElt, PositiveLinearMap.toPreGNS, PositiveLinearMap.ofPreGNS, mul_add]
  map_smul' r x := by
    have h : D.mixedState.ofPreGNS (r • x) = r • D.mixedState.ofPreGNS x := map_smul _ _ _
    have h2 : D.prodElt a (r • D.mixedState.ofPreGNS x)
        = r • D.prodElt a (D.mixedState.ofPreGNS x) := by
      simp [prodElt]
    show D.totalState.toPreGNS (D.prodElt a (D.mixedState.ofPreGNS (r • x)))
        = r • D.totalState.toPreGNS (D.prodElt a (D.mixedState.ofPreGNS x))
    rw [h, h2, map_smul]

@[simp] theorem preProdₗ_apply (a : D.Pure) (b : D.Mixed) :
    D.preProdₗ a (D.mixedState.toPreGNS b) = D.totalState.toPreGNS (D.prodElt a b) := rfl

theorem preProdₗ_add_left (a a' : D.Pure) (b : D.mixedState.PreGNS) :
    D.preProdₗ (a + a') b = D.preProdₗ a b + D.preProdₗ a' b := by
  simp [preProdₗ, prodElt, PositiveLinearMap.toPreGNS, PositiveLinearMap.ofPreGNS, add_mul]

theorem preProdₗ_smul_left (r : ℂ) (a : D.Pure) (b : D.mixedState.PreGNS) :
    D.preProdₗ (r • a) b = r • D.preProdₗ a b := by
  simp [preProdₗ, prodElt, PositiveLinearMap.toPreGNS, PositiveLinearMap.ofPreGNS]

theorem norm_preProdₗ (a : D.Pure) (b : D.mixedState.PreGNS) :
    ‖D.preProdₗ a b‖ = ‖D.pureState.toPreGNS a‖ * ‖b‖ :=
  D.norm_prodElt a (D.mixedState.ofPreGNS b)

/-- The same map, valued in the total GNS Hilbert space. -/
noncomputable def preProd (a : D.Pure) : D.mixedState.PreGNS →L[ℂ] D.TotalGNS :=
  (coeCLM D.totalState.PreGNS).comp
    ((D.preProdₗ a).mkContinuous ‖D.pureState.toPreGNS a‖ (fun b => le_of_eq (D.norm_preProdₗ a b)))

@[simp] theorem preProd_apply (a : D.Pure) (b : D.mixedState.PreGNS) :
    D.preProd a b = ((D.preProdₗ a b : D.totalState.PreGNS) : D.TotalGNS) := rfl

theorem norm_preProd_le (a : D.Pure) (b : D.mixedState.PreGNS) :
    ‖D.preProd a b‖ ≤ ‖D.pureState.toPreGNS a‖ * ‖b‖ := by
  rw [preProd_apply, Completion.norm_coe]
  exact le_of_eq (D.norm_preProdₗ a b)

/-- The product map with the second variable completed. -/
noncomputable def prodRight (a : D.Pure) : D.MixedGNS →L[ℂ] D.TotalGNS :=
  clmExtend (D.preProd a)

@[simp] theorem prodRight_coe (a : D.Pure) (b : D.mixedState.PreGNS) :
    D.prodRight a (b : D.MixedGNS) = ((D.preProdₗ a b : D.totalState.PreGNS) : D.TotalGNS) :=
  clmExtend_coe _ _

theorem norm_prodRight_apply_le (a : D.Pure) (y : D.MixedGNS) :
    ‖D.prodRight a y‖ ≤ ‖D.pureState.toPreGNS a‖ * ‖y‖ :=
  norm_clmExtend_le _ _ (D.norm_preProd_le a) y

theorem prodRight_add (a a' : D.Pure) : D.prodRight (a + a') = D.prodRight a + D.prodRight a' := by
  ext y
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih b =>
    simp only [prodRight_coe, ContinuousLinearMap.add_apply]
    rw [← Completion.coe_add, D.preProdₗ_add_left]

theorem prodRight_smul (r : ℂ) (a : D.Pure) : D.prodRight (r • a) = r • D.prodRight a := by
  ext y
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih b =>
    simp only [prodRight_coe, ContinuousLinearMap.smul_apply]
    rw [← Completion.coe_smul, D.preProdₗ_smul_left]

/-- The product bilinear map, with both variables completed: `prodCLM D x y` is the GNS vector
of the total product state corresponding to the pair `(x, y)` of factor GNS vectors. -/
noncomputable def prodCLM :=
  extendOfBound (X := D.pureState.PreGNS) (Y := D.MixedGNS →L[ℂ] D.TotalGNS)
    (fun a => D.prodRight (D.pureState.ofPreGNS a)) 1
    (fun x y => by
      have h : D.pureState.ofPreGNS (x + y)
          = D.pureState.ofPreGNS x + D.pureState.ofPreGNS y := map_add _ _ _
      show D.prodRight (D.pureState.ofPreGNS (x + y))
          = D.prodRight (D.pureState.ofPreGNS x) + D.prodRight (D.pureState.ofPreGNS y)
      rw [h, D.prodRight_add])
    (fun r x => by
      have h : D.pureState.ofPreGNS (r • x) = r • D.pureState.ofPreGNS x := map_smul _ _ _
      show D.prodRight (D.pureState.ofPreGNS (r • x)) = r • D.prodRight (D.pureState.ofPreGNS x)
      rw [h, D.prodRight_smul])
    (fun a => by
      have hb : ∀ y : D.MixedGNS, ‖D.prodRight (D.pureState.ofPreGNS a) y‖ ≤ ‖a‖ * ‖y‖ := by
        intro y
        simpa using D.norm_prodRight_apply_le (D.pureState.ofPreGNS a) y
      rw [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound (D.prodRight (D.pureState.ofPreGNS a))
        (norm_nonneg a) hb)

@[simp] theorem prodCLM_coe (a : D.pureState.PreGNS) :
    D.prodCLM (a : D.PureGNS) = D.prodRight (D.pureState.ofPreGNS a) := by
  rw [prodCLM, extendOfBound_coe]

/-- The defining formula for `prodCLM` on the images of algebra elements. -/
theorem prodCLM_coe_coe (a : D.Pure) (b : D.Mixed) :
    D.prodCLM ((D.pureState.toPreGNS a : D.pureState.PreGNS) : D.PureGNS)
        ((D.mixedState.toPreGNS b : D.mixedState.PreGNS) : D.MixedGNS)
      = ((D.totalState.toPreGNS (D.prodElt a b) : D.totalState.PreGNS) : D.TotalGNS) := by
  rw [prodCLM_coe, PositiveLinearMap.ofPreGNS_toPreGNS, prodRight_coe, preProdₗ_apply]

/-! ## 3. The inner-product identity for the product map -/

theorem prodCLM_coe_coe' (a : D.pureState.PreGNS) (b : D.mixedState.PreGNS) :
    D.prodCLM (a : D.PureGNS) (b : D.MixedGNS)
      = ((D.preProdₗ (D.pureState.ofPreGNS a) b : D.totalState.PreGNS) : D.TotalGNS) := by
  rw [prodCLM_coe, prodRight_coe]

theorem continuous_prodCLM_left (y : D.MixedGNS) :
    Continuous fun x : D.PureGNS => D.prodCLM x y :=
  (D.prodCLM.flip y).continuous

theorem inner_prodCLM_coe (a a' : D.pureState.PreGNS) (b b' : D.mixedState.PreGNS) :
    ⟪D.prodCLM (a : D.PureGNS) (b : D.MixedGNS),
        D.prodCLM (a' : D.PureGNS) (b' : D.MixedGNS)⟫_ℂ
      = ⟪(a : D.PureGNS), (a' : D.PureGNS)⟫_ℂ * ⟪(b : D.MixedGNS), (b' : D.MixedGNS)⟫_ℂ := by
  rw [prodCLM_coe_coe', prodCLM_coe_coe', Completion.inner_coe, Completion.inner_coe,
    Completion.inner_coe]
  have h := D.preInner_prodElt (D.pureState.ofPreGNS a) (D.pureState.ofPreGNS a')
    (D.mixedState.ofPreGNS b) (D.mixedState.ofPreGNS b')
  simpa using h

/-- **The product inner-product identity.**  Inner products of product vectors factorize exactly
as in the Hilbert tensor product of the two factor GNS spaces. -/
theorem inner_prodCLM (x x' : D.PureGNS) (y y' : D.MixedGNS) :
    ⟪D.prodCLM x y, D.prodCLM x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (Continuous.inner (D.continuous_prodCLM_left y) continuous_const)
      ((Continuous.inner continuous_id continuous_const).mul continuous_const)
  | ih a =>
    induction x' using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (Continuous.inner continuous_const (D.continuous_prodCLM_left y'))
        ((Continuous.inner continuous_const continuous_id).mul continuous_const)
    | ih a' =>
      induction y using Completion.induction_on with
      | hp =>
        exact isClosed_eq
          (Continuous.inner (by fun_prop) continuous_const)
          (continuous_const.mul (Continuous.inner continuous_id continuous_const))
      | ih b =>
        induction y' using Completion.induction_on with
        | hp =>
          exact isClosed_eq
            (Continuous.inner continuous_const (by fun_prop))
            (continuous_const.mul (Continuous.inner continuous_const continuous_id))
        | ih b' => exact D.inner_prodCLM_coe a a' b b'

/-! ## 4. The tensor lift and its isometry property -/

/-- The algebraic tensor product of the two factor GNS Hilbert spaces, with Mathlib's canonical
inner product `⟪x ⊗ y, x' ⊗ y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫`. -/
abbrev TensorPre : Type _ := D.PureGNS ⊗[ℂ] D.MixedGNS

/-- The Hilbert tensor product of the two factor GNS spaces: the completion of the algebraic
tensor product. -/
abbrev TensorGNS : Type _ := Completion D.TensorPre

/-- The bilinear product map, as an unbundled bilinear map. -/
noncomputable def prodBil : D.PureGNS →ₗ[ℂ] D.MixedGNS →ₗ[ℂ] D.TotalGNS :=
  LinearMap.mk₂ ℂ (fun x y => D.prodCLM x y)
    (fun x x' y => by
      show D.prodCLM (x + x') y = D.prodCLM x y + D.prodCLM x' y
      rw [map_add]; rfl)
    (fun c x y => by
      show D.prodCLM (c • x) y = c • D.prodCLM x y
      rw [map_smul]; rfl)
    (fun x y y' => by
      show D.prodCLM x (y + y') = D.prodCLM x y + D.prodCLM x y'
      rw [map_add])
    (fun c x y => by
      show D.prodCLM x (c • y) = c • D.prodCLM x y
      rw [map_smul])

@[simp] theorem prodBil_apply (x : D.PureGNS) (y : D.MixedGNS) :
    D.prodBil x y = D.prodCLM x y := rfl

/-- The induced linear map on the algebraic tensor product. -/
noncomputable def tensorLiftₗ : D.TensorPre →ₗ[ℂ] D.TotalGNS := TensorProduct.lift D.prodBil

@[simp] theorem tensorLiftₗ_tmul (x : D.PureGNS) (y : D.MixedGNS) :
    D.tensorLiftₗ (x ⊗ₜ[ℂ] y) = D.prodCLM x y := rfl

/-- **Inner products are preserved by the tensor lift.** -/
theorem inner_tensorLiftₗ (t s : D.TensorPre) :
    ⟪D.tensorLiftₗ t, D.tensorLiftₗ s⟫_ℂ = ⟪t, s⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
      rw [tensorLiftₗ_tmul, tensorLiftₗ_tmul, TensorProduct.inner_tmul, D.inner_prodCLM]
    | add s₁ s₂ hs₁ hs₂ =>
      rw [map_add, inner_add_right, inner_add_right, hs₁, hs₂]
  | add t₁ t₂ ht₁ ht₂ =>
    rw [map_add, inner_add_left, inner_add_left, ht₁, ht₂]

theorem norm_tensorLiftₗ (t : D.TensorPre) : ‖D.tensorLiftₗ t‖ = ‖t‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), D.inner_tensorLiftₗ]

/-- The tensor lift as a linear isometry of the algebraic tensor product into the total GNS
space. -/
noncomputable def tensorLiftIsometry : D.TensorPre →ₗᵢ[ℂ] D.TotalGNS :=
  ⟨D.tensorLiftₗ, D.norm_tensorLiftₗ⟩

/-! ## 5. The product GNS unitary -/

/-- The canonical map from the Hilbert tensor product of the two factor GNS spaces into the GNS
space of the product state. -/
noncomputable def tensorUnitaryCLM : D.TensorGNS →L[ℂ] D.TotalGNS :=
  clmExtend D.tensorLiftIsometry.toContinuousLinearMap

@[simp] theorem tensorUnitaryCLM_coe (t : D.TensorPre) :
    D.tensorUnitaryCLM (t : D.TensorGNS) = D.tensorLiftₗ t :=
  clmExtend_coe _ _

theorem norm_tensorUnitaryCLM (z : D.TensorGNS) : ‖D.tensorUnitaryCLM z‖ = ‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih t => rw [tensorUnitaryCLM_coe, Completion.norm_coe, D.norm_tensorLiftₗ]

theorem isometry_tensorUnitaryCLM : Isometry D.tensorUnitaryCLM :=
  AddMonoidHomClass.isometry_of_norm _ D.norm_tensorUnitaryCLM

/-! ### 5.1 The canonical map of the total algebra into its GNS space -/

theorem norm_totalCoe_le (x : D.Total) :
    ‖((D.totalState.toPreGNS x : D.totalState.PreGNS) : D.TotalGNS)‖ ≤ ‖x‖ := by
  rw [Completion.norm_coe, PositiveLinearMap.preGNS_norm_def]
  have h1 : (D.totalState (star x * x)).re ≤ ‖x‖ ^ 2 := by
    have h2 : ‖D.totalState (star x * x)‖ ≤ ‖star x * x‖ := D.state_norm_le _
    have h3 : ‖star x * x‖ = ‖x‖ ^ 2 := by
      rw [CStarRing.norm_star_mul_self, sq]
    have h4 : (D.totalState (star x * x)).re ≤ ‖D.totalState (star x * x)‖ :=
      Complex.re_le_norm _
    linarith [h2, h3 ▸ h2, h4]
  calc √((D.totalState (star (D.totalState.ofPreGNS (D.totalState.toPreGNS x)) *
        D.totalState.ofPreGNS (D.totalState.toPreGNS x))).re)
      = √((D.totalState (star x * x)).re) := by rw [PositiveLinearMap.ofPreGNS_toPreGNS]
    _ ≤ √(‖x‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = ‖x‖ := by rw [Real.sqrt_sq (norm_nonneg x)]

/-- The canonical continuous linear map from the total algebra to its GNS space. -/
noncomputable def totalCoe : D.Total →L[ℂ] D.TotalGNS :=
  LinearMap.mkContinuous
    { toFun := fun x => ((D.totalState.toPreGNS x : D.totalState.PreGNS) : D.TotalGNS)
      map_add' := fun x y => by
        rw [map_add]
        exact Completion.coe_add _ _
      map_smul' := fun r x => by
        rw [map_smul]
        exact Completion.coe_smul r _ } 1
    (fun x => by rw [one_mul]; exact D.norm_totalCoe_le x)

@[simp] theorem totalCoe_apply (x : D.Total) :
    D.totalCoe x = ((D.totalState.toPreGNS x : D.totalState.PreGNS) : D.TotalGNS) := rfl

/-! ### 5.2 Density of the range -/

theorem totalCoe_prodElt (a : D.Pure) (b : D.Mixed) :
    D.totalCoe (D.prodElt a b)
      = D.tensorUnitaryCLM
          ((((D.pureState.toPreGNS a : D.pureState.PreGNS) : D.PureGNS) ⊗ₜ[ℂ]
            ((D.mixedState.toPreGNS b : D.mixedState.PreGNS) : D.MixedGNS) :
              D.TensorPre) : D.TensorGNS) := by
  rw [tensorUnitaryCLM_coe, tensorLiftₗ_tmul, D.prodCLM_coe_coe, totalCoe_apply]

theorem span_dense' :
    Dense ((Submodule.span ℂ (Set.range fun p : D.Pure × D.Mixed => D.prodElt p.1 p.2) :
      Submodule ℂ D.Total) : Set D.Total) := D.span_dense

theorem totalCoe_mem_range_of_mem_span {x : D.Total}
    (hx : x ∈ Submodule.span ℂ (Set.range fun p : D.Pure × D.Mixed => D.prodElt p.1 p.2)) :
    D.totalCoe x ∈ LinearMap.range (D.tensorUnitaryCLM : D.TensorGNS →ₗ[ℂ] D.TotalGNS) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, rfl⟩ := hz
    exact ⟨_, (D.totalCoe_prodElt p.1 p.2).symm⟩
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add z w _ _ hz hw =>
    rw [map_add]
    exact Submodule.add_mem _ hz hw
  | smul c z _ hz =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hz

theorem denseRange_tensorUnitaryCLM : DenseRange D.tensorUnitaryCLM := by
  classical
  set S : Submodule ℂ D.TotalGNS :=
    LinearMap.range (D.tensorUnitaryCLM : D.TensorGNS →ₗ[ℂ] D.TotalGNS) with hS
  have hSrange : (S : Set D.TotalGNS) = Set.range D.tensorUnitaryCLM := by
    ext z; simp [hS, LinearMap.mem_range]
  have hcoe : ∀ x : D.Total, D.totalCoe x ∈ closure (S : Set D.TotalGNS) := by
    intro x
    have hx : x ∈ closure
        ((Submodule.span ℂ (Set.range fun p : D.Pure × D.Mixed => D.prodElt p.1 p.2) :
          Submodule ℂ D.Total) : Set D.Total) := by
      rw [D.span_dense'.closure_eq]; trivial
    have h2 : D.totalCoe x ∈ closure (D.totalCoe ''
        ((Submodule.span ℂ (Set.range fun p : D.Pure × D.Mixed => D.prodElt p.1 p.2) :
          Submodule ℂ D.Total) : Set D.Total)) :=
      image_closure_subset_closure_image D.totalCoe.continuous ⟨x, hx, rfl⟩
    refine closure_mono ?_ h2
    rintro _ ⟨w, hw, rfl⟩
    exact D.totalCoe_mem_range_of_mem_span hw
  have hdense : Dense (S : Set D.TotalGNS) := by
    rw [dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    have hcl : Set.range (fun x : D.totalState.PreGNS => (x : D.TotalGNS))
        ⊆ closure (S : Set D.TotalGNS) := by
      rintro _ ⟨x, rfl⟩
      exact hcoe (D.totalState.ofPreGNS x)
    calc (Set.univ : Set D.TotalGNS)
        = closure (Set.range (fun x : D.totalState.PreGNS => (x : D.TotalGNS))) :=
          (Completion.denseRange_coe (α := D.totalState.PreGNS)).closure_eq.symm
      _ ⊆ closure (closure (S : Set D.TotalGNS)) := closure_mono hcl
      _ = closure (S : Set D.TotalGNS) := closure_closure
  rw [DenseRange, ← hSrange]
  exact hdense

theorem surjective_tensorUnitaryCLM : Function.Surjective D.tensorUnitaryCLM := by
  have hclosed : IsClosed (Set.range D.tensorUnitaryCLM) :=
    D.isometry_tensorUnitaryCLM.isClosedEmbedding.isClosed_range
  have h : closure (Set.range D.tensorUnitaryCLM) = Set.univ :=
    D.denseRange_tensorUnitaryCLM.closure_range
  rw [hclosed.closure_eq] at h
  intro z
  have hz : z ∈ Set.range D.tensorUnitaryCLM := by rw [h]; trivial
  exact hz

/-- **The product GNS unitary.**  The GNS Hilbert space of the product state is canonically
unitarily isomorphic to the Hilbert tensor product of the GNS spaces of the two factor states:
`H_ω ≅ K_pure ⊗ K_mixed`. -/
noncomputable def productGNSUnitary : D.TensorGNS ≃ₗᵢ[ℂ] D.TotalGNS :=
  LinearIsometryEquiv.ofSurjective
    ⟨(D.tensorUnitaryCLM : D.TensorGNS →ₗ[ℂ] D.TotalGNS), D.norm_tensorUnitaryCLM⟩
    D.surjective_tensorUnitaryCLM

@[simp] theorem productGNSUnitary_apply (z : D.TensorGNS) :
    D.productGNSUnitary z = D.tensorUnitaryCLM z := rfl

theorem productGNSUnitary_tmul (x : D.PureGNS) (y : D.MixedGNS) :
    D.productGNSUnitary ((x ⊗ₜ[ℂ] y : D.TensorPre) : D.TensorGNS) = D.prodCLM x y := by
  rw [productGNSUnitary_apply, tensorUnitaryCLM_coe, tensorLiftₗ_tmul]


/-! ## 6. The intertwining identity

This section proves that the product GNS unitary intertwines the (algebraic) tensor product of
the two factor GNS representations with the GNS representation of the total algebra restricted to
the elementary product elements.  These are *constructed* facts: nothing beyond the explicit
fields of `ProductGNSData` is used. -/

theorem prodCLM_coe_coe'' (p : D.pureState.PreGNS) (q : D.mixedState.PreGNS) :
    D.prodCLM (p : D.PureGNS) (q : D.MixedGNS)
      = ((D.totalState.toPreGNS
          (D.prodElt (D.pureState.ofPreGNS p) (D.mixedState.ofPreGNS q)) :
            D.totalState.PreGNS) : D.TotalGNS) :=
  D.prodCLM_coe_coe' p q

theorem pureRep_coe (a : D.Pure) (p : D.pureState.PreGNS) :
    D.pureRep a (p : D.PureGNS)
      = ((D.pureState.toPreGNS (a * D.pureState.ofPreGNS p) :
          D.pureState.PreGNS) : D.PureGNS) := by
  simp [pureRep]

theorem mixedRep_coe (b : D.Mixed) (q : D.mixedState.PreGNS) :
    D.mixedRep b (q : D.MixedGNS)
      = ((D.mixedState.toPreGNS (b * D.mixedState.ofPreGNS q) :
          D.mixedState.PreGNS) : D.MixedGNS) := by
  simp [mixedRep]

theorem totalRep_coe (z : D.Total) (w : D.totalState.PreGNS) :
    D.totalRep z (w : D.TotalGNS)
      = ((D.totalState.toPreGNS (z * D.totalState.ofPreGNS w) :
          D.totalState.PreGNS) : D.TotalGNS) := by
  simp [totalRep]

theorem prodCLM_intertwine_coe (a : D.Pure) (b : D.Mixed)
    (p : D.pureState.PreGNS) (q : D.mixedState.PreGNS) :
    D.prodCLM (D.pureRep a (p : D.PureGNS)) (D.mixedRep b (q : D.MixedGNS))
      = D.totalRep (D.prodElt a b) (D.prodCLM (p : D.PureGNS) (q : D.MixedGNS)) := by
  rw [pureRep_coe, mixedRep_coe, prodCLM_coe_coe'', prodCLM_coe_coe'', totalRep_coe]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [D.prodElt_mul]

/-- **The intertwining identity on product vectors.** -/
theorem prodCLM_intertwine (a : D.Pure) (b : D.Mixed) (x : D.PureGNS) (y : D.MixedGNS) :
    D.prodCLM (D.pureRep a x) (D.mixedRep b y)
      = D.totalRep (D.prodElt a b) (D.prodCLM x y) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((D.continuous_prodCLM_left (D.mixedRep b y)).comp (D.pureRep a).continuous)
      ((D.totalRep (D.prodElt a b)).continuous.comp (D.continuous_prodCLM_left y))
  | ih p =>
    induction y using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        ((D.prodCLM (D.pureRep a (p : D.PureGNS))).continuous.comp (D.mixedRep b).continuous)
        ((D.totalRep (D.prodElt a b)).continuous.comp (D.prodCLM (p : D.PureGNS)).continuous)
    | ih q => exact D.prodCLM_intertwine_coe a b p q

/-! ### 6.1 The algebraic tensor operator and its norm bound -/

/-- The algebraic tensor product operator `π₁(a) ⊗ π₂(b)` on `TensorPre`. -/
noncomputable def tensorMapₗ (a : D.Pure) (b : D.Mixed) : D.TensorPre →ₗ[ℂ] D.TensorPre :=
  TensorProduct.map (D.pureRep a).toLinearMap (D.mixedRep b).toLinearMap

@[simp] theorem tensorMapₗ_tmul (a : D.Pure) (b : D.Mixed) (x : D.PureGNS) (y : D.MixedGNS) :
    D.tensorMapₗ a b (x ⊗ₜ[ℂ] y) = (D.pureRep a x) ⊗ₜ[ℂ] (D.mixedRep b y) := rfl

/-- The tensor lift intertwines the algebraic tensor operator with the total GNS
representation. -/
theorem tensorLiftₗ_tensorMapₗ (a : D.Pure) (b : D.Mixed) (t : D.TensorPre) :
    D.tensorLiftₗ (D.tensorMapₗ a b t) = D.totalRep (D.prodElt a b) (D.tensorLiftₗ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [tensorMapₗ_tmul, tensorLiftₗ_tmul, tensorLiftₗ_tmul, D.prodCLM_intertwine]
  | add t s ht hs => simp only [map_add, ht, hs]

theorem norm_totalRep_apply_le (z : D.Total) (w : D.TotalGNS) :
    ‖D.totalRep z w‖ ≤ ‖z‖ * ‖w‖ := by
  refine (D.totalRep z).le_opNorm w |>.trans ?_
  exact mul_le_mul_of_nonneg_right
    (NonUnitalStarAlgHom.norm_apply_le (D.totalRep : D.Total →⋆ₐ[ℂ] _) z) (norm_nonneg w)

/-- **Boundedness of the algebraic tensor operator**, obtained for free from the intertwining
identity together with the isometry property of the tensor lift.  (Pinned Mathlib has no general
bound `‖T ⊗ S‖ ≤ ‖T‖ ‖S‖` on an algebraic tensor product of inner-product spaces.) -/
theorem norm_tensorMapₗ_le (a : D.Pure) (b : D.Mixed) (t : D.TensorPre) :
    ‖D.tensorMapₗ a b t‖ ≤ ‖D.prodElt a b‖ * ‖t‖ := by
  rw [← D.norm_tensorLiftₗ (D.tensorMapₗ a b t), tensorLiftₗ_tensorMapₗ,
    ← D.norm_tensorLiftₗ t]
  exact D.norm_totalRep_apply_le _ _

/-! ## 7. The completed tensor operator and the unitary conjugation -/

/-- The elementary tensor operator `π₁(a) ⊗ π₂(b)` as a bounded operator on the algebraic
tensor product. -/
noncomputable def tensorOp (a : D.Pure) (b : D.Mixed) : D.TensorPre →L[ℂ] D.TensorPre :=
  (D.tensorMapₗ a b).mkContinuous ‖D.prodElt a b‖ (D.norm_tensorMapₗ_le a b)

@[simp] theorem tensorOp_apply (a : D.Pure) (b : D.Mixed) (t : D.TensorPre) :
    D.tensorOp a b t = D.tensorMapₗ a b t := rfl

/-- The elementary tensor operator on the Hilbert tensor product `K_pure ⊗ K_mixed`. -/
noncomputable def tensorOpC (a : D.Pure) (b : D.Mixed) : D.TensorGNS →L[ℂ] D.TensorGNS :=
  (D.tensorOp a b).completion

@[simp] theorem tensorOpC_coe (a : D.Pure) (b : D.Mixed) (t : D.TensorPre) :
    D.tensorOpC a b (t : D.TensorGNS) = ((D.tensorMapₗ a b t : D.TensorPre) : D.TensorGNS) :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- **The intertwining identity on the Hilbert tensor product.** -/
theorem tensorUnitaryCLM_tensorOpC (a : D.Pure) (b : D.Mixed) (z : D.TensorGNS) :
    D.tensorUnitaryCLM (D.tensorOpC a b z)
      = D.totalRep (D.prodElt a b) (D.tensorUnitaryCLM z) := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq (D.tensorUnitaryCLM.continuous.comp (D.tensorOpC a b).continuous)
      ((D.totalRep (D.prodElt a b)).continuous.comp D.tensorUnitaryCLM.continuous)
  | ih t => rw [tensorOpC_coe, tensorUnitaryCLM_coe, tensorUnitaryCLM_coe, tensorLiftₗ_tensorMapₗ]

/-- Conjugation by the product GNS unitary, as a `⋆`-algebra equivalence between the bounded
operators on `K_pure ⊗ K_mixed` and those on the GNS space of the product state. -/
noncomputable def unitaryConj :
    (D.TensorGNS →L[ℂ] D.TensorGNS) ≃⋆ₐ[ℂ] (D.TotalGNS →L[ℂ] D.TotalGNS) :=
  D.productGNSUnitary.conjStarAlgEquiv

@[simp] theorem unitaryConj_apply (T : D.TensorGNS →L[ℂ] D.TensorGNS) (y : D.TotalGNS) :
    D.unitaryConj T y = D.productGNSUnitary (T (D.productGNSUnitary.symm y)) := rfl

/-- **The represented elementary product operators are exactly the conjugates of the elementary
tensor operators.** -/
theorem unitaryConj_tensorOpC (a : D.Pure) (b : D.Mixed) :
    D.unitaryConj (D.tensorOpC a b) = D.totalRep (D.prodElt a b) := by
  ext y
  have h : D.tensorUnitaryCLM (D.productGNSUnitary.symm y) = y :=
    D.productGNSUnitary.apply_symm_apply y
  rw [unitaryConj_apply, productGNSUnitary_apply, D.tensorUnitaryCLM_tensorOpC, h]

/-! ## 8. Identification of the represented algebra

The manuscript step identifies the represented regional algebra with a tensor product of the two
factor algebras.  Everything below is *constructed* from the fields of `ProductGNSData`; the
remaining, genuinely missing ingredient (a spatial von Neumann tensor product in pinned Mathlib)
is discussed in the module docstring and is **not** assumed anywhere. -/

/-- The set of elementary tensor operators `π₁(a) ⊗ π₂(b)` on `K_pure ⊗ K_mixed`. -/
def elementaryTensorSet : Set (D.TensorGNS →L[ℂ] D.TensorGNS) :=
  Set.range fun p : D.Pure × D.Mixed => D.tensorOpC p.1 p.2

/-- The set of represented elementary product elements `π(ι₁(a) ι₂(b))` on the GNS space of the
product state. -/
def representedProductSet : Set (D.TotalGNS →L[ℂ] D.TotalGNS) :=
  Set.range fun p : D.Pure × D.Mixed => D.totalRep (D.prodElt p.1 p.2)

theorem unitaryConj_image_elementaryTensorSet :
    D.unitaryConj '' D.elementaryTensorSet = D.representedProductSet := by
  rw [elementaryTensorSet, representedProductSet, ← Set.range_comp]
  exact congrArg Set.range (funext fun p => D.unitaryConj_tensorOpC p.1 p.2)

/-! ### 8.1 Norm density: the elementary operators already determine the commutant -/

theorem continuous_totalRep : Continuous (fun z : D.Total => D.totalRep z) :=
  AddMonoidHomClass.continuous_of_bound D.totalRep 1 (fun z => by
    simpa using NonUnitalStarAlgHom.norm_apply_le (D.totalRep : D.Total →⋆ₐ[ℂ] _) z)

/-- An operator commuting with all represented elementary product elements commutes with the whole
represented algebra.  This uses the density field `span_dense` together with contractivity of the
GNS representation. -/
theorem commute_totalRep_of_commute_prodElt (T : D.TotalGNS →L[ℂ] D.TotalGNS)
    (hT : ∀ (a : D.Pure) (b : D.Mixed),
      D.totalRep (D.prodElt a b) * T = T * D.totalRep (D.prodElt a b)) (z : D.Total) :
    D.totalRep z * T = T * D.totalRep z := by
  have hclosed : IsClosed {w : D.Total | D.totalRep w * T = T * D.totalRep w} :=
    isClosed_eq (D.continuous_totalRep.mul continuous_const)
      (continuous_const.mul D.continuous_totalRep)
  have hspan : ((Submodule.span ℂ (Set.range fun p : D.Pure × D.Mixed => D.prodElt p.1 p.2) :
      Submodule ℂ D.Total) : Set D.Total)
      ⊆ {w : D.Total | D.totalRep w * T = T * D.totalRep w} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨p, rfl⟩ := hu
      exact hT p.1 p.2
    | zero => simp
    | add u v _ _ hu hv =>
      simp only [Set.mem_setOf_eq] at hu hv ⊢
      rw [map_add, add_mul, mul_add, hu, hv]
    | smul c u _ hu =>
      simp only [Set.mem_setOf_eq] at hu ⊢
      rw [map_smul, smul_mul_assoc, mul_smul_comm, hu]
  have hz : z ∈ closure {w : D.Total | D.totalRep w * T = T * D.totalRep w} :=
    closure_mono hspan (by rw [D.span_dense'.closure_eq]; trivial)
  rwa [hclosed.closure_eq] at hz

/-- **The elementary product operators have the same commutant as the whole represented
algebra.** -/
theorem centralizer_representedProductSet :
    D.representedProductSet.centralizer = (Set.range D.totalRep).centralizer := by
  refine Set.Subset.antisymm ?_ (Set.centralizer_subset ?_)
  · intro T hT
    rintro _ ⟨z, rfl⟩
    exact D.commute_totalRep_of_commute_prodElt T
      (fun a b => hT _ ⟨(a, b), rfl⟩) z
  · rintro _ ⟨p, rfl⟩
    exact ⟨D.prodElt p.1 p.2, rfl⟩

/-! ### 8.2 Transport of commutants and bicommutants along the unitary -/

theorem unitaryConj_image_centralizer (S : Set (D.TensorGNS →L[ℂ] D.TensorGNS)) :
    D.unitaryConj '' S.centralizer = (D.unitaryConj '' S).centralizer :=
  StabilizerHyperfinite.BoundedStateGNS.image_centralizer_of_mulEquiv
    (D.unitaryConj.toRingEquiv.toMulEquiv) S

/-- **Commutant transport.**  The commutant of the elementary tensor operators is carried by the
product GNS unitary onto the commutant of the represented regional algebra. -/
theorem unitaryConj_image_centralizer_elementaryTensorSet :
    D.unitaryConj '' D.elementaryTensorSet.centralizer = (Set.range D.totalRep).centralizer := by
  rw [D.unitaryConj_image_centralizer, D.unitaryConj_image_elementaryTensorSet,
    D.centralizer_representedProductSet]

/-- **The product GNS tensor factorization of the represented algebra.**

Conjugation by the product GNS unitary carries the von Neumann algebra generated (in the
bicommutant sense) by the elementary tensor operators `π₁(a) ⊗ π₂(b)` on `K_pure ⊗ K_mixed`
exactly onto the represented regional algebra `π(Total)''` on the GNS space of the product
state.  This is the strongest form of the manuscript identification available without a spatial
von Neumann tensor product. -/
theorem unitaryConj_image_bicommutant_elementaryTensorSet :
    D.unitaryConj '' D.elementaryTensorSet.centralizer.centralizer
      = (Set.range D.totalRep).centralizer.centralizer := by
  rw [D.unitaryConj_image_centralizer, D.unitaryConj_image_centralizer_elementaryTensorSet]

/-! ## 9. The two commuting factors and the spatial tensor product

The two families `{π₁(a) ⊗ 1}` and `{1 ⊗ π₂(b)}` of operators on `K_pure ⊗ K_mixed` are
constructed here, together with the factorization `π₁(a) ⊗ π₂(b) = (π₁(a) ⊗ 1)(1 ⊗ π₂(b))`.
The bicommutant of their union is, by definition, the spatial (von Neumann) tensor product of the
two represented factor algebras; we prove that it coincides with the bicommutant of the
elementary tensor operators, and hence is carried by the product GNS unitary exactly onto the
represented regional algebra. -/

theorem tensorMapₗ_split (a : D.Pure) (b : D.Mixed) (t : D.TensorPre) :
    D.tensorMapₗ a b t = D.tensorMapₗ a 1 (D.tensorMapₗ 1 b t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [tensorMapₗ_tmul, tensorMapₗ_tmul, tensorMapₗ_tmul]
    simp [pureRep, mixedRep]
  | add t s ht hs => simp only [map_add, ht, hs]

theorem tensorMapₗ_split' (a : D.Pure) (b : D.Mixed) (t : D.TensorPre) :
    D.tensorMapₗ a b t = D.tensorMapₗ 1 b (D.tensorMapₗ a 1 t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [tensorMapₗ_tmul, tensorMapₗ_tmul, tensorMapₗ_tmul]
    simp [pureRep, mixedRep]
  | add t s ht hs => simp only [map_add, ht, hs]

theorem tensorOpC_split (a : D.Pure) (b : D.Mixed) :
    D.tensorOpC a b = D.tensorOpC a 1 * D.tensorOpC 1 b := by
  ext z
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq (D.tensorOpC a b).continuous
      ((D.tensorOpC a 1).continuous.comp (D.tensorOpC 1 b).continuous)
  | ih t =>
    show D.tensorOpC a b (t : D.TensorGNS) = D.tensorOpC a 1 (D.tensorOpC 1 b (t : D.TensorGNS))
    rw [tensorOpC_coe, tensorOpC_coe, tensorOpC_coe, D.tensorMapₗ_split a b t]

theorem tensorOpC_split' (a : D.Pure) (b : D.Mixed) :
    D.tensorOpC a b = D.tensorOpC 1 b * D.tensorOpC a 1 := by
  ext z
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq (D.tensorOpC a b).continuous
      ((D.tensorOpC 1 b).continuous.comp (D.tensorOpC a 1).continuous)
  | ih t =>
    show D.tensorOpC a b (t : D.TensorGNS) = D.tensorOpC 1 b (D.tensorOpC a 1 (t : D.TensorGNS))
    rw [tensorOpC_coe, tensorOpC_coe, tensorOpC_coe, D.tensorMapₗ_split' a b t]

/-- The two families of operators commute. -/
theorem tensorOpC_commute (a : D.Pure) (b : D.Mixed) :
    D.tensorOpC a 1 * D.tensorOpC 1 b = D.tensorOpC 1 b * D.tensorOpC a 1 := by
  rw [← D.tensorOpC_split, D.tensorOpC_split']

/-- The represented pure factor `π₁(A₁) ⊗ 1` on `K_pure ⊗ K_mixed`. -/
def pureFactorSet : Set (D.TensorGNS →L[ℂ] D.TensorGNS) :=
  Set.range fun a : D.Pure => D.tensorOpC a 1

/-- The represented mixed factor `1 ⊗ π₂(A₂)` on `K_pure ⊗ K_mixed`. -/
def mixedFactorSet : Set (D.TensorGNS →L[ℂ] D.TensorGNS) :=
  Set.range fun b : D.Mixed => D.tensorOpC 1 b

/-- The spatial (von Neumann) tensor product of the two represented factor algebras, defined in
the standard way as the bicommutant of the union of the two commuting families. -/
def spatialTensorAlgebra : Set (D.TensorGNS →L[ℂ] D.TensorGNS) :=
  (D.pureFactorSet ∪ D.mixedFactorSet).centralizer.centralizer

theorem union_factorSet_subset_elementary :
    D.pureFactorSet ∪ D.mixedFactorSet ⊆ D.elementaryTensorSet := by
  rintro T (⟨a, rfl⟩ | ⟨b, rfl⟩)
  · exact ⟨(a, 1), rfl⟩
  · exact ⟨(1, b), rfl⟩

theorem elementary_subset_spatialTensorAlgebra :
    D.elementaryTensorSet ⊆ D.spatialTensorAlgebra := by
  rintro _ ⟨p, rfl⟩
  show D.tensorOpC p.1 p.2 ∈ D.spatialTensorAlgebra
  rw [spatialTensorAlgebra, D.tensorOpC_split p.1 p.2]
  exact Set.mul_mem_centralizer
    (Set.subset_centralizer_centralizer (Or.inl ⟨p.1, rfl⟩))
    (Set.subset_centralizer_centralizer (Or.inr ⟨p.2, rfl⟩))

/-- **The bicommutant of the elementary tensor operators is the spatial tensor product of the two
represented factor algebras.** -/
theorem bicommutant_elementary_eq_spatial :
    D.elementaryTensorSet.centralizer.centralizer = D.spatialTensorAlgebra := by
  refine Set.Subset.antisymm ?_
    (Set.centralizer_subset (Set.centralizer_subset D.union_factorSet_subset_elementary))
  calc D.elementaryTensorSet.centralizer.centralizer
      ⊆ D.spatialTensorAlgebra.centralizer.centralizer :=
        Set.centralizer_subset (Set.centralizer_subset D.elementary_subset_spatialTensorAlgebra)
    _ = D.spatialTensorAlgebra := by
        rw [spatialTensorAlgebra, Set.centralizer_centralizer_centralizer]

/-- **The manuscript identification, in the strongest form supported by pinned Mathlib.**

Conjugation by the product GNS unitary carries the spatial tensor product of the two represented
factor algebras on `K_pure ⊗ K_mixed` exactly onto the represented regional algebra
`π(Total)''` on the GNS space of the product state. -/
theorem unitaryConj_image_spatialTensorAlgebra :
    D.unitaryConj '' D.spatialTensorAlgebra = (Set.range D.totalRep).centralizer.centralizer := by
  rw [← D.bicommutant_elementary_eq_spatial,
    D.unitaryConj_image_bicommutant_elementaryTensorSet]

end ProductGNSData

/-! ## 10. Non-vacuity of the data

`ProductGNSData` is inhabited: the fields are jointly satisfiable.  This rules out a vacuous
reading of all the statements above. -/

/-- The identity functional on `ℂ`, as a positive linear map. -/
def idPositive : ℂ →ₚ[ℂ] ℂ where
  toLinearMap := LinearMap.id
  monotone' _ _ h := h

/-- The trivial product datum on `ℂ`: both factors and the total algebra are `ℂ`, with the
identity embeddings and the identity state. -/
noncomputable def trivialProductGNSData : ProductGNSData.{0} where
  Pure := ℂ
  Mixed := ℂ
  Total := ℂ
  pureEmb := StarAlgHom.id ℂ ℂ
  mixedEmb := StarAlgHom.id ℂ ℂ
  pureState := idPositive
  mixedState := idPositive
  totalState := idPositive
  commuting a b := mul_comm _ _
  product _ _ := rfl
  state_norm_le _ := le_rfl
  span_dense := by
    have hr : (Set.range fun p : ℂ × ℂ =>
        (StarAlgHom.id ℂ ℂ) p.1 * (StarAlgHom.id ℂ ℂ) p.2) = Set.univ := by
      ext x
      exact ⟨fun _ => trivial, fun _ => ⟨(x, 1), by simp⟩⟩
    rw [hr, Submodule.span_univ]
    simp

instance : Nonempty ProductGNSData.{0} := ⟨trivialProductGNSData⟩

namespace ProductGNSData
end ProductGNSData
end ProductGNSTensor
end AristotleCandidates
