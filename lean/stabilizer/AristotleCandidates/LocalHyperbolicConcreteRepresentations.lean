import AristotleCandidates.LocalHyperbolicSourceUHFBridge
import AristotleCandidates.UHFReferenceRepresentation
import AristotleCandidates.ConcreteCStarCompletion

/-!
# P55C — faithful concrete representations for the source and regional limits

**Context declaration: infrastructure only.**  No manuscript claim is asserted
in this module.

## Plan alignment

* Package `P55C`, lane `H`; predecessors `P53`
  (`AristotleCandidates.LocalHyperbolicAlgebraicAlpha`), `P54`
  (`AristotleCandidates.UHFReferenceRepresentation`) and `P55B`
  (`AristotleCandidates.LocalHyperbolicSourceUHFBridge`).
* Gate: construct *faithful* algebraic operator representations of the P53
  source and target (regional) direct limits, and their closed operator-range
  C⋆-algebras together with canonical injective star-algebra embeddings with
  dense range.
* Forbidden downstream claims, none of which is made here: no completed
  C⋆-extension of `alpha` between the closures (that is the P55D gate), no
  product-state identity, no GNS tensor split, no factor classification, and
  no trace or weight theorem.

## What is constructed

1. A small reusable API for the **closed operator range** of an arbitrary
   star-algebra homomorphism into the bounded operators of a Hilbert space
   (`rangeCStar`, `rangeEmbedding`, injectivity, dense range, minimality).
   The C⋆-algebra structure is the genuine one carried by a closed
   star-subalgebra of `H →L[ℂ] H`; nothing is supplied.
2. The **uniform branch interface** `AlphaData.SourceConcreteRep`: a faithful
   representation of the P53 source limit on the P54 GNS Hilbert space
   `UHFGNS`.  Every field of every instance produced below is *constructed*
   here; no representation, injectivity, closure or dense-range statement is
   accepted as a hypothesis.
3. From such data: the **regional representation** obtained by transporting
   through `A.alpha.symm`, its faithfulness, the intertwining identity
   `targetRep (alpha z) = rep z`, both closed operator-range C⋆-algebras and
   their canonical injective embeddings with dense range.
4. The **infinite branch** `AlphaData.infiniteSourceRep`: the P54 faithful
   representation `uhfRep` transported through the P55B star equivalence
   `A.sourceUHFEquiv`.
5. The **finite branch** `AlphaData.finiteSourceRep`: the P54 faithful
   finite-stage matrix representation `uhfStageRep (Nat.card I)` transported
   through the P55B terminal-stage equivalence `A.sourceFiniteEquiv`.
6. The **branch-uniform datum** `AlphaData.branchSourceRep`, defined by the
   finite/infinite case split and proved to agree with each branch.
7. The **pulled-back pre-C⋆ structure**: the norm `‖rep z‖` induces a genuine
   `NormedRing`/`NormedAlgebra` structure on the algebraic source limit whose
   C⋆-identity is *proved* from the faithful representation
   (`SourceConcreteRep.sourceCStarRing`); norm preservation is never assumed.

## Auxiliary assumptions

Only the explicit `Finite I` versus `Infinite I` typeclass branch, beyond the
predecessor data.
-/

namespace StabilizerHyperfinite

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open scoped Topology

/-! ## 1. The closed operator range of a star-algebra homomorphism -/

namespace ConcreteRange

variable {A B H : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]
  [Semiring B] [StarRing B] [Algebra ℂ B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The concrete C⋆-algebra attached to a representation: the closure of its
operator range inside the bounded operators on `H`. -/
noncomputable def rangeCStar (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  rho.range.topologicalClosure

instance instIsClosedRangeCStar (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed ((rangeCStar rho : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :=
  rho.range.isClosed_topologicalClosure

/-- A closed star-subalgebra of the bounded operators on a Hilbert space is a
genuine C⋆-algebra. -/
noncomputable instance instCStarAlgebraRangeCStar (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    CStarAlgebra (rangeCStar rho) :=
  StarSubalgebra.cstarAlgebra _

theorem mem_rangeCStar (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) : rho a ∈ rangeCStar rho :=
  rho.range.le_topologicalClosure ⟨a, rfl⟩

/-- The canonical star-algebra homomorphism into the closed operator range. -/
noncomputable def rangeEmbedding (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : A →⋆ₐ[ℂ] rangeCStar rho :=
  rho.codRestrict _ (mem_rangeCStar rho)

@[simp] theorem coe_rangeEmbedding (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    (rangeEmbedding rho a : H →L[ℂ] H) = rho a := rfl

theorem rangeEmbedding_injective {rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)} (h : Function.Injective rho) :
    Function.Injective (rangeEmbedding rho) :=
  fun _ _ hab => h (congrArg Subtype.val hab)

/-- The image of the algebra is dense in its closed operator range. -/
theorem rangeEmbedding_denseRange (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    DenseRange (rangeEmbedding rho) := by
  have hcoe : ((rangeCStar rho : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))
      = closure (Set.range ⇑rho) := by
    rw [rangeCStar, StarSubalgebra.topologicalClosure_coe]
    rfl
  rw [DenseRange, Subtype.dense_iff]
  intro x hx
  rw [hcoe] at hx
  refine closure_mono ?_ hx
  rintro _ ⟨a, rfl⟩
  exact ⟨rangeEmbedding rho a, ⟨a, rfl⟩, rfl⟩

/-- Minimality of the closed operator range. -/
theorem rangeCStar_le {rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : IsClosed (S : Set (H →L[ℂ] H))) (hr : ∀ a, rho a ∈ S) : rangeCStar rho ≤ S :=
  StarSubalgebra.topologicalClosure_minimal (by rintro _ ⟨a, rfl⟩; exact hr a) hS

/-- The closed operator range is the *least* closed star-subalgebra containing
the operator range. -/
theorem rangeCStar_isLeast (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    IsLeast {S : StarSubalgebra ℂ (H →L[ℂ] H) |
        IsClosed (S : Set (H →L[ℂ] H)) ∧ ∀ a, rho a ∈ S} (rangeCStar rho) :=
  ⟨⟨instIsClosedRangeCStar rho, mem_rangeCStar rho⟩, fun _ hS => rangeCStar_le hS.1 hS.2⟩

/-- Two representations with the same operator range have the same closed
operator range. -/
theorem rangeCStar_congr {rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {psi : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (h : Set.range ⇑rho = Set.range ⇑psi) : rangeCStar rho = rangeCStar psi := by
  have hr : rho.range = psi.range := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      have : rho a ∈ Set.range ⇑psi := h ▸ Set.mem_range_self a
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩
    · rintro ⟨a, rfl⟩
      have : psi a ∈ Set.range ⇑rho := h ▸ Set.mem_range_self a
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩
  rw [rangeCStar, rangeCStar, hr]

end ConcreteRange

/-! ## 2. The branch interface for the local-hyperbolic limits -/

namespace LocalHyperbolicAlpha

namespace AlphaData

open ConcreteRange

variable {L I : Type*} [LinearOrder I] (A : AlphaData L I)

/-- **The uniform branch interface.**  A faithful representation of the P53
algebraic source limit on the P54 trace-GNS Hilbert space `UHFGNS`.  Both
branches below *construct* such a datum; nothing in this file accepts one as an
external hypothesis. -/
structure SourceConcreteRep where
  /-- The representation of the algebraic source limit by bounded operators. -/
  rep : A.SourceLimit →⋆ₐ[ℂ] (UHFGNS →L[ℂ] UHFGNS)
  /-- Faithfulness of the representation, proved in each construction. -/
  rep_injective : Function.Injective rep

namespace SourceConcreteRep

variable {A} (R : A.SourceConcreteRep)

/-- **The regional representation**, obtained by transporting the source
representation through the P53 algebraic equivalence `A.alpha.symm`. -/
noncomputable def targetRep : A.TargetLimit →⋆ₐ[ℂ] (UHFGNS →L[ℂ] UHFGNS) :=
  R.rep.comp (StarAlgHomClass.toStarAlgHom A.alpha.symm)

@[simp] theorem targetRep_apply (y : A.TargetLimit) : R.targetRep y = R.rep (A.alpha.symm y) :=
  rfl

/-- **The intertwining identity**: the regional representation composed with the
algebraic `alpha` is the source representation. -/
@[simp] theorem targetRep_alpha (z : A.SourceLimit) : R.targetRep (A.alpha z) = R.rep z := by
  simp

/-- **Faithfulness of the regional representation.** -/
theorem targetRep_injective : Function.Injective R.targetRep :=
  R.rep_injective.comp (EquivLike.injective A.alpha.symm)

/-! ### The two closed operator-range C⋆-algebras -/

/-- The concrete C⋆-algebra of the source limit: the closure of the operator
range of `R.rep`. -/
noncomputable def sourceCStar : StarSubalgebra ℂ (UHFGNS →L[ℂ] UHFGNS) := rangeCStar R.rep

/-- The concrete C⋆-algebra of the regional limit: the closure of the operator
range of `R.targetRep`. -/
noncomputable def targetCStar : StarSubalgebra ℂ (UHFGNS →L[ℂ] UHFGNS) := rangeCStar R.targetRep

instance : IsClosed ((R.sourceCStar : StarSubalgebra ℂ (UHFGNS →L[ℂ] UHFGNS)) :
    Set (UHFGNS →L[ℂ] UHFGNS)) := instIsClosedRangeCStar _

instance : IsClosed ((R.targetCStar : StarSubalgebra ℂ (UHFGNS →L[ℂ] UHFGNS)) :
    Set (UHFGNS →L[ℂ] UHFGNS)) := instIsClosedRangeCStar _

noncomputable instance : CStarAlgebra R.sourceCStar := instCStarAlgebraRangeCStar _

noncomputable instance : CStarAlgebra R.targetCStar := instCStarAlgebraRangeCStar _

/-- The canonical embedding of the algebraic source limit into its concrete
C⋆-model. -/
noncomputable def sourceEmbedding : A.SourceLimit →⋆ₐ[ℂ] R.sourceCStar := rangeEmbedding R.rep

/-- The canonical embedding of the algebraic regional limit into its concrete
C⋆-model. -/
noncomputable def targetEmbedding : A.TargetLimit →⋆ₐ[ℂ] R.targetCStar :=
  rangeEmbedding R.targetRep

@[simp] theorem coe_sourceEmbedding (z : A.SourceLimit) :
    (R.sourceEmbedding z : UHFGNS →L[ℂ] UHFGNS) = R.rep z := rfl

@[simp] theorem coe_targetEmbedding (y : A.TargetLimit) :
    (R.targetEmbedding y : UHFGNS →L[ℂ] UHFGNS) = R.targetRep y := rfl

theorem sourceEmbedding_injective : Function.Injective R.sourceEmbedding :=
  rangeEmbedding_injective R.rep_injective

theorem targetEmbedding_injective : Function.Injective R.targetEmbedding :=
  rangeEmbedding_injective R.targetRep_injective

theorem sourceEmbedding_denseRange : DenseRange R.sourceEmbedding := rangeEmbedding_denseRange _

theorem targetEmbedding_denseRange : DenseRange R.targetEmbedding := rangeEmbedding_denseRange _

/-- Minimality of the source C⋆-model. -/
theorem sourceCStar_le {S : StarSubalgebra ℂ (UHFGNS →L[ℂ] UHFGNS)}
    (hS : IsClosed (S : Set (UHFGNS →L[ℂ] UHFGNS))) (hr : ∀ z, R.rep z ∈ S) :
    R.sourceCStar ≤ S := rangeCStar_le hS hr

/-- Minimality of the regional C⋆-model. -/
theorem targetCStar_le {S : StarSubalgebra ℂ (UHFGNS →L[ℂ] UHFGNS)}
    (hS : IsClosed (S : Set (UHFGNS →L[ℂ] UHFGNS))) (hr : ∀ y, R.targetRep y ∈ S) :
    R.targetCStar ≤ S := rangeCStar_le hS hr

/-- Because the regional representation is the source representation composed
with the *bijection* `A.alpha.symm`, the two operator ranges are literally the
same set of bounded operators, hence so are the two closures.

This is a statement about ranges only.  **No** C⋆-extension of `alpha` between
the two closures is constructed or claimed here; that is the separate P55D
gate. -/
theorem targetCStar_eq_sourceCStar : R.targetCStar = R.sourceCStar := by
  refine rangeCStar_congr ?_
  ext T
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨A.alpha.symm y, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨A.alpha z, by simp⟩

/-! ### The pulled-back pre-C⋆ structure on the algebraic source limit -/

/-- The norm pulled back from the faithful representation. -/
noncomputable def sourceNorm (z : A.SourceLimit) : ℝ := ‖R.rep z‖

theorem sourceNorm_nonneg (z : A.SourceLimit) : 0 ≤ R.sourceNorm z := norm_nonneg _

/-- **Definiteness of the pulled-back norm**, i.e. faithfulness in normed
form. -/
theorem sourceNorm_eq_zero_iff (z : A.SourceLimit) : R.sourceNorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h0 : R.rep z = 0 := by
      simpa [sourceNorm] using norm_eq_zero.mp h
    have : R.rep z = R.rep 0 := by rw [h0, map_zero]
    exact R.rep_injective this
  · rintro rfl
    simp [sourceNorm]

theorem sourceNorm_mul_le (z w : A.SourceLimit) :
    R.sourceNorm (z * w) ≤ R.sourceNorm z * R.sourceNorm w := by
  simpa [sourceNorm, map_mul] using norm_mul_le (R.rep z) (R.rep w)

theorem sourceNorm_star (z : A.SourceLimit) : R.sourceNorm (star z) = R.sourceNorm z := by
  show ‖R.rep (star z)‖ = ‖R.rep z‖
  rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map _

/-- **The C⋆-identity for the pulled-back norm**, proved from the faithful
representation.  Norm preservation is never assumed. -/
theorem sourceNorm_star_mul_self (z : A.SourceLimit) :
    R.sourceNorm (star z * z) = R.sourceNorm z * R.sourceNorm z := by
  have h : R.rep (star z * z) = star (R.rep z) * R.rep z := by
    rw [map_mul, map_star]
  show ‖R.rep (star z * z)‖ = ‖R.rep z‖ * ‖R.rep z‖
  rw [h, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.norm_adjoint_comp_self _

/-- The additive inverses of the algebraic source limit, which its stagewise
semiring structure does not carry directly, come from its complex module
structure. -/
noncomputable def sourceRing : Ring A.SourceLimit :=
  ringOfComplexAlgebra A.SourceLimit

/-- The pulled-back normed ring structure on the algebraic source limit. -/
noncomputable def sourceNormedRing : NormedRing A.SourceLimit :=
  letI := sourceRing (A := A)
  NormedRing.induced _ _ R.rep R.rep_injective

/-- The pulled-back normed ℂ-algebra structure on the algebraic source limit. -/
noncomputable def sourceNormedAlgebra :
    letI := R.sourceNormedRing
    NormedAlgebra ℂ A.SourceLimit :=
  letI := R.sourceNormedRing
  NormedAlgebra.induced ℂ _ _ R.rep

/-- **The pulled-back structure is a pre-C⋆ structure**: its C⋆-identity is a
theorem, derived from the faithful representation. -/
theorem sourceCStarRing :
    letI := R.sourceNormedRing
    CStarRing A.SourceLimit := by
  letI := R.sourceNormedRing
  refine ⟨fun z => ?_⟩
  exact le_of_eq (R.sourceNorm_star_mul_self z).symm

end SourceConcreteRep

/-! ## 3. The infinite branch -/

/-- **The infinite-coordinate branch.**  The P54 faithful trace-GNS
representation `uhfRep` of the dyadic UHF algebra, transported through the P55B
identification `A.sourceUHFEquiv` of the P53 source limit with that algebra. -/
noncomputable def infiniteSourceRep [Infinite I] : A.SourceConcreteRep where
  rep := uhfRep.comp (StarAlgHomClass.toStarAlgHom A.sourceUHFEquiv)
  rep_injective := uhfRep_injective.comp (EquivLike.injective A.sourceUHFEquiv)

@[simp] theorem infiniteSourceRep_rep [Infinite I] (z : A.SourceLimit) :
    (A.infiniteSourceRep).rep z = uhfRep (A.sourceUHFEquiv z) := rfl

/-- The infinite-branch stage formula: on the image of a stage-`n` element the
representation is the P54 finite-stage representation of the corresponding
dyadic element. -/
theorem infiniteSourceRep_stage [Infinite I] (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    (A.infiniteSourceRep).rep (A.sourceOf n x) =
      uhfStageRep (A.stageCard n) (A.stageUHFEquiv n x) := by
  rw [infiniteSourceRep_rep, A.sourceUHFEquiv_of n x]
  rfl

/-! ## 4. The finite branch -/

/-- **The finite-coordinate branch.**  The P54 faithful finite-stage matrix
representation of the terminal dyadic block, transported through the P55B
terminal-stage identification `A.sourceFiniteEquiv`. -/
noncomputable def finiteSourceRep [Finite I] : A.SourceConcreteRep where
  rep := (uhfStageRep (Nat.card I)).comp (StarAlgHomClass.toStarAlgHom A.sourceFiniteEquiv)
  rep_injective :=
    (uhfStageRep_injective (Nat.card I)).comp (EquivLike.injective A.sourceFiniteEquiv)

@[simp] theorem finiteSourceRep_rep [Finite I] (z : A.SourceLimit) :
    (A.finiteSourceRep).rep z = uhfStageRep (Nat.card I) (A.sourceFiniteEquiv z) := rfl

/-- The finite-branch stage formula, at every stage past the terminal one. -/
theorem finiteSourceRep_stage [Finite I] {n : ℕ} (hn : A.terminalStage ≤ n)
    (x : pauliAlgebra (A.sourceForm n)) :
    (A.finiteSourceRep).rep (A.sourceOf n x) =
      uhfStageRep (Nat.card I)
        (UHFBridge.qubitTensorPowerCongr (A.stageCard_eq_card hn) (A.stageUHFEquiv n x)) := by
  rw [finiteSourceRep_rep, A.sourceFiniteEquiv_of hn]

/-! ## 5. The branch-uniform datum -/

open Classical in
/-- **The uniform branch datum.**  Every field is filled by the constructions of
this file: the finite branch when the coordinate index type is finite, the
infinite branch otherwise. -/
noncomputable def branchSourceRep : A.SourceConcreteRep :=
  if h : Finite I then
    letI := h
    A.finiteSourceRep
  else
    letI : Infinite I := not_finite_iff_infinite.mp h
    A.infiniteSourceRep

theorem branchSourceRep_finite [hI : Finite I] : A.branchSourceRep = A.finiteSourceRep := by
  classical
  rw [branchSourceRep, dif_pos hI]

theorem branchSourceRep_infinite [hI : Infinite I] : A.branchSourceRep = A.infiniteSourceRep := by
  classical
  have h : ¬ Finite I := not_finite_iff_infinite.mpr hI
  rw [branchSourceRep, dif_neg h]

/-- The uniform datum is faithful on the source limit. -/
theorem branchSourceRep_injective : Function.Injective (A.branchSourceRep).rep :=
  (A.branchSourceRep).rep_injective

/-- The uniform datum is faithful on the regional limit. -/
theorem branchTargetRep_injective : Function.Injective (A.branchSourceRep).targetRep :=
  (A.branchSourceRep).targetRep_injective

/-- The canonical embedding of the algebraic source limit into the branch
C⋆-model is injective with dense range. -/
theorem branchSourceEmbedding_injective_denseRange :
    Function.Injective (A.branchSourceRep).sourceEmbedding ∧
      DenseRange (A.branchSourceRep).sourceEmbedding :=
  ⟨(A.branchSourceRep).sourceEmbedding_injective,
    (A.branchSourceRep).sourceEmbedding_denseRange⟩

/-- The canonical embedding of the algebraic regional limit into the branch
C⋆-model is injective with dense range. -/
theorem branchTargetEmbedding_injective_denseRange :
    Function.Injective (A.branchSourceRep).targetEmbedding ∧
      DenseRange (A.branchSourceRep).targetEmbedding :=
  ⟨(A.branchSourceRep).targetEmbedding_injective,
    (A.branchSourceRep).targetEmbedding_denseRange⟩

end AlphaData

/-! ## 6. Non-vacuity -/

/-- **Non-vacuity of the infinite branch.**  The P53 tautological
`standardAlphaData` on the lattice `ℕ` has an infinite coordinate index type, so
its branch datum is the constructed infinite branch. -/
theorem standardAlphaData_branchSourceRep :
    standardAlphaData.branchSourceRep = standardAlphaData.infiniteSourceRep :=
  AlphaData.branchSourceRep_infinite _

/-- **Non-vacuity, faithful form.**  For the tautological data the source and
regional representations are faithful and the two canonical embeddings into the
closed operator ranges are injective with dense range. -/
theorem standardAlphaData_concrete :
    Function.Injective (standardAlphaData.branchSourceRep).rep ∧
      Function.Injective (standardAlphaData.branchSourceRep).targetRep ∧
      Function.Injective (standardAlphaData.branchSourceRep).sourceEmbedding ∧
      DenseRange (standardAlphaData.branchSourceRep).sourceEmbedding ∧
      Function.Injective (standardAlphaData.branchSourceRep).targetEmbedding ∧
      DenseRange (standardAlphaData.branchSourceRep).targetEmbedding :=
  ⟨AlphaData.branchSourceRep_injective _, AlphaData.branchTargetRep_injective _,
    (standardAlphaData.branchSourceRep).sourceEmbedding_injective,
    (standardAlphaData.branchSourceRep).sourceEmbedding_denseRange,
    (standardAlphaData.branchSourceRep).targetEmbedding_injective,
    (standardAlphaData.branchSourceRep).targetEmbedding_denseRange⟩

end LocalHyperbolicAlpha

end StabilizerHyperfinite
