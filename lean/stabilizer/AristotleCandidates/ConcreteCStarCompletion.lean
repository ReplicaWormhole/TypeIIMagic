import Mathlib

/-!
# A concrete C⋆-completion from an isometric operator representation

**Context declaration.** Infrastructure only: reusable Lean infrastructure; no
manuscript claim.

Let `A` be a normed complex `*`-algebra satisfying the C⋆-identity (a
*pre*-C⋆-algebra: completeness of `A` is *not* assumed) and let `H` be a complex
Hilbert space.  An `OperatorRepresentation A H` is an explicitly supplied pair

* `rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)`, a complex star-algebra homomorphism into the
  bounded operators on `H`, together with
* `norm_rho : ∀ a, ‖rho a‖ = ‖a‖`, the hypothesis that `rho` is norm preserving.

Both are fields of the structure, so every statement below is explicitly
conditional on them.

From this data we build the **concrete** C⋆-completion

`OperatorRepresentation.rangeClosure R = (rho.range).topologicalClosure`,

the closure of the operator range inside `H →L[ℂ] H`.  It is a closed
star-subalgebra of a C⋆-algebra, hence carries a genuine `CStarAlgebra`
instance (`StarSubalgebra.cstarAlgebra`).  Nothing here repackages an arbitrary
ambient C⋆-algebra: the ambient object *is* the closed operator range inside the
bounded operators on `H`.

## Main results

* `OperatorRepresentation.embedding : A →⋆ₐ[ℂ] R.rangeClosure` — the canonical
  complex star-algebra homomorphism, with `coe_embedding` identifying it with
  `rho`;
* `OperatorRepresentation.norm_embedding`, `isometry_embedding`,
  `injective_embedding` — it is isometric, hence injective;
* `OperatorRepresentation.denseRange_embedding` — its range is dense in
  `R.rangeClosure`;
* `OperatorRepresentation.rangeClosure_le` and
  `OperatorRepresentation.rangeClosure_isLeast` — minimality among closed
  star-subalgebras of `H →L[ℂ] H` containing the operator range;
* `existsUnique_starAlgEquiv` — for two isometric representations `R₁`, `R₂` of
  the *same* `A` (on possibly different Hilbert spaces) there is a *unique*
  continuous star-algebra equivalence
  `R₁.rangeClosure ≃⋆ₐ[ℂ] R₂.rangeClosure` compatible with the two canonical
  embeddings; it is moreover isometric (`isometry_comparison`).

The uniqueness/existence statement is powered by a general extension section
(`extendAlongDenseRange`, `extendStarAlgHom`), which extends an isometric
star-algebra homomorphism `j : A →⋆ₐ[ℂ] Y` along an isometric star-algebra
homomorphism `i : A →⋆ₐ[ℂ] X` with dense range, `X` and `Y` being C⋆-algebras.

## What is *not* claimed

No von Neumann algebra, bicommutant, GNS state identity, tensor product, factor
classification, trace or weight, and no gLU or refinement statement appears
here.
-/

namespace Formalization
namespace ConcreteCStarCompletion

open scoped Topology

/-! ## Extension of a star-algebra homomorphism along a dense isometric image -/

section Extension

variable {A X Y : Type*}
  [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
  [CStarAlgebra X] [CStarAlgebra Y]
  {i : A →⋆ₐ[ℂ] X} {j : A →⋆ₐ[ℂ] Y}

/-- A star-algebra homomorphism which preserves norms is an isometry. -/
theorem isometry_of_norm_map (f : A →⋆ₐ[ℂ] X) (hf : ∀ a, ‖f a‖ = ‖a‖) : Isometry f :=
  AddMonoidHomClass.isometry_of_norm f hf

/-- An isometric star-algebra homomorphism preserves norms. -/
theorem norm_map_of_isometry (f : A →⋆ₐ[ℂ] X) (hf : Isometry f) (a : A) : ‖f a‖ = ‖a‖ :=
  hf.norm_map_of_map_zero (map_zero f) a

/-- Two continuous maps out of `X` which agree on the dense image of `i` are equal. -/
theorem eq_of_continuous_of_eq_comp (hd : DenseRange i) {Z : Type*} [TopologicalSpace Z]
    [T2Space Z] {f g : X → Z} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ a, f (i a) = g (i a)) : f = g :=
  Continuous.ext_on hd hf hg (by rintro _ ⟨a, rfl⟩; exact h a)

/-- Two continuous binary operations which agree on the dense image of `i` are equal. -/
theorem eq_of_continuous₂_of_eq_comp (hd : DenseRange i) {Z : Type*} [TopologicalSpace Z]
    [T2Space Z] {f g : X → X → Z} (hf : Continuous fun p : X × X => f p.1 p.2)
    (hg : Continuous fun p : X × X => g p.1 p.2) (h : ∀ a b, f (i a) (i b) = g (i a) (i b))
    (x y : X) : f x y = g x y := by
  have hfun : (fun p : X × X => f p.1 p.2) = fun p : X × X => g p.1 p.2 :=
    Continuous.ext_on (hd.prodMap hd) hf hg (by rintro _ ⟨⟨a, b⟩, rfl⟩; exact h a b)
  exact congrFun hfun (x, y)

/-- The extension of `j : A →⋆ₐ[ℂ] Y` to `X`, along an isometric star-algebra homomorphism
`i : A →⋆ₐ[ℂ] X` with dense range. -/
noncomputable def extendAlongDenseRange (hi : Isometry i) (hd : DenseRange i)
    (j : A →⋆ₐ[ℂ] Y) : X → Y :=
  IsDenseInducing.extend (hi.isUniformInducing.isDenseInducing hd) j

variable (hi : Isometry i) (hd : DenseRange i) (hj : Isometry j)

include hj in
theorem extendAlongDenseRange_apply (a : A) : extendAlongDenseRange hi hd j (i a) = j a :=
  uniformly_extend_of_ind hi.isUniformInducing hd hj.uniformContinuous a

include hj in
theorem continuous_extendAlongDenseRange : Continuous (extendAlongDenseRange hi hd j) :=
  (uniformContinuous_uniformly_extend hi.isUniformInducing hd hj.uniformContinuous).continuous

include hj in
theorem extendAlongDenseRange_add (x y : X) :
    extendAlongDenseRange hi hd j (x + y) =
      extendAlongDenseRange hi hd j x + extendAlongDenseRange hi hd j y := by
  have hc := continuous_extendAlongDenseRange hi hd hj
  refine eq_of_continuous₂_of_eq_comp hd (f := fun x y => extendAlongDenseRange hi hd j (x + y))
    (g := fun x y => extendAlongDenseRange hi hd j x + extendAlongDenseRange hi hd j y)
    (hc.comp (continuous_fst.add continuous_snd))
    ((hc.comp continuous_fst).add (hc.comp continuous_snd)) (fun a b => ?_) x y
  dsimp only
  rw [← map_add i, extendAlongDenseRange_apply hi hd hj, extendAlongDenseRange_apply hi hd hj,
    extendAlongDenseRange_apply hi hd hj, map_add j]

include hj in
theorem extendAlongDenseRange_mul (x y : X) :
    extendAlongDenseRange hi hd j (x * y) =
      extendAlongDenseRange hi hd j x * extendAlongDenseRange hi hd j y := by
  have hc := continuous_extendAlongDenseRange hi hd hj
  refine eq_of_continuous₂_of_eq_comp hd (f := fun x y => extendAlongDenseRange hi hd j (x * y))
    (g := fun x y => extendAlongDenseRange hi hd j x * extendAlongDenseRange hi hd j y)
    (hc.comp (continuous_fst.mul continuous_snd))
    ((hc.comp continuous_fst).mul (hc.comp continuous_snd)) (fun a b => ?_) x y
  dsimp only
  rw [← map_mul i, extendAlongDenseRange_apply hi hd hj, extendAlongDenseRange_apply hi hd hj,
    extendAlongDenseRange_apply hi hd hj, map_mul j]

include hj in
theorem extendAlongDenseRange_smul (c : ℂ) (x : X) :
    extendAlongDenseRange hi hd j (c • x) = c • extendAlongDenseRange hi hd j x := by
  have hc := continuous_extendAlongDenseRange hi hd hj
  refine congrFun (eq_of_continuous_of_eq_comp hd
    (f := fun x => extendAlongDenseRange hi hd j (c • x))
    (g := fun x => c • extendAlongDenseRange hi hd j x)
    (hc.comp (continuous_const_smul c)) ((continuous_const_smul c).comp hc) (fun a => ?_)) x
  dsimp only
  rw [← map_smul i, extendAlongDenseRange_apply hi hd hj, extendAlongDenseRange_apply hi hd hj,
    map_smul j]

include hj in
theorem extendAlongDenseRange_star (x : X) :
    extendAlongDenseRange hi hd j (star x) = star (extendAlongDenseRange hi hd j x) := by
  have hc := continuous_extendAlongDenseRange hi hd hj
  refine congrFun (eq_of_continuous_of_eq_comp hd
    (f := fun x => extendAlongDenseRange hi hd j (star x))
    (g := fun x => star (extendAlongDenseRange hi hd j x))
    (hc.comp continuous_star) (continuous_star.comp hc) (fun a => ?_)) x
  dsimp only
  rw [← map_star i, extendAlongDenseRange_apply hi hd hj, extendAlongDenseRange_apply hi hd hj,
    map_star j]

include hj in
theorem norm_extendAlongDenseRange (x : X) : ‖extendAlongDenseRange hi hd j x‖ = ‖x‖ := by
  have hc := continuous_extendAlongDenseRange hi hd hj
  refine congrFun (eq_of_continuous_of_eq_comp hd
    (f := fun x => ‖extendAlongDenseRange hi hd j x‖) (g := fun x => ‖x‖)
    (continuous_norm.comp hc) continuous_norm (fun a => ?_)) x
  dsimp only
  rw [extendAlongDenseRange_apply hi hd hj, norm_map_of_isometry j hj,
    norm_map_of_isometry i hi]

include hj in
/-- The extension, bundled as a complex star-algebra homomorphism `X →⋆ₐ[ℂ] Y`. -/
noncomputable def extendStarAlgHom : X →⋆ₐ[ℂ] Y where
  toFun := extendAlongDenseRange hi hd j
  map_one' := by
    rw [← map_one i, extendAlongDenseRange_apply hi hd hj, map_one j]
  map_mul' := extendAlongDenseRange_mul hi hd hj
  map_zero' := by
    rw [← map_zero i, extendAlongDenseRange_apply hi hd hj, map_zero j]
  map_add' := extendAlongDenseRange_add hi hd hj
  commutes' r := by
    rw [← AlgHomClass.commutes i r, extendAlongDenseRange_apply hi hd hj,
      AlgHomClass.commutes j r]
  map_star' := extendAlongDenseRange_star hi hd hj

@[simp] theorem extendStarAlgHom_coe :
    ⇑(extendStarAlgHom hi hd hj) = extendAlongDenseRange hi hd j := rfl

@[simp] theorem extendStarAlgHom_apply (a : A) : extendStarAlgHom hi hd hj (i a) = j a :=
  extendAlongDenseRange_apply hi hd hj a

include hj in
theorem norm_extendStarAlgHom (x : X) : ‖extendStarAlgHom hi hd hj x‖ = ‖x‖ :=
  norm_extendAlongDenseRange hi hd hj x

include hj in
theorem isometry_extendStarAlgHom : Isometry (extendStarAlgHom hi hd hj) :=
  isometry_of_norm_map _ (norm_extendAlongDenseRange hi hd hj)

include hj in
theorem injective_extendStarAlgHom : Function.Injective (extendStarAlgHom hi hd hj) :=
  (isometry_extendStarAlgHom hi hd hj).injective

include hj in
theorem surjective_extendStarAlgHom (hjd : DenseRange j) :
    Function.Surjective (extendStarAlgHom hi hd hj) := by
  have hclosed : IsClosed (Set.range (extendStarAlgHom hi hd hj)) :=
    ((isometry_extendStarAlgHom hi hd hj).isUniformInducing.isComplete_range).isClosed
  have hsub : Set.range ⇑j ⊆ Set.range ⇑(extendStarAlgHom hi hd hj) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨i a, extendStarAlgHom_apply hi hd hj a⟩
  have huniv : (Set.univ : Set Y) ⊆ Set.range ⇑(extendStarAlgHom hi hd hj) := by
    rw [← hjd.closure_range]
    exact hclosed.closure_subset_iff.mpr hsub
  exact fun y => huniv (Set.mem_univ y)

include hj in
/-- The extension is a star-algebra equivalence as soon as `j` also has dense range. -/
noncomputable def extendStarAlgEquiv (hjd : DenseRange j) : X ≃⋆ₐ[ℂ] Y :=
  StarAlgEquiv.ofBijective (extendStarAlgHom hi hd hj)
    ⟨injective_extendStarAlgHom hi hd hj, surjective_extendStarAlgHom hi hd hj hjd⟩

@[simp] theorem extendStarAlgEquiv_apply (hjd : DenseRange j) (a : A) :
    extendStarAlgEquiv hi hd hj hjd (i a) = j a :=
  extendStarAlgHom_apply hi hd hj a

include hj in
theorem continuous_extendStarAlgEquiv (hjd : DenseRange j) :
    Continuous (extendStarAlgEquiv hi hd hj hjd) :=
  continuous_extendAlongDenseRange hi hd hj

include hj in
theorem isometry_extendStarAlgEquiv (hjd : DenseRange j) :
    Isometry (extendStarAlgEquiv hi hd hj hjd) :=
  isometry_extendStarAlgHom hi hd hj

end Extension

/-! ## The concrete completion of an isometric operator representation -/

/-- An explicitly supplied isometric complex star-algebra representation of a normed
complex `*`-algebra `A` on the bounded operators of a Hilbert space `H`.  Both the
representation and the isometry hypothesis are fields, so all conclusions drawn below are
conditional on them. -/
structure OperatorRepresentation (A : Type*) (H : Type*)
    [NormedRing A] [StarRing A] [NormedAlgebra ℂ A] [CStarRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The representation, a complex star-algebra homomorphism into bounded operators. -/
  rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)
  /-- The supplied hypothesis that the representation is norm preserving. -/
  norm_rho : ∀ a, ‖rho a‖ = ‖a‖

namespace OperatorRepresentation

variable {A H : Type*}
  [NormedRing A] [StarRing A] [NormedAlgebra ℂ A] [CStarRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : OperatorRepresentation A H)

/-- The concrete completion: the closure of the operator range inside `H →L[ℂ] H`. -/
noncomputable def rangeClosure : StarSubalgebra ℂ (H →L[ℂ] H) := R.rho.range.topologicalClosure

instance instIsClosedRangeClosure :
    IsClosed ((R.rangeClosure : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :=
  R.rho.range.isClosed_topologicalClosure

/-- The closed operator range is a genuine C⋆-algebra. -/
noncomputable instance instCStarAlgebraRangeClosure : CStarAlgebra R.rangeClosure :=
  StarSubalgebra.cstarAlgebra _

theorem rho_mem_rangeClosure (a : A) : R.rho a ∈ R.rangeClosure :=
  R.rho.range.le_topologicalClosure ⟨a, rfl⟩

/-- The canonical embedding of `A` into its concrete C⋆-completion; by construction a
complex star-algebra homomorphism. -/
noncomputable def embedding : A →⋆ₐ[ℂ] R.rangeClosure :=
  R.rho.codRestrict R.rangeClosure R.rho_mem_rangeClosure

@[simp] theorem coe_embedding (a : A) : (R.embedding a : H →L[ℂ] H) = R.rho a := rfl

theorem norm_embedding (a : A) : ‖R.embedding a‖ = ‖a‖ := R.norm_rho a

theorem isometry_embedding : Isometry R.embedding :=
  isometry_of_norm_map _ R.norm_embedding

theorem injective_embedding : Function.Injective R.embedding :=
  R.isometry_embedding.injective

/-- The image of `A` is dense in the concrete completion. -/
theorem denseRange_embedding : DenseRange R.embedding := by
  have hcoe : ((R.rangeClosure : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))
      = closure (Set.range ⇑R.rho) := by
    rw [rangeClosure, StarSubalgebra.topologicalClosure_coe]
    rfl
  rw [DenseRange, Subtype.dense_iff]
  intro x hx
  rw [hcoe] at hx
  refine closure_mono ?_ hx
  rintro _ ⟨a, rfl⟩
  exact ⟨R.embedding a, ⟨a, rfl⟩, rfl⟩

/-- Minimality: the concrete completion is contained in every closed star-subalgebra of
`H →L[ℂ] H` containing the operator range. -/
theorem rangeClosure_le {S : StarSubalgebra ℂ (H →L[ℂ] H)} (hS : IsClosed (S : Set (H →L[ℂ] H)))
    (hrange : ∀ a, R.rho a ∈ S) : R.rangeClosure ≤ S :=
  StarSubalgebra.topologicalClosure_minimal (by rintro _ ⟨a, rfl⟩; exact hrange a) hS

/-- The concrete completion is the *least* closed star-subalgebra of `H →L[ℂ] H` containing
the operator range. -/
theorem rangeClosure_isLeast :
    IsLeast {S : StarSubalgebra ℂ (H →L[ℂ] H) |
        IsClosed (S : Set (H →L[ℂ] H)) ∧ ∀ a, R.rho a ∈ S} R.rangeClosure :=
  ⟨⟨R.instIsClosedRangeClosure, R.rho_mem_rangeClosure⟩,
    fun _ hS => R.rangeClosure_le hS.1 hS.2⟩

/-- Non-vacuity of the hypotheses: the identity representation of the C⋆-algebra of bounded
operators on a Hilbert space `H` on itself is an `OperatorRepresentation`. -/
noncomputable def id (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : OperatorRepresentation (H →L[ℂ] H) H where
  rho := StarAlgHom.id ℂ (H →L[ℂ] H)
  norm_rho _ := rfl

end OperatorRepresentation

/-! ## Uniqueness of the concrete completion -/

section Uniqueness

variable {A H₁ H₂ : Type*}
  [NormedRing A] [StarRing A] [NormedAlgebra ℂ A] [CStarRing A]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  (R₁ : OperatorRepresentation A H₁) (R₂ : OperatorRepresentation A H₂)

/-- The comparison star-algebra equivalence between two concrete completions of the same
pre-C⋆-algebra. -/
noncomputable def comparison : R₁.rangeClosure ≃⋆ₐ[ℂ] R₂.rangeClosure :=
  extendStarAlgEquiv R₁.isometry_embedding R₁.denseRange_embedding R₂.isometry_embedding
    R₂.denseRange_embedding

@[simp] theorem comparison_embedding (a : A) :
    comparison R₁ R₂ (R₁.embedding a) = R₂.embedding a :=
  extendStarAlgEquiv_apply _ _ _ _ a

theorem continuous_comparison : Continuous (comparison R₁ R₂) :=
  continuous_extendStarAlgEquiv _ _ _ _

theorem isometry_comparison : Isometry (comparison R₁ R₂) :=
  isometry_extendStarAlgEquiv _ _ _ _

/-- Two concrete completions of the same pre-C⋆-algebra are *uniquely* equivalent: there is
exactly one continuous star-algebra equivalence intertwining the canonical embeddings. -/
theorem existsUnique_starAlgEquiv :
    ∃! e : R₁.rangeClosure ≃⋆ₐ[ℂ] R₂.rangeClosure,
      Continuous e ∧ ∀ a, e (R₁.embedding a) = R₂.embedding a := by
  refine ⟨comparison R₁ R₂, ⟨continuous_comparison R₁ R₂, comparison_embedding R₁ R₂⟩, ?_⟩
  rintro e ⟨hcont, hemb⟩
  have hfun : ⇑e = ⇑(comparison R₁ R₂) :=
    eq_of_continuous_of_eq_comp R₁.denseRange_embedding hcont (continuous_comparison R₁ R₂)
      (fun a => by rw [hemb a, comparison_embedding])
  exact DFunLike.coe_injective hfun

end Uniqueness

end ConcreteCStarCompletion
end Formalization
