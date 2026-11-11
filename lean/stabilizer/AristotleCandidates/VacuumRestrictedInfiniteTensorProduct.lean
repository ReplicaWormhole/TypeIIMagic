/-
P57A — vacuum-restricted infinite-tensor pre-Hilbert core.

**Context declaration: Infrastructure only.**  This file makes no manuscript
claim.  It develops, from scratch and entirely inside this repository, the
*algebraic* (finite-support) part of the vacuum-restricted infinite tensor
product of a family of complex inner-product spaces:

* `VacuumTensor Ω` — elementary tensors which agree with the reference
  ("vacuum") vector `Ω i` outside a finite set of active modes;
* `kern` — the finite-product kernel `∏ ⟪v i, w i⟫`, computed over the union of
  the two active sets;
* `ITPSpan Ω` — the free complex vector space on elementary tensors (the
  algebraic finite span);
* `itpInner` — the sesquilinear extension of `kern` to `ITPSpan Ω`;
* `exists_finiteMode_realization` — *finite-mode realization*: for any finite
  family of elementary tensors and any finite mode set `s` containing their
  active sets, all pairings are realized as inner products in a genuinely
  finite-dimensional (finite-mode) tensor-product Hilbert space
  `EuclideanSpace ℂ (∀ i : s, Fin (m i))`;
* `itpInner_nonneg` — positivity on an arbitrary finite linear combination,
  together with conjugate symmetry, additivity and scalar compatibility;
* `itpCore` — the exported `PreInnerProductSpace.Core ℂ (ITPSpan Ω)`;
* `vacuumVector` — the algebraic vacuum, with `⟪Ω, Ω⟫ = 1`.

**Deliberate boundary.**  The construction stops before the quotient by the
null space and before any completion.  Nothing here asserts the existence of a
completed infinite tensor-product Hilbert space, a tensor-factor GNS theorem,
or a spatial von Neumann tensor product; no axiom, `sorry`, or interface
wrapper is used.

**Note on provenance.**  The packet nominates
`bound_beating/formalize_itp/Formalization/InfiniteTensorProductHilbert.lean` as the local source model.
A local closeout comparison confirmed that this module independently re-expresses its proved
finite-support core against this repository's pinned Mathlib.  No external project is imported,
and none of the excluded wrappers
(`VacuumRestrictedITPInnerProductAxioms`, `ITPCompletionAxioms`,
`canonicalVacuumRestrictedITPInnerProductAxioms`) appear here in any form.

**Note on the finite tensor model.**  The pinned Mathlib provides an inner
product space structure on the *binary* tensor product only
(`Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`); there is no inner
product on `PiTensorProduct`, and no Schur (Hadamard) product theorem for
positive semidefinite matrices.  The finite-mode realization below therefore
uses the concrete finite tensor-product model
`EuclideanSpace ℂ (∀ i : s, Fin (m i)) ≃ ⨂_{i ∈ s} EuclideanSpace ℂ (Fin (m i))`,
obtained from per-mode orthonormal coordinates.  This is a proved statement,
not an assumption, and it is exactly what positivity requires.
-/
import Mathlib

open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace AristotleCandidates
namespace VacuumRestrictedITP

universe u v

/-! ## Finite Gram coordinates in a single mode -/

/-- Every finite family of vectors in a complex inner-product space admits finitely many
coordinates reproducing its Gram matrix: this is the coordinate form of the fact that the
family spans a finite-dimensional subspace, which carries an orthonormal basis. -/
theorem exists_gram_coords {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {n : Type*} [Fintype n] (u : n → F) :
    ∃ (m : ℕ) (lam : n → Fin m → ℂ), ∀ a b, ⟪u a, u b⟫_ℂ = ∑ k, conj (lam a k) * lam b k := by
  classical
  set W := Submodule.span ℂ (Set.range u) with hW
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  set b := stdOrthonormalBasis ℂ W with hb
  have hmem : ∀ a, u a ∈ W := fun a => Submodule.subset_span ⟨a, rfl⟩
  refine ⟨Module.finrank ℂ W, fun a k => ⟪b k, (⟨u a, hmem a⟩ : W)⟫_ℂ, ?_⟩
  intro a c
  have h := b.sum_inner_mul_inner (⟨u a, hmem a⟩ : W) (⟨u c, hmem c⟩ : W)
  have hco : ⟪u a, u c⟫_ℂ = ⟪(⟨u a, hmem a⟩ : W), (⟨u c, hmem c⟩ : W)⟫_ℂ := rfl
  rw [hco, ← h]
  exact Finset.sum_congr rfl fun k _ => by rw [inner_conj_symm]

variable {ι : Type u} {E : ι → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

/-! ## Finite-mode realization -/

/-- **Finite-mode realization.**  Given finitely many families of vectors `u a : ∀ i, E i` and a
finite mode set `s`, there is a finite tensor-product Hilbert space
`EuclideanSpace ℂ (∀ i : s, Fin (m i))` and vectors `Φ a` in it whose inner products are exactly
the finite mode products `∏ i ∈ s, ⟪u a i, u b i⟫`. -/
theorem exists_finiteMode_realization {n : Type*} [Fintype n] (s : Finset ι) (u : n → ∀ i, E i) :
    ∃ (K : Type u) (_ : Fintype K) (Φ : n → EuclideanSpace ℂ K),
      ∀ a b, ⟪Φ a, Φ b⟫_ℂ = ∏ i ∈ s, ⟪u a i, u b i⟫_ℂ := by
  classical
  choose m lam hlam using fun i => exists_gram_coords (fun a => u a i)
  refine ⟨(∀ i : s, Fin (m i)), inferInstance,
    fun a => WithLp.toLp 2 (fun κ => ∏ i : s, lam i a (κ i)), ?_⟩
  intro a b
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  rw [← Finset.prod_coe_sort s (fun i => ⟪u a i, u b i⟫_ℂ)]
  have hco : ∀ i : s, ⟪u a i, u b i⟫_ℂ = ∑ k, conj (lam i a k) * lam i b k := fun i => hlam i a b
  simp_rw [hco]
  rw [Fintype.prod_sum (fun (i : s) (k : Fin (m i)) => conj (lam i a k) * lam i b k)]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun x _ => mul_comm _ _

/-- **Positivity of the finite mode kernel on an arbitrary finite linear combination.**
This is the Schur-product-type statement underlying positivity of the infinite tensor product
inner product; it is deduced from the finite-mode realization. -/
theorem sum_prod_inner_nonneg {n : Type*} [Fintype n] (s : Finset ι) (u : n → ∀ i, E i)
    (c : n → ℂ) :
    0 ≤ ∑ a, ∑ b, conj (c a) * c b * ∏ i ∈ s, ⟪u a i, u b i⟫_ℂ := by
  obtain ⟨K, _, Φ, hΦ⟩ := exists_finiteMode_realization s u
  have key : ∑ a, ∑ b, conj (c a) * c b * ∏ i ∈ s, ⟪u a i, u b i⟫_ℂ
      = ⟪∑ a, c a • Φ a, ∑ b, c b • Φ b⟫_ℂ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [inner_smul_left, inner_smul_right, hΦ]
    ring
  rw [key]
  exact CStarModule.inner_self_nonneg

/-! ## Vacuum-restricted elementary tensors -/

/-- A vacuum-restricted elementary tensor: a choice of vector in each mode, equal to the
reference vector `Ω i` outside a finite set of active modes. -/
structure VacuumTensor (Ω : ∀ i, E i) where
  /-- The vector chosen in each mode. -/
  vec : ∀ i, E i
  /-- A finite set of modes outside of which the tensor is the reference vector. -/
  active : Finset ι
  /-- Outside `active` the tensor agrees with the reference vector. -/
  vec_eq_vacuum : ∀ i ∉ active, vec i = Ω i

variable {Ω : ∀ i, E i}

/-- The vacuum elementary tensor. -/
def VacuumTensor.vacuum (Ω : ∀ i, E i) : VacuumTensor Ω :=
  ⟨Ω, ∅, fun _ _ => rfl⟩

omit [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] in
@[simp] theorem VacuumTensor.vacuum_vec (i : ι) : (VacuumTensor.vacuum Ω).vec i = Ω i := rfl

omit [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] in
@[simp] theorem VacuumTensor.vacuum_active :
    (VacuumTensor.vacuum Ω).active = (∅ : Finset ι) := rfl

variable [DecidableEq ι]

/-- The finite-product kernel of two vacuum-restricted elementary tensors, computed over the
union of their active mode sets. -/
noncomputable def kern (v w : VacuumTensor Ω) : ℂ :=
  ∏ i ∈ v.active ∪ w.active, ⟪v.vec i, w.vec i⟫_ℂ

/-- The kernel may be computed over any finite mode set containing both active sets:
outside the active sets both entries are the unit reference vector. -/
theorem kern_eq_prod_of_subset (hΩ : ∀ i, ⟪Ω i, Ω i⟫_ℂ = 1) {v w : VacuumTensor Ω} {s : Finset ι}
    (hv : v.active ⊆ s) (hw : w.active ⊆ s) :
    kern v w = ∏ i ∈ s, ⟪v.vec i, w.vec i⟫_ℂ := by
  refine Finset.prod_subset (Finset.union_subset hv hw) ?_
  intro i _ hi
  rw [Finset.mem_union, not_or] at hi
  rw [v.vec_eq_vacuum i hi.1, w.vec_eq_vacuum i hi.2, hΩ i]

@[simp] theorem kern_vacuum_vacuum :
    kern (VacuumTensor.vacuum Ω) (VacuumTensor.vacuum Ω) = 1 := by
  simp [kern]

/-- Conjugate symmetry of the kernel. -/
theorem conj_kern (v w : VacuumTensor Ω) : conj (kern w v) = kern v w := by
  rw [kern, kern, map_prod, Finset.union_comm]
  exact Finset.prod_congr rfl fun i _ => inner_conj_symm _ _

/-! ## The algebraic span and its sesquilinear form -/

/-- The algebraic finite span of the vacuum-restricted elementary tensors: the free complex
vector space on `VacuumTensor Ω`. -/
abbrev ITPSpan (Ω : ∀ i, E i) := VacuumTensor Ω →₀ ℂ

/-- The sesquilinear extension of the kernel to the algebraic span, conjugate linear in the
first variable (Mathlib's convention). -/
noncomputable def itpInner (x y : ITPSpan Ω) : ℂ :=
  ∑ v ∈ x.support, ∑ w ∈ y.support, conj (x v) * y w * kern v w

/-- The defining double sum may be taken over any pair of finite sets containing the two
supports. -/
theorem itpInner_eq_sum₂ {x y : ITPSpan Ω} {t₁ t₂ : Finset (VacuumTensor Ω)}
    (hx : x.support ⊆ t₁) (hy : y.support ⊆ t₂) :
    itpInner x y = ∑ v ∈ t₁, ∑ w ∈ t₂, conj (x v) * y w * kern v w := by
  have inner_ext : ∀ v : VacuumTensor Ω,
      ∑ w ∈ y.support, conj (x v) * y w * kern v w
        = ∑ w ∈ t₂, conj (x v) * y w * kern v w := by
    intro v
    refine Finset.sum_subset hy ?_
    intro w _ hw
    rw [Finsupp.notMem_support_iff.mp hw]
    ring
  rw [itpInner]
  rw [Finset.sum_congr rfl fun v _ => inner_ext v]
  refine Finset.sum_subset hx ?_
  intro v _ hv
  rw [Finsupp.notMem_support_iff.mp hv]
  simp

/-- The defining double sum may be taken over any finite set containing both supports. -/
theorem itpInner_eq_sum {x y : ITPSpan Ω} {t : Finset (VacuumTensor Ω)}
    (hx : x.support ⊆ t) (hy : y.support ⊆ t) :
    itpInner x y = ∑ v ∈ t, ∑ w ∈ t, conj (x v) * y w * kern v w :=
  itpInner_eq_sum₂ hx hy

/-- The sesquilinear form on elementary tensors is the kernel. -/
@[simp] theorem itpInner_single (v w : VacuumTensor Ω) (a b : ℂ) :
    itpInner (Finsupp.single v a) (Finsupp.single w b) = conj a * b * kern v w := by
  rw [itpInner_eq_sum₂ (t₁ := {v}) (t₂ := {w}) Finsupp.support_single_subset
    Finsupp.support_single_subset]
  simp

/-- Conjugate symmetry of the sesquilinear extension. -/
theorem conj_itpInner_symm (x y : ITPSpan Ω) : conj (itpInner y x) = itpInner x y := by
  classical
  set t := x.support ∪ y.support with ht
  have hx : x.support ⊆ t := Finset.subset_union_left
  have hy : y.support ⊆ t := Finset.subset_union_right
  rw [itpInner_eq_sum hy hx, itpInner_eq_sum hx hy, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul, map_mul, conj_kern, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

/-- Additivity in the first variable. -/
theorem itpInner_add_left (x y z : ITPSpan Ω) :
    itpInner (x + y) z = itpInner x z + itpInner y z := by
  classical
  set t := (x.support ∪ y.support) ∪ z.support with ht
  have hx : x.support ⊆ t := (Finset.subset_union_left).trans Finset.subset_union_left
  have hy : y.support ⊆ t := (Finset.subset_union_right).trans Finset.subset_union_left
  have hz : z.support ⊆ t := Finset.subset_union_right
  have hxy : (x + y).support ⊆ t := (Finsupp.support_add).trans (Finset.union_subset hx hy)
  rw [itpInner_eq_sum hxy hz, itpInner_eq_sum hx hz, itpInner_eq_sum hy hz, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.add_apply, map_add]
  ring

/-- Scalar compatibility (conjugate linearity in the first variable). -/
theorem itpInner_smul_left (x y : ITPSpan Ω) (r : ℂ) :
    itpInner (r • x) y = conj r * itpInner x y := by
  classical
  set t := x.support ∪ y.support with ht
  have hx : x.support ⊆ t := Finset.subset_union_left
  have hy : y.support ⊆ t := Finset.subset_union_right
  have hrx : (r • x).support ⊆ t := (Finsupp.support_smul).trans hx
  rw [itpInner_eq_sum hrx hy, itpInner_eq_sum hx hy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, map_mul]
  ring

/-- **Positivity on an arbitrary finite linear combination** of vacuum-restricted elementary
tensors. -/
theorem itpInner_nonneg (hΩ : ∀ i, ⟪Ω i, Ω i⟫_ℂ = 1) (x : ITPSpan Ω) : 0 ≤ itpInner x x := by
  classical
  set t := x.support with ht
  set s : Finset ι := t.sup VacuumTensor.active with hs
  have hact : ∀ v ∈ t, v.active ⊆ s := fun v hv => Finset.le_sup (f := VacuumTensor.active) hv
  have hkern : ∀ v ∈ t, ∀ w ∈ t,
      kern v w = ∏ i ∈ s, ⟪v.vec i, w.vec i⟫_ℂ :=
    fun v hv w hw => kern_eq_prod_of_subset hΩ (hact v hv) (hact w hw)
  have hsum : itpInner x x
      = ∑ v : t, ∑ w : t, conj (x (v : VacuumTensor Ω)) * x (w : VacuumTensor Ω)
          * ∏ i ∈ s, ⟪(v : VacuumTensor Ω).vec i, (w : VacuumTensor Ω).vec i⟫_ℂ := by
    rw [itpInner]
    rw [← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hkern _ v.2 _ w.2]
  rw [hsum]
  exact sum_prod_inner_nonneg s (fun v : t => (v : VacuumTensor Ω).vec)
    (fun v : t => x (v : VacuumTensor Ω))

/-- Positivity in the real-part form required by `PreInnerProductSpace.Core`. -/
theorem re_itpInner_nonneg (hΩ : ∀ i, ⟪Ω i, Ω i⟫_ℂ = 1) (x : ITPSpan Ω) :
    0 ≤ RCLike.re (itpInner x x) := by
  have h := itpInner_nonneg hΩ x
  simpa using (Complex.le_def.mp h).1

/-- **The exported pre-inner-product core** on the algebraic span of vacuum-restricted
elementary tensors.  No quotient and no completion is taken. -/
noncomputable def itpCore (hΩ : ∀ i, ⟪Ω i, Ω i⟫_ℂ = 1) :
    PreInnerProductSpace.Core ℂ (ITPSpan Ω) where
  inner := itpInner
  conj_inner_symm := conj_itpInner_symm
  re_inner_nonneg := re_itpInner_nonneg hΩ
  add_left := itpInner_add_left
  smul_left := itpInner_smul_left

@[simp] theorem itpCore_inner (hΩ : ∀ i, ⟪Ω i, Ω i⟫_ℂ = 1) (x y : ITPSpan Ω) :
    (itpCore hΩ).inner x y = itpInner x y := rfl

/-! ## The algebraic vacuum vector -/

/-- The algebraic vacuum vector of the vacuum-restricted infinite tensor product. -/
noncomputable def vacuumVector (Ω : ∀ i, E i) : ITPSpan Ω :=
  Finsupp.single (VacuumTensor.vacuum Ω) 1

/-- The algebraic vacuum has norm square one.  (The normalization hypothesis
`⟪Ω i, Ω i⟫ = 1` is not needed here, because the vacuum tensor has empty active set and its
self-kernel is the empty product; the hypothesis is what makes this consistent with evaluating
the kernel over any larger finite mode set, see `kern_eq_prod_of_subset`.) -/
theorem itpInner_vacuumVector :
    itpInner (vacuumVector Ω) (vacuumVector Ω) = 1 := by
  classical
  have hsupp : (vacuumVector Ω).support ⊆ {VacuumTensor.vacuum Ω} :=
    Finsupp.support_single_subset
  rw [itpInner_eq_sum hsupp hsupp]
  simp [vacuumVector, kern_vacuum_vacuum]

/-! ## Finite-mode realization for the algebraic span -/

/-- **Finite-mode realization of the kernel.**  All pairings inside a finite family of
vacuum-restricted elementary tensors are realized as inner products of vectors in a finite
tensor-product Hilbert space. -/
theorem exists_finiteMode_realization_kern (hΩ : ∀ i, ⟪Ω i, Ω i⟫_ℂ = 1)
    (t : Finset (VacuumTensor Ω)) :
    ∃ (K : Type u) (_ : Fintype K) (Φ : VacuumTensor Ω → EuclideanSpace ℂ K),
      ∀ v ∈ t, ∀ w ∈ t, ⟪Φ v, Φ w⟫_ℂ = kern v w := by
  classical
  set s : Finset ι := t.sup VacuumTensor.active with hs
  obtain ⟨K, hK, Φ, hΦ⟩ :=
    exists_finiteMode_realization (E := E) s (fun v : t => (v : VacuumTensor Ω).vec)
  refine ⟨K, hK, fun v => if hv : v ∈ t then Φ ⟨v, hv⟩ else (0 : EuclideanSpace ℂ K), ?_⟩
  intro v hv w hw
  have hact : ∀ z ∈ t, z.active ⊆ s := fun z hz => Finset.le_sup (f := VacuumTensor.active) hz
  simp only [dif_pos hv, dif_pos hw]
  rw [hΦ ⟨v, hv⟩ ⟨w, hw⟩, kern_eq_prod_of_subset hΩ (hact v hv) (hact w hw)]

/-- The sesquilinear form is computed entirely inside a finite mode sector. -/
theorem itpInner_eq_finiteMode (hΩ : ∀ i, ⟪Ω i, Ω i⟫_ℂ = 1) {x y : ITPSpan Ω}
    {t : Finset (VacuumTensor Ω)} (hx : x.support ⊆ t) (hy : y.support ⊆ t)
    {s : Finset ι} (hs : ∀ v ∈ t, v.active ⊆ s) :
    itpInner x y
      = ∑ v ∈ t, ∑ w ∈ t, conj (x v) * y w * ∏ i ∈ s, ⟪v.vec i, w.vec i⟫_ℂ := by
  rw [itpInner_eq_sum hx hy]
  refine Finset.sum_congr rfl fun v hv => ?_
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [kern_eq_prod_of_subset hΩ (hs v hv) (hs w hw)]

/-! ## A concrete non-degenerate instance

A sanity check that the definitions are not vacuous: with `ι = ℕ`, `E i = ℂ` and `Ω i = 1`,
the elementary tensor which is `2` in mode `0` and vacuum elsewhere has self-kernel `4`. -/

section Sanity

/-- An elementary vacuum-restricted tensor over `ι = ℕ` with all factors `ℂ` and vacuum `1`. -/
def sanityTensor : VacuumTensor (fun _ : ℕ => (1 : ℂ)) where
  vec i := if i = 0 then 2 else 1
  active := {0}
  vec_eq_vacuum i hi := by
    simp only [Finset.mem_singleton] at hi
    simp [hi]

example : kern sanityTensor sanityTensor = 4 := by
  simp [kern, sanityTensor]
  norm_num

example : itpInner (Finsupp.single sanityTensor (1 : ℂ)) (Finsupp.single sanityTensor (1 : ℂ))
    = 4 := by
  rw [itpInner_single]
  simp [kern, sanityTensor]
  norm_num

end Sanity

end VacuumRestrictedITP
end AristotleCandidates

