import AristotleCandidates.CStarTransport

/-!
# Conditional transport of a finite tracial-weight core

This module formalizes only the *algebraic finite part* that a prospective
tracial weight has to provide, and transports it along a **supplied** complex
star-algebra equivalence.

A `TracialWeightCore A` consists of

* a complex-linear subspace `finitePart` of `A` (the elements on which the
  putative weight is finite),
* two-sided absorption of `finitePart` under multiplication by arbitrary
  elements of `A` (so `finitePart` is a two-sided ideal, the finite trace
  ideal),
* a complex-linear functional `tau` on `finitePart`, and
* the tracial identity `tau (x * y) = tau (y * x)` whenever one of the two
  factors lies in the finite trace ideal, with all subtype-membership evidence
  written out explicitly.

## Accuracy boundary

`TracialWeightCore` is **only** the finite complex-linear trace ideal of a
prospective tracial weight together with a linear functional on it.  It is
*not* a definition or construction of an extended-positive normal semifinite
tracial weight.  Nothing here claims normality, faithfulness, semifiniteness,
positivity, a GNS or spatial tensor identification, bicommutant passage,
hyperfiniteness, or factor type.  No C⋆ completion, weight, GNS representation
or von Neumann algebra is constructed.

The only analytic input used is the one already supplied by the ambient
interface: when the source and target carry *supplied* C⋆ structures, a
complex star-algebra equivalence between them is automatically isometric,
hence continuous (see `SuppliedCStarModel.isometry_equivalence`).  That
continuity plays no role in the algebraic transport below; it is recorded
merely because the C⋆ structures are supplied.
-/

namespace StabilizerHyperfinite

universe u v

section Algebraic

variable {A : Type u} {B : Type v}
  [Ring A] [StarRing A] [Algebra ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B]

/-- The algebraic finite part of a prospective tracial weight on a complex
star algebra `A`: a two-sided ideal of "finite" elements carrying a
complex-linear functional which is cyclic on products with one factor in the
ideal.

This is deliberately *not* an extended-positive normal semifinite tracial
weight: no positivity, normality, faithfulness or semifiniteness is asserted. -/
structure TracialWeightCore (A : Type u) [Ring A] [StarRing A] [Algebra ℂ A] where
  /-- The complex-linear subspace of elements of finite weight. -/
  finitePart : Submodule ℂ A
  /-- The finite part absorbs left multiplication by arbitrary elements. -/
  mul_mem_left : ∀ (a : A) {x : A}, x ∈ finitePart → a * x ∈ finitePart
  /-- The finite part absorbs right multiplication by arbitrary elements. -/
  mul_mem_right : ∀ (a : A) {x : A}, x ∈ finitePart → x * a ∈ finitePart
  /-- The complex-linear functional defined on the finite part. -/
  tau : finitePart →ₗ[ℂ] ℂ
  /-- Traciality when the *left* factor is finite. -/
  tau_cyclic_left : ∀ (x : A) (hx : x ∈ finitePart) (y : A),
      tau ⟨x * y, mul_mem_right y hx⟩ = tau ⟨y * x, mul_mem_left y hx⟩
  /-- Traciality when the *right* factor is finite. -/
  tau_cyclic_right : ∀ (x : A) (y : A) (hy : y ∈ finitePart),
      tau ⟨x * y, mul_mem_left x hy⟩ = tau ⟨y * x, mul_mem_right x hy⟩

namespace TracialWeightCore

variable (C : TracialWeightCore A)

/-- The finite part is closed under the two-sided multiplication action, i.e.
it is a two-sided ideal of `A`. -/
theorem mul_mem_of_mem_left_or_right {x y : A}
    (h : x ∈ C.finitePart ∨ y ∈ C.finitePart) : x * y ∈ C.finitePart := by
  rcases h with h | h
  · exact C.mul_mem_right y h
  · exact C.mul_mem_left x h

/-- Membership of `finitePart` is preserved by the (subtype-level) product of
two finite elements. -/
theorem mul_mem_of_both {x y : A} (hx : x ∈ C.finitePart) (_hy : y ∈ C.finitePart) :
    x * y ∈ C.finitePart :=
  C.mul_mem_right y hx

/-- Reformulation of traciality with membership evidence supplied as an
explicit proof-irrelevant coercion. -/
theorem tau_congr {x y : A} (hx : x ∈ C.finitePart) (hy : y ∈ C.finitePart)
    (h : x = y) : C.tau ⟨x, hx⟩ = C.tau ⟨y, hy⟩ := by
  subst h; rfl

end TracialWeightCore

/-- The complex-linear map underlying a star-algebra equivalence. -/
def starAlgEquivLinearMap (e : A ≃⋆ₐ[ℂ] B) : A →ₗ[ℂ] B where
  toFun x := e x
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp]
theorem starAlgEquivLinearMap_apply (e : A ≃⋆ₐ[ℂ] B) (x : A) :
    starAlgEquivLinearMap e x = e x :=
  rfl

/-- The pullback finite part: the preimage of the target finite trace ideal. -/
def pullbackFinitePart (e : A ≃⋆ₐ[ℂ] B) (C : TracialWeightCore B) : Submodule ℂ A :=
  C.finitePart.comap (starAlgEquivLinearMap e)

@[simp]
theorem mem_pullbackFinitePart (e : A ≃⋆ₐ[ℂ] B) (C : TracialWeightCore B) (x : A) :
    x ∈ pullbackFinitePart e C ↔ e x ∈ C.finitePart :=
  Iff.rfl

theorem pullbackFinitePart_mul_mem_left (e : A ≃⋆ₐ[ℂ] B) (C : TracialWeightCore B)
    (a : A) {x : A} (hx : x ∈ pullbackFinitePart e C) :
    a * x ∈ pullbackFinitePart e C := by
  rw [mem_pullbackFinitePart] at hx ⊢
  rw [map_mul]
  exact C.mul_mem_left (e a) hx

theorem pullbackFinitePart_mul_mem_right (e : A ≃⋆ₐ[ℂ] B) (C : TracialWeightCore B)
    (a : A) {x : A} (hx : x ∈ pullbackFinitePart e C) :
    x * a ∈ pullbackFinitePart e C := by
  rw [mem_pullbackFinitePart] at hx ⊢
  rw [map_mul]
  exact C.mul_mem_right (e a) hx

/-- The pullback functional on the pullback finite part. -/
def pullbackTau (e : A ≃⋆ₐ[ℂ] B) (C : TracialWeightCore B) :
    pullbackFinitePart e C →ₗ[ℂ] ℂ where
  toFun x := C.tau ⟨e x.1, x.2⟩
  map_add' x y := by
    have h : ((⟨e (x + y).1, (x + y).2⟩ : C.finitePart))
        = (⟨e x.1, x.2⟩ : C.finitePart) + ⟨e y.1, y.2⟩ := by
      apply Subtype.ext
      simp
    simp only [h, map_add]
  map_smul' c x := by
    have h : ((⟨e (c • x).1, (c • x).2⟩ : C.finitePart))
        = c • (⟨e x.1, x.2⟩ : C.finitePart) := by
      apply Subtype.ext
      simp
    simp only [h, map_smul, RingHom.id_apply]

@[simp]
theorem pullbackTau_apply (e : A ≃⋆ₐ[ℂ] B) (C : TracialWeightCore B)
    (x : A) (hx : x ∈ pullbackFinitePart e C) :
    pullbackTau e C ⟨x, hx⟩ = C.tau ⟨e x, hx⟩ :=
  rfl

/-- Pull a tracial weight core back along a supplied star-algebra equivalence.

Only the algebraic data is transported; nothing analytic is constructed. -/
def TracialWeightCore.pullback (e : A ≃⋆ₐ[ℂ] B) (C : TracialWeightCore B) :
    TracialWeightCore A where
  finitePart := pullbackFinitePart e C
  mul_mem_left a _ hx := pullbackFinitePart_mul_mem_left e C a hx
  mul_mem_right a _ hx := pullbackFinitePart_mul_mem_right e C a hx
  tau := pullbackTau e C
  tau_cyclic_left x hx y := by
    have hex : e x ∈ C.finitePart := hx
    have h1 : C.tau ⟨e (x * y), pullbackFinitePart_mul_mem_right e C y hx⟩
        = C.tau ⟨e x * e y, C.mul_mem_right (e y) hex⟩ :=
      C.tau_congr _ _ (map_mul e x y)
    have h2 : C.tau ⟨e (y * x), pullbackFinitePart_mul_mem_left e C y hx⟩
        = C.tau ⟨e y * e x, C.mul_mem_left (e y) hex⟩ :=
      C.tau_congr _ _ (map_mul e y x)
    simpa [pullbackTau_apply, h1, h2] using C.tau_cyclic_left (e x) hex (e y)
  tau_cyclic_right x y hy := by
    have hey : e y ∈ C.finitePart := hy
    have h1 : C.tau ⟨e (x * y), pullbackFinitePart_mul_mem_left e C x hy⟩
        = C.tau ⟨e x * e y, C.mul_mem_left (e x) hey⟩ :=
      C.tau_congr _ _ (map_mul e x y)
    have h2 : C.tau ⟨e (y * x), pullbackFinitePart_mul_mem_right e C x hy⟩
        = C.tau ⟨e y * e x, C.mul_mem_right (e x) hey⟩ :=
      C.tau_congr _ _ (map_mul e y x)
    simpa [pullbackTau_apply, h1, h2] using C.tau_cyclic_right (e x) (e y) hey

@[simp]
theorem TracialWeightCore.pullback_finitePart (e : A ≃⋆ₐ[ℂ] B)
    (C : TracialWeightCore B) :
    (C.pullback e).finitePart = pullbackFinitePart e C :=
  rfl

@[simp]
theorem TracialWeightCore.mem_pullback_finitePart (e : A ≃⋆ₐ[ℂ] B)
    (C : TracialWeightCore B) (x : A) :
    x ∈ (C.pullback e).finitePart ↔ e x ∈ C.finitePart :=
  Iff.rfl

theorem TracialWeightCore.pullback_tau_apply (e : A ≃⋆ₐ[ℂ] B)
    (C : TracialWeightCore B) (x : A) (hx : x ∈ (C.pullback e).finitePart) :
    (C.pullback e).tau ⟨x, hx⟩ = C.tau ⟨e x, hx⟩ :=
  rfl

/-- Conditional existence transfer: a tracial weight core on `B` yields one on
`A` along a supplied star-algebra equivalence.  This transfers only the finite
algebraic trace ideal, not any analytic weight-theoretic property. -/
theorem nonempty_tracialWeightCore_of_equiv (e : A ≃⋆ₐ[ℂ] B) :
    Nonempty (TracialWeightCore B) → Nonempty (TracialWeightCore A) := fun ⟨C⟩ =>
  ⟨C.pullback e⟩

/-- The transfer is available in both directions, since the equivalence is
invertible. -/
theorem nonempty_tracialWeightCore_iff (e : A ≃⋆ₐ[ℂ] B) :
    Nonempty (TracialWeightCore A) ↔ Nonempty (TracialWeightCore B) :=
  ⟨nonempty_tracialWeightCore_of_equiv e.symm,
    nonempty_tracialWeightCore_of_equiv e⟩

end Algebraic

namespace SuppliedCStarModel

variable (D : Data)

/-- Pull a tracial weight core on the supplied target back to the supplied
source.  The C⋆ structures are only used to know that the equivalence is
automatically isometric (`isometry_equivalence`); the construction itself is
purely algebraic. -/
def inducedTracialWeightCore (C : TracialWeightCore D.target) :
    TracialWeightCore D.source :=
  C.pullback D.equivalence

@[simp]
theorem mem_inducedTracialWeightCore_finitePart (C : TracialWeightCore D.target)
    (x : D.source) :
    x ∈ (inducedTracialWeightCore D C).finitePart ↔
      D.equivalence x ∈ C.finitePart :=
  Iff.rfl

theorem inducedTracialWeightCore_tau_apply (C : TracialWeightCore D.target)
    (x : D.source) (hx : x ∈ (inducedTracialWeightCore D C).finitePart) :
    (inducedTracialWeightCore D C).tau ⟨x, hx⟩ = C.tau ⟨D.equivalence x, hx⟩ :=
  rfl

/-- Conditional existence transfer for the supplied C⋆ model interface. -/
theorem nonempty_tracialWeightCore_source_of_target :
    Nonempty (TracialWeightCore D.target) → Nonempty (TracialWeightCore D.source) :=
  nonempty_tracialWeightCore_of_equiv D.equivalence

/-- Both directions of the transfer for the supplied interface. -/
theorem nonempty_tracialWeightCore_source_iff_target :
    Nonempty (TracialWeightCore D.source) ↔ Nonempty (TracialWeightCore D.target) :=
  nonempty_tracialWeightCore_iff D.equivalence

/-- Record of the only analytic content available here: because the C⋆
structures are *supplied*, the star-algebra equivalence used for the transport
is automatically isometric, hence continuous in both directions.  This plays no
role in the algebraic transport of the finite trace ideal. -/
theorem tracialWeightCore_transport_is_isometric_because_cstar_supplied :
    Isometry D.equivalence ∧ Isometry D.equivalence.symm ∧
      Continuous D.equivalence ∧ Continuous D.equivalence.symm :=
  ⟨isometry_equivalence D, isometry_equivalence_symm D,
    continuous_equivalence D, continuous_equivalence_symm D⟩

end SuppliedCStarModel

end StabilizerHyperfinite
