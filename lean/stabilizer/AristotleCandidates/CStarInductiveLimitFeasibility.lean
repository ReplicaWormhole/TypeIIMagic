import Formalization.DyadicTensorTower

/-!
# Feasibility audit: C⋆-completion of the algebraic dyadic (UHF) direct limit

**Context declaration.** Source basis: `main.tex:1915-1924`.

This file is an *API audit*, in Lean, of the pinned Mathlib version
(`v4.28.0`-era Mathlib, commit recorded in `lake-manifest.json`) with respect to
one question:

> can the C⋆-completion of the algebraic dyadic/UHF direct limit be constructed
> with the definitions and theorems that Mathlib currently provides?

The answer this file records is **partially**: Mathlib supplies every ingredient
needed *once an ambient C⋆-algebra containing the finite stages is available*,
and it supplies the finite dyadic stages themselves as genuine C⋆-algebras, but
it supplies **no** construction of the ambient algebra — i.e. no C⋆-completion
of a pre-C⋆-algebra, and no inductive (direct) limit of C⋆-algebras.

Accordingly the file has three parts.

## Part 1 — existing Mathlib support (Section `Existing`)

Each item is witnessed by a declaration that compiles here, so the claim
"Mathlib has this" is machine-checked rather than asserted:

* `Existing.closedStarSubalgebra_cstarAlgebra` — a **closed** `StarSubalgebra`
  of a C⋆-algebra is itself a C⋆-algebra (`StarSubalgebra.cstarAlgebra`).
* `Existing.isClosed_topologicalClosure`, `Existing.le_topologicalClosure`,
  `Existing.topologicalClosure_minimal` — the topological closure of a
  `StarSubalgebra` exists, is closed, contains the algebra, and is minimal
  among closed star subalgebras containing it.
* `Existing.injective_starAlgHom_isometry` — an injective ⋆-homomorphism of
  complex C⋆-algebras is isometric (`NonUnitalStarAlgHom.isometry`).  This is
  what makes a C⋆-norm on an inductive system automatically unique and the
  connecting maps automatically isometric.
* `Existing.dense_ext` — continuous maps agreeing on a dense set are equal
  (`Continuous.ext_on`); this is the uniqueness half of every
  finite-stage-to-completion statement.
* `DyadicStage`, `dyadicStageCStar`, `dyadicSucc`, `isometry_dyadicSucc` — the
  **finite** dyadic stages `M₂(M₂(⋯ℂ))` are available as genuine C⋆-algebras
  through `CStarMatrix`, and the unital connecting ⋆-homomorphism
  `a ↦ diag (a, a)` is injective, hence isometric.
* The purely algebraic direct limit of the dyadic tower already exists in this
  project as `StabilizerHyperfinite.QubitUHFAlgebra`; Mathlib supplies the
  algebraic colimit machinery it is built from.

## Part 2 — the smallest working finite-stage-to-completion interface
(Section `AmbientTower`)

Given a C⋆-algebra `Ambient` and a monotone chain `stage : ℕ → StarSubalgebra ℂ
Ambient`, everything one wants from a completion is constructed and proved
here, with no additional assumption:

* `AmbientTower.chainUnion` — the directed union of the stages, as a
  `StarSubalgebra` (Mathlib has `Subalgebra.coe_iSup_of_directed` but no
  `StarSubalgebra` analogue, so the union is built directly);
* `AmbientTower.limitAlgebra` — its topological closure, which **is** a
  C⋆-algebra (instance `AmbientTower.limitAlgebra_isClosed` plus
  `StarSubalgebra.cstarAlgebra`);
* `AmbientTower.stageIncl` — isometric injective ⋆-homomorphisms of the finite
  stages into the completion, compatible with the chain (`stageIncl_trans`);
* `AmbientTower.dense_stages` — the finite stages are dense in the completion;
* `AmbientTower.limitAlgebra_minimal` — the completion is the smallest closed
  star subalgebra containing all stages;
* `AmbientTower.ext_of_continuous` — a continuous map out of the completion is
  determined by its restrictions to the finite stages.

`trivialTower` is a non-vacuity witness for this interface.

## Part 3 — missing Mathlib support (Section `Missing`)

The following are **not** available in the pinned Mathlib.  They are recorded
here as ordinary Lean `Prop`s (via bundling structures), *not* as axioms and
*not* as `sorry`-ed theorems: nothing in this file assumes any of them, and
nothing in this file proves any of them.

* `Missing.PreCStarCompletionAPI` — every pre-C⋆-algebra (a normed complex
  ⋆-algebra satisfying the C⋆-identity, not assumed complete) embeds
  isometrically with dense range in a C⋆-algebra.  Mathlib does have
  `UniformSpace.Completion` with `NormedRing` structure, but it carries **no**
  `StarRing`/`CStarRing`/`NormedAlgebra ℂ` transfer, so the completion of a
  pre-C⋆-algebra is not available as a C⋆-algebra.
* `Missing.CStarInductiveLimitAPI` — every inductive system of C⋆-algebras
  indexed by `ℕ` with injective connecting ⋆-homomorphisms has a C⋆-inductive
  limit (`Missing.CStarLimit`).  Mathlib has algebraic direct limits only.
* `Missing.DyadicAlgebraicLimitCompletionAPI` — the specific instance for this
  project: the algebraic direct limit `StabilizerHyperfinite.QubitUHFAlgebra`
  embeds injectively with dense range into a C⋆-algebra (equivalently, it
  carries a C⋆-norm and can be completed).

**Minimal upstream abstraction.**  `Missing.CStarInductiveLimitAPI` alone is
enough for the dyadic case, and it feeds straight into Part 2:

* `Missing.dyadic_cstarLimit_of_api` — the API applied to the dyadic tower
  `dyadicTower` produces a C⋆-algebra containing all finite dyadic stages
  isometrically and compatibly, with dense union;
* `Missing.CStarLimit.toAmbientTower` and
  `Missing.CStarLimit.toAmbientTower_limitAlgebra_eq_top` — any such limit is
  an instance of the Part 2 interface, whose `limitAlgebra` is the whole
  algebra.  So no further completion API is needed downstream of the ambient
  algebra.

## Boundary

No von Neumann algebra, weak closure, bicommutant, normality, spatial or any
tensor product, factor type, hyperfiniteness, trace, or weight is used or
claimed anywhere in this file.  No gLU, refinement, or layer-coherence
hypothesis appears.  No manuscript claim is proved here: the file reports what
the pinned Mathlib does and does not support.
-/

open scoped ComplexOrder

namespace AristotleCandidates

namespace CStarInductiveLimitFeasibility

/-! ## Part 1 — existing Mathlib support

Every declaration in this section is a checked witness that the pinned Mathlib
provides the stated ingredient. -/

namespace Existing

/-- **Available.** A closed `StarSubalgebra` of a complex C⋆-algebra is a
C⋆-algebra (`StarSubalgebra.cstarAlgebra`). -/
noncomputable def closedStarSubalgebra_cstarAlgebra (A : Type) [CStarAlgebra A]
    (S : StarSubalgebra ℂ A) (_hS : IsClosed (S : Set A)) : CStarAlgebra S :=
  letI : IsClosed (S : Set A) := _hS
  inferInstance

/-- **Available.** The topological closure of a `StarSubalgebra` is closed. -/
theorem isClosed_topologicalClosure (A : Type) [CStarAlgebra A] (S : StarSubalgebra ℂ A) :
    IsClosed ((S.topologicalClosure : StarSubalgebra ℂ A) : Set A) := by
  rw [StarSubalgebra.topologicalClosure_coe]
  exact isClosed_closure

/-- **Available.** A `StarSubalgebra` is contained in its topological closure. -/
theorem le_topologicalClosure (A : Type) [CStarAlgebra A] (S : StarSubalgebra ℂ A) :
    S ≤ S.topologicalClosure :=
  StarSubalgebra.le_topologicalClosure S

/-- **Available.** The topological closure is the smallest closed star subalgebra
containing the given one. -/
theorem topologicalClosure_minimal (A : Type) [CStarAlgebra A] {S T : StarSubalgebra ℂ A}
    (h : S ≤ T) (hT : IsClosed (T : Set A)) : S.topologicalClosure ≤ T :=
  StarSubalgebra.topologicalClosure_minimal h hT

/-- **Available.** An injective ⋆-homomorphism of complex C⋆-algebras is isometric
(`NonUnitalStarAlgHom.isometry`).  Consequently a C⋆-norm on an inductive
system is unique and the connecting maps are automatically isometric. -/
theorem injective_starAlgHom_isometry (A B : Type) [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f) : Isometry f :=
  NonUnitalStarAlgHom.isometry f hf

/-- **Available.** Continuous maps that agree on a dense set are equal; this is
the uniqueness half of every finite-stage-to-completion statement. -/
theorem dense_ext {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {s : Set X} (hs : Dense s) {f g : X → Y} (hf : Continuous f) (hg : Continuous g)
    (h : Set.EqOn f g s) : f = g :=
  Continuous.ext_on hs hf hg h

end Existing

/-! ### The finite dyadic stages are C⋆-algebras in the pinned Mathlib

`CStarMatrix n n A` is Mathlib's C⋆-algebra of matrices over a C⋆-algebra.
Iterating it gives the finite dyadic stages `ℂ, M₂(ℂ), M₂(M₂(ℂ)), …` as genuine
C⋆-algebras.  This is *existing* support: only the recursive bookkeeping is
done here. -/

/-- The bundled algebraic data carried by each finite dyadic stage: it is a
unital complex C⋆-algebra with its spectral order, which is exactly what
`CStarMatrix.instCStarAlgebra` needs at the next stage. -/
structure CStarStageData (A : Type) where
  /-- The C⋆-algebra structure of the stage. -/
  cstar : CStarAlgebra A
  /-- The (spectral) order of the stage. -/
  order : PartialOrder A
  /-- The stage is a star-ordered ring for that order. -/
  starOrdered :
    @StarOrderedRing A (letI := cstar; inferInstance) order (letI := cstar; inferInstance)

/-- The finite dyadic stages, as iterated `CStarMatrix` algebras over `ℂ`:
stage `n` is `M₂^{⊗n}(ℂ)` in iterated-amplification form. -/
def DyadicStage : ℕ → Type
  | 0 => ℂ
  | n + 1 => CStarMatrix (Fin 2) (Fin 2) (DyadicStage n)

/-- The recursive C⋆-structure of the finite dyadic stages. -/
noncomputable def dyadicStageData : (n : ℕ) → CStarStageData (DyadicStage n)
  | 0 => by
      change CStarStageData ℂ
      exact ⟨inferInstance, inferInstance, inferInstance⟩
  | n + 1 => by
      change CStarStageData (CStarMatrix (Fin 2) (Fin 2) (DyadicStage n))
      let d := dyadicStageData n
      letI := d.cstar
      letI := d.order
      letI := d.starOrdered
      exact ⟨inferInstance, inferInstance, inferInstance⟩

noncomputable instance dyadicStageCStar (n : ℕ) : CStarAlgebra (DyadicStage n) :=
  (dyadicStageData n).cstar

noncomputable instance dyadicStagePartialOrder (n : ℕ) : PartialOrder (DyadicStage n) :=
  (dyadicStageData n).order

instance dyadicStageStarOrdered (n : ℕ) : StarOrderedRing (DyadicStage n) :=
  (dyadicStageData n).starOrdered

/-- The diagonal embedding `a ↦ diag (a, a)` as a ⋆-homomorphism into `2 × 2`
matrices. -/
noncomputable def scalarStarAlgHom (A : Type) [Semiring A] [StarRing A] [Algebra ℂ A] :
    A →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) A :=
  { Matrix.scalarAlgHom (Fin 2) ℂ with
    map_star' := by
      intro x
      change Matrix.scalar (Fin 2) (star x) = star (Matrix.scalar (Fin 2) x)
      ext i j
      by_cases h : i = j
      · subst j
        simp [Matrix.scalar_apply, Matrix.star_apply]
      · have h' : j ≠ i := Ne.symm h
        simp [Matrix.scalar_apply, Matrix.star_apply, h, h'] }

theorem scalarStarAlgHom_injective (A : Type) [Semiring A] [StarRing A] [Algebra ℂ A] :
    Function.Injective (scalarStarAlgHom A) := by
  intro x y h
  have hx := congrFun (congrFun (congrArg (fun M => (M : Matrix (Fin 2) (Fin 2) A)) h) 0) 0
  simpa [scalarStarAlgHom, Matrix.scalar_apply] using hx

/-- The unital connecting ⋆-homomorphism of the dyadic tower, `a ↦ diag (a, a)`. -/
noncomputable def dyadicSucc (n : ℕ) : DyadicStage n →⋆ₐ[ℂ] DyadicStage (n + 1) :=
  (StarAlgHomClass.toStarAlgHom
      (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin 2) (A := DyadicStage n))).comp
    (scalarStarAlgHom (DyadicStage n))

theorem dyadicSucc_injective (n : ℕ) : Function.Injective (dyadicSucc n) := fun _ _ h =>
  scalarStarAlgHom_injective _ (CStarMatrix.ofMatrixStarAlgEquiv.injective h)

/-- **Available.** The connecting maps of the dyadic tower are isometric, because
they are injective ⋆-homomorphisms of C⋆-algebras. -/
theorem isometry_dyadicSucc (n : ℕ) : Isometry (dyadicSucc n) :=
  NonUnitalStarAlgHom.isometry _ (dyadicSucc_injective n)

/-! ## Part 2 — the working finite-stage-to-completion interface

Everything below is constructed from Mathlib as it stands: the only input is an
ambient C⋆-algebra together with a monotone chain of star subalgebras. -/

/-- A monotone chain of star subalgebras inside a fixed complex C⋆-algebra.
This is the *sufficient* input for a completion in the pinned Mathlib. -/
structure AmbientTower where
  /-- The ambient C⋆-algebra. -/
  Ambient : Type
  /-- Its C⋆-structure. -/
  cstar : CStarAlgebra Ambient
  /-- The finite stages. -/
  stage : ℕ → StarSubalgebra ℂ Ambient
  /-- The stages increase. -/
  stage_mono : Monotone stage

attribute [instance] AmbientTower.cstar

namespace AmbientTower

variable (T : AmbientTower)

/-- The directed union of the stages, as a star subalgebra.  (Mathlib has
`Subalgebra.coe_iSup_of_directed` but no `StarSubalgebra` analogue, so this is
built by hand.) -/
def chainUnion : StarSubalgebra ℂ T.Ambient where
  carrier := ⋃ n, (T.stage n : Set T.Ambient)
  mul_mem' := by
    rintro a b ⟨_, ⟨m, rfl⟩, ha⟩ ⟨_, ⟨n, rfl⟩, hb⟩
    exact Set.mem_iUnion.2 ⟨max m n, mul_mem (T.stage_mono (le_max_left m n) ha)
      (T.stage_mono (le_max_right m n) hb)⟩
  add_mem' := by
    rintro a b ⟨_, ⟨m, rfl⟩, ha⟩ ⟨_, ⟨n, rfl⟩, hb⟩
    exact Set.mem_iUnion.2 ⟨max m n, add_mem (T.stage_mono (le_max_left m n) ha)
      (T.stage_mono (le_max_right m n) hb)⟩
  algebraMap_mem' := fun r => Set.mem_iUnion.2 ⟨0, (T.stage 0).algebraMap_mem' r⟩
  star_mem' := by
    rintro a ⟨_, ⟨n, rfl⟩, ha⟩
    exact Set.mem_iUnion.2 ⟨n, star_mem ha⟩

theorem stage_le_chainUnion (n : ℕ) : T.stage n ≤ T.chainUnion :=
  fun _ hx => Set.mem_iUnion.2 ⟨n, hx⟩

theorem mem_chainUnion_iff (x : T.Ambient) :
    x ∈ T.chainUnion ↔ ∃ n, x ∈ T.stage n := Set.mem_iUnion

/-- **The completion.** The closure of the union of the finite stages inside the
ambient C⋆-algebra. -/
def limitAlgebra : StarSubalgebra ℂ T.Ambient := T.chainUnion.topologicalClosure

instance limitAlgebra_isClosed :
    IsClosed ((T.limitAlgebra : StarSubalgebra ℂ T.Ambient) : Set T.Ambient) := by
  rw [limitAlgebra, StarSubalgebra.topologicalClosure_coe]
  exact isClosed_closure

/-- The completion is itself a complex C⋆-algebra: this is
`StarSubalgebra.cstarAlgebra` applied to the closed subalgebra `limitAlgebra`. -/
example : CStarAlgebra T.limitAlgebra := inferInstance

theorem stage_le_limitAlgebra (n : ℕ) : T.stage n ≤ T.limitAlgebra :=
  (T.stage_le_chainUnion n).trans (StarSubalgebra.le_topologicalClosure _)

/-- The finite-stage embedding into the completion. -/
def stageIncl (n : ℕ) : T.stage n →⋆ₐ[ℂ] T.limitAlgebra :=
  StarSubalgebra.inclusion (T.stage_le_limitAlgebra n)

theorem injective_stageIncl (n : ℕ) : Function.Injective (T.stageIncl n) :=
  StarSubalgebra.inclusion_injective _

theorem isometry_stageIncl (n : ℕ) : Isometry (T.stageIncl n) :=
  Isometry.of_dist_eq fun _ _ => rfl

/-- The stage embeddings are compatible with the inclusions of the chain. -/
theorem stageIncl_trans {m n : ℕ} (h : m ≤ n) (x : T.stage m) :
    T.stageIncl n (StarSubalgebra.inclusion (T.stage_mono h) x) = T.stageIncl m x := rfl

/-- **Density.** The finite stages are dense in the completion. -/
theorem dense_stages : Dense (⋃ n, Set.range (T.stageIncl n) : Set T.limitAlgebra) := by
  rw [Subtype.dense_iff]
  have hsub : (T.chainUnion : Set T.Ambient) ⊆
      Subtype.val '' (⋃ n, Set.range (T.stageIncl n)) := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    exact ⟨T.stageIncl n ⟨x, hn⟩, Set.mem_iUnion.2 ⟨n, ⟨⟨x, hn⟩, rfl⟩⟩, rfl⟩
  intro x hx
  refine closure_mono hsub ?_
  rw [← StarSubalgebra.topologicalClosure_coe]
  exact hx

/-- **Minimality.** The completion is the smallest closed star subalgebra of the
ambient algebra containing every finite stage. -/
theorem limitAlgebra_minimal (S : StarSubalgebra ℂ T.Ambient) (hS : IsClosed (S : Set T.Ambient))
    (h : ∀ n, T.stage n ≤ S) : T.limitAlgebra ≤ S :=
  StarSubalgebra.topologicalClosure_minimal
    (fun x hx => by
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
      exact h n hn) hS

/-- **Uniqueness of extensions.** A continuous map out of the completion is
determined by its restrictions to the finite stages. -/
theorem ext_of_continuous {Y : Type} [TopologicalSpace Y] [T2Space Y]
    (f g : T.limitAlgebra → Y) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ n (x : T.stage n), f (T.stageIncl n x) = g (T.stageIncl n x)) : f = g := by
  refine Continuous.ext_on T.dense_stages hf hg ?_
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_range] at hy
  obtain ⟨n, x, rfl⟩ := hy
  exact h n x

end AmbientTower

/-- A non-vacuity witness for the Part 2 interface: inside the C⋆-algebra
`M₂(ℂ)`, the chain `ℂ·1 ⊆ M₂(ℂ) ⊆ M₂(ℂ) ⊆ ⋯`.  This checks that all fields of
`AmbientTower` can be met simultaneously; it is not a model of the manuscript's
regional algebras. -/
noncomputable def trivialTower : AmbientTower where
  Ambient := DyadicStage 1
  cstar := inferInstance
  stage := fun n => if n = 0 then ⊥ else ⊤
  stage_mono := by
    refine monotone_nat_of_le_succ fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [Nat.ne_of_gt hn]

theorem trivialTower_limitAlgebra_eq_top : trivialTower.limitAlgebra = ⊤ :=
  top_le_iff.1 (by
    have h : trivialTower.stage 1 ≤ trivialTower.limitAlgebra :=
      trivialTower.stage_le_limitAlgebra 1
    simpa [trivialTower] using h)

/-! ## Part 3 — missing Mathlib support

The statements below are *not* proved here and *not* assumed anywhere: they are
recorded as `Prop`s so that the exact missing upstream API is unambiguous.  No
axiom and no `sorry` is used. -/

namespace Missing

/-! ### Missing item 1: completion of a pre-C⋆-algebra

Mathlib provides `UniformSpace.Completion` with a `NormedRing` instance, but no
transfer of `StarRing`, `CStarRing`, `NormedAlgebra ℂ` or `StarModule ℂ` to the
completion.  So "the completion of a pre-C⋆-algebra is a C⋆-algebra" is not
available. -/

/-- A pre-C⋆-algebra: a normed complex ⋆-algebra satisfying the C⋆-identity,
**not** assumed complete. -/
structure PreCStarAlgebra where
  /-- The underlying type. -/
  Carrier : Type
  /-- Its normed ring structure. -/
  normedRing : NormedRing Carrier
  /-- Its ⋆-structure. -/
  starRing : StarRing Carrier
  /-- The C⋆-identity. -/
  cstarRing : CStarRing Carrier
  /-- The complex normed algebra structure. -/
  normedAlgebra : NormedAlgebra ℂ Carrier
  /-- Compatibility of `star` with the complex scalars. -/
  starModule : StarModule ℂ Carrier

attribute [instance] PreCStarAlgebra.normedRing PreCStarAlgebra.starRing
  PreCStarAlgebra.cstarRing PreCStarAlgebra.normedAlgebra PreCStarAlgebra.starModule

/-- A C⋆-completion of a pre-C⋆-algebra: an isometric ⋆-embedding with dense
range into a C⋆-algebra. -/
structure CStarCompletionOf (P : PreCStarAlgebra) where
  /-- The completed algebra. -/
  Ambient : Type
  /-- Its C⋆-structure. -/
  cstar : CStarAlgebra Ambient
  /-- The embedding of the pre-C⋆-algebra. -/
  embed : P.Carrier →⋆ₐ[ℂ] Ambient
  /-- The embedding is isometric. -/
  embed_isometry : Isometry embed
  /-- The embedding has dense range. -/
  embed_dense : Dense (Set.range embed)

attribute [instance] CStarCompletionOf.cstar

/-- **Missing from the pinned Mathlib.** Every pre-C⋆-algebra has a
C⋆-completion.  Stated, not proved, and not used as a hypothesis anywhere
except where explicitly displayed. -/
def PreCStarCompletionAPI : Prop := ∀ P : PreCStarAlgebra, Nonempty (CStarCompletionOf P)

/-! ### Missing item 2: inductive limits of C⋆-algebras

Mathlib has algebraic direct limits (`Module.DirectLimit`, `Ring.DirectLimit`,
and the star version used in this project) but no colimit in the category of
C⋆-algebras. -/

/-- An inductive system of complex C⋆-algebras indexed by `ℕ`, with injective
(hence automatically isometric) connecting ⋆-homomorphisms. -/
structure CStarTower where
  /-- The stages. -/
  A : ℕ → Type
  /-- Their C⋆-structures. -/
  cstar : ∀ n, CStarAlgebra (A n)
  /-- The connecting ⋆-homomorphisms. -/
  f : ∀ n, A n →⋆ₐ[ℂ] A (n + 1)
  /-- The connecting maps are injective. -/
  f_injective : ∀ n, Function.Injective (f n)

attribute [instance] CStarTower.cstar

/-- The connecting maps of a `CStarTower` are isometric — this part *is*
available in Mathlib (`NonUnitalStarAlgHom.isometry`). -/
theorem CStarTower.isometry_f (T : CStarTower) (n : ℕ) : Isometry (T.f n) :=
  NonUnitalStarAlgHom.isometry _ (T.f_injective n)

/-- A C⋆-inductive limit of a `CStarTower`: a C⋆-algebra receiving all stages
isometrically and compatibly, with dense union of the images. -/
structure CStarLimit (T : CStarTower) where
  /-- The limit algebra. -/
  Ambient : Type
  /-- Its C⋆-structure. -/
  cstar : CStarAlgebra Ambient
  /-- The stage embeddings. -/
  incl : ∀ n, T.A n →⋆ₐ[ℂ] Ambient
  /-- They are isometric. -/
  incl_isometry : ∀ n, Isometry (incl n)
  /-- They are compatible with the connecting maps. -/
  incl_compat : ∀ n x, incl (n + 1) (T.f n x) = incl n x
  /-- Their images exhaust the limit algebra. -/
  incl_dense : Dense (⋃ n, Set.range (incl n))

attribute [instance] CStarLimit.cstar

/-- **Missing from the pinned Mathlib.** Every `ℕ`-indexed inductive system of
C⋆-algebras with injective connecting maps has a C⋆-inductive limit.  This is
the *minimal upstream abstraction* needed for the dyadic/UHF completion. -/
def CStarInductiveLimitAPI : Prop := ∀ T : CStarTower, Nonempty (CStarLimit T)

/-- The dyadic tower of Part 1, packaged as an inductive system of
C⋆-algebras.  Note that this datum is fully available in the pinned Mathlib:
only its limit is not. -/
noncomputable def dyadicTower : CStarTower where
  A := DyadicStage
  cstar := dyadicStageCStar
  f := dyadicSucc
  f_injective := dyadicSucc_injective

/-- **Reduction.** The missing inductive-limit API immediately yields the
dyadic (UHF `2^∞`) C⋆-algebra: a C⋆-algebra containing every finite dyadic
stage isometrically and compatibly, with dense union. -/
theorem dyadic_cstarLimit_of_api (h : CStarInductiveLimitAPI) :
    Nonempty (CStarLimit dyadicTower) := h dyadicTower

/-! ### From a C⋆-inductive limit back to the Part 2 interface

The next two results show that nothing further is missing downstream: as soon
as an ambient limit algebra exists, the finite-stage-to-completion interface of
Part 2 applies to it and its `limitAlgebra` is everything. -/

variable {T : CStarTower}

theorem CStarLimit.range_mono (L : CStarLimit T) : Monotone fun n => (L.incl n).range := by
  refine monotone_nat_of_le_succ fun n => ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨T.f n x, L.incl_compat n x⟩

/-- Any C⋆-inductive limit is an instance of the Part 2 `AmbientTower`
interface, with the images of the finite stages as the chain. -/
noncomputable def CStarLimit.toAmbientTower (L : CStarLimit T) : AmbientTower where
  Ambient := L.Ambient
  cstar := L.cstar
  stage := fun n => (L.incl n).range
  stage_mono := L.range_mono

@[simp]
theorem CStarLimit.toAmbientTower_stage (L : CStarLimit T) (n : ℕ) :
    L.toAmbientTower.stage n = (L.incl n).range := rfl

/-- For a C⋆-inductive limit, the Part 2 completion of the chain of stage
images is the whole limit algebra. -/
theorem CStarLimit.toAmbientTower_limitAlgebra_eq_top (L : CStarLimit T) :
    L.toAmbientTower.limitAlgebra = ⊤ := by
  have hsub : (⋃ n, Set.range (L.incl n)) ⊆
      (L.toAmbientTower.chainUnion : Set L.toAmbientTower.Ambient) := by
    rintro y hy
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨n, z, rfl⟩ := hy
    exact Set.mem_iUnion.2 ⟨n, ⟨z, rfl⟩⟩
  refine top_le_iff.1 fun x _ => ?_
  have hx : x ∈ closure ((L.toAmbientTower.chainUnion : Set L.toAmbientTower.Ambient)) :=
    closure_mono hsub (L.incl_dense x)
  rw [AmbientTower.limitAlgebra]
  rwa [← StarSubalgebra.topologicalClosure_coe] at hx

/-! ### Missing item 3: the completion of *this* project's algebraic limit

`StabilizerHyperfinite.QubitUHFAlgebra` is the purely algebraic direct limit of
the dyadic tower, constructed in `Formalization.DyadicTensorTower`.  It carries
no norm, and the pinned Mathlib provides no way to give it one. -/

/-- A C⋆-completion of the project's algebraic dyadic direct limit: an injective
⋆-homomorphism with dense range into a C⋆-algebra. -/
structure DyadicAlgebraicLimitCompletion where
  /-- The completed algebra. -/
  Ambient : Type
  /-- Its C⋆-structure. -/
  cstar : CStarAlgebra Ambient
  /-- The embedding of the algebraic direct limit. -/
  embed : StabilizerHyperfinite.QubitUHFAlgebra →⋆ₐ[ℂ] Ambient
  /-- The embedding is injective. -/
  embed_injective : Function.Injective embed
  /-- The embedding has dense range. -/
  embed_dense : Dense (Set.range embed)

attribute [instance] DyadicAlgebraicLimitCompletion.cstar

/-- **Missing from the pinned Mathlib.** The algebraic dyadic direct limit
`StabilizerHyperfinite.QubitUHFAlgebra` admits a C⋆-completion.  Equivalently:
it carries a C⋆-norm (necessarily unique) and can be completed. -/
def DyadicAlgebraicLimitCompletionAPI : Prop := Nonempty DyadicAlgebraicLimitCompletion

end Missing

end CStarInductiveLimitFeasibility

end AristotleCandidates
