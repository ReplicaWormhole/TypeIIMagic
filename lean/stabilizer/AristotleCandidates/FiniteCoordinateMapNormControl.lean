import AristotleCandidates.FiniteCoordinateEquivCoherence
import Formalization.CStarEquivExtension
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Norm control for the coherent finite coordinate maps

**Context declaration.** Source basis: `main.tex:1915-1924`.

This module adds the *norm-theoretic* layer to the finite-stage picture built
in P29 (`AristotleCandidates.FiniteAdaptedCoordinateStarEquiv`) and P30
(`AristotleCandidates.FiniteCoordinateEquivCoherence`).  Nothing analytic is
constructed here: the C⋆-structures on the finite stages, the finite
dimensionality of the stages, the stage embeddings into an ambient C⋆-algebra
and the density of their union are all *supplied inputs*.  What is *proved* is
the norm control that these inputs force.

## Supplied data

* `FiniteCStarCoordinateFamily`: exactly the P30 directed family of finite
  adapted-coordinate systems, but with the finite stages carrying supplied
  finite-dimensional C⋆-algebra structures, and with the supplied connecting
  maps assumed injective (they are *inclusions* of stages).  As in P30 the
  finite-stage star-algebra equivalences are **constructed** by P29 from the
  word/basis/phase data, never assumed, and their coherence with the
  connecting maps is **proved**, never assumed.
* `StageCStarEmbeddings`: supplied ambient C⋆-algebras with supplied injective
  stage embeddings compatible with the connecting maps, and supplied density
  of the union of the stage images.  No completion is constructed: the ambient
  algebras and the embeddings are hypotheses.

## What is proved

* Each constructed finite-stage equivalence is isometric and continuous, as is
  its inverse (`isometry_starEquiv`, `norm_starEquiv`, `continuous_starEquiv`,
  ...), with the explicit Pauli-word norm identity `norm_starEquiv_word`.
* The connecting maps are norm-nonincreasing in general
  (`norm_starAlgHom_apply_le`) and isometric under the supplied injectivity
  (`norm_sourceConnecting`, `norm_targetConnecting`).
* **The inclusion squares preserve the norm estimates**: for a stage element
  `x` all four corners of the P30 commuting square have the same norm
  (`norm_square`, `norm_square_of_le`, `dist_square`).
* **The dense-subalgebra estimate**: on the union of the stage images — the
  dense `*`-subalgebra of the supplied ambient source algebra — the coherent
  algebraic map `x ↦ targetIncl (stageEquiv x)` is well defined
  (`targetIncl_stageEquiv_congr`) and distance preserving
  (`norm_sub_stageImages`, `dist_stageImages`, `core_estimate`).  This is
  exactly the estimate needed to extend the coherent algebraic alpha to
  completions: any continuous map with the finite-stage formula is
  automatically isometric (`isometry_of_stage_formula`) and unique
  (`ext_of_stage_formula`).

## What is *not* claimed

No completion, GNS representation, normality, spatial tensor product, factor
type, trace or weight, and no gLU or refinement statement appears anywhere in
this file.
-/

namespace AristotleCandidates

namespace FiniteCoordinateMapNormControl

open StabilizerHyperfinite
open StabilizerHyperfinite.FiniteAdaptedCoordinate
open StabilizerHyperfinite.FiniteCoordinateEquivCoherence

/-! ## Norm control of a single constructed finite-stage equivalence -/

section Stage

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A star-algebra homomorphism of C⋆-algebras is norm-nonincreasing. -/
theorem norm_starAlgHom_apply_le (f : A →⋆ₐ[ℂ] B) (a : A) : ‖f a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le f a

/-- An injective star-algebra homomorphism of C⋆-algebras is norm preserving. -/
theorem norm_starAlgHom_apply_of_injective (f : A →⋆ₐ[ℂ] B)
    (hf : Function.Injective f) (a : A) : ‖f a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map f hf a

/-- An injective star-algebra homomorphism of C⋆-algebras is isometric. -/
theorem isometry_starAlgHom_of_injective (f : A →⋆ₐ[ℂ] B)
    (hf : Function.Injective f) : Isometry f :=
  NonUnitalStarAlgHom.isometry f hf

end Stage

section StageData

variable {I V W A B : Type*}
variable [AddCommGroup V] [Module PauliBit V] [AddCommGroup W]
variable [CStarAlgebra A] [CStarAlgebra B]
variable (D : FiniteAdaptedCoordinateStarData I V W A B)

/-- **The constructed finite-stage equivalence is isometric.** -/
theorem isometry_starEquiv : Isometry D.starEquiv :=
  cstar_starAlgEquiv_isometry D.starEquiv

/-- The inverse of the constructed finite-stage equivalence is isometric. -/
theorem isometry_starEquiv_symm : Isometry D.starEquiv.symm :=
  cstar_starAlgEquiv_isometry D.starEquiv.symm

/-- The constructed finite-stage equivalence preserves norms. -/
@[simp]
theorem norm_starEquiv (x : A) : ‖D.starEquiv x‖ = ‖x‖ :=
  StarAlgEquiv.norm_map D.starEquiv x

/-- The inverse of the constructed finite-stage equivalence preserves norms. -/
@[simp]
theorem norm_starEquiv_symm (y : B) : ‖D.starEquiv.symm y‖ = ‖y‖ :=
  StarAlgEquiv.norm_map D.starEquiv.symm y

/-- The constructed finite-stage equivalence preserves distances. -/
theorem dist_starEquiv (x y : A) : dist (D.starEquiv x) (D.starEquiv y) = dist x y :=
  (isometry_starEquiv D).dist_eq x y

/-- The constructed finite-stage equivalence is continuous. -/
theorem continuous_starEquiv : Continuous D.starEquiv :=
  (isometry_starEquiv D).continuous

/-- The inverse of the constructed finite-stage equivalence is continuous. -/
theorem continuous_starEquiv_symm : Continuous D.starEquiv.symm :=
  (isometry_starEquiv_symm D).continuous

/-- The constructed finite-stage equivalence packaged as a continuous complex
linear equivalence of the two supplied finite C⋆-realizations. -/
noncomputable def stageContinuousLinearEquiv : A ≃L[ℂ] B :=
  cstarStarAlgEquivToContinuousLinearEquiv D.starEquiv

@[simp]
theorem stageContinuousLinearEquiv_apply (x : A) :
    stageContinuousLinearEquiv D x = D.starEquiv x := rfl

/-- **The Pauli-word norm identity.**  The phase-corrected target word has the
same norm as the source word it comes from. -/
theorem norm_starEquiv_word (v : V) :
    ‖D.phase v • D.target.word (D.labelMap v)‖ = ‖D.source.word v‖ := by
  rw [← D.starEquiv_word v, norm_starEquiv]

end StageData

/-! ## The supplied family of finite C⋆-realizations -/

/-- A directed family of finite adapted-coordinate systems (P30) whose finite
stages carry **supplied** finite-dimensional C⋆-algebra structures and whose
**supplied** connecting maps are injective inclusions of stages.

As in P30, the finite-stage star-algebra equivalences are not fields: they are
constructed by P29 from the supplied word, basis and phase data, and their
coherence with the connecting maps is a theorem. -/
structure FiniteCStarCoordinateFamily where
  /-- The index type of finite stages. -/
  Index : Type*
  [indexPreorder : Preorder Index]
  [indexDirected : IsDirectedOrder Index]
  [indexNonempty : Nonempty Index]
  /-- The finite adapted coordinate index type of each stage. -/
  Coord : Index → Type*
  /-- The source Pauli-word label group of each stage. -/
  SourceLabel : Index → Type*
  /-- The target Pauli-word label group of each stage. -/
  TargetLabel : Index → Type*
  [sourceLabelGroup : ∀ i, AddCommGroup (SourceLabel i)]
  [sourceLabelModule : ∀ i, Module PauliBit (SourceLabel i)]
  [targetLabelGroup : ∀ i, AddCommGroup (TargetLabel i)]
  /-- The finite source Pauli/star algebras. -/
  Source : Index → Type*
  /-- The finite target regional/star algebras. -/
  Target : Index → Type*
  /-- The supplied C⋆-structure on each finite source stage. -/
  [sourceCStar : ∀ i, CStarAlgebra (Source i)]
  /-- The supplied C⋆-structure on each finite target stage. -/
  [targetCStar : ∀ i, CStarAlgebra (Target i)]
  /-- The supplied finite dimensionality of each source stage. -/
  [sourceFiniteDimensional : ∀ i, FiniteDimensional ℂ (Source i)]
  /-- The supplied finite dimensionality of each target stage. -/
  [targetFiniteDimensional : ∀ i, FiniteDimensional ℂ (Target i)]
  /-- The supplied finite adapted-coordinate star data of each stage (P29). -/
  stage : ∀ i, FiniteAdaptedCoordinateStarData
    (Coord i) (SourceLabel i) (TargetLabel i) (Source i) (Target i)
  /-- The supplied connecting star-algebra maps of the source system. -/
  sourceConnecting : ∀ i j : Index, i ≤ j → Source i →⋆ₐ[ℂ] Source j
  /-- The supplied connecting star-algebra maps of the target system. -/
  targetConnecting : ∀ i j : Index, i ≤ j → Target i →⋆ₐ[ℂ] Target j
  [sourceDirected : DirectedSystem Source (fun i j le => sourceConnecting i j le)]
  [targetDirected : DirectedSystem Target (fun i j le => targetConnecting i j le)]
  /-- The connecting maps of the source system are injective inclusions. -/
  sourceConnecting_injective : ∀ (i j : Index) (le : i ≤ j),
    Function.Injective (sourceConnecting i j le)
  /-- The connecting maps of the target system are injective inclusions. -/
  targetConnecting_injective : ∀ (i j : Index) (le : i ≤ j),
    Function.Injective (targetConnecting i j le)
  /-- The supplied inclusion of source Pauli-word labels. -/
  sourceLabelIncl : ∀ i j : Index, i ≤ j → SourceLabel i → SourceLabel j
  /-- The supplied inclusion of target Pauli-word labels. -/
  targetLabelIncl : ∀ i j : Index, i ≤ j → TargetLabel i → TargetLabel j
  /-- **Word compatibility, source side.** -/
  sourceWord_connecting : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
    sourceConnecting i j le ((stage i).source.word v) =
      (stage j).source.word (sourceLabelIncl i j le v)
  /-- **Word compatibility, target side.** -/
  targetWord_connecting : ∀ (i j : Index) (le : i ≤ j) (w : TargetLabel i),
    targetConnecting i j le ((stage i).target.word w) =
      (stage j).target.word (targetLabelIncl i j le w)
  /-- **Label compatibility.** -/
  labelMap_incl : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
    (stage j).labelMap (sourceLabelIncl i j le v) =
      targetLabelIncl i j le ((stage i).labelMap v)
  /-- **Phase compatibility.** -/
  phase_incl : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
    (stage j).phase (sourceLabelIncl i j le v) = (stage i).phase v

attribute [instance] FiniteCStarCoordinateFamily.indexPreorder
  FiniteCStarCoordinateFamily.indexDirected
  FiniteCStarCoordinateFamily.indexNonempty
  FiniteCStarCoordinateFamily.sourceLabelGroup
  FiniteCStarCoordinateFamily.sourceLabelModule
  FiniteCStarCoordinateFamily.targetLabelGroup
  FiniteCStarCoordinateFamily.sourceCStar
  FiniteCStarCoordinateFamily.targetCStar
  FiniteCStarCoordinateFamily.sourceFiniteDimensional
  FiniteCStarCoordinateFamily.targetFiniteDimensional
  FiniteCStarCoordinateFamily.sourceDirected
  FiniteCStarCoordinateFamily.targetDirected

namespace FiniteCStarCoordinateFamily

variable (F : FiniteCStarCoordinateFamily)

/-- The finite-stage star-algebra equivalence of a stage, *constructed* from
the P29 coordinate data. -/
noncomputable def stageEquiv (i : F.Index) : F.Source i ≃⋆ₐ[ℂ] F.Target i :=
  (F.stage i).starEquiv

/-- The explicit Pauli-word formula of each constructed stage equivalence. -/
theorem stageEquiv_word (i : F.Index) (v : F.SourceLabel i) :
    F.stageEquiv i ((F.stage i).source.word v) =
      (F.stage i).phase v • (F.stage i).target.word ((F.stage i).labelMap v) :=
  (F.stage i).starEquiv_word v

/-- **The whole-stage commuting squares** (P30), derived from the Pauli-basis
compatibility data rather than assumed. -/
theorem stageEquiv_connecting (i j : F.Index) (le : i ≤ j) (x : F.Source i) :
    F.stageEquiv j (F.sourceConnecting i j le x) =
      F.targetConnecting i j le (F.stageEquiv i x) :=
  starEquiv_connecting_of_pauliBasis (F.stage i) (F.stage j)
    (F.sourceConnecting i j le) (F.targetConnecting i j le)
    (F.sourceLabelIncl i j le) (F.targetLabelIncl i j le)
    (F.sourceWord_connecting i j le) (F.targetWord_connecting i j le)
    (F.labelMap_incl i j le) (F.phase_incl i j le) x

/-! ### Isometry and continuity of the constructed stage maps -/

/-- Each constructed stage equivalence is isometric. -/
theorem isometry_stageEquiv (i : F.Index) : Isometry (F.stageEquiv i) :=
  isometry_starEquiv (F.stage i)

/-- Each constructed stage equivalence preserves norms. -/
@[simp]
theorem norm_stageEquiv (i : F.Index) (x : F.Source i) : ‖F.stageEquiv i x‖ = ‖x‖ :=
  norm_starEquiv (F.stage i) x

/-- Each constructed stage equivalence preserves distances. -/
theorem dist_stageEquiv (i : F.Index) (x y : F.Source i) :
    dist (F.stageEquiv i x) (F.stageEquiv i y) = dist x y :=
  (F.isometry_stageEquiv i).dist_eq x y

/-- Each constructed stage equivalence is continuous. -/
theorem continuous_stageEquiv (i : F.Index) : Continuous (F.stageEquiv i) :=
  (F.isometry_stageEquiv i).continuous

/-- Each inverse stage equivalence is isometric. -/
theorem isometry_stageEquiv_symm (i : F.Index) : Isometry (F.stageEquiv i).symm :=
  isometry_starEquiv_symm (F.stage i)

/-- Each inverse stage equivalence preserves norms. -/
@[simp]
theorem norm_stageEquiv_symm (i : F.Index) (y : F.Target i) :
    ‖(F.stageEquiv i).symm y‖ = ‖y‖ :=
  norm_starEquiv_symm (F.stage i) y

/-- Each inverse stage equivalence is continuous. -/
theorem continuous_stageEquiv_symm (i : F.Index) : Continuous (F.stageEquiv i).symm :=
  (F.isometry_stageEquiv_symm i).continuous

/-- Each constructed stage equivalence packaged as a continuous complex linear
equivalence of finite C⋆-realizations. -/
noncomputable def stageContinuousLinearEquiv (i : F.Index) : F.Source i ≃L[ℂ] F.Target i :=
  FiniteCoordinateMapNormControl.stageContinuousLinearEquiv (F.stage i)

@[simp]
theorem stageContinuousLinearEquiv_apply (i : F.Index) (x : F.Source i) :
    F.stageContinuousLinearEquiv i x = F.stageEquiv i x := rfl

/-! ### Norm control of the connecting maps -/

/-- The source connecting maps are isometric. -/
theorem isometry_sourceConnecting (i j : F.Index) (le : i ≤ j) :
    Isometry (F.sourceConnecting i j le) :=
  isometry_starAlgHom_of_injective _ (F.sourceConnecting_injective i j le)

/-- The target connecting maps are isometric. -/
theorem isometry_targetConnecting (i j : F.Index) (le : i ≤ j) :
    Isometry (F.targetConnecting i j le) :=
  isometry_starAlgHom_of_injective _ (F.targetConnecting_injective i j le)

/-- The source connecting maps preserve norms. -/
@[simp]
theorem norm_sourceConnecting (i j : F.Index) (le : i ≤ j) (x : F.Source i) :
    ‖F.sourceConnecting i j le x‖ = ‖x‖ :=
  norm_starAlgHom_apply_of_injective _ (F.sourceConnecting_injective i j le) x

/-- The target connecting maps preserve norms. -/
@[simp]
theorem norm_targetConnecting (i j : F.Index) (le : i ≤ j) (y : F.Target i) :
    ‖F.targetConnecting i j le y‖ = ‖y‖ :=
  norm_starAlgHom_apply_of_injective _ (F.targetConnecting_injective i j le) y

/-- The connecting maps are continuous. -/
theorem continuous_sourceConnecting (i j : F.Index) (le : i ≤ j) :
    Continuous (F.sourceConnecting i j le) :=
  (F.isometry_sourceConnecting i j le).continuous

/-- The connecting maps are continuous. -/
theorem continuous_targetConnecting (i j : F.Index) (le : i ≤ j) :
    Continuous (F.targetConnecting i j le) :=
  (F.isometry_targetConnecting i j le).continuous

/-! ### The inclusion squares preserve the norm estimates -/

/-- **Norm control of the inclusion square.**  All four corners of the P30
commuting square attached to a stage element have the same norm. -/
theorem norm_square (i j : F.Index) (le : i ≤ j) (x : F.Source i) :
    ‖F.stageEquiv j (F.sourceConnecting i j le x)‖ = ‖x‖ ∧
      ‖F.targetConnecting i j le (F.stageEquiv i x)‖ = ‖x‖ ∧
      ‖F.sourceConnecting i j le x‖ = ‖x‖ ∧ ‖F.stageEquiv i x‖ = ‖x‖ := by
  refine ⟨?_, ?_, F.norm_sourceConnecting i j le x, F.norm_stageEquiv i x⟩
  · rw [F.norm_stageEquiv, F.norm_sourceConnecting]
  · rw [F.norm_targetConnecting, F.norm_stageEquiv]

/-- The two composite routes around the inclusion square agree, and preserve
the norm. -/
theorem norm_square_of_le (i j : F.Index) (le : i ≤ j) (x : F.Source i) :
    ‖F.stageEquiv j (F.sourceConnecting i j le x)‖ =
      ‖F.targetConnecting i j le (F.stageEquiv i x)‖ := by
  rw [F.stageEquiv_connecting]

/-- Distance form of the square estimate. -/
theorem dist_square (i j : F.Index) (le : i ≤ j) (x y : F.Source i) :
    dist (F.targetConnecting i j le (F.stageEquiv i x))
        (F.targetConnecting i j le (F.stageEquiv i y)) = dist x y := by
  rw [(F.isometry_targetConnecting i j le).dist_eq, F.dist_stageEquiv]

/-- The square estimate in the norm of the *later* stage: passing through the
later stage does not change the norm of the transported element. -/
theorem norm_stageEquiv_connecting (i j : F.Index) (le : i ≤ j) (x : F.Source i) :
    ‖F.stageEquiv j (F.sourceConnecting i j le x)‖ = ‖F.stageEquiv i x‖ := by
  rw [F.norm_stageEquiv, F.norm_sourceConnecting, F.norm_stageEquiv]

end FiniteCStarCoordinateFamily

/-! ## The dense-subalgebra estimate

Supplied ambient C⋆-algebras with supplied injective stage embeddings.  No
completion is constructed: the ambient algebras, the embeddings, their
compatibility with the connecting maps, and the density of the union of the
stage images are all hypotheses. -/

/-- Supplied embeddings of the finite stages of `F` into ambient C⋆-algebras. -/
structure StageCStarEmbeddings (F : FiniteCStarCoordinateFamily) where
  /-- The supplied ambient source C⋆-algebra. -/
  SourceCStar : Type*
  /-- The supplied ambient target C⋆-algebra. -/
  TargetCStar : Type*
  /-- Its supplied C⋆-structure. -/
  [sourceCStar : CStarAlgebra SourceCStar]
  /-- Its supplied C⋆-structure. -/
  [targetCStar : CStarAlgebra TargetCStar]
  /-- The supplied stage embeddings of the source system. -/
  sourceIncl : ∀ i, F.Source i →⋆ₐ[ℂ] SourceCStar
  /-- The supplied stage embeddings of the target system. -/
  targetIncl : ∀ i, F.Target i →⋆ₐ[ℂ] TargetCStar
  /-- The stage embeddings are injective. -/
  sourceIncl_injective : ∀ i, Function.Injective (sourceIncl i)
  /-- The stage embeddings are injective. -/
  targetIncl_injective : ∀ i, Function.Injective (targetIncl i)
  /-- Compatibility with the source connecting maps. -/
  sourceIncl_connecting : ∀ (i j : F.Index) (le : i ≤ j) (x : F.Source i),
    sourceIncl j (F.sourceConnecting i j le x) = sourceIncl i x
  /-- Compatibility with the target connecting maps. -/
  targetIncl_connecting : ∀ (i j : F.Index) (le : i ≤ j) (y : F.Target i),
    targetIncl j (F.targetConnecting i j le y) = targetIncl i y
  /-- The union of the stage images is dense in the ambient source algebra. -/
  sourceCore_dense : Dense (⋃ i, Set.range (sourceIncl i))

attribute [instance] StageCStarEmbeddings.sourceCStar StageCStarEmbeddings.targetCStar

namespace StageCStarEmbeddings

variable {F : FiniteCStarCoordinateFamily} (E : StageCStarEmbeddings F)

/-- Each stage embedding is isometric. -/
theorem isometry_sourceIncl (i : F.Index) : Isometry (E.sourceIncl i) :=
  isometry_starAlgHom_of_injective _ (E.sourceIncl_injective i)

/-- Each stage embedding is isometric. -/
theorem isometry_targetIncl (i : F.Index) : Isometry (E.targetIncl i) :=
  isometry_starAlgHom_of_injective _ (E.targetIncl_injective i)

/-- Each stage embedding preserves norms. -/
@[simp]
theorem norm_sourceIncl (i : F.Index) (x : F.Source i) : ‖E.sourceIncl i x‖ = ‖x‖ :=
  norm_starAlgHom_apply_of_injective _ (E.sourceIncl_injective i) x

/-- Each stage embedding preserves norms. -/
@[simp]
theorem norm_targetIncl (i : F.Index) (y : F.Target i) : ‖E.targetIncl i y‖ = ‖y‖ :=
  norm_starAlgHom_apply_of_injective _ (E.targetIncl_injective i) y

/-- The dense `*`-subalgebra of the ambient source algebra spanned by the
finite stages, as a set. -/
def sourceCore : Set E.SourceCStar := ⋃ i, Set.range (E.sourceIncl i)

theorem mem_sourceCore (i : F.Index) (x : F.Source i) : E.sourceIncl i x ∈ E.sourceCore :=
  Set.mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩

theorem dense_sourceCore : Dense E.sourceCore := E.sourceCore_dense

/-- **Well-definedness of the coherent algebraic map on the dense
subalgebra.**  Two stage representatives with the same image in the ambient
source algebra have the same transported image in the ambient target
algebra. -/
theorem targetIncl_stageEquiv_congr {i j : F.Index} {x : F.Source i} {y : F.Source j}
    (h : E.sourceIncl i x = E.sourceIncl j y) :
    E.targetIncl i (F.stageEquiv i x) = E.targetIncl j (F.stageEquiv j y) := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hk : F.sourceConnecting i k hik x = F.sourceConnecting j k hjk y := by
    refine E.sourceIncl_injective k ?_
    rw [E.sourceIncl_connecting, E.sourceIncl_connecting, h]
  have h' : F.targetConnecting i k hik (F.stageEquiv i x) =
      F.targetConnecting j k hjk (F.stageEquiv j y) := by
    rw [← F.stageEquiv_connecting, ← F.stageEquiv_connecting, hk]
  have := congrArg (E.targetIncl k) h'
  rwa [E.targetIncl_connecting, E.targetIncl_connecting] at this

/-- **The dense-subalgebra estimate.**  Across arbitrary stages, the coherent
algebraic map preserves the norm of differences. -/
theorem norm_sub_stageImages (i j : F.Index) (x : F.Source i) (y : F.Source j) :
    ‖E.targetIncl i (F.stageEquiv i x) - E.targetIncl j (F.stageEquiv j y)‖ =
      ‖E.sourceIncl i x - E.sourceIncl j y‖ := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hsx : E.sourceIncl i x = E.sourceIncl k (F.sourceConnecting i k hik x) :=
    (E.sourceIncl_connecting i k hik x).symm
  have hsy : E.sourceIncl j y = E.sourceIncl k (F.sourceConnecting j k hjk y) :=
    (E.sourceIncl_connecting j k hjk y).symm
  have htx : E.targetIncl i (F.stageEquiv i x) =
      E.targetIncl k (F.stageEquiv k (F.sourceConnecting i k hik x)) := by
    rw [F.stageEquiv_connecting, E.targetIncl_connecting]
  have hty : E.targetIncl j (F.stageEquiv j y) =
      E.targetIncl k (F.stageEquiv k (F.sourceConnecting j k hjk y)) := by
    rw [F.stageEquiv_connecting, E.targetIncl_connecting]
  rw [hsx, hsy, htx, hty, ← map_sub, ← map_sub, ← map_sub, E.norm_targetIncl,
    F.norm_stageEquiv, E.norm_sourceIncl]

/-- Distance form of the dense-subalgebra estimate. -/
theorem dist_stageImages (i j : F.Index) (x : F.Source i) (y : F.Source j) :
    dist (E.targetIncl i (F.stageEquiv i x)) (E.targetIncl j (F.stageEquiv j y)) =
      dist (E.sourceIncl i x) (E.sourceIncl j y) := by
  simp only [dist_eq_norm]
  exact E.norm_sub_stageImages i j x y

/-- **The packaged estimate.**  Any map on the ambient source algebra that has
the coherent finite-stage formula is distance preserving on the dense
subalgebra of stage elements.  This is exactly the estimate required to extend
the coherent algebraic map to the completions. -/
theorem core_estimate (g : E.SourceCStar → E.TargetCStar)
    (hg : ∀ (i : F.Index) (x : F.Source i),
      g (E.sourceIncl i x) = E.targetIncl i (F.stageEquiv i x))
    {a b : E.SourceCStar} (ha : a ∈ E.sourceCore) (hb : b ∈ E.sourceCore) :
    dist (g a) (g b) = dist a b := by
  obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 ha
  obtain ⟨j, y, rfl⟩ := Set.mem_iUnion.1 hb
  rw [hg, hg]
  exact E.dist_stageImages i j x y

/-- **Uniqueness of a continuous extension.**  Two continuous maps with the
coherent finite-stage formula agree on the whole ambient source algebra. -/
theorem ext_of_stage_formula (g h : E.SourceCStar → E.TargetCStar)
    (hgc : Continuous g) (hhc : Continuous h)
    (hg : ∀ (i : F.Index) (x : F.Source i),
      g (E.sourceIncl i x) = E.targetIncl i (F.stageEquiv i x))
    (hh : ∀ (i : F.Index) (x : F.Source i),
      h (E.sourceIncl i x) = E.targetIncl i (F.stageEquiv i x)) :
    g = h := by
  refine Continuous.ext_on E.sourceCore_dense hgc hhc ?_
  rintro a ha
  obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 ha
  rw [hg, hh]

/-- **Automatic isometry of a continuous extension.**  A continuous map with
the coherent finite-stage formula is isometric on the whole ambient source
algebra: the estimate on the dense subalgebra propagates to the closure. -/
theorem isometry_of_stage_formula (g : E.SourceCStar → E.TargetCStar)
    (hgc : Continuous g)
    (hg : ∀ (i : F.Index) (x : F.Source i),
      g (E.sourceIncl i x) = E.targetIncl i (F.stageEquiv i x)) :
    Isometry g := by
  rw [isometry_iff_dist_eq]
  have hcont₁ : Continuous fun p : E.SourceCStar × E.SourceCStar => dist (g p.1) (g p.2) :=
    Continuous.dist (hgc.comp continuous_fst) (hgc.comp continuous_snd)
  have hcont₂ : Continuous fun p : E.SourceCStar × E.SourceCStar => dist p.1 p.2 :=
    continuous_dist
  have hdense : Dense (E.sourceCore ×ˢ E.sourceCore) :=
    E.sourceCore_dense.prod E.sourceCore_dense
  have h := Continuous.ext_on hdense hcont₁ hcont₂ ?_
  · intro a b
    exact congrFun h (a, b)
  · rintro ⟨a, b⟩ hab
    exact E.core_estimate g hg hab.1 hab.2

end StageCStarEmbeddings

/-! ## A sanity instance

The interfaces are not vacuous: the one-stage family built from the trivial
P29 data, with `ℂ` as both finite stage and ambient algebra, satisfies every
field simultaneously.  This is a consistency check on the bundles, not a model
of the manuscript's regional algebras. -/

/-- A one-stage instance of `FiniteCStarCoordinateFamily`. -/
noncomputable def trivialCStarFamily : FiniteCStarCoordinateFamily where
  Index := Unit
  Coord := fun _ => Empty
  SourceLabel := fun _ => PUnit
  TargetLabel := fun _ => PUnit
  Source := fun _ => ℂ
  Target := fun _ => ℂ
  stage := fun _ => FiniteAdaptedCoordinate.trivialData
  sourceConnecting := fun _ _ _ => StarAlgHom.id ℂ ℂ
  targetConnecting := fun _ _ _ => StarAlgHom.id ℂ ℂ
  sourceDirected := ⟨by intros; rfl, by intros; rfl⟩
  targetDirected := ⟨by intros; rfl, by intros; rfl⟩
  sourceConnecting_injective := fun _ _ _ _ _ h => h
  targetConnecting_injective := fun _ _ _ _ _ h => h
  sourceLabelIncl := fun _ _ _ v => v
  targetLabelIncl := fun _ _ _ w => w
  sourceWord_connecting := by intros; rfl
  targetWord_connecting := by intros; rfl
  labelMap_incl := by intros; rfl
  phase_incl := by intros; rfl

/-- A one-stage instance of `StageCStarEmbeddings`. -/
noncomputable def trivialEmbeddings : StageCStarEmbeddings trivialCStarFamily where
  SourceCStar := ℂ
  TargetCStar := ℂ
  sourceIncl := fun _ => StarAlgHom.id ℂ ℂ
  targetIncl := fun _ => StarAlgHom.id ℂ ℂ
  sourceIncl_injective := fun _ _ _ h => h
  targetIncl_injective := fun _ _ _ h => h
  sourceIncl_connecting := by intros; rfl
  targetIncl_connecting := by intros; rfl
  sourceCore_dense := by
    refine dense_univ.mono ?_
    intro z _
    exact Set.mem_iUnion.2 ⟨(), z, rfl⟩

end FiniteCoordinateMapNormControl

end AristotleCandidates
