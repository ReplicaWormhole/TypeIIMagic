import AristotleCandidates.FiniteAdaptedCoordinateStarEquiv
import AristotleCandidates.InfiniteAlgebraicRegionalEquiv
import Formalization.CoherentBasisEquiv

/-!
# Coherence of the constructed finite coordinate equivalences

Context declaration: source basis `main.tex:1671-1679` (the local/adapted
symplectic basis with finite support) and `main.tex:1915-1920` (the *proposed*
star isomorphism from a Pauli algebra to a regional algebra).  This module
formalizes only the finite-stage, purely algebraic coherence step of that
proposal.

## What is supplied and what is derived

For each stage `i` of a directed index type the supplied data
(`DirectedFiniteCoordinateFamily`) consists of

* the finite adapted-coordinate star data of P29
  (`FiniteAdaptedCoordinate.FiniteAdaptedCoordinateStarData`), from which the
  finite-stage star-algebra equivalence `starEquiv i` is *constructed*, never
  assumed;
* connecting star-algebra maps `sourceConnecting`, `targetConnecting` of the
  two finite directed systems;
* inclusion maps `sourceLabelIncl`, `targetLabelIncl` of the finite Pauli-word
  label sets; and
* three *explicit* Pauli-basis compatibility equations: the connecting maps
  send Pauli words to Pauli words of the included labels
  (`sourceWord_connecting`, `targetWord_connecting`), the label maps commute
  with the inclusions (`labelMap_incl`), and the phases are compatible with the
  source inclusion (`phase_incl`).

From this data — and from nothing else — the whole-stage commuting square

`starEquiv j (sourceConnecting i j le x) = targetConnecting i j le (starEquiv i x)`

is *proved* for every `x`, by basis extensionality on the finite Pauli-word
basis (`starAlgEquiv_commutes_of_source_basis` of
`Formalization/CoherentBasisEquiv.lean`).  This is exactly the field
`stageEquiv_connecting` required by the P23 interface
`InfiniteAlgebraicRegionalEquiv.RegionalLimitData`, and
`toRegionalLimitData` assembles that structure with the coherence *derived*
rather than assumed.

## What is *not* claimed

The three compatibility equations are genuine auxiliary assumptions on the
chosen finite Pauli-word bases; they are not consequences of symplecticity of
the adapted coordinates, which controls commutators of words but not the
chosen multiplier, involution or phase conventions.  No gLU condition,
refinement scheme, layer-coherence assumption, C⋆-norm, completion,
continuity, normality or von Neumann statement is used or claimed anywhere in
this file; the content is finite-stage algebra plus the purely algebraic
direct-limit interface.
-/

namespace StabilizerHyperfinite

namespace FiniteCoordinateEquivCoherence

open FiniteAdaptedCoordinate

/-!
### The single commuting square

The following theorem is the whole content of the coherence step: an equality
of two star-algebra maps on a whole finite stage, deduced from equations on the
chosen finite Pauli-word basis only.
-/

section Square

variable {I₁ V₁ W₁ A₁ B₁ I₂ V₂ W₂ A₂ B₂ : Type*}
variable [AddCommGroup V₁] [Module PauliBit V₁] [AddCommGroup W₁]
variable [Semiring A₁] [Algebra ℂ A₁] [StarRing A₁] [StarModule ℂ A₁]
variable [Semiring B₁] [Algebra ℂ B₁] [StarRing B₁] [StarModule ℂ B₁]
variable [AddCommGroup V₂] [Module PauliBit V₂] [AddCommGroup W₂]
variable [Semiring A₂] [Algebra ℂ A₂] [StarRing A₂] [StarModule ℂ A₂]
variable [Semiring B₂] [Algebra ℂ B₂] [StarRing B₂] [StarModule ℂ B₂]

/-- **The finite-stage commuting square.**

Given two stages of finite adapted-coordinate data, connecting star maps of the
source and target algebras, and the explicit compatibility of the connecting
maps with the finite Pauli-word bases, the labels and the phases, the
*constructed* finite-stage equivalences of P29 commute with the connecting maps
on the whole source algebra. -/
theorem starEquiv_connecting_of_pauliBasis
    (D₁ : FiniteAdaptedCoordinateStarData I₁ V₁ W₁ A₁ B₁)
    (D₂ : FiniteAdaptedCoordinateStarData I₂ V₂ W₂ A₂ B₂)
    (sourceConnecting : A₁ →⋆ₐ[ℂ] A₂) (targetConnecting : B₁ →⋆ₐ[ℂ] B₂)
    (sourceLabelIncl : V₁ → V₂) (targetLabelIncl : W₁ → W₂)
    (h_sourceWord : ∀ v, sourceConnecting (D₁.source.word v) =
      D₂.source.word (sourceLabelIncl v))
    (h_targetWord : ∀ w, targetConnecting (D₁.target.word w) =
      D₂.target.word (targetLabelIncl w))
    (h_labelMap : ∀ v, D₂.labelMap (sourceLabelIncl v) = targetLabelIncl (D₁.labelMap v))
    (h_phase : ∀ v, D₂.phase (sourceLabelIncl v) = D₁.phase v)
    (x : A₁) :
    D₂.starEquiv (sourceConnecting x) = targetConnecting (D₁.starEquiv x) := by
  refine starAlgEquiv_commutes_of_source_basis
    (sourceBasis := D₁.wordBasis) (sourceBasis' := D₂.wordBasis)
    (sourceLabelMap := sourceLabelIncl)
    (targetVector := fun v => D₁.phase v • D₁.target.word (D₁.labelMap v))
    (targetVector' := fun v => D₂.phase v • D₂.target.word (D₂.labelMap v))
    (f := sourceConnecting) (h := targetConnecting)
    (e := D₁.starEquiv) (e' := D₂.starEquiv) ?_ ?_ ?_ ?_ x
  · intro v
    rw [D₁.wordBasis_apply, D₂.wordBasis_apply, h_sourceWord]
  · intro v
    rw [D₁.wordBasis_apply, D₁.starEquiv_word]
  · intro v
    rw [D₂.wordBasis_apply, D₂.starEquiv_word]
  · intro v
    rw [map_smul, h_targetWord]
    simp only [h_phase, h_labelMap]

end Square

/-!
### A directed family of finite coordinate systems
-/

/-- A directed family of finite adapted-coordinate systems together with the
connecting maps of the two finite directed systems and the explicit Pauli-basis
compatibility data.

All fields are inputs, but note that no coherence of the finite-stage
star-algebra equivalences is assumed: those equivalences are constructed by
P29, and their coherence is *proved* in `stageEquiv_connecting`. -/
structure DirectedFiniteCoordinateFamily where
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
  /-- The finite source Pauli/star algebras. -/
  Source : Index → Type*
  /-- The finite target regional/star algebras. -/
  Target : Index → Type*
  [sourceLabelGroup : ∀ i, AddCommGroup (SourceLabel i)]
  [sourceLabelModule : ∀ i, Module PauliBit (SourceLabel i)]
  [targetLabelGroup : ∀ i, AddCommGroup (TargetLabel i)]
  [sourceSemiring : ∀ i, Semiring (Source i)]
  [sourceAlgebra : ∀ i, Algebra ℂ (Source i)]
  [sourceStar : ∀ i, StarRing (Source i)]
  [sourceStarModule : ∀ i, StarModule ℂ (Source i)]
  [targetSemiring : ∀ i, Semiring (Target i)]
  [targetAlgebra : ∀ i, Algebra ℂ (Target i)]
  [targetStar : ∀ i, StarRing (Target i)]
  [targetStarModule : ∀ i, StarModule ℂ (Target i)]
  /-- The supplied finite adapted-coordinate star data of each stage (P29). -/
  stage : ∀ i, FiniteAdaptedCoordinateStarData
    (Coord i) (SourceLabel i) (TargetLabel i) (Source i) (Target i)
  /-- The supplied connecting star-algebra maps of the source system. -/
  sourceConnecting : ∀ i j : Index, i ≤ j → Source i →⋆ₐ[ℂ] Source j
  /-- The supplied connecting star-algebra maps of the target system. -/
  targetConnecting : ∀ i j : Index, i ≤ j → Target i →⋆ₐ[ℂ] Target j
  [sourceDirected : DirectedSystem Source (fun i j le => sourceConnecting i j le)]
  [targetDirected : DirectedSystem Target (fun i j le => targetConnecting i j le)]
  /-- The supplied inclusion of source Pauli-word labels. -/
  sourceLabelIncl : ∀ i j : Index, i ≤ j → SourceLabel i → SourceLabel j
  /-- The supplied inclusion of target Pauli-word labels. -/
  targetLabelIncl : ∀ i j : Index, i ≤ j → TargetLabel i → TargetLabel j
  /-- **Word compatibility, source side.**  The connecting map carries each
  source Pauli word to the source Pauli word of the included label. -/
  sourceWord_connecting : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
    sourceConnecting i j le ((stage i).source.word v) =
      (stage j).source.word (sourceLabelIncl i j le v)
  /-- **Word compatibility, target side.**  The connecting map carries each
  target Pauli word to the target Pauli word of the included label. -/
  targetWord_connecting : ∀ (i j : Index) (le : i ≤ j) (w : TargetLabel i),
    targetConnecting i j le ((stage i).target.word w) =
      (stage j).target.word (targetLabelIncl i j le w)
  /-- **Label compatibility.**  The stagewise label maps commute with the
  inclusions. -/
  labelMap_incl : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
    (stage j).labelMap (sourceLabelIncl i j le v) =
      targetLabelIncl i j le ((stage i).labelMap v)
  /-- **Phase compatibility.**  The stagewise phases agree along the source
  inclusion. -/
  phase_incl : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
    (stage j).phase (sourceLabelIncl i j le v) = (stage i).phase v

attribute [instance] DirectedFiniteCoordinateFamily.indexPreorder
  DirectedFiniteCoordinateFamily.indexDirected
  DirectedFiniteCoordinateFamily.indexNonempty
  DirectedFiniteCoordinateFamily.sourceLabelGroup
  DirectedFiniteCoordinateFamily.sourceLabelModule
  DirectedFiniteCoordinateFamily.targetLabelGroup
  DirectedFiniteCoordinateFamily.sourceSemiring
  DirectedFiniteCoordinateFamily.sourceAlgebra
  DirectedFiniteCoordinateFamily.sourceStar
  DirectedFiniteCoordinateFamily.sourceStarModule
  DirectedFiniteCoordinateFamily.targetSemiring
  DirectedFiniteCoordinateFamily.targetAlgebra
  DirectedFiniteCoordinateFamily.targetStar
  DirectedFiniteCoordinateFamily.targetStarModule
  DirectedFiniteCoordinateFamily.sourceDirected
  DirectedFiniteCoordinateFamily.targetDirected

namespace DirectedFiniteCoordinateFamily

variable (F : DirectedFiniteCoordinateFamily)

/-- The finite-stage star-algebra equivalence of a stage, *constructed* from
the P29 coordinate data. -/
noncomputable def stageEquiv (i : F.Index) : F.Source i ≃⋆ₐ[ℂ] F.Target i :=
  (F.stage i).starEquiv

/-- The explicit Pauli-word formula of each constructed stage equivalence. -/
theorem stageEquiv_word (i : F.Index) (v : F.SourceLabel i) :
    F.stageEquiv i ((F.stage i).source.word v) =
      (F.stage i).phase v • (F.stage i).target.word ((F.stage i).labelMap v) :=
  (F.stage i).starEquiv_word v

/-- **The whole-stage commuting squares.**

This is exactly the coherence required as the field
`stageEquiv_connecting` of `RegionalLimitData`; it is derived from the
Pauli-basis compatibility data, not assumed. -/
theorem stageEquiv_connecting (i j : F.Index) (le : i ≤ j) (x : F.Source i) :
    F.stageEquiv j (F.sourceConnecting i j le x) =
      F.targetConnecting i j le (F.stageEquiv i x) :=
  starEquiv_connecting_of_pauliBasis (F.stage i) (F.stage j)
    (F.sourceConnecting i j le) (F.targetConnecting i j le)
    (F.sourceLabelIncl i j le) (F.targetLabelIncl i j le)
    (F.sourceWord_connecting i j le) (F.targetWord_connecting i j le)
    (F.labelMap_incl i j le) (F.phase_incl i j le) x

/-- The inverse stage equivalences satisfy the mirrored commuting squares. -/
theorem stageEquiv_symm_connecting (i j : F.Index) (le : i ≤ j) (y : F.Target i) :
    (F.stageEquiv j).symm (F.targetConnecting i j le y) =
      F.sourceConnecting i j le ((F.stageEquiv i).symm y) := by
  have h := F.stageEquiv_connecting i j le ((F.stageEquiv i).symm y)
  rw [(F.stageEquiv i).apply_symm_apply] at h
  exact (F.stageEquiv j).symm_apply_eq.mpr h.symm

/-- **The P23 interface, with derived coherence.**  The directed family of
finite coordinate systems assembles into the `RegionalLimitData` of P23; its
`stageEquiv_connecting` field is the theorem above rather than an assumption. -/
noncomputable def toRegionalLimitData :
    InfiniteAlgebraicRegionalEquiv.RegionalLimitData where
  Index := F.Index
  Source := F.Source
  Target := F.Target
  sourceConnecting := F.sourceConnecting
  targetConnecting := F.targetConnecting
  stageEquiv := F.stageEquiv
  stageEquiv_connecting := F.stageEquiv_connecting

@[simp]
theorem toRegionalLimitData_stageEquiv (i : F.Index) :
    F.toRegionalLimitData.stageEquiv i = F.stageEquiv i := rfl

end DirectedFiniteCoordinateFamily

/-!
### A sanity instance

The interface is not vacuous: the one-stage family built from the trivial P29
data satisfies every field simultaneously.  This is a consistency check on the
bundle, not a model of the manuscript's regional algebras.
-/

/-- A one-stage instance of `DirectedFiniteCoordinateFamily`, showing that all
fields can be met at once. -/
noncomputable def trivialFamily : DirectedFiniteCoordinateFamily where
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
  sourceLabelIncl := fun _ _ _ v => v
  targetLabelIncl := fun _ _ _ w => w
  sourceWord_connecting := by intros; rfl
  targetWord_connecting := by intros; rfl
  labelMap_incl := by intros; rfl
  phase_incl := by intros; rfl

end FiniteCoordinateEquivCoherence

end StabilizerHyperfinite
