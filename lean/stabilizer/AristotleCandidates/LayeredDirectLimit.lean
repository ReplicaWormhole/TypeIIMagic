import Formalization.CoherentBasisEquiv
import Formalization.AlgebraicLimitStarHom

/-!
# Conditional layered direct-limit equivalence

This module bundles the data of two finite-stage directed systems that are
already identified stage by stage, and passes that identification to the
algebraic direct limits.

Everything in the bundle is *supplied input*:

* the finite-stage star-algebra equivalences `stageEquiv i`;
* the finite Pauli-word bases `sourceBasis i` and `targetBasis i` of the two
  finite stages;
* the refinement embeddings `sourceEmbedding` and `targetEmbedding` of both
  directed systems;
* the label maps `sourceLabelMap`, `targetLabelMap`, `wordMap` and the phase
  function producing the phase-corrected word images; and
* the finite-stage basis equations saying that each finite square commutes on
  Pauli words.

Nothing here claims that a bare gLU condition, a finite-support hypothesis, or
an adapted symplectic basis by itself produces these finite-stage maps or their
coherence: they are hypotheses of the structure `LayeredSystem`.

From those hypotheses the whole-stage compatibility is derived with
`StabilizerHyperfinite.starAlgEquiv_commutes_of_source_basis`, and the induced
equivalence of the two algebraic directed limits is obtained from
`StabilizerHyperfinite.algebraicLimitStarAlgEquiv`.  Its value on every
finite-stage representative is computed.

No C⋆ completion, normal representation, GNS equivalence, or factor
classification is constructed here; the entire content is purely algebraic.
-/

namespace StabilizerHyperfinite

namespace LayeredDirectLimit

/-- A pair of finite-stage directed systems, together with supplied
finite-stage star-algebra equivalences and the finite Pauli-word data
witnessing that every finite square commutes on words.

All of the finite-stage maps (`stageEquiv`), the two Pauli-word bases, the
refinement embeddings, the label maps and the phases are *inputs*; so are the
coherence equations relating them. -/
structure LayeredSystem where
  /-- The index type of finite stages. -/
  Index : Type*
  [indexPreorder : Preorder Index]
  [indexDirected : IsDirectedOrder Index]
  [indexNonempty : Nonempty Index]
  /-- The source finite-stage algebras. -/
  Source : Index → Type*
  /-- The target finite-stage algebras. -/
  Target : Index → Type*
  [sourceSemiring : ∀ i, Semiring (Source i)]
  [sourceStar : ∀ i, StarRing (Source i)]
  [sourceAlgebra : ∀ i, Algebra ℂ (Source i)]
  [targetSemiring : ∀ i, Semiring (Target i)]
  [targetStar : ∀ i, StarRing (Target i)]
  [targetAlgebra : ∀ i, Algebra ℂ (Target i)]
  /-- Supplied refinement embeddings of the source system. -/
  sourceEmbedding : ∀ i j : Index, i ≤ j → Source i →⋆ₐ[ℂ] Source j
  /-- Supplied refinement embeddings of the target system. -/
  targetEmbedding : ∀ i j : Index, i ≤ j → Target i →⋆ₐ[ℂ] Target j
  [sourceDirected : DirectedSystem Source (fun i j le => sourceEmbedding i j le)]
  [targetDirected : DirectedSystem Target (fun i j le => targetEmbedding i j le)]
  /-- Labels of the finite source Pauli words at each stage. -/
  SourceLabel : Index → Type*
  /-- Labels of the finite target Pauli words at each stage. -/
  TargetLabel : Index → Type*
  /-- The supplied finite source Pauli-word basis. -/
  sourceBasis : ∀ i, Module.Basis (SourceLabel i) ℂ (Source i)
  /-- The supplied finite target Pauli-word basis. -/
  targetBasis : ∀ i, Module.Basis (TargetLabel i) ℂ (Target i)
  /-- The supplied finite-stage star-algebra equivalences. -/
  stageEquiv : ∀ i, Source i ≃⋆ₐ[ℂ] Target i
  /-- The label map recording how a source word is relabelled by refinement. -/
  sourceLabelMap : ∀ i j : Index, i ≤ j → SourceLabel i → SourceLabel j
  /-- The label map recording how a target word is relabelled by refinement. -/
  targetLabelMap : ∀ i j : Index, i ≤ j → TargetLabel i → TargetLabel j
  /-- The word map underlying the finite-stage equivalence. -/
  wordMap : ∀ i, SourceLabel i → TargetLabel i
  /-- The phase attached to the image of a source word. -/
  phase : ∀ i, SourceLabel i → ℂ
  /-- Refinement sends a source Pauli word to a source Pauli word. -/
  sourceBasis_embedding : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
    sourceEmbedding i j le (sourceBasis i v) = sourceBasis j (sourceLabelMap i j le v)
  /-- Refinement sends a target Pauli word to a target Pauli word. -/
  targetBasis_embedding : ∀ (i j : Index) (le : i ≤ j) (w : TargetLabel i),
    targetEmbedding i j le (targetBasis i w) = targetBasis j (targetLabelMap i j le w)
  /-- The finite-stage equivalence sends each source Pauli word to a
  phase-corrected target Pauli word. -/
  stageEquiv_basis : ∀ (i : Index) (v : SourceLabel i),
    stageEquiv i (sourceBasis i v) = phase i v • targetBasis i (wordMap i v)
  /-- Phases are unchanged by refinement. -/
  phase_sourceLabelMap : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
    phase j (sourceLabelMap i j le v) = phase i v
  /-- The word map intertwines the two label maps. -/
  wordMap_sourceLabelMap : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
    wordMap j (sourceLabelMap i j le v) = targetLabelMap i j le (wordMap i v)

attribute [instance] LayeredSystem.indexPreorder LayeredSystem.indexDirected
  LayeredSystem.indexNonempty LayeredSystem.sourceSemiring LayeredSystem.sourceStar
  LayeredSystem.sourceAlgebra LayeredSystem.targetSemiring LayeredSystem.targetStar
  LayeredSystem.targetAlgebra LayeredSystem.sourceDirected LayeredSystem.targetDirected

namespace LayeredSystem

variable (S : LayeredSystem)

/-- The phase-corrected image of a finite source Pauli word inside the
corresponding finite target stage. -/
noncomputable def phaseWord (i : S.Index) (v : S.SourceLabel i) : S.Target i :=
  S.phase i v • S.targetBasis i (S.wordMap i v)

theorem stageEquiv_sourceBasis (i : S.Index) (v : S.SourceLabel i) :
    S.stageEquiv i (S.sourceBasis i v) = S.phaseWord i v :=
  S.stageEquiv_basis i v

/-- Refinement of the target system carries phase-corrected words to
phase-corrected words. -/
theorem targetEmbedding_phaseWord (i j : S.Index) (le : i ≤ j) (v : S.SourceLabel i) :
    S.targetEmbedding i j le (S.phaseWord i v) = S.phaseWord j (S.sourceLabelMap i j le v) := by
  unfold phaseWord
  rw [map_smul, S.targetBasis_embedding, S.phase_sourceLabelMap,
    S.wordMap_sourceLabelMap]

/-- **Whole-stage compatibility.**  The finite-stage Pauli-word equations force
the finite-stage equivalences to commute with the refinement embeddings on all
of each source stage.  This is exactly the hypothesis needed to pass to the
algebraic limits. -/
theorem stageEquiv_compatible (i j : S.Index) (le : i ≤ j) (x : S.Source i) :
    S.stageEquiv j (S.sourceEmbedding i j le x) =
      S.targetEmbedding i j le (S.stageEquiv i x) :=
  starAlgEquiv_commutes_of_source_basis
    (sourceBasis := S.sourceBasis i) (sourceBasis' := S.sourceBasis j)
    (sourceLabelMap := S.sourceLabelMap i j le)
    (targetVector := S.phaseWord i) (targetVector' := S.phaseWord j)
    (f := S.sourceEmbedding i j le) (h := S.targetEmbedding i j le)
    (e := S.stageEquiv i) (e' := S.stageEquiv j)
    (S.sourceBasis_embedding i j le)
    (S.stageEquiv_sourceBasis i)
    (S.stageEquiv_sourceBasis j)
    (S.targetEmbedding_phaseWord i j le)
    x

/-- The algebraic direct limit of the source system. -/
abbrev SourceLimit : Type _ :=
  DirectLimit S.Source (fun i j le => S.sourceEmbedding i j le)

/-- The algebraic direct limit of the target system. -/
abbrev TargetLimit : Type _ :=
  DirectLimit S.Target (fun i j le => S.targetEmbedding i j le)

/-- The canonical map of a source stage into the source limit. -/
noncomputable abbrev sourceOf (i : S.Index) (x : S.Source i) : S.SourceLimit :=
  DirectLimit.Module.of ℂ S.Index S.Source (fun i j le => S.sourceEmbedding i j le) i x

/-- The canonical map of a target stage into the target limit. -/
noncomputable abbrev targetOf (i : S.Index) (y : S.Target i) : S.TargetLimit :=
  DirectLimit.Module.of ℂ S.Index S.Target (fun i j le => S.targetEmbedding i j le) i y

/-- The star-algebra equivalence of algebraic direct limits induced by the
supplied, coherent finite-stage equivalences. -/
noncomputable def limitEquiv : S.SourceLimit ≃⋆ₐ[ℂ] S.TargetLimit :=
  algebraicLimitStarAlgEquiv
    (A := S.Source) (f := fun i j le => S.sourceEmbedding i j le)
    (D := S.Target) (h := fun i j le => S.targetEmbedding i j le)
    S.stageEquiv S.stageEquiv_compatible

/-- The induced limit equivalence is computed on every finite-stage
representative by the corresponding finite-stage equivalence. -/
@[simp]
theorem limitEquiv_of (i : S.Index) (x : S.Source i) :
    S.limitEquiv (S.sourceOf i x) = S.targetOf i (S.stageEquiv i x) :=
  rfl

/-- On a finite-stage Pauli word, the induced limit equivalence is the
phase-corrected target word. -/
theorem limitEquiv_of_sourceBasis (i : S.Index) (v : S.SourceLabel i) :
    S.limitEquiv (S.sourceOf i (S.sourceBasis i v)) = S.targetOf i (S.phaseWord i v) := by
  rw [limitEquiv_of, S.stageEquiv_sourceBasis]

/-- The inverse of the induced limit equivalence is computed on every
finite-stage representative by the inverse finite-stage equivalence. -/
@[simp]
theorem limitEquiv_symm_of (i : S.Index) (y : S.Target i) :
    S.limitEquiv.symm (S.targetOf i y) = S.sourceOf i ((S.stageEquiv i).symm y) := by
  have h_forward : S.limitEquiv (S.sourceOf i ((S.stageEquiv i).symm y)) = S.targetOf i y := by
    rw [limitEquiv_of, (S.stageEquiv i).apply_symm_apply]
  rw [← h_forward, StarAlgEquiv.symm_apply_apply]

end LayeredSystem

/-!
### A sanity example

The interface is not vacuous: the one-stage system with `Source = Target = ℂ`,
identity refinement embeddings and the singleton Pauli-word basis `{1}`
satisfies every field.
-/

/-- A one-stage instance of `LayeredSystem`, showing that all fields of the
interface can be met simultaneously. -/
noncomputable def trivialSystem : LayeredSystem where
  Index := Unit
  Source := fun _ => ℂ
  Target := fun _ => ℂ
  sourceEmbedding := fun _ _ _ => StarAlgHom.id ℂ ℂ
  targetEmbedding := fun _ _ _ => StarAlgHom.id ℂ ℂ
  sourceDirected := ⟨by intros; rfl, by intros; rfl⟩
  targetDirected := ⟨by intros; rfl, by intros; rfl⟩
  SourceLabel := fun _ => Unit
  TargetLabel := fun _ => Unit
  sourceBasis := fun _ => Module.Basis.singleton Unit ℂ
  targetBasis := fun _ => Module.Basis.singleton Unit ℂ
  stageEquiv := fun _ => StarAlgEquiv.refl
  sourceLabelMap := fun _ _ _ v => v
  targetLabelMap := fun _ _ _ w => w
  wordMap := fun _ v => v
  phase := fun _ _ => 1
  sourceBasis_embedding := fun _ _ _ _ => rfl
  targetBasis_embedding := fun _ _ _ _ => rfl
  stageEquiv_basis := fun _ _ => by simp
  phase_sourceLabelMap := fun _ _ _ _ => rfl
  wordMap_sourceLabelMap := fun _ _ _ _ => rfl

end LayeredDirectLimit

end StabilizerHyperfinite
