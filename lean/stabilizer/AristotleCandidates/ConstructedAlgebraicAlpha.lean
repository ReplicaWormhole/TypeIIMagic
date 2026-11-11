import AristotleCandidates.FiniteCoordinateEquivCoherence

/-!
# The constructed algebraic `alpha` from finite coordinate data

Context declaration: source basis `main.tex:1671-1679` (the local/adapted
symplectic basis with finite support) and `main.tex:1915-1924` (the *proposed*
star isomorphism `alpha : P_I → A_Γ` from an infinite Pauli algebra to a
regional algebra).  This module formalizes only the algebraic direct-limit
step of that proposal, with the finite-stage equivalences **constructed** and
their coherence **proved**.

## What this file adds to P23/P29/P30

* P29 (`AristotleCandidates/FiniteAdaptedCoordinateStarEquiv.lean`) constructs
  one finite-stage star-algebra equivalence out of finite adapted-coordinate
  word/basis/cocycle/phase data.
* P30 (`AristotleCandidates/FiniteCoordinateEquivCoherence.lean`) proves the
  whole-stage commuting squares of those constructed equivalences from explicit
  Pauli-basis inclusion compatibility.
* P23 (`AristotleCandidates/InfiniteAlgebraicRegionalEquiv.lean`) turns a
  coherent family of finite-stage equivalences into the algebraic direct-limit
  equivalence `alpha`.

Here the three are combined: from a `DirectedFiniteCoordinateFamily` — which
contains **no** `StarAlgEquiv` field and **no** coherence field — the algebraic
direct-limit equivalence `alpha` is defined, and its finite-stage Pauli-word
formula, inverse formulas and uniqueness from the word formula are proved.

The flagship statement is
`exists_unique_alpha_of_finiteCoordinateData`: it takes only finite
word/basis/cocycle/phase data and inclusion-compatibility data, and concludes
that there is a *unique* star-algebra equivalence of the two algebraic direct
limits whose value on every finite-stage Pauli word is the phase-corrected
target Pauli word.

## Which data remain supplied

The following are genuine auxiliary inputs; nothing below is derived from
symplecticity or from a finite-support condition alone.

1. **Finite coordinate data** at each stage: a finite adapted X/Z coordinate
   basis `coordinates i` of the source label group.
2. **Finite Pauli-word data** at each stage: the source word system
   `sourceWords i` (with its multiplier and involution phases), the target word
   system `targetWords i`, the fact that the source words form a complex linear
   basis `wordBasis i` of the finite source algebra, and the fact that the
   target words form a complex linear basis `targetBasis i` of the finite
   target algebra.
3. **Cocycle data** at each stage: the additive label map `labelMap i`, the
   explicit phase `phase i`, and the two exact compatibility equations
   `h_mul` (multiplier) and `h_star` (involution).
4. **The finite linear model** at each stage: a complex-linear equivalence
   `linearMap i` which is unital (`h_one`) and sends every source Pauli word to
   the phase-corrected target Pauli word (`h_word`).
5. **Inclusion data**: the connecting star maps of the two finite directed
   systems, the label inclusions, and the four explicit compatibility equations
   `h_sourceWord_conn`, `h_targetWord_conn`, `h_labelMap_incl`, `h_phase_incl`.

What is **not** supplied, and is instead constructed or proved: the
finite-stage star-algebra equivalences, their whole-stage coherence with the
connecting maps, the limit equivalence `alpha`, and all of its formulas.

## What is *not* claimed

Everything here is algebra.  No C⋆-norm, completion, continuity, boundedness,
GNS representation, normality, spatial (or any other) tensor product, von
Neumann bicommutant, hyperfiniteness, factor type or trace/weight statement is
used or claimed.  No gLU condition, refinement scheme or layer-coherence
hypothesis appears.
-/

namespace StabilizerHyperfinite

open FiniteAdaptedCoordinate FiniteCoordinateEquivCoherence
open InfiniteAlgebraicRegionalEquiv

namespace FiniteCoordinateEquivCoherence.DirectedFiniteCoordinateFamily

variable (F : DirectedFiniteCoordinateFamily)

/-- The P23 direct-limit package attached to a directed family of finite
coordinate systems.  Its stage equivalences are constructed by P29 and its
coherence field is the theorem of P30. -/
noncomputable abbrev limitData : RegionalLimitData := F.toRegionalLimitData

/-- The algebraic direct limit of the finite source Pauli/star algebras. -/
abbrev SourceLimit : Type _ := F.limitData.SourceLimit

/-- The algebraic direct limit of the finite target regional/star algebras. -/
abbrev TargetLimit : Type _ := F.limitData.TargetLimit

/-- The canonical map of a finite source stage into the source limit. -/
noncomputable abbrev sourceOf (i : F.Index) (x : F.Source i) : F.SourceLimit :=
  F.limitData.sourceOf i x

/-- The canonical map of a finite target stage into the target limit. -/
noncomputable abbrev targetOf (i : F.Index) (y : F.Target i) : F.TargetLimit :=
  F.limitData.targetOf i y

/-- **The constructed algebraic `alpha`.**

No finite-stage `StarAlgEquiv` and no whole-stage coherence hypothesis enters:
the stage equivalences come from the finite coordinate data by P29 and their
coherence is the P30 theorem. -/
noncomputable def alpha : F.SourceLimit ≃⋆ₐ[ℂ] F.TargetLimit :=
  F.limitData.alpha

/-- On the image of a finite stage, `alpha` is the constructed finite-stage
equivalence of that stage. -/
@[simp]
theorem alpha_of (i : F.Index) (x : F.Source i) :
    F.alpha (F.sourceOf i x) = F.targetOf i (F.stageEquiv i x) :=
  rfl

/-- **The finite-stage Pauli-word formula.**  On the image of a source Pauli
word of a finite stage, `alpha` is the phase-corrected target Pauli word of the
same stage. -/
theorem alpha_word (i : F.Index) (v : F.SourceLabel i) :
    F.alpha (F.sourceOf i ((F.stage i).source.word v)) =
      F.targetOf i ((F.stage i).phase v • (F.stage i).target.word ((F.stage i).labelMap v)) := by
  rw [alpha_of, F.stageEquiv_word]

/-- The finite-stage Pauli-word formula written with the phase-corrected word
of the target word system. -/
theorem alpha_correctedWord (i : F.Index) (v : F.SourceLabel i) :
    F.alpha (F.sourceOf i ((F.stage i).source.word v)) =
      F.targetOf i (PauliWordStarSystem.correctedWordBetween
        (F.stage i).target (F.stage i).labelMap (F.stage i).phase v) :=
  F.alpha_word i v

/-- The finite-stage formula on the Pauli word of a single adapted Z
coordinate. -/
theorem alpha_zWord (i : F.Index) (c : F.Coord i) :
    F.alpha (F.sourceOf i ((F.stage i).source.word ((F.stage i).coordinates.z c))) =
      F.targetOf i ((F.stage i).phase ((F.stage i).coordinates.z c) •
        (F.stage i).target.word ((F.stage i).labelMap ((F.stage i).coordinates.z c))) :=
  F.alpha_word i _

/-- The finite-stage formula on the Pauli word of a single adapted X
coordinate. -/
theorem alpha_xWord (i : F.Index) (c : F.Coord i) :
    F.alpha (F.sourceOf i ((F.stage i).source.word ((F.stage i).coordinates.x c))) =
      F.targetOf i ((F.stage i).phase ((F.stage i).coordinates.x c) •
        (F.stage i).target.word ((F.stage i).labelMap ((F.stage i).coordinates.x c))) :=
  F.alpha_word i _

/-- **Inverse-stage formula.**  On the image of a finite target stage, the
inverse of `alpha` is the inverse of the constructed finite-stage
equivalence. -/
@[simp]
theorem alpha_symm_of (i : F.Index) (y : F.Target i) :
    F.alpha.symm (F.targetOf i y) = F.sourceOf i ((F.stageEquiv i).symm y) :=
  F.limitData.alpha_symm_of i y

/-- **Inverse Pauli-word formula.**  The inverse of `alpha` sends the image of
the phase-corrected target word back to the image of the source Pauli word. -/
theorem alpha_symm_correctedWord (i : F.Index) (v : F.SourceLabel i) :
    F.alpha.symm (F.targetOf i ((F.stage i).phase v •
        (F.stage i).target.word ((F.stage i).labelMap v))) =
      F.sourceOf i ((F.stage i).source.word v) := by
  rw [← F.alpha_word i v, StarAlgEquiv.symm_apply_apply]

/-- If the stage phase never vanishes, the inverse of `alpha` recovers each
source Pauli word from the corresponding target Pauli word. -/
theorem alpha_symm_targetWord (i : F.Index) (v : F.SourceLabel i)
    (h_phase : (F.stage i).phase v ≠ 0) :
    F.alpha.symm (F.targetOf i ((F.stage i).target.word ((F.stage i).labelMap v))) =
      ((F.stage i).phase v)⁻¹ • F.sourceOf i ((F.stage i).source.word v) := by
  have h := F.alpha_symm_correctedWord i v
  have h0 : F.targetOf i ((F.stage i).phase v •
      (F.stage i).target.word ((F.stage i).labelMap v)) =
      (F.stage i).phase v • F.targetOf i ((F.stage i).target.word ((F.stage i).labelMap v)) :=
    map_smul _ _ _
  rw [h0] at h
  have h1 : F.alpha.symm ((F.stage i).phase v •
      F.targetOf i ((F.stage i).target.word ((F.stage i).labelMap v))) =
      (F.stage i).phase v •
        F.alpha.symm (F.targetOf i ((F.stage i).target.word ((F.stage i).labelMap v))) :=
    map_smul _ _ _
  rw [h1] at h
  rw [← h, smul_smul, inv_mul_cancel₀ h_phase, one_smul]

/-- The value of `alpha` on a whole finite stage is determined by its values on
that stage's Pauli words. -/
theorem eq_stageEquiv_of_word (psi : F.SourceLimit ≃⋆ₐ[ℂ] F.TargetLimit)
    (h_psi : ∀ (i : F.Index) (v : F.SourceLabel i),
      psi (F.sourceOf i ((F.stage i).source.word v)) =
        F.targetOf i ((F.stage i).phase v • (F.stage i).target.word ((F.stage i).labelMap v)))
    (i : F.Index) (x : F.Source i) :
    psi (F.sourceOf i x) = F.targetOf i (F.stageEquiv i x) := by
  have h_lin :
      (psi.toAlgEquiv.toLinearMap).comp
          (DirectLimit.Module.of ℂ F.Index F.Source
            (fun i j le => F.sourceConnecting i j le) i) =
        (DirectLimit.Module.of ℂ F.Index F.Target
            (fun i j le => F.targetConnecting i j le) i).comp
          (F.stageEquiv i).toAlgEquiv.toLinearMap := by
    apply (F.stage i).wordBasis.ext
    intro v
    show psi (F.sourceOf i ((F.stage i).wordBasis v)) =
      F.targetOf i (F.stageEquiv i ((F.stage i).wordBasis v))
    rw [(F.stage i).wordBasis_apply, h_psi i v, F.stageEquiv_word]
  exact congrArg (fun f : F.Source i →ₗ[ℂ] F.TargetLimit => f x) h_lin

/-- **Uniqueness from the finite-stage Pauli-word formula.**  A star-algebra
equivalence of the two algebraic limits with the constructed word formula is
`alpha`. -/
theorem alpha_unique_of_word (psi : F.SourceLimit ≃⋆ₐ[ℂ] F.TargetLimit)
    (h_psi : ∀ (i : F.Index) (v : F.SourceLabel i),
      psi (F.sourceOf i ((F.stage i).source.word v)) =
        F.targetOf i ((F.stage i).phase v • (F.stage i).target.word ((F.stage i).labelMap v))) :
    psi = F.alpha :=
  F.limitData.alpha_unique psi (F.eq_stageEquiv_of_word psi h_psi)

/-- The value of a star-algebra *homomorphism* on a whole finite stage is
determined by its values on that stage's Pauli words. -/
theorem hom_eq_stageEquiv_of_word (psi : F.SourceLimit →⋆ₐ[ℂ] F.TargetLimit)
    (h_psi : ∀ (i : F.Index) (v : F.SourceLabel i),
      psi (F.sourceOf i ((F.stage i).source.word v)) =
        F.targetOf i ((F.stage i).phase v • (F.stage i).target.word ((F.stage i).labelMap v)))
    (i : F.Index) (x : F.Source i) :
    psi (F.sourceOf i x) = F.targetOf i (F.stageEquiv i x) := by
  have h_lin :
      (psi.toAlgHom.toLinearMap).comp
          (DirectLimit.Module.of ℂ F.Index F.Source
            (fun i j le => F.sourceConnecting i j le) i) =
        (DirectLimit.Module.of ℂ F.Index F.Target
            (fun i j le => F.targetConnecting i j le) i).comp
          (F.stageEquiv i).toAlgEquiv.toLinearMap := by
    apply (F.stage i).wordBasis.ext
    intro v
    show psi (F.sourceOf i ((F.stage i).wordBasis v)) =
      F.targetOf i (F.stageEquiv i ((F.stage i).wordBasis v))
    rw [(F.stage i).wordBasis_apply, h_psi i v, F.stageEquiv_word]
  exact congrArg (fun f : F.Source i →ₗ[ℂ] F.TargetLimit => f x) h_lin

/-- **Homomorphism uniqueness.**  A star-algebra homomorphism of the two
algebraic limits with the constructed finite-stage word formula agrees with
`alpha` everywhere. -/
theorem alpha_hom_unique_of_word (psi : F.SourceLimit →⋆ₐ[ℂ] F.TargetLimit)
    (h_psi : ∀ (i : F.Index) (v : F.SourceLabel i),
      psi (F.sourceOf i ((F.stage i).source.word v)) =
        F.targetOf i ((F.stage i).phase v • (F.stage i).target.word ((F.stage i).labelMap v))) :
    ∀ z, psi z = F.alpha z :=
  F.limitData.alpha_hom_unique psi (F.hom_eq_stageEquiv_of_word psi h_psi)

/-- **Uniqueness of the inverse from the word formula.**  A star-algebra
equivalence of the two algebraic limits sending the image of each
phase-corrected target Pauli word back to the image of the corresponding source
Pauli word is `alpha.symm`. -/
theorem alpha_symm_unique_of_word (chi : F.TargetLimit ≃⋆ₐ[ℂ] F.SourceLimit)
    (h_chi : ∀ (i : F.Index) (v : F.SourceLabel i),
      chi (F.targetOf i ((F.stage i).phase v •
          (F.stage i).target.word ((F.stage i).labelMap v))) =
        F.sourceOf i ((F.stage i).source.word v)) :
    chi = F.alpha.symm := by
  have h : chi.symm = F.alpha := by
    refine F.alpha_unique_of_word chi.symm (fun i v => ?_)
    rw [← h_chi i v, StarAlgEquiv.symm_apply_apply]
  rw [← h]
  exact (StarAlgEquiv.symm_symm chi).symm

/-- **Existence and uniqueness, family form.**  There is exactly one
star-algebra equivalence of the two algebraic direct limits satisfying the
finite-stage Pauli-word formula, namely the constructed `alpha`. -/
theorem existsUnique_alpha :
    ∃! psi : F.SourceLimit ≃⋆ₐ[ℂ] F.TargetLimit,
      ∀ (i : F.Index) (v : F.SourceLabel i),
        psi (F.sourceOf i ((F.stage i).source.word v)) =
          F.targetOf i ((F.stage i).phase v •
            (F.stage i).target.word ((F.stage i).labelMap v)) :=
  ⟨F.alpha, F.alpha_word, fun psi h => F.alpha_unique_of_word psi h⟩

end FiniteCoordinateEquivCoherence.DirectedFiniteCoordinateFamily

namespace ConstructedAlgebraicAlpha

/-!
### The flagship statement from raw finite coordinate data

The theorem below takes no `StarAlgEquiv` between finite stages and no
whole-stage coherence hypothesis.  Its inputs are exactly the finite
coordinate, Pauli-word, cocycle and inclusion-compatibility data listed in the
module docstring.
-/

section RawData

variable {Index : Type*} [Preorder Index] [IsDirectedOrder Index] [Nonempty Index]
variable {Coord SourceLabel TargetLabel Source Target : Index → Type*}
variable [∀ i, Finite (Coord i)]
variable [∀ i, AddCommGroup (SourceLabel i)] [∀ i, Module PauliBit (SourceLabel i)]
variable [∀ i, AddCommGroup (TargetLabel i)]
variable [∀ i, Semiring (Source i)] [∀ i, Algebra ℂ (Source i)]
variable [∀ i, StarRing (Source i)] [∀ i, StarModule ℂ (Source i)]
variable [∀ i, Semiring (Target i)] [∀ i, Algebra ℂ (Target i)]
variable [∀ i, StarRing (Target i)] [∀ i, StarModule ℂ (Target i)]

/-- The directed family of finite coordinate systems assembled from raw
stagewise data.  Each stage is the P29 bundle; the connecting and inclusion
data are the P30 compatibility inputs. -/
noncomputable def familyOfCoordinateData
    (coordinates : ∀ i, AdaptedPauliCoordinateBasis (I := Coord i) (V := SourceLabel i))
    (sourceWords : ∀ i, PauliWordStarSystem (SourceLabel i) (Source i))
    (targetWords : ∀ i, PauliWordStarSystem (TargetLabel i) (Target i))
    (wordBasis : ∀ i, Module.Basis (SourceLabel i) ℂ (Source i))
    (h_wordBasis : ∀ i v, wordBasis i v = (sourceWords i).word v)
    (targetBasis : ∀ i, Module.Basis (TargetLabel i) ℂ (Target i))
    (h_targetBasis : ∀ i w, targetBasis i w = (targetWords i).word w)
    (labelMap : ∀ i, SourceLabel i →+ TargetLabel i)
    (phase : ∀ i, SourceLabel i → ℂ)
    (h_mul : ∀ i, PauliWordStarSystem.MultiplicationCompatibleBetween
      (sourceWords i) (targetWords i) (labelMap i) (phase i))
    (h_star : ∀ i, PauliWordStarSystem.StarCompatibleBetween
      (sourceWords i) (targetWords i) (labelMap i) (phase i))
    (linearMap : ∀ i, Source i ≃ₗ[ℂ] Target i)
    (h_one : ∀ i, linearMap i 1 = 1)
    (h_word : ∀ i v, linearMap i ((sourceWords i).word v) =
      PauliWordStarSystem.correctedWordBetween (targetWords i) (labelMap i) (phase i) v)
    (sourceConnecting : ∀ i j : Index, i ≤ j → Source i →⋆ₐ[ℂ] Source j)
    (targetConnecting : ∀ i j : Index, i ≤ j → Target i →⋆ₐ[ℂ] Target j)
    [DirectedSystem Source (fun i j le => sourceConnecting i j le)]
    [DirectedSystem Target (fun i j le => targetConnecting i j le)]
    (sourceLabelIncl : ∀ i j : Index, i ≤ j → SourceLabel i → SourceLabel j)
    (targetLabelIncl : ∀ i j : Index, i ≤ j → TargetLabel i → TargetLabel j)
    (h_sourceWord_conn : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
      sourceConnecting i j le ((sourceWords i).word v) =
        (sourceWords j).word (sourceLabelIncl i j le v))
    (h_targetWord_conn : ∀ (i j : Index) (le : i ≤ j) (w : TargetLabel i),
      targetConnecting i j le ((targetWords i).word w) =
        (targetWords j).word (targetLabelIncl i j le w))
    (h_labelMap_incl : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
      labelMap j (sourceLabelIncl i j le v) = targetLabelIncl i j le (labelMap i v))
    (h_phase_incl : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
      phase j (sourceLabelIncl i j le v) = phase i v) :
    FiniteCoordinateEquivCoherence.DirectedFiniteCoordinateFamily where
  Index := Index
  Coord := Coord
  SourceLabel := SourceLabel
  TargetLabel := TargetLabel
  Source := Source
  Target := Target
  stage := fun i =>
    { coordinates := coordinates i
      source := sourceWords i
      target := targetWords i
      wordBasis := wordBasis i
      wordBasis_apply := h_wordBasis i
      targetBasis := targetBasis i
      targetBasis_apply := h_targetBasis i
      labelMap := labelMap i
      phase := phase i
      mulCompatible := h_mul i
      starCompatible := h_star i
      linearMap := linearMap i
      linearMap_one := h_one i
      linearMap_word := h_word i }
  sourceConnecting := sourceConnecting
  targetConnecting := targetConnecting
  sourceLabelIncl := sourceLabelIncl
  targetLabelIncl := targetLabelIncl
  sourceWord_connecting := h_sourceWord_conn
  targetWord_connecting := h_targetWord_conn
  labelMap_incl := h_labelMap_incl
  phase_incl := h_phase_incl

/-- **The constructed algebraic `alpha` from raw finite coordinate data.**

Given only

* finite adapted coordinate data, source and target Pauli-word systems and
  their complex word bases at each stage,
* an additive label map, an explicit phase and the two exact
  multiplier/involution compatibility equations at each stage,
* a unital complex-linear equivalence realizing the phase-corrected word map at
  each stage, and
* the connecting star maps, label inclusions and their four explicit Pauli-word,
  label and phase compatibility equations,

there is a **unique** star-algebra equivalence of the two algebraic direct
limits whose value on the image of every finite-stage source Pauli word is the
image of the phase-corrected target Pauli word.  No finite-stage
`StarAlgEquiv`, and no whole-stage coherence, is assumed: the stage
equivalences are constructed (P29), their coherence is proved (P30) and the
limit equivalence is the algebraic direct limit of P23. -/
theorem exists_unique_alpha_of_finiteCoordinateData
    (coordinates : ∀ i, AdaptedPauliCoordinateBasis (I := Coord i) (V := SourceLabel i))
    (sourceWords : ∀ i, PauliWordStarSystem (SourceLabel i) (Source i))
    (targetWords : ∀ i, PauliWordStarSystem (TargetLabel i) (Target i))
    (wordBasis : ∀ i, Module.Basis (SourceLabel i) ℂ (Source i))
    (h_wordBasis : ∀ i v, wordBasis i v = (sourceWords i).word v)
    (targetBasis : ∀ i, Module.Basis (TargetLabel i) ℂ (Target i))
    (h_targetBasis : ∀ i w, targetBasis i w = (targetWords i).word w)
    (labelMap : ∀ i, SourceLabel i →+ TargetLabel i)
    (phase : ∀ i, SourceLabel i → ℂ)
    (h_mul : ∀ i, PauliWordStarSystem.MultiplicationCompatibleBetween
      (sourceWords i) (targetWords i) (labelMap i) (phase i))
    (h_star : ∀ i, PauliWordStarSystem.StarCompatibleBetween
      (sourceWords i) (targetWords i) (labelMap i) (phase i))
    (linearMap : ∀ i, Source i ≃ₗ[ℂ] Target i)
    (h_one : ∀ i, linearMap i 1 = 1)
    (h_word : ∀ i v, linearMap i ((sourceWords i).word v) =
      PauliWordStarSystem.correctedWordBetween (targetWords i) (labelMap i) (phase i) v)
    (sourceConnecting : ∀ i j : Index, i ≤ j → Source i →⋆ₐ[ℂ] Source j)
    (targetConnecting : ∀ i j : Index, i ≤ j → Target i →⋆ₐ[ℂ] Target j)
    [DirectedSystem Source (fun i j le => sourceConnecting i j le)]
    [DirectedSystem Target (fun i j le => targetConnecting i j le)]
    (sourceLabelIncl : ∀ i j : Index, i ≤ j → SourceLabel i → SourceLabel j)
    (targetLabelIncl : ∀ i j : Index, i ≤ j → TargetLabel i → TargetLabel j)
    (h_sourceWord_conn : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
      sourceConnecting i j le ((sourceWords i).word v) =
        (sourceWords j).word (sourceLabelIncl i j le v))
    (h_targetWord_conn : ∀ (i j : Index) (le : i ≤ j) (w : TargetLabel i),
      targetConnecting i j le ((targetWords i).word w) =
        (targetWords j).word (targetLabelIncl i j le w))
    (h_labelMap_incl : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
      labelMap j (sourceLabelIncl i j le v) = targetLabelIncl i j le (labelMap i v))
    (h_phase_incl : ∀ (i j : Index) (le : i ≤ j) (v : SourceLabel i),
      phase j (sourceLabelIncl i j le v) = phase i v) :
    ∃! psi : DirectLimit Source (fun i j le => sourceConnecting i j le) ≃⋆ₐ[ℂ]
        DirectLimit Target (fun i j le => targetConnecting i j le),
      ∀ (i : Index) (v : SourceLabel i),
        psi (DirectLimit.Module.of ℂ Index Source
            (fun i j le => sourceConnecting i j le) i ((sourceWords i).word v)) =
          DirectLimit.Module.of ℂ Index Target
            (fun i j le => targetConnecting i j le) i
            (phase i v • (targetWords i).word (labelMap i v)) := by
  exact (familyOfCoordinateData coordinates sourceWords targetWords wordBasis h_wordBasis
    targetBasis h_targetBasis labelMap phase h_mul h_star linearMap h_one h_word
    sourceConnecting targetConnecting sourceLabelIncl targetLabelIncl
    h_sourceWord_conn h_targetWord_conn h_labelMap_incl h_phase_incl).existsUnique_alpha

end RawData

/-!
### A sanity instance

The interface is not vacuous: the one-stage family of P30 built from the
trivial P29 data yields a constructed `alpha`.  This is a consistency check,
not a model of the manuscript's regional algebras.
-/

/-- The constructed `alpha` of the trivial one-stage family exists. -/
noncomputable def trivialAlpha :
    (FiniteCoordinateEquivCoherence.trivialFamily).SourceLimit ≃⋆ₐ[ℂ]
      (FiniteCoordinateEquivCoherence.trivialFamily).TargetLimit :=
  (FiniteCoordinateEquivCoherence.trivialFamily).alpha

end ConstructedAlgebraicAlpha

end StabilizerHyperfinite
