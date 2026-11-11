import AristotleCandidates.InfiniteAlgebraicStateTransport
import AristotleCandidates.CStarTransport

/-!
# The C⋆-completion interface for the regional `alpha`

**Context declaration.** Source basis: `main.tex:1915-1924`.

This module packages the *first analytic boundary* after P23
(`AristotleCandidates.InfiniteAlgebraicRegionalEquiv`) and P24
(`AristotleCandidates.InfiniteAlgebraicStateTransport`).  It does **not**
construct a C⋆-norm or a completion of the algebraic direct limits: both
completions, both dense algebraic embeddings, and the C⋆ star-algebra
equivalence extending the algebraic `alpha` are *supplied inputs*.

## Supplied data (`CStarCompletionData`)

* a P23 `RegionalLimitData` object `limitData` (all finite-stage star-algebra
  equivalences and their coherence with the connecting maps are themselves
  supplied there);
* unital complex C⋆-algebras `SourceCStar` and `TargetCStar`;
* star-algebra embeddings `sourceEmbed : limitData.SourceLimit →⋆ₐ[ℂ] SourceCStar`
  and `targetEmbed : limitData.TargetLimit →⋆ₐ[ℂ] TargetCStar` of the two
  algebraic direct limits;
* density of the ranges of those two embeddings; and
* a C⋆ star-algebra equivalence `alphaCStar : SourceCStar ≃⋆ₐ[ℂ] TargetCStar`
  together with the *exact* extension formula `alphaCStar_stage`, which says
  that on the image of every P23 finite-stage representative `alphaCStar`
  agrees with the supplied finite-stage equivalence.

## Checked consequences

None of the following is assumed; each is proved from the supplied data.

* `alphaCStar_sourceEmbed`: the extension formula upgrades from finite-stage
  representatives to the whole algebraic limit, i.e. `alphaCStar` restricted
  along `sourceEmbed` is `targetEmbed ∘ alpha`.
* `isometry_alphaCStar`, `isometry_alphaCStar_symm`, `continuous_alphaCStar`,
  `continuous_alphaCStar_symm`, `continuousLinearEquiv`: the extension is
  isometric and continuous, and so is its inverse (via
  `Formalization.CStarEquivExtension`).
* `alphaCStar_symm_targetEmbed`: the inverse-stage formulas.
* `alphaCStar_unique_of_continuous`, `alphaCStar_symm_unique_of_continuous`:
  the extension and its inverse are the *unique* continuous maps with the
  finite-stage formulas, by density of the embeddings.
* `continuous_inducedFunctional`, `inducedFunctional_sourceEmbed_sourceOf`,
  `inducedFunctional_sourceEmbed`: a supplied continuous target functional
  pulls back to a continuous functional on `SourceCStar` whose value on every
  finite-stage representative is the expected P24 expectation
  `S.omega i (limitData.stageEquiv i x)`, i.e. it restricts along
  `sourceEmbed` to P24's `pulledBackState`.
* `inducedFunctional_unique_of_continuous`: uniqueness of that pullback among
  continuous functionals, again by density.

## What is *not* claimed

Nothing here asserts normality of any map or functional, a GNS representation
or GNS equivalence, a spatial (or any) tensor product, a von Neumann closure or
bicommutant, quasi-equivalence, hyperfiniteness, a factor type, or the
existence of a trace or weight.  No C⋆-norm or completion is constructed from
the algebraic limit.  No gLU condition, refinement scheme, or layer-coherence
hypothesis appears.
-/

namespace AristotleCandidates

namespace CStarCompletionAlphaInterface

open StabilizerHyperfinite
open StabilizerHyperfinite.InfiniteAlgebraicRegionalEquiv
open AristotleCandidates.InfiniteAlgebraicStateTransport

/-! ## The supplied completion/extension data -/

/-- **Supplied** C⋆ completion data for the P23 algebraic equivalence `alpha`.

Every field is an input.  In particular the C⋆-algebras, the two dense
algebraic embeddings, and the star-algebra equivalence `alphaCStar` extending
`alpha` are assumptions: none of them is constructed from the algebraic direct
limits. -/
structure CStarCompletionData where
  /-- The supplied P23 algebraic direct-limit data. -/
  limitData : RegionalLimitData
  /-- The supplied C⋆ completion of the source algebraic limit. -/
  SourceCStar : Type*
  /-- The supplied C⋆ completion of the target algebraic limit. -/
  TargetCStar : Type*
  /-- The supplied unital complex C⋆ structure on the source completion. -/
  sourceCStar : CStarAlgebra SourceCStar
  /-- The supplied unital complex C⋆ structure on the target completion. -/
  targetCStar : CStarAlgebra TargetCStar
  /-- The supplied algebraic embedding of the source direct limit. -/
  sourceEmbed : limitData.SourceLimit →⋆ₐ[ℂ] SourceCStar
  /-- The supplied algebraic embedding of the target direct limit. -/
  targetEmbed : limitData.TargetLimit →⋆ₐ[ℂ] TargetCStar
  /-- Supplied density of the source embedding. -/
  sourceEmbed_dense : Dense (Set.range sourceEmbed)
  /-- Supplied density of the target embedding. -/
  targetEmbed_dense : Dense (Set.range targetEmbed)
  /-- The supplied C⋆ star-algebra equivalence of the two completions. -/
  alphaCStar : SourceCStar ≃⋆ₐ[ℂ] TargetCStar
  /-- The supplied **exact extension formula**: on every P23 finite-stage
  representative, `alphaCStar` is the supplied finite-stage equivalence. -/
  alphaCStar_stage : ∀ (i : limitData.Index) (x : limitData.Source i),
    alphaCStar (sourceEmbed (limitData.sourceOf i x)) =
      targetEmbed (limitData.targetOf i (limitData.stageEquiv i x))

attribute [instance] CStarCompletionData.sourceCStar CStarCompletionData.targetCStar

namespace CStarCompletionData

variable (C : CStarCompletionData)

/-! ## Checked consequence: the extension formula on the whole algebraic limit -/

/-- The supplied finite-stage extension formula extends to all of the source
algebraic limit: along the embeddings, `alphaCStar` *is* the P23 algebraic
equivalence `alpha`. -/
theorem alphaCStar_sourceEmbed (z : C.limitData.SourceLimit) :
    C.alphaCStar (C.sourceEmbed z) = C.targetEmbed (C.limitData.alpha z) := by
  induction z using DirectLimit.induction with
  | _ i x =>
    change C.alphaCStar (C.sourceEmbed (C.limitData.sourceOf i x)) =
      C.targetEmbed (C.limitData.alpha (C.limitData.sourceOf i x))
    rw [C.limitData.alpha_of, C.alphaCStar_stage]

/-- Inverse form of the finite-stage formula. -/
theorem alphaCStar_symm_targetEmbed_stage (i : C.limitData.Index) (y : C.limitData.Target i) :
    C.alphaCStar.symm (C.targetEmbed (C.limitData.targetOf i y)) =
      C.sourceEmbed (C.limitData.sourceOf i ((C.limitData.stageEquiv i).symm y)) := by
  have h := C.alphaCStar_stage i ((C.limitData.stageEquiv i).symm y)
  rw [(C.limitData.stageEquiv i).apply_symm_apply] at h
  rw [← h, StarAlgEquiv.symm_apply_apply]

/-- Along the embeddings, the inverse of `alphaCStar` is the inverse of the
P23 algebraic equivalence `alpha`. -/
theorem alphaCStar_symm_targetEmbed (w : C.limitData.TargetLimit) :
    C.alphaCStar.symm (C.targetEmbed w) = C.sourceEmbed (C.limitData.alpha.symm w) := by
  induction w using DirectLimit.induction with
  | _ i y =>
    change C.alphaCStar.symm (C.targetEmbed (C.limitData.targetOf i y)) =
      C.sourceEmbed (C.limitData.alpha.symm (C.limitData.targetOf i y))
    rw [C.limitData.alpha_symm_of, C.alphaCStar_symm_targetEmbed_stage]

/-! ## Checked consequence: isometry and continuity -/

/-- The supplied C⋆ extension is isometric. -/
theorem isometry_alphaCStar : Isometry C.alphaCStar :=
  cstar_starAlgEquiv_isometry C.alphaCStar

/-- The inverse of the supplied C⋆ extension is isometric. -/
theorem isometry_alphaCStar_symm : Isometry C.alphaCStar.symm :=
  cstar_starAlgEquiv_isometry C.alphaCStar.symm

/-- The supplied C⋆ extension is continuous. -/
theorem continuous_alphaCStar : Continuous C.alphaCStar :=
  C.isometry_alphaCStar.continuous

/-- The inverse of the supplied C⋆ extension is continuous. -/
theorem continuous_alphaCStar_symm : Continuous C.alphaCStar.symm :=
  C.isometry_alphaCStar_symm.continuous

/-- Norms are preserved by the extension. -/
theorem norm_alphaCStar (a : C.SourceCStar) : ‖C.alphaCStar a‖ = ‖a‖ := by
  simpa using C.isometry_alphaCStar.dist_eq a 0

/-- The extension packaged as a continuous complex-linear equivalence of the
two supplied completions. -/
noncomputable def continuousLinearEquiv : C.SourceCStar ≃L[ℂ] C.TargetCStar :=
  cstarStarAlgEquivToContinuousLinearEquiv C.alphaCStar

@[simp]
theorem continuousLinearEquiv_apply (a : C.SourceCStar) :
    C.continuousLinearEquiv a = C.alphaCStar a :=
  rfl

/-! ## Checked consequence: uniqueness of the extension by density -/

/-- **Uniqueness of the extension.**  Any continuous map on the source
completion that satisfies the finite-stage formula equals `alphaCStar`; the
dense algebraic embedding leaves no freedom. -/
theorem alphaCStar_unique_of_continuous (g : C.SourceCStar → C.TargetCStar)
    (hg : Continuous g)
    (h_stage : ∀ (i : C.limitData.Index) (x : C.limitData.Source i),
      g (C.sourceEmbed (C.limitData.sourceOf i x)) =
        C.targetEmbed (C.limitData.targetOf i (C.limitData.stageEquiv i x))) :
    g = C.alphaCStar := by
  refine Continuous.ext_on C.sourceEmbed_dense hg C.continuous_alphaCStar ?_
  rintro _ ⟨z, rfl⟩
  induction z using DirectLimit.induction with
  | _ i x =>
    change g (C.sourceEmbed (C.limitData.sourceOf i x)) =
      C.alphaCStar (C.sourceEmbed (C.limitData.sourceOf i x))
    rw [h_stage, C.alphaCStar_stage]

/-- **Uniqueness of the inverse extension.** -/
theorem alphaCStar_symm_unique_of_continuous (g : C.TargetCStar → C.SourceCStar)
    (hg : Continuous g)
    (h_stage : ∀ (i : C.limitData.Index) (y : C.limitData.Target i),
      g (C.targetEmbed (C.limitData.targetOf i y)) =
        C.sourceEmbed (C.limitData.sourceOf i ((C.limitData.stageEquiv i).symm y))) :
    g = (C.alphaCStar.symm : C.TargetCStar → C.SourceCStar) := by
  refine Continuous.ext_on C.targetEmbed_dense hg C.continuous_alphaCStar_symm ?_
  rintro _ ⟨w, rfl⟩
  induction w using DirectLimit.induction with
  | _ i y =>
    change g (C.targetEmbed (C.limitData.targetOf i y)) =
      C.alphaCStar.symm (C.targetEmbed (C.limitData.targetOf i y))
    rw [h_stage, C.alphaCStar_symm_targetEmbed_stage]

/-! ## Checked consequence: pullback of a supplied continuous target functional -/

section Functional

variable (phi : C.TargetCStar →ₗ[ℂ] ℂ)

/-- The pullback of a target functional along the supplied C⋆ extension. -/
noncomputable def inducedFunctional : C.SourceCStar →ₗ[ℂ] ℂ :=
  pullback C.alphaCStar phi

@[simp]
theorem inducedFunctional_apply (a : C.SourceCStar) :
    C.inducedFunctional phi a = phi (C.alphaCStar a) :=
  rfl

/-- A supplied continuous target functional pulls back to a continuous
functional on the source completion. -/
theorem continuous_inducedFunctional (h_phi : Continuous phi) :
    Continuous (C.inducedFunctional phi) :=
  continuous_pullback_of_cstarStarAlgEquiv C.alphaCStar phi h_phi

/-- Pulling back along the inverse recovers the target functional. -/
theorem inducedFunctional_pullback_symm :
    pullback C.alphaCStar.symm (C.inducedFunctional phi) = phi :=
  pullback_symm_pullback C.alphaCStar phi

/-- **The expected finite-stage formula.**  If the supplied continuous target
functional restricts along `targetEmbed` to the supplied P24 target-stage
expectations, then its pullback takes on every source finite-stage
representative the value `S.omega i (stageEquiv i x)`. -/
theorem inducedFunctional_sourceEmbed_sourceOf
    (S : TargetStageStates C.limitData)
    (h_restrict : ∀ (i : C.limitData.Index) (y : C.limitData.Target i),
      phi (C.targetEmbed (C.limitData.targetOf i y)) = S.omega i y)
    (i : C.limitData.Index) (x : C.limitData.Source i) :
    C.inducedFunctional phi (C.sourceEmbed (C.limitData.sourceOf i x)) =
      S.omega i (C.limitData.stageEquiv i x) := by
  rw [inducedFunctional_apply, C.alphaCStar_stage, h_restrict]

/-- The pullback restricts along `sourceEmbed` to P24's algebraic transported
state `pulledBackState`. -/
theorem inducedFunctional_sourceEmbed
    (S : TargetStageStates C.limitData)
    (h_restrict : ∀ (i : C.limitData.Index) (y : C.limitData.Target i),
      phi (C.targetEmbed (C.limitData.targetOf i y)) = S.omega i y)
    (z : C.limitData.SourceLimit) :
    C.inducedFunctional phi (C.sourceEmbed z) = S.pulledBackState z := by
  induction z using DirectLimit.induction with
  | _ i x =>
    change C.inducedFunctional phi (C.sourceEmbed (C.limitData.sourceOf i x)) =
      S.pulledBackState (C.limitData.sourceOf i x)
    rw [C.inducedFunctional_sourceEmbed_sourceOf phi S h_restrict,
      TargetStageStates.pulledBackState_sourceOf]

/-- **Uniqueness of the continuous pullback.**  A continuous functional on the
source completion with the expected finite-stage values is the pullback. -/
theorem inducedFunctional_unique_of_continuous
    (h_phi : Continuous phi)
    (S : TargetStageStates C.limitData)
    (h_restrict : ∀ (i : C.limitData.Index) (y : C.limitData.Target i),
      phi (C.targetEmbed (C.limitData.targetOf i y)) = S.omega i y)
    (psi : C.SourceCStar →ₗ[ℂ] ℂ) (h_psi : Continuous psi)
    (h_stage : ∀ (i : C.limitData.Index) (x : C.limitData.Source i),
      psi (C.sourceEmbed (C.limitData.sourceOf i x)) =
        S.omega i (C.limitData.stageEquiv i x)) :
    psi = C.inducedFunctional phi := by
  have h_fun : (psi : C.SourceCStar → ℂ) = C.inducedFunctional phi := by
    refine Continuous.ext_on C.sourceEmbed_dense h_psi
      (C.continuous_inducedFunctional phi h_phi) ?_
    rintro _ ⟨z, rfl⟩
    induction z using DirectLimit.induction with
    | _ i x =>
      change psi (C.sourceEmbed (C.limitData.sourceOf i x)) =
        C.inducedFunctional phi (C.sourceEmbed (C.limitData.sourceOf i x))
      rw [h_stage, C.inducedFunctional_sourceEmbed_sourceOf phi S h_restrict]
  exact LinearMap.ext fun a => congrFun h_fun a

end Functional

/-! ## Reuse of the `CStarTransport` interface -/

/-- The supplied completion data together with a supplied continuous target
functional is an instance of the `SuppliedCStarModel.Data` interface of
`AristotleCandidates.CStarTransport`. -/
def toSuppliedCStarModel (phi : C.TargetCStar →ₗ[ℂ] ℂ) (h_phi : Continuous phi) :
    SuppliedCStarModel.Data where
  source := C.SourceCStar
  target := C.TargetCStar
  sourceCStar := C.sourceCStar
  targetCStar := C.targetCStar
  equivalence := C.alphaCStar
  targetFunctional := phi
  targetFunctional_continuous := h_phi

@[simp]
theorem toSuppliedCStarModel_inducedFunctional
    (phi : C.TargetCStar →ₗ[ℂ] ℂ) (h_phi : Continuous phi) (a : C.SourceCStar) :
    SuppliedCStarModel.inducedFunctional (C.toSuppliedCStarModel phi h_phi) a =
      C.inducedFunctional phi a :=
  rfl

/-- Summary of the checked analytic consequences of the supplied data. -/
theorem analytic_package (phi : C.TargetCStar →ₗ[ℂ] ℂ) (h_phi : Continuous phi) :
    Isometry C.alphaCStar ∧ Isometry C.alphaCStar.symm ∧
      Continuous C.alphaCStar ∧ Continuous C.alphaCStar.symm ∧
      Continuous (C.inducedFunctional phi) ∧
      ∀ z, C.alphaCStar (C.sourceEmbed z) = C.targetEmbed (C.limitData.alpha z) :=
  ⟨C.isometry_alphaCStar, C.isometry_alphaCStar_symm, C.continuous_alphaCStar,
    C.continuous_alphaCStar_symm, C.continuous_inducedFunctional phi h_phi,
    C.alphaCStar_sourceEmbed⟩

end CStarCompletionData

/-! ## A sanity instance

The interface is not vacuous: with the one-stage P23 `trivialData`, both
completions equal `ℂ`, both embeddings are the induced maps of the identity
stage maps (with dense — indeed full — range), and `alphaCStar` is the identity.
This is a consistency check on the bundle, not a model of the manuscript's
regional algebras. -/

/-- The induced star-algebra map from the direct limit of the one-stage system
of `ℂ`'s to `ℂ`. -/
noncomputable def trivialEmbed :
    (trivialData.SourceLimit) →⋆ₐ[ℂ] ℂ :=
  algebraicLimitStarAlgHom (A := trivialData.Source)
    (f := fun i j le => trivialData.sourceConnecting i j le)
    (fun _ => StarAlgHom.id ℂ ℂ) (fun _ _ _ _ => rfl)

theorem trivialEmbed_of (i : trivialData.Index) (x : trivialData.Source i) :
    trivialEmbed (trivialData.sourceOf i x) = x :=
  algebraicLimitStarAlgHom_of (A := trivialData.Source)
    (f := fun i j le => trivialData.sourceConnecting i j le)
    (fun _ => StarAlgHom.id ℂ ℂ) (fun _ _ _ _ => rfl) i x

theorem trivialEmbed_dense : Dense (Set.range (trivialEmbed : trivialData.SourceLimit → ℂ)) := by
  have h : Set.range (trivialEmbed : trivialData.SourceLimit → ℂ) = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    exact ⟨trivialData.sourceOf (Classical.arbitrary trivialData.Index) c,
      trivialEmbed_of _ c⟩
  rw [h]
  exact dense_univ

/-- A one-stage instance of `CStarCompletionData`, showing all fields can be
met simultaneously. -/
noncomputable def trivialCompletionData : CStarCompletionData where
  limitData := trivialData
  SourceCStar := ℂ
  TargetCStar := ℂ
  sourceCStar := inferInstance
  targetCStar := inferInstance
  sourceEmbed := trivialEmbed
  targetEmbed := trivialEmbed
  sourceEmbed_dense := trivialEmbed_dense
  targetEmbed_dense := trivialEmbed_dense
  alphaCStar := StarAlgEquiv.refl
  alphaCStar_stage := by
    intro i x
    change trivialEmbed (trivialData.sourceOf i x) =
      trivialEmbed (trivialData.targetOf i x)
    rw [trivialEmbed_of]
    exact (trivialEmbed_of i x).symm

end CStarCompletionAlphaInterface

end AristotleCandidates
