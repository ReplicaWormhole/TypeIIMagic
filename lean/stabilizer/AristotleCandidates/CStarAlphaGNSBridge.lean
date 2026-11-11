import AristotleCandidates.CStarCompletionAlphaInterface
import AristotleCandidates.CStarGNSBridge

/-!
# From the supplied C⋆ completion of `alpha` to the GNS bridge

**Context declaration.** Source basis: `main.tex:1921-1958`.

This module combines the two interfaces that are already available:

* P25, `AristotleCandidates.CStarCompletionAlphaInterface.CStarCompletionData`:
  a supplied pair of unital complex C⋆ completions of the P23 algebraic direct
  limits, supplied dense algebraic embeddings, and a supplied C⋆ star-algebra
  equivalence `alphaCStar` extending the algebraic `alpha` on every finite-stage
  representative; and
* P19, `StabilizerHyperfinite.CStarGNSBridge.Data`: a supplied C⋆ model together
  with the order data, the supplied positive unital states, and their
  compatibility required by the bounded-state GNS interface (P13–P16).

## Supplied data (`AlphaGNSData`)

Everything is an input:

* a P25 `CStarCompletionData` object `completion`;
* partial orders and star-ordered-ring structures on the two completions, as
  required by Mathlib's positive-functional/GNS API;
* positive linear functionals `sourceState` and `targetState` on the two
  completions, both unital;
* continuity of the supplied target state; and
* the **exact compatibility** `sourceState a = targetState (alphaCStar a)`.

## Checked consequences

* `AlphaGNSData.toBridge`: the supplied data *is* a P19 `CStarGNSBridge.Data`,
  hence also a P13 `BoundedStateGNS.Data`; nothing about GNS is re-proved.
* `AlphaGNSData.gnsUnitary`, `gnsUnitary_inner`, `gnsUnitary_norm`: the GNS
  unitary of P15 as a `ℂ`-linear isometric equivalence of the two GNS Hilbert
  spaces.
* `AlphaGNSData.gnsUnitary_intertwines` (and its inverse form): the intertwining
  formula along `alphaCStar`.
* `AlphaGNSData.gnsConjStarAlgEquiv`, `gnsConj_range`, `gnsConj_commute_iff`,
  `gnsConj_image_centralizer`, `gnsConj_image_centralizer_centralizer`: the
  conjugation star-algebra equivalence of P16 and the transport of the purely
  **algebraic** `Set.centralizer` commutant and bicommutant.
* `AlphaGNSData.sourceState_sourceEmbed_sourceOf` and
  `sourceState_sourceEmbed`: the **finite-stage formula** inherited from
  P25/P24 — if the supplied target state restricts along `targetEmbed` to the
  supplied P24 stage expectations `S.omega`, then the supplied source state
  takes the value `S.omega i (stageEquiv i x)` on every finite-stage
  representative, i.e. it restricts along `sourceEmbed` to P24's
  `pulledBackState`.
* `AlphaGNSData.sourceState_unique_of_continuous`: by density that formula
  determines the source state among continuous functionals.

## What is *not* claimed

Nothing here asserts normality of any map or functional, quasi-equivalence, a
spatial (or any) tensor product, a von Neumann closure or bicommutant, factor
type, hyperfiniteness, or the existence of a trace or weight.  The commutants
appearing below are the algebraic `Set.centralizer` ones inherited from P16.
No C⋆-norm or completion is constructed here, and no gLU, refinement, or
layer-coherence hypothesis appears.
-/

namespace AristotleCandidates

namespace CStarAlphaGNSBridge

open StabilizerHyperfinite
open StabilizerHyperfinite.InfiniteAlgebraicRegionalEquiv
open AristotleCandidates.InfiniteAlgebraicStateTransport
open AristotleCandidates.CStarCompletionAlphaInterface

open scoped ComplexOrder InnerProductSpace

/-! ## The supplied data -/

/-- **Supplied** data joining the P25 C⋆ completion interface for `alpha` with
the state data required by the P19 GNS bridge.

Every field is an input: the completions, embeddings and `alphaCStar` come from
P25, and the order structures, the two positive unital states, the continuity of
the target state and their exact compatibility along `alphaCStar` are
assumptions. -/
structure AlphaGNSData where
  /-- The supplied P25 C⋆ completion data for the algebraic `alpha`. -/
  completion : CStarCompletionData
  /-- Supplied partial order on the source completion, as required by the GNS API. -/
  [sourceOrder : PartialOrder completion.SourceCStar]
  /-- Supplied partial order on the target completion, as required by the GNS API. -/
  [targetOrder : PartialOrder completion.TargetCStar]
  /-- The source order is a star-ordered ring structure. -/
  [sourceStarOrdered : StarOrderedRing completion.SourceCStar]
  /-- The target order is a star-ordered ring structure. -/
  [targetStarOrdered : StarOrderedRing completion.TargetCStar]
  /-- The supplied positive functional (state) on the source completion. -/
  sourceState : completion.SourceCStar →ₚ[ℂ] ℂ
  /-- The supplied positive functional (state) on the target completion. -/
  targetState : completion.TargetCStar →ₚ[ℂ] ℂ
  /-- The supplied source state is unital. -/
  sourceState_one : sourceState 1 = 1
  /-- The supplied target state is unital. -/
  targetState_one : targetState 1 = 1
  /-- The supplied target state is continuous. -/
  targetState_continuous : Continuous targetState.toLinearMap
  /-- **Exact compatibility** of the two supplied states along `alphaCStar`. -/
  state_compat : ∀ a : completion.SourceCStar,
    sourceState a = targetState (completion.alphaCStar a)

attribute [instance] AlphaGNSData.sourceOrder AlphaGNSData.targetOrder
  AlphaGNSData.sourceStarOrdered AlphaGNSData.targetStarOrdered

namespace AlphaGNSData

variable (A : AlphaGNSData)

/-- The supplied source C⋆ completion. -/
abbrev SourceCStar : Type _ := A.completion.SourceCStar

/-- The supplied target C⋆ completion. -/
abbrev TargetCStar : Type _ := A.completion.TargetCStar

/-- The supplied C⋆ extension of the algebraic `alpha`. -/
abbrev alphaCStar : A.SourceCStar ≃⋆ₐ[ℂ] A.TargetCStar := A.completion.alphaCStar

/-- The supplied target state, viewed as a continuous linear functional. -/
noncomputable abbrev targetFunctional : A.TargetCStar →ₗ[ℂ] ℂ := A.targetState.toLinearMap

/-! ## The induced P19 bridge datum -/

/-- The supplied data, packaged as a P25 `SuppliedCStarModel.Data`. -/
noncomputable def model : SuppliedCStarModel.Data :=
  A.completion.toSuppliedCStarModel A.targetFunctional A.targetState_continuous

/-- **The P19 GNS bridge datum** determined by the supplied data. -/
noncomputable def toBridge : CStarGNSBridge.Data where
  model := A.model
  sourceOrder := A.sourceOrder
  targetOrder := A.targetOrder
  sourceStarOrdered := A.sourceStarOrdered
  targetStarOrdered := A.targetStarOrdered
  sourceState := A.sourceState
  targetState := A.targetState
  sourceState_one := A.sourceState_one
  targetState_one := A.targetState_one
  state_compat := A.state_compat
  targetFunctional_eq := fun _ => rfl

@[simp] theorem toBridge_equivalence : A.toBridge.model.equivalence = A.alphaCStar := rfl
@[simp] theorem toBridge_sourceState : A.toBridge.sourceState = A.sourceState := rfl
@[simp] theorem toBridge_targetState : A.toBridge.targetState = A.targetState := rfl

/-- The induced bounded-state GNS datum (P13). -/
noncomputable def gns : BoundedStateGNS.Data := A.toBridge.gns

/-! ## Analytic facts inherited from P25 -/

/-- The supplied C⋆ extension is isometric. -/
theorem isometry_alphaCStar : Isometry A.alphaCStar :=
  A.completion.isometry_alphaCStar

/-- The inverse of the supplied C⋆ extension is isometric. -/
theorem isometry_alphaCStar_symm : Isometry A.alphaCStar.symm :=
  A.completion.isometry_alphaCStar_symm

/-- The supplied source state is continuous: it is the pullback of the supplied
continuous target state along the isometric C⋆ extension. -/
theorem continuous_sourceState : Continuous fun a : A.SourceCStar => A.sourceState a :=
  A.toBridge.continuous_sourceState

/-- The supplied target state is continuous. -/
theorem continuous_targetState : Continuous fun b : A.TargetCStar => A.targetState b :=
  A.toBridge.continuous_targetState

/-- The supplied source state is the P25 pullback of the supplied target state
along `alphaCStar`. -/
theorem sourceState_eq_inducedFunctional (a : A.SourceCStar) :
    A.sourceState a = A.completion.inducedFunctional A.targetFunctional a :=
  A.state_compat a

/-! ## The GNS Hilbert spaces, representations and unitary (P13–P15) -/

/-- The GNS Hilbert space of the supplied source state. -/
abbrev sourceGNS : Type _ := A.sourceState.GNS

/-- The GNS Hilbert space of the supplied target state. -/
abbrev targetGNS : Type _ := A.targetState.GNS

/-- The GNS representation of the source completion. -/
noncomputable abbrev sourceGNSRepresentation :
    A.SourceCStar →⋆ₐ[ℂ] (A.sourceGNS →L[ℂ] A.sourceGNS) :=
  A.toBridge.sourceGNSRepresentation

/-- The GNS representation of the target completion. -/
noncomputable abbrev targetGNSRepresentation :
    A.TargetCStar →⋆ₐ[ℂ] (A.targetGNS →L[ℂ] A.targetGNS) :=
  A.toBridge.targetGNSRepresentation

/-- **The GNS unitary** attached to the supplied data (P15). -/
noncomputable def gnsUnitary : A.sourceGNS ≃ₗᵢ[ℂ] A.targetGNS :=
  A.toBridge.gnsUnitary

/-- The GNS unitary preserves inner products. -/
theorem gnsUnitary_inner (x y : A.sourceGNS) :
    ⟪A.gnsUnitary x, A.gnsUnitary y⟫_ℂ = ⟪x, y⟫_ℂ :=
  A.toBridge.gnsUnitary_inner x y

/-- The GNS unitary preserves norms. -/
theorem gnsUnitary_norm (x : A.sourceGNS) : ‖A.gnsUnitary x‖ = ‖x‖ :=
  A.toBridge.gnsUnitary_norm x

/-- **The intertwining formula.**  The GNS unitary carries the source GNS
representation of `a` to the target GNS representation of `alphaCStar a`. -/
theorem gnsUnitary_intertwines (a : A.SourceCStar) (x : A.sourceGNS) :
    A.gnsUnitary (A.sourceGNSRepresentation a x) =
      A.targetGNSRepresentation (A.alphaCStar a) (A.gnsUnitary x) :=
  A.toBridge.gnsUnitary_intertwines a x

/-- The intertwining formula, read in the inverse direction. -/
theorem gnsUnitary_symm_intertwines (a : A.SourceCStar) (y : A.targetGNS) :
    A.gnsUnitary.symm (A.targetGNSRepresentation (A.alphaCStar a) y) =
      A.sourceGNSRepresentation a (A.gnsUnitary.symm y) :=
  A.toBridge.gnsUnitary_symm_intertwines a y

/-! ## The conjugation equivalence and algebraic centralizer transport (P16) -/

/-- Conjugation of a bounded operator by the GNS unitary. -/
noncomputable def gnsConj (T : A.sourceGNS →L[ℂ] A.sourceGNS) :
    A.targetGNS →L[ℂ] A.targetGNS :=
  A.toBridge.gnsConj T

/-- **The conjugation star-algebra equivalence** of the bounded operators on the
two GNS Hilbert spaces. -/
noncomputable def gnsConjStarAlgEquiv :
    (A.sourceGNS →L[ℂ] A.sourceGNS) ≃⋆ₐ[ℂ] (A.targetGNS →L[ℂ] A.targetGNS) :=
  A.toBridge.gnsConjStarAlgEquiv

@[simp]
theorem gnsConjStarAlgEquiv_apply (T : A.sourceGNS →L[ℂ] A.sourceGNS) :
    A.gnsConjStarAlgEquiv T = A.gnsConj T := rfl

/-- Conjugation carries the source GNS representative of `a` to the target GNS
representative of `alphaCStar a`. -/
theorem gnsConj_sourceGNSRepresentation (a : A.SourceCStar) :
    A.gnsConj (A.sourceGNSRepresentation a) =
      A.targetGNSRepresentation (A.alphaCStar a) :=
  A.toBridge.gnsConj_sourceGNSRepresentation a

/-- Conjugation carries the range of the source GNS representation onto the
range of the target GNS representation. -/
theorem gnsConj_range :
    A.gnsConj '' Set.range A.sourceGNSRepresentation = Set.range A.targetGNSRepresentation :=
  A.toBridge.gnsConj_range

/-- Transport of commutation along the conjugation. -/
theorem gnsConj_commute_iff (T : A.sourceGNS →L[ℂ] A.sourceGNS) :
    (∀ a : A.SourceCStar, Commute T (A.sourceGNSRepresentation a)) ↔
      ∀ b : A.TargetCStar, Commute (A.gnsConj T) (A.targetGNSRepresentation b) :=
  A.toBridge.gnsConj_commute_iff T

/-- **Transport of the algebraic centralizer** (commutant) along the
conjugation. -/
theorem gnsConj_image_centralizer :
    A.gnsConj '' (Set.range A.sourceGNSRepresentation).centralizer =
      (Set.range A.targetGNSRepresentation).centralizer :=
  A.toBridge.gnsConj_image_centralizer

/-- Transport of the algebraic bicentralizer along the conjugation. -/
theorem gnsConj_image_centralizer_centralizer :
    A.gnsConj '' (Set.range A.sourceGNSRepresentation).centralizer.centralizer =
      (Set.range A.targetGNSRepresentation).centralizer.centralizer :=
  A.toBridge.gnsConj_image_centralizer_centralizer

/-! ## The finite-stage formula inherited from P25/P24 -/

section FiniteStage

variable (S : TargetStageStates A.completion.limitData)
  (h_restrict : ∀ (i : A.completion.limitData.Index) (y : A.completion.limitData.Target i),
    A.targetState (A.completion.targetEmbed (A.completion.limitData.targetOf i y)) = S.omega i y)

include h_restrict

/-- **The finite-stage formula.**  If the supplied target state restricts along
`targetEmbed` to the supplied P24 target-stage expectations, then the supplied
source state takes on every P23 finite-stage representative the value
`S.omega i (stageEquiv i x)`. -/
theorem sourceState_sourceEmbed_sourceOf
    (i : A.completion.limitData.Index) (x : A.completion.limitData.Source i) :
    A.sourceState (A.completion.sourceEmbed (A.completion.limitData.sourceOf i x)) =
      S.omega i (A.completion.limitData.stageEquiv i x) := by
  rw [A.state_compat, A.completion.alphaCStar_stage, h_restrict]

/-- The supplied source state restricts along `sourceEmbed` to P24's algebraic
transported state `pulledBackState`. -/
theorem sourceState_sourceEmbed (z : A.completion.limitData.SourceLimit) :
    A.sourceState (A.completion.sourceEmbed z) = S.pulledBackState z := by
  rw [A.state_compat, A.completion.alphaCStar_sourceEmbed,
    TargetStageStates.pulledBackState_eq_targetLimitState_alpha]
  induction A.completion.limitData.alpha z using DirectLimit.induction with
  | _ i y =>
    change A.targetState (A.completion.targetEmbed (A.completion.limitData.targetOf i y)) =
      S.targetLimitState (A.completion.limitData.targetOf i y)
    rw [h_restrict, TargetStageStates.targetLimitState_targetOf]

/-- **Uniqueness by density.**  A continuous functional on the source completion
with the expected finite-stage values agrees with the supplied source state. -/
theorem sourceState_unique_of_continuous
    (psi : A.SourceCStar →ₗ[ℂ] ℂ) (h_psi : Continuous psi)
    (h_stage : ∀ (i : A.completion.limitData.Index) (x : A.completion.limitData.Source i),
      psi (A.completion.sourceEmbed (A.completion.limitData.sourceOf i x)) =
        S.omega i (A.completion.limitData.stageEquiv i x)) :
    (psi : A.SourceCStar → ℂ) = fun a => A.sourceState a := by
  refine Continuous.ext_on A.completion.sourceEmbed_dense h_psi A.continuous_sourceState ?_
  rintro _ ⟨z, rfl⟩
  induction z using DirectLimit.induction with
  | _ i x =>
    change psi (A.completion.sourceEmbed (A.completion.limitData.sourceOf i x)) =
      A.sourceState (A.completion.sourceEmbed (A.completion.limitData.sourceOf i x))
    rw [h_stage, A.sourceState_sourceEmbed_sourceOf S h_restrict]

end FiniteStage

end AlphaGNSData

/-! ## The packaged bridge theorem -/

/-- **The P26 bridge theorem.**  Supplied C⋆ completions of the two P23
algebraic direct limits with a supplied C⋆ extension `alphaCStar` of the
algebraic `alpha` (P25), together with supplied positive unital continuous
source and target states which are *exactly compatible* along `alphaCStar`,
yield:

* a `ℂ`-linear isometric equivalence (GNS unitary) `U` of the two GNS Hilbert
  spaces, intertwining the two GNS representations along `alphaCStar`;
* the star-algebra equivalence given by conjugation by `U`, carrying the source
  GNS representation onto the target GNS representation and transporting the
  algebraic centralizer and bicentralizer; and
* the finite-stage formula for the source state inherited from P25/P24.

Everything is conditional on the supplied data.  No normality, quasi-equivalence,
spatial tensor product, von Neumann closure, hyperfiniteness, factor type, trace
or weight is claimed. -/
theorem alpha_gns_bridge_package (A : AlphaGNSData)
    (S : TargetStageStates A.completion.limitData)
    (h_restrict : ∀ (i : A.completion.limitData.Index) (y : A.completion.limitData.Target i),
      A.targetState (A.completion.targetEmbed (A.completion.limitData.targetOf i y)) =
        S.omega i y) :
    Isometry A.alphaCStar ∧
      (∀ (a : A.SourceCStar) (x : A.sourceGNS),
        A.gnsUnitary (A.sourceGNSRepresentation a x) =
          A.targetGNSRepresentation (A.alphaCStar a) (A.gnsUnitary x)) ∧
      (∀ x y : A.sourceGNS, ⟪A.gnsUnitary x, A.gnsUnitary y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      (∀ a : A.SourceCStar, A.gnsConjStarAlgEquiv (A.sourceGNSRepresentation a) =
        A.targetGNSRepresentation (A.alphaCStar a)) ∧
      A.gnsConj '' Set.range A.sourceGNSRepresentation = Set.range A.targetGNSRepresentation ∧
      A.gnsConj '' (Set.range A.sourceGNSRepresentation).centralizer =
        (Set.range A.targetGNSRepresentation).centralizer ∧
      A.gnsConj '' (Set.range A.sourceGNSRepresentation).centralizer.centralizer =
        (Set.range A.targetGNSRepresentation).centralizer.centralizer ∧
      (∀ (i : A.completion.limitData.Index) (x : A.completion.limitData.Source i),
        A.sourceState (A.completion.sourceEmbed (A.completion.limitData.sourceOf i x)) =
          S.omega i (A.completion.limitData.stageEquiv i x)) ∧
      (∀ z : A.completion.limitData.SourceLimit,
        A.sourceState (A.completion.sourceEmbed z) = S.pulledBackState z) :=
  ⟨A.isometry_alphaCStar, A.gnsUnitary_intertwines, A.gnsUnitary_inner,
    A.gnsConj_sourceGNSRepresentation, A.gnsConj_range, A.gnsConj_image_centralizer,
    A.gnsConj_image_centralizer_centralizer,
    A.sourceState_sourceEmbed_sourceOf S h_restrict, A.sourceState_sourceEmbed S h_restrict⟩

/-! ## A sanity instance

The interface is not vacuous: over the one-stage P25 `trivialCompletionData`
both completions are `ℂ`, `alphaCStar` is the identity, and the identity
functional on `ℂ` is a positive unital continuous state compatible with itself.
This is a consistency check on the bundle, not a model of the manuscript's
regional algebras. -/

/-- The identity functional on `ℂ`, as a positive linear map. -/
noncomputable def trivialState : ℂ →ₚ[ℂ] ℂ :=
  ⟨LinearMap.id, fun _ _ h => h⟩

@[simp] theorem trivialState_apply (z : ℂ) : trivialState z = z := rfl

/-- A one-stage instance of `AlphaGNSData`, showing all fields can be met
simultaneously. -/
noncomputable def trivialAlphaGNSData : AlphaGNSData where
  completion := trivialCompletionData
  sourceOrder := inferInstanceAs (PartialOrder ℂ)
  targetOrder := inferInstanceAs (PartialOrder ℂ)
  sourceStarOrdered := inferInstanceAs (StarOrderedRing ℂ)
  targetStarOrdered := inferInstanceAs (StarOrderedRing ℂ)
  sourceState := trivialState
  targetState := trivialState
  sourceState_one := rfl
  targetState_one := rfl
  targetState_continuous := continuous_id
  state_compat := fun _ => rfl

end CStarAlphaGNSBridge

end AristotleCandidates
