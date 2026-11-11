import AristotleCandidates.ConcreteQuasilocalCStarModel
import AristotleCandidates.CStarAlphaGNSBridge

/-!
# A state-preserving C⋆-`alpha` on the concrete quasilocal model, and GNS transport

**Context declaration.** Source basis: `main.tex:1921-1958` (the state
`ω̃ = ω_S ∘ α` on the infinite Pauli algebra, its finite-stage density-matrix
formula, and the resulting GNS Hilbert space `H_ω̃` with representation
`π_ω̃`).

This module packages three ingredients into one bundle and derives the
analytic and GNS consequences:

1. the **concrete completion of P38**
   (`StabilizerHyperfinite.ConcreteQuasilocalCStarModel.quasilocalCStarAlgebra`)
   of the *source* system of a supplied P23 `RegionalLimitData`: given a
   supplied Hilbert space `H` and a supplied compatible family of finite-stage
   representations `rho i : Source i →⋆ₐ[ℂ] (H →L[ℂ] H)`, the source
   C⋆-algebra is **constructed** here as the closed operator range of the
   induced representation of the algebraic direct limit, together with its
   canonical dense embedding;
2. a **supplied regional completion**: a unital complex C⋆-algebra
   `TargetCStar` with a supplied dense star-algebra embedding of the algebraic
   target direct limit; and
3. a **supplied state-preserving extension** `alphaCStar` of the
   finite-coordinate algebraic `alpha`: a C⋆ star-algebra equivalence of the
   concrete source completion with the supplied regional completion which on
   every finite-stage representative is the supplied finite-stage equivalence,
   together with supplied positive unital states on the two completions that
   are *exactly compatible* along `alphaCStar`.

## Checked consequences

Everything below is proved from that data; nothing about it is assumed.

* `RegionalConcreteCompletionData.denseRange_sourceEmbed`,
  `coe_sourceSubalgebra_eq_closure_iUnion`, `sourceSubalgebra_isLeast`: the
  constructed source completion is the closure of the union of the
  finite-stage operator ranges, and the least closed star-subalgebra with that
  property.
* `RegionalConcreteCompletionData.injective_sourceEmbed`: faithfulness of the
  concrete embedding, conditional on injectivity of the stage
  representations.
* `RegionalConcreteCompletionData.alphaCStar_sourceEmbed`,
  `alphaCStar_symm_targetEmbed`, `isometry_alphaCStar`, `norm_alphaCStar`,
  `alphaCStar_unique_of_continuous`: the extension formula on the whole
  algebraic limit, isometry, and uniqueness of the extension by density.
* `RegionalConcreteCompletionData.eq_of_stage_formulas`: **equality from dense
  finite-stage formulas** — two continuous functionals on the concrete source
  completion agreeing on every finite-stage operator `rho i x` are equal.
* `StatePreservingData.continuous_sourceState`,
  `sourceState_eq_pullback`: **the continuous state pullback**: the supplied
  source state is the pullback `targetState ∘ alphaCStar` and is continuous.
* `StatePreservingData.sourceState_stageElem`, `sourceState_sourceEmbed`,
  `sourceState_unique_of_continuous`: the value of the source state on the
  concrete operator `rho i x` is the supplied finite-stage expectation, and
  the source state is the unique continuous functional with those values.
* `StatePreservingData.gnsUnitary`, `gnsUnitary_inner`,
  `gnsUnitary_intertwines`, `gnsUnitary_symm_intertwines`,
  `gnsConjStarAlgEquiv`, `gnsConj_range`, `gnsConj_image_centralizer`,
  `gnsConj_image_centralizer_centralizer`: **the canonical GNS unitary and its
  intertwining consequences**, obtained through the existing GNS bridge
  (P13–P16, P19, P26).
* `state_preserving_gns_package`: the packaged statement.
* `opStatePreserving`: a one-stage instance showing that the whole bundle of
  hypotheses — including the order structures and the two states — is
  simultaneously satisfiable, so none of the statements above is vacuous.

## The exact unfinished geometric input

The following manuscript data is **not** constructed here and appears only as
explicit hypotheses (fields of `RegionalConcreteCompletionData` and
`StatePreservingData`):

* the finite adapted-coordinate data of `main.tex:1900-1920`: the local
  isotropic subspace `W_Γ = W ∩ V_Γ`, a symplectic (hyperbolic) basis
  `{z_i, x_i}` of `V_Γ` adapted to it, and the resulting finite-stage
  star-algebra equivalences `stageEquiv i` together with their coherence with
  the connecting maps (these are the fields of the supplied P23
  `RegionalLimitData`);
* the finite-stage operator representations `rho` of the source stages on a
  supplied Hilbert space `H`, their compatibility `rho_compat`, and (where
  used) their injectivity;
* the regional C⋆-completion `TargetCStar` of the algebraic regional limit,
  its dense embedding `targetEmbed`, and the boundedness statement that lets
  the algebraic `alpha` extend, i.e. the equivalence `alphaCStar` with its
  finite-stage formula `alphaCStar_stage`;
* the states: the positive unital continuous regional state `targetState`
  (the manuscript's `ω_S` on `A_Γ`), the source state `sourceState`, and the
  state-preservation identity `state_compat`; the manuscript's
  density-matrix formula `eq:tilde_omega` enters only through the supplied
  finite-stage expectations `S.omega` of P24.

## What is *not* claimed

No normality of any map or functional, no von Neumann closure, bicommutant,
quasi-equivalence, spatial or any tensor-product decomposition, no factor
type, no hyperfiniteness, and no trace or weight.  The commutants below are
the purely algebraic `Set.centralizer` ones inherited from P16.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace AristotleCandidates

namespace StatePreservingGNSModel

open StabilizerHyperfinite
open StabilizerHyperfinite.InfiniteAlgebraicRegionalEquiv
open StabilizerHyperfinite.ConcreteQuasilocalCStarModel
open AristotleCandidates.InfiniteAlgebraicStateTransport
open AristotleCandidates.CStarCompletionAlphaInterface
open AristotleCandidates.CStarAlphaGNSBridge

open scoped ComplexOrder InnerProductSpace

/-! ## The supplied completion data with a concrete source side -/

/-- **Supplied** data for a state-preserving C⋆-extension of the algebraic
`alpha` whose *source* completion is the concrete P38 model.

The source C⋆-algebra is not an assumption: it is the closed operator range
`quasilocalCStarAlgebra rho rho_compat` of the representation of the algebraic
source limit induced by the supplied stage representations.  The regional
(target) completion, its dense embedding, and the extension `alphaCStar` of
the finite-coordinate algebraic `alpha` are supplied inputs. -/
structure RegionalConcreteCompletionData where
  /-- The supplied P23 algebraic direct-limit data (the finite adapted
  coordinates enter only here). -/
  limitData : RegionalLimitData
  /-- The supplied Hilbert space carrying the finite-stage representations. -/
  H : Type*
  [normedH : NormedAddCommGroup H]
  [innerH : InnerProductSpace ℂ H]
  [completeH : CompleteSpace H]
  /-- The supplied finite-stage operator representations of the source stages. -/
  rho : ∀ i, limitData.Source i →⋆ₐ[ℂ] (H →L[ℂ] H)
  /-- Supplied compatibility of the stage representations with the connecting
  maps of the source system. -/
  rho_compat : ∀ (i j : limitData.Index) (le : i ≤ j) (x : limitData.Source i),
    rho j (limitData.sourceConnecting i j le x) = rho i x
  /-- The supplied regional C⋆-completion of the algebraic target limit. -/
  TargetCStar : Type*
  /-- The supplied unital complex C⋆ structure on the regional completion. -/
  targetCStar : CStarAlgebra TargetCStar
  /-- The supplied dense algebraic embedding of the target direct limit. -/
  targetEmbed : limitData.TargetLimit →⋆ₐ[ℂ] TargetCStar
  /-- Supplied density of the target embedding. -/
  targetEmbed_dense : Dense (Set.range targetEmbed)
  /-- The supplied C⋆ extension of the finite-coordinate algebraic `alpha`,
  from the *constructed* concrete source completion to the supplied regional
  completion. -/
  alphaCStar : (quasilocalCStarAlgebra rho rho_compat) ≃⋆ₐ[ℂ] TargetCStar
  /-- The supplied **exact extension formula** on finite-stage
  representatives. -/
  alphaCStar_stage : ∀ (i : limitData.Index) (x : limitData.Source i),
    alphaCStar (quasilocalEmbedding rho rho_compat (limitData.sourceOf i x)) =
      targetEmbed (limitData.targetOf i (limitData.stageEquiv i x))

attribute [instance] RegionalConcreteCompletionData.normedH
  RegionalConcreteCompletionData.innerH RegionalConcreteCompletionData.completeH
  RegionalConcreteCompletionData.targetCStar

namespace RegionalConcreteCompletionData

variable (M : RegionalConcreteCompletionData)

/-- The **constructed** concrete source C⋆-completion, as a closed
star-subalgebra of the bounded operators: the closed operator range of the
induced representation of the algebraic source limit. -/
noncomputable def sourceSubalgebra : StarSubalgebra ℂ (M.H →L[ℂ] M.H) :=
  quasilocalCStarAlgebra M.rho M.rho_compat

/-- The bundle, viewed as a P25 `CStarCompletionData`.  The source completion
and its dense embedding are the constructed concrete ones; only the target
side and `alphaCStar` are supplied. -/
noncomputable def toCStarCompletionData : CStarCompletionData where
  limitData := M.limitData
  SourceCStar := quasilocalCStarAlgebra M.rho M.rho_compat
  TargetCStar := M.TargetCStar
  sourceCStar := instCStarAlgebra M.rho M.rho_compat
  targetCStar := M.targetCStar
  sourceEmbed := quasilocalEmbedding M.rho M.rho_compat
  targetEmbed := M.targetEmbed
  sourceEmbed_dense := denseRange_quasilocalEmbedding M.rho M.rho_compat
  targetEmbed_dense := M.targetEmbed_dense
  alphaCStar := M.alphaCStar
  alphaCStar_stage := M.alphaCStar_stage

@[simp] theorem toCStarCompletionData_limitData :
    M.toCStarCompletionData.limitData = M.limitData := rfl

/-- The carrier of the concrete source C⋆-completion. -/
noncomputable abbrev SourceCStar : Type _ := M.toCStarCompletionData.SourceCStar

/-- The canonical dense embedding of the algebraic source limit into the
constructed concrete source completion. -/
noncomputable abbrev sourceEmbed : M.limitData.SourceLimit →⋆ₐ[ℂ] M.SourceCStar :=
  M.toCStarCompletionData.sourceEmbed

/-- The supplied C⋆ extension of `alpha`, read on the concrete source
completion. -/
noncomputable abbrev alphaCStarMap : M.SourceCStar ≃⋆ₐ[ℂ] M.TargetCStar :=
  M.toCStarCompletionData.alphaCStar

/-- The finite-stage operator `rho i x`, viewed inside the concrete source
completion. -/
noncomputable def stageElem (i : M.limitData.Index) (x : M.limitData.Source i) :
    M.SourceCStar :=
  M.sourceEmbed (M.limitData.sourceOf i x)

/-- The concrete source element attached to a finite stage **is** the supplied
finite-stage operator `rho i x`. -/
theorem val_stageElem (i : M.limitData.Index) (x : M.limitData.Source i) :
    (M.stageElem i x).val = M.rho i x :=
  coe_quasilocalEmbedding_of M.rho M.rho_compat i x

/-- The finite-stage extension formula, phrased with `stageElem`. -/
theorem alphaCStar_stageElem (i : M.limitData.Index) (x : M.limitData.Source i) :
    M.alphaCStarMap (M.stageElem i x) =
      M.targetEmbed (M.limitData.targetOf i (M.limitData.stageEquiv i x)) :=
  M.alphaCStar_stage i x

/-- The concrete source completion is the closure of the union of the
finite-stage operator ranges. -/
theorem coe_sourceSubalgebra_eq_closure_iUnion :
    ((M.sourceSubalgebra : StarSubalgebra ℂ (M.H →L[ℂ] M.H)) : Set (M.H →L[ℂ] M.H)) =
      closure (⋃ i, Set.range (M.rho i)) :=
  coe_quasilocalCStarAlgebra_eq_closure_iUnion M.rho M.rho_compat

/-- The concrete source completion is the least closed star-subalgebra of the
bounded operators containing all finite-stage operator ranges. -/
theorem sourceSubalgebra_isLeast :
    IsLeast {S : StarSubalgebra ℂ (M.H →L[ℂ] M.H) |
        IsClosed (S : Set (M.H →L[ℂ] M.H)) ∧ ∀ i x, M.rho i x ∈ S} M.sourceSubalgebra :=
  quasilocalCStarAlgebra_isLeast M.rho M.rho_compat

/-- Density of the constructed source embedding. -/
theorem denseRange_sourceEmbed : Dense (Set.range M.sourceEmbed) :=
  M.toCStarCompletionData.sourceEmbed_dense

/-- **Conditional faithfulness** of the concrete source embedding. -/
theorem injective_sourceEmbed (h_inj : ∀ i, Function.Injective (M.rho i)) :
    Function.Injective M.sourceEmbed :=
  injective_quasilocalEmbedding M.rho M.rho_compat h_inj

/-! ### Checked analytic consequences -/

/-- The extension formula on the whole algebraic source limit. -/
theorem alphaCStar_sourceEmbed (z : M.limitData.SourceLimit) :
    M.alphaCStarMap (M.sourceEmbed z) = M.targetEmbed (M.limitData.alpha z) :=
  M.toCStarCompletionData.alphaCStar_sourceEmbed z

/-- The inverse extension formula on the whole algebraic target limit. -/
theorem alphaCStar_symm_targetEmbed (w : M.limitData.TargetLimit) :
    M.alphaCStarMap.symm (M.targetEmbed w) = M.sourceEmbed (M.limitData.alpha.symm w) :=
  M.toCStarCompletionData.alphaCStar_symm_targetEmbed w

/-- The supplied extension is isometric. -/
theorem isometry_alphaCStar : Isometry M.alphaCStarMap :=
  M.toCStarCompletionData.isometry_alphaCStar

/-- The inverse of the supplied extension is isometric. -/
theorem isometry_alphaCStar_symm : Isometry M.alphaCStarMap.symm :=
  M.toCStarCompletionData.isometry_alphaCStar_symm

theorem continuous_alphaCStar : Continuous M.alphaCStarMap :=
  M.toCStarCompletionData.continuous_alphaCStar

theorem norm_alphaCStar (a : M.SourceCStar) : ‖M.alphaCStarMap a‖ = ‖a‖ :=
  M.toCStarCompletionData.norm_alphaCStar a

/-- **Uniqueness of the extension** among continuous maps with the
finite-stage formula. -/
theorem alphaCStar_unique_of_continuous (g : M.SourceCStar → M.TargetCStar)
    (hg : Continuous g)
    (h_stage : ∀ (i : M.limitData.Index) (x : M.limitData.Source i),
      g (M.stageElem i x) =
        M.targetEmbed (M.limitData.targetOf i (M.limitData.stageEquiv i x))) :
    g = M.alphaCStarMap :=
  M.toCStarCompletionData.alphaCStar_unique_of_continuous g hg h_stage

/-- **Equality from dense finite-stage formulas.**  Two continuous functionals
on the concrete source completion that agree on every finite-stage operator
`rho i x` are equal. -/
theorem eq_of_stage_formulas
    (psi chi : M.SourceCStar →ₗ[ℂ] ℂ) (h_psi : Continuous psi) (h_chi : Continuous chi)
    (h_stage : ∀ (i : M.limitData.Index) (x : M.limitData.Source i),
      psi (M.stageElem i x) = chi (M.stageElem i x)) :
    psi = chi := by
  have h_fun : (psi : M.SourceCStar → ℂ) = chi := by
    refine Continuous.ext_on M.denseRange_sourceEmbed h_psi h_chi ?_
    rintro _ ⟨z, rfl⟩
    induction z using DirectLimit.induction with
    | _ i x => exact h_stage i x
  exact LinearMap.ext fun a => congrFun h_fun a

/-- **Equality of continuous maps** into the regional completion from the dense
finite-stage formulas. -/
theorem funext_of_stage_formulas (g h : M.SourceCStar → M.TargetCStar)
    (hg : Continuous g) (hh : Continuous h)
    (h_stage : ∀ (i : M.limitData.Index) (x : M.limitData.Source i),
      g (M.stageElem i x) = h (M.stageElem i x)) :
    g = h := by
  refine Continuous.ext_on M.denseRange_sourceEmbed hg hh ?_
  rintro _ ⟨z, rfl⟩
  induction z using DirectLimit.induction with
  | _ i x => exact h_stage i x

end RegionalConcreteCompletionData

/-! ## Adding the state-preserving data -/

/-- **Supplied** state data making the concrete C⋆-extension of `alpha`
*state preserving*, together with the order structures required by Mathlib's
positive-functional/GNS API. -/
structure StatePreservingData where
  /-- The supplied concrete-source completion data. -/
  completion : RegionalConcreteCompletionData
  /-- Supplied partial order on the concrete source completion. -/
  [sourceOrder : PartialOrder completion.SourceCStar]
  /-- Supplied partial order on the supplied regional completion. -/
  [targetOrder : PartialOrder completion.TargetCStar]
  /-- The source order is a star-ordered ring structure. -/
  [sourceStarOrdered : StarOrderedRing completion.SourceCStar]
  /-- The target order is a star-ordered ring structure. -/
  [targetStarOrdered : StarOrderedRing completion.TargetCStar]
  /-- The supplied positive functional on the concrete source completion. -/
  sourceState : completion.SourceCStar →ₚ[ℂ] ℂ
  /-- The supplied positive functional on the regional completion (the
  manuscript's regional state). -/
  targetState : completion.TargetCStar →ₚ[ℂ] ℂ
  /-- The supplied source state is unital. -/
  sourceState_one : sourceState 1 = 1
  /-- The supplied target state is unital. -/
  targetState_one : targetState 1 = 1
  /-- The supplied target state is continuous. -/
  targetState_continuous : Continuous targetState.toLinearMap
  /-- **State preservation**: the supplied extension of `alpha` carries the
  source state to the regional state. -/
  state_compat : ∀ a : completion.SourceCStar,
    sourceState a = targetState (completion.alphaCStarMap a)

attribute [instance] StatePreservingData.sourceOrder StatePreservingData.targetOrder
  StatePreservingData.sourceStarOrdered StatePreservingData.targetStarOrdered

namespace StatePreservingData

variable (M : StatePreservingData)

/-- The concrete source completion. -/
noncomputable abbrev SourceCStar : Type _ := M.completion.SourceCStar

/-- The supplied regional completion. -/
abbrev TargetCStar : Type _ := M.completion.TargetCStar

/-- The supplied state-preserving C⋆ extension of `alpha`. -/
noncomputable abbrev alphaCStar : M.SourceCStar ≃⋆ₐ[ℂ] M.TargetCStar :=
  M.completion.alphaCStarMap

/-- The supplied data, packaged as a P26 `AlphaGNSData`. -/
noncomputable def toAlphaGNSData : AlphaGNSData where
  completion := M.completion.toCStarCompletionData
  sourceOrder := M.sourceOrder
  targetOrder := M.targetOrder
  sourceStarOrdered := M.sourceStarOrdered
  targetStarOrdered := M.targetStarOrdered
  sourceState := M.sourceState
  targetState := M.targetState
  sourceState_one := M.sourceState_one
  targetState_one := M.targetState_one
  targetState_continuous := M.targetState_continuous
  state_compat := M.state_compat

/-! ### The continuous state pullback -/

/-- **The state pullback formula.**  The supplied source state is the pullback
of the supplied regional state along the extension of `alpha`. -/
theorem sourceState_eq_pullback (a : M.SourceCStar) :
    M.sourceState a = M.targetState (M.alphaCStar a) :=
  M.state_compat a

/-- **Continuity of the pullback state.**  The source state is continuous,
being the pullback of the continuous regional state along an isometric
C⋆-equivalence. -/
theorem continuous_sourceState : Continuous fun a : M.SourceCStar => M.sourceState a :=
  M.toAlphaGNSData.continuous_sourceState

/-- The supplied regional state is continuous. -/
theorem continuous_targetState : Continuous fun b : M.TargetCStar => M.targetState b :=
  M.toAlphaGNSData.continuous_targetState

/-! ### Equality from dense finite-stage formulas -/

section FiniteStage

variable (S : TargetStageStates M.completion.limitData)
  (h_restrict : ∀ (i : M.completion.limitData.Index) (y : M.completion.limitData.Target i),
    M.targetState (M.completion.targetEmbed (M.completion.limitData.targetOf i y)) = S.omega i y)

include h_restrict

/-- **The finite-stage formula.**  On the concrete finite-stage operator
`rho i x` the source state takes the supplied finite-stage expectation of the
transported element. -/
theorem sourceState_stageElem (i : M.completion.limitData.Index)
    (x : M.completion.limitData.Source i) :
    M.sourceState (M.completion.stageElem i x) =
      S.omega i (M.completion.limitData.stageEquiv i x) := by
  rw [M.state_compat, M.completion.alphaCStar_stageElem, h_restrict]

/-- The source state restricts along the concrete dense embedding to P24's
algebraic transported state. -/
theorem sourceState_sourceEmbed (z : M.completion.limitData.SourceLimit) :
    M.sourceState (M.completion.sourceEmbed z) = S.pulledBackState z :=
  M.toAlphaGNSData.sourceState_sourceEmbed S h_restrict z

/-- **Equality from the dense finite-stage formulas.**  A continuous
functional on the concrete source completion with the expected finite-stage
values *is* the source state. -/
theorem sourceState_unique_of_continuous
    (psi : M.SourceCStar →ₗ[ℂ] ℂ) (h_psi : Continuous psi)
    (h_stage : ∀ (i : M.completion.limitData.Index) (x : M.completion.limitData.Source i),
      psi (M.completion.stageElem i x) = S.omega i (M.completion.limitData.stageEquiv i x)) :
    (psi : M.SourceCStar → ℂ) = fun a => M.sourceState a :=
  M.toAlphaGNSData.sourceState_unique_of_continuous S h_restrict psi h_psi h_stage

end FiniteStage

/-! ### The canonical GNS unitary and intertwining -/

/-- The GNS Hilbert space of the source state. -/
noncomputable abbrev sourceGNS : Type _ := M.toAlphaGNSData.sourceGNS

/-- The GNS Hilbert space of the regional state. -/
noncomputable abbrev targetGNS : Type _ := M.toAlphaGNSData.targetGNS

/-- The GNS representation of the concrete source completion. -/
noncomputable abbrev sourceGNSRepresentation :
    M.toAlphaGNSData.SourceCStar →⋆ₐ[ℂ] (M.sourceGNS →L[ℂ] M.sourceGNS) :=
  M.toAlphaGNSData.sourceGNSRepresentation

/-- The GNS representation of the regional completion. -/
noncomputable abbrev targetGNSRepresentation :
    M.toAlphaGNSData.TargetCStar →⋆ₐ[ℂ] (M.targetGNS →L[ℂ] M.targetGNS) :=
  M.toAlphaGNSData.targetGNSRepresentation

/-- **The canonical GNS unitary** determined by the state-preserving
extension. -/
noncomputable def gnsUnitary : M.sourceGNS ≃ₗᵢ[ℂ] M.targetGNS :=
  M.toAlphaGNSData.gnsUnitary

theorem gnsUnitary_inner (x y : M.sourceGNS) :
    ⟪M.gnsUnitary x, M.gnsUnitary y⟫_ℂ = ⟪x, y⟫_ℂ :=
  M.toAlphaGNSData.gnsUnitary_inner x y

theorem gnsUnitary_norm (x : M.sourceGNS) : ‖M.gnsUnitary x‖ = ‖x‖ :=
  M.toAlphaGNSData.gnsUnitary_norm x

/-- **Intertwining.**  The GNS unitary carries the source GNS representation
of `a` to the regional GNS representation of `alphaCStar a`. -/
theorem gnsUnitary_intertwines (a : M.toAlphaGNSData.SourceCStar) (x : M.sourceGNS) :
    M.gnsUnitary (M.sourceGNSRepresentation a x) =
      M.targetGNSRepresentation (M.toAlphaGNSData.alphaCStar a) (M.gnsUnitary x) :=
  M.toAlphaGNSData.gnsUnitary_intertwines a x

/-- The intertwining formula in the inverse direction. -/
theorem gnsUnitary_symm_intertwines (a : M.toAlphaGNSData.SourceCStar) (y : M.targetGNS) :
    M.gnsUnitary.symm (M.targetGNSRepresentation (M.toAlphaGNSData.alphaCStar a) y) =
      M.sourceGNSRepresentation a (M.gnsUnitary.symm y) :=
  M.toAlphaGNSData.gnsUnitary_symm_intertwines a y

/-- Conjugation of a bounded operator by the GNS unitary. -/
noncomputable def gnsConj (T : M.sourceGNS →L[ℂ] M.sourceGNS) :
    M.targetGNS →L[ℂ] M.targetGNS :=
  M.toAlphaGNSData.gnsConj T

/-- The conjugation star-algebra equivalence of the bounded operators on the
two GNS Hilbert spaces. -/
noncomputable def gnsConjStarAlgEquiv :
    (M.sourceGNS →L[ℂ] M.sourceGNS) ≃⋆ₐ[ℂ] (M.targetGNS →L[ℂ] M.targetGNS) :=
  M.toAlphaGNSData.gnsConjStarAlgEquiv

@[simp] theorem gnsConjStarAlgEquiv_apply (T : M.sourceGNS →L[ℂ] M.sourceGNS) :
    M.gnsConjStarAlgEquiv T = M.gnsConj T := rfl

theorem gnsConj_sourceGNSRepresentation (a : M.toAlphaGNSData.SourceCStar) :
    M.gnsConj (M.sourceGNSRepresentation a) =
      M.targetGNSRepresentation (M.toAlphaGNSData.alphaCStar a) :=
  M.toAlphaGNSData.gnsConj_sourceGNSRepresentation a

theorem gnsConj_range :
    M.gnsConj '' Set.range M.sourceGNSRepresentation = Set.range M.targetGNSRepresentation :=
  M.toAlphaGNSData.gnsConj_range

/-- Transport of the algebraic centralizer (commutant) along the
conjugation. -/
theorem gnsConj_image_centralizer :
    M.gnsConj '' (Set.range M.sourceGNSRepresentation).centralizer =
      (Set.range M.targetGNSRepresentation).centralizer :=
  M.toAlphaGNSData.gnsConj_image_centralizer

/-- Transport of the algebraic bicentralizer along the conjugation. -/
theorem gnsConj_image_centralizer_centralizer :
    M.gnsConj '' (Set.range M.sourceGNSRepresentation).centralizer.centralizer =
      (Set.range M.targetGNSRepresentation).centralizer.centralizer :=
  M.toAlphaGNSData.gnsConj_image_centralizer_centralizer

end StatePreservingData

/-! ## The packaged theorem -/

/-- **The P39 package.**  Given

* a supplied P23 finite-coordinate `RegionalLimitData`,
* a supplied Hilbert space with a supplied compatible family of finite-stage
  representations of the source stages — from which the concrete source
  C⋆-completion is *constructed* as the closed operator range (P38),
* a supplied regional C⋆-completion with a dense algebraic embedding,
* a supplied state-preserving C⋆ extension `alphaCStar` of the algebraic
  `alpha`, and
* supplied positive unital states, continuous on the regional side, exactly
  compatible along `alphaCStar`,

one obtains: the isometry of the extension; the continuous state pullback; the
finite-stage formula for the source state on each concrete operator `rho i x`
and its determination by density; and the canonical GNS unitary with its
intertwining and (algebraic) commutant transport. -/
theorem state_preserving_gns_package (M : StatePreservingData)
    (S : TargetStageStates M.completion.limitData)
    (h_restrict : ∀ (i : M.completion.limitData.Index) (y : M.completion.limitData.Target i),
      M.targetState (M.completion.targetEmbed (M.completion.limitData.targetOf i y)) =
        S.omega i y) :
    Isometry M.alphaCStar ∧
      Continuous (fun a : M.SourceCStar => M.sourceState a) ∧
      (∀ a : M.SourceCStar, M.sourceState a = M.targetState (M.alphaCStar a)) ∧
      (∀ (i : M.completion.limitData.Index) (x : M.completion.limitData.Source i),
        M.sourceState (M.completion.stageElem i x) =
          S.omega i (M.completion.limitData.stageEquiv i x)) ∧
      (∀ z : M.completion.limitData.SourceLimit,
        M.sourceState (M.completion.sourceEmbed z) = S.pulledBackState z) ∧
      (∀ (a : M.toAlphaGNSData.SourceCStar) (x : M.sourceGNS),
        M.gnsUnitary (M.sourceGNSRepresentation a x) =
          M.targetGNSRepresentation (M.toAlphaGNSData.alphaCStar a) (M.gnsUnitary x)) ∧
      (∀ x y : M.sourceGNS, ⟪M.gnsUnitary x, M.gnsUnitary y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      M.gnsConj '' (Set.range M.sourceGNSRepresentation).centralizer =
        (Set.range M.targetGNSRepresentation).centralizer :=
  ⟨M.completion.isometry_alphaCStar, M.continuous_sourceState, M.state_compat,
    M.sourceState_stageElem S h_restrict, M.sourceState_sourceEmbed S h_restrict,
    M.gnsUnitary_intertwines, M.gnsUnitary_inner, M.gnsConj_image_centralizer⟩


/-! ## Non-vacuity of the supplied hypotheses

The bundle above is not vacuous.  Over the one-stage constant system of the
bounded operators on `ℂ`, the identity stage representations are faithful and
isometric, the concrete P38 completion is the closed operator range they
generate, the regional completion may be taken to be that same C⋆-algebra with
`alphaCStar` the identity, and the vector state at `1 ∈ ℂ` is a positive
unital continuous state compatible with itself.  This is a consistency check
on the bundle, **not** a model of the manuscript's regional algebras. -/

section NonVacuity

/-- The one-stage constant directed system of bounded operators on `ℂ`, with
identity connecting maps and identity stage equivalences. -/
noncomputable def opLimitData : RegionalLimitData where
  Index := Unit
  Source := fun _ => ℂ →L[ℂ] ℂ
  Target := fun _ => ℂ →L[ℂ] ℂ
  sourceConnecting := fun _ _ _ => StarAlgHom.id ℂ (ℂ →L[ℂ] ℂ)
  targetConnecting := fun _ _ _ => StarAlgHom.id ℂ (ℂ →L[ℂ] ℂ)
  sourceDirected := ⟨by intros; rfl, by intros; rfl⟩
  targetDirected := ⟨by intros; rfl, by intros; rfl⟩
  stageEquiv := fun _ => StarAlgEquiv.refl
  stageEquiv_connecting := fun _ _ _ _ => rfl

/-- The identity stage representations of the one-stage system on `H = ℂ`. -/
noncomputable def opRho : ∀ i : opLimitData.Index,
    opLimitData.Source i →⋆ₐ[ℂ] (ℂ →L[ℂ] ℂ) :=
  fun _ => StarAlgHom.id ℂ (ℂ →L[ℂ] ℂ)

theorem opRho_compat : ∀ (i j : opLimitData.Index) (le : i ≤ j) (x : opLimitData.Source i),
    opRho j (opLimitData.sourceConnecting i j le x) = opRho i x :=
  fun _ _ _ _ => rfl

/-- The concrete P38 completion of the one-stage system. -/
noncomputable def opAlgebra : StarSubalgebra ℂ (ℂ →L[ℂ] ℂ) :=
  quasilocalCStarAlgebra opRho opRho_compat

noncomputable instance : CStarAlgebra opAlgebra := instCStarAlgebra opRho opRho_compat

/-- A one-stage instance of `RegionalConcreteCompletionData`, showing that all
its fields can be met simultaneously. -/
noncomputable def opConcreteCompletion : RegionalConcreteCompletionData where
  limitData := opLimitData
  H := ℂ
  rho := opRho
  rho_compat := opRho_compat
  TargetCStar := opAlgebra
  targetCStar := instCStarAlgebra opRho opRho_compat
  targetEmbed := quasilocalEmbedding opRho opRho_compat
  targetEmbed_dense := denseRange_quasilocalEmbedding opRho opRho_compat
  alphaCStar := StarAlgEquiv.refl
  alphaCStar_stage := fun _ _ => rfl

/-- The spectral order on the concrete one-stage algebra. -/
noncomputable instance opOrder : PartialOrder opAlgebra :=
  CStarAlgebra.spectralOrder _

/-- The spectral order makes the concrete one-stage algebra a star-ordered
ring. -/
noncomputable instance opStarOrdered : StarOrderedRing opAlgebra :=
  CStarAlgebra.spectralOrderedRing _

/-- The vector state at `1 ∈ ℂ`, as a linear functional on the concrete
one-stage algebra. -/
noncomputable def opEval : opAlgebra →ₗ[ℂ] ℂ where
  toFun T := (T : ℂ →L[ℂ] ℂ) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem opEval_apply (T : opAlgebra) : opEval T = (T : ℂ →L[ℂ] ℂ) 1 := rfl

theorem opEval_nonneg_of_star_mul_self (y : opAlgebra) : 0 ≤ opEval (star y * y) := by
  have hone : ∀ z : ℂ, ⟪(1 : ℂ), z⟫_ℂ = z := fun z => by simp
  have hstar : opEval (star y * y) =
      ContinuousLinearMap.adjoint (y : ℂ →L[ℂ] ℂ) ((y : ℂ →L[ℂ] ℂ) 1) := by
    simp [opEval_apply, ContinuousLinearMap.star_eq_adjoint]
  rw [hstar, ← hone (ContinuousLinearMap.adjoint (y : ℂ →L[ℂ] ℂ) ((y : ℂ →L[ℂ] ℂ) 1)),
    ContinuousLinearMap.adjoint_inner_right]
  exact CStarModule.inner_self_nonneg

theorem opEval_monotone : @Monotone opAlgebra ℂ opOrder.toPreorder _ opEval.toFun := by
  letI := opOrder
  letI := opStarOrdered
  intro a b hab
  rw [StarOrderedRing.le_iff] at hab
  obtain ⟨s, hs, rfl⟩ := hab
  have hs0 : 0 ≤ opEval s := by
    induction hs using AddSubmonoid.closure_induction with
    | mem u hu =>
      obtain ⟨y, rfl⟩ := hu
      exact opEval_nonneg_of_star_mul_self y
    | zero => simp
    | add u v _ _ hu hv => simpa [map_add] using add_nonneg hu hv
  have hadd : opEval (a + s) = opEval a + opEval s := map_add _ _ _
  simpa [hadd] using hs0

/-- The vector state at `1 ∈ ℂ`, as a positive linear functional. -/
noncomputable def opState : opAlgebra →ₚ[ℂ] ℂ :=
  @PositiveLinearMap.mk ℂ opAlgebra ℂ _ _ opOrder _ _ _ _ opEval opEval_monotone

theorem opState_one : opState 1 = 1 := by
  change ((1 : opAlgebra) : ℂ →L[ℂ] ℂ) 1 = 1
  simp

theorem opState_continuous : Continuous opState.toLinearMap := by
  have h : (opState.toLinearMap : opAlgebra → ℂ) =
      fun T : opAlgebra => (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) (T : ℂ →L[ℂ] ℂ) := rfl
  rw [h]
  exact (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp continuous_subtype_val

/-- A one-stage instance of `StatePreservingData`, showing that all fields —
the concrete completion, the supplied regional completion, the
state-preserving extension of `alpha`, the order structures and the two
states — can be met simultaneously. -/
noncomputable def opStatePreserving : StatePreservingData where
  completion := opConcreteCompletion
  sourceOrder := opOrder
  targetOrder := opOrder
  sourceStarOrdered := opStarOrdered
  targetStarOrdered := opStarOrdered
  sourceState := opState
  targetState := opState
  sourceState_one := opState_one
  targetState_one := opState_one
  targetState_continuous := opState_continuous
  state_compat := fun _ => rfl

end NonVacuity

end StatePreservingGNSModel

end AristotleCandidates
