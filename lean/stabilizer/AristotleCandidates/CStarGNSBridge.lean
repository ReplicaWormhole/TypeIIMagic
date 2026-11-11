import AristotleCandidates.CStarTransport
import AristotleCandidates.BoundedStateGNS
import AristotleCandidates.GNSCommutantConjugation

/-!
# From a supplied C⋆ model to the GNS unitary and its conjugation equivalence

This module is the bridge between the two supplied interfaces already present in
the project:

* `StabilizerHyperfinite.SuppliedCStarModel.Data` (P3): two supplied unital
  complex C⋆ algebras, a supplied star-algebra equivalence between them, and a
  supplied continuous linear functional on the target; and
* `StabilizerHyperfinite.BoundedStateGNS.Data` (P13): the same two algebras with
  the order structure required by Mathlib's positive-functional/GNS API,
  supplied positive unital functionals on both sides, and their compatibility
  along the equivalence.

The bundled datum `CStarGNSBridge.Data` supplies a `SuppliedCStarModel.Data`
together with exactly the extra data that the bounded-state GNS interface
requires (order structures, positive unital functionals, compatibility, and the
identification of the supplied continuous target functional with the supplied
target state).  From it we produce

* `Data.gns : BoundedStateGNS.Data`, the induced bounded-state GNS datum;
* `Data.gnsUnitary`, the GNS unitary of P15 (a `ℂ`-linear isometric equivalence
  of the two GNS Hilbert spaces) and its intertwining identity; and
* `Data.gnsConjStarAlgEquiv`, the star-algebra equivalence of P16 obtained by
  conjugating bounded operators by that unitary, together with the transport of
  the representations, their ranges, commutation, commutants and bicommutants.

No GNS construction is re-proved here: everything is reused from P13–P16.

**Everything below is conditional on the supplied data.**  In particular this
module claims **no** spatial tensor product, **no** von Neumann bicommutant
theorem, **no** normality, quasi-equivalence, faithfulness, semifiniteness,
hyperfiniteness or factor classification, and **no** trace or weight theorem.
The commutants appearing here are the purely algebraic `Set.centralizer` ones
inherited from P16.
-/

namespace StabilizerHyperfinite

namespace CStarGNSBridge

open scoped ComplexOrder InnerProductSpace

/-! ### The bundled supplied data -/

/-- Supplied data bridging `SuppliedCStarModel.Data` and
`BoundedStateGNS.Data`: a supplied C⋆ model (two unital complex C⋆ algebras, a
supplied star-algebra equivalence, and a supplied continuous target functional),
the order structures required by the GNS API, supplied positive unital
functionals on both sides, their compatibility along the equivalence, and the
identification of the supplied continuous target functional with the supplied
target state. -/
structure Data where
  /-- The supplied C⋆ model of `AristotleCandidates.CStarTransport`. -/
  model : SuppliedCStarModel.Data
  /-- Supplied partial order on the source, as required by the GNS API. -/
  [sourceOrder : PartialOrder model.source]
  /-- Supplied partial order on the target, as required by the GNS API. -/
  [targetOrder : PartialOrder model.target]
  /-- The source order is a star-ordered ring structure. -/
  [sourceStarOrdered : StarOrderedRing model.source]
  /-- The target order is a star-ordered ring structure. -/
  [targetStarOrdered : StarOrderedRing model.target]
  /-- The supplied positive functional (state) on the source. -/
  sourceState : model.source →ₚ[ℂ] ℂ
  /-- The supplied positive functional (state) on the target. -/
  targetState : model.target →ₚ[ℂ] ℂ
  /-- The source functional is unital. -/
  sourceState_one : sourceState 1 = 1
  /-- The target functional is unital. -/
  targetState_one : targetState 1 = 1
  /-- The two supplied functionals agree along the supplied equivalence. -/
  state_compat : ∀ a : model.source, sourceState a = targetState (model.equivalence a)
  /-- The supplied continuous target functional of the C⋆ model is the supplied
  target state. -/
  targetFunctional_eq : ∀ b : model.target, model.targetFunctional b = targetState b

attribute [instance] Data.sourceOrder Data.targetOrder Data.sourceStarOrdered
  Data.targetStarOrdered

namespace Data

variable (B : Data)

/-- The source C⋆ algebra of the supplied model. -/
abbrev source : Type _ := B.model.source

/-- The target C⋆ algebra of the supplied model. -/
abbrev target : Type _ := B.model.target

/-- The supplied star-algebra equivalence of the model. -/
abbrev equivalence : B.source ≃⋆ₐ[ℂ] B.target := B.model.equivalence

/-! ### The induced bounded-state GNS datum -/

/-- The bounded-state GNS datum (P13) determined by the supplied bridge data. -/
def gns : BoundedStateGNS.Data where
  source := B.model.source
  target := B.model.target
  sourceCStar := B.model.sourceCStar
  targetCStar := B.model.targetCStar
  sourceOrder := B.sourceOrder
  targetOrder := B.targetOrder
  sourceStarOrdered := B.sourceStarOrdered
  targetStarOrdered := B.targetStarOrdered
  equivalence := B.model.equivalence
  sourceState := B.sourceState
  targetState := B.targetState
  sourceState_one := B.sourceState_one
  targetState_one := B.targetState_one
  state_compat := B.state_compat

@[simp] theorem gns_source : B.gns.source = B.source := rfl
@[simp] theorem gns_target : B.gns.target = B.target := rfl
@[simp] theorem gns_equivalence : B.gns.equivalence = B.model.equivalence := rfl
@[simp] theorem gns_sourceState : B.gns.sourceState = B.sourceState := rfl
@[simp] theorem gns_targetState : B.gns.targetState = B.targetState := rfl

/-! ### Consistency with the supplied C⋆ transport interface -/

/-- The supplied equivalence is isometric (from P3). -/
theorem isometry_equivalence : Isometry B.model.equivalence :=
  SuppliedCStarModel.isometry_equivalence B.model

/-- The supplied equivalence is isometric in the inverse direction. -/
theorem isometry_equivalence_symm : Isometry B.model.equivalence.symm :=
  SuppliedCStarModel.isometry_equivalence_symm B.model

/-- The functional induced on the source by transporting the supplied
continuous target functional along the equivalence is continuous (from P3). -/
theorem continuous_inducedFunctional :
    Continuous (SuppliedCStarModel.inducedFunctional B.model) :=
  SuppliedCStarModel.continuous_inducedFunctional B.model

/-- The transported target functional of the C⋆ model agrees with the supplied
source state: the two supplied interfaces are compatible. -/
theorem inducedFunctional_eq_sourceState (a : B.source) :
    SuppliedCStarModel.inducedFunctional B.model a = B.sourceState a := by
  rw [SuppliedCStarModel.inducedFunctional_apply, B.targetFunctional_eq,
    B.state_compat a]

/-- The supplied source state is continuous, being the transport of the supplied
continuous target functional. -/
theorem continuous_sourceState : Continuous fun a : B.source => B.sourceState a := by
  have h : (fun a : B.source => B.sourceState a) =
      fun a => SuppliedCStarModel.inducedFunctional B.model a :=
    funext fun a => (B.inducedFunctional_eq_sourceState a).symm
  rw [h]
  exact B.continuous_inducedFunctional

/-- The supplied target state is continuous, being the supplied continuous
target functional. -/
theorem continuous_targetState : Continuous fun b : B.target => B.targetState b := by
  have h : (fun b : B.target => B.targetState b) =
      fun b => B.model.targetFunctional b :=
    funext fun b => (B.targetFunctional_eq b).symm
  rw [h]
  exact B.model.targetFunctional_continuous

/-! ### The GNS Hilbert spaces, representations and unitary (reused from P13–P15) -/

/-- The GNS Hilbert space of the supplied source state. -/
abbrev sourceGNS : Type _ := BoundedStateGNS.sourceGNS B.gns

/-- The GNS Hilbert space of the supplied target state. -/
abbrev targetGNS : Type _ := BoundedStateGNS.targetGNS B.gns

/-- The GNS representation of the source algebra. -/
noncomputable abbrev sourceGNSRepresentation :
    B.source →⋆ₐ[ℂ] (B.sourceGNS →L[ℂ] B.sourceGNS) :=
  BoundedStateGNS.sourceGNSRepresentation B.gns

/-- The GNS representation of the target algebra. -/
noncomputable abbrev targetGNSRepresentation :
    B.target →⋆ₐ[ℂ] (B.targetGNS →L[ℂ] B.targetGNS) :=
  BoundedStateGNS.targetGNSRepresentation B.gns

/-- **The GNS unitary** (P15) attached to the supplied bridge data. -/
noncomputable def gnsUnitary : B.sourceGNS ≃ₗᵢ[ℂ] B.targetGNS :=
  BoundedStateGNS.gnsUnitary B.gns

/-- The GNS unitary preserves inner products. -/
theorem gnsUnitary_inner (x y : B.sourceGNS) :
    ⟪B.gnsUnitary x, B.gnsUnitary y⟫_ℂ = ⟪x, y⟫_ℂ :=
  BoundedStateGNS.gnsUnitary_inner B.gns x y

/-- The GNS unitary preserves norms. -/
theorem gnsUnitary_norm (x : B.sourceGNS) : ‖B.gnsUnitary x‖ = ‖x‖ :=
  BoundedStateGNS.gnsUnitary_norm B.gns x

/-- **The intertwining identity.**  The GNS unitary carries the source GNS
representation of `a` to the target GNS representation of `equivalence a`. -/
theorem gnsUnitary_intertwines (a : B.source) (x : B.sourceGNS) :
    B.gnsUnitary (B.sourceGNSRepresentation a x) =
      B.targetGNSRepresentation (B.model.equivalence a) (B.gnsUnitary x) :=
  BoundedStateGNS.gnsUnitary_intertwines B.gns a x

/-- The intertwining identity, read in the inverse direction. -/
theorem gnsUnitary_symm_intertwines (a : B.source) (y : B.targetGNS) :
    B.gnsUnitary.symm (B.targetGNSRepresentation (B.model.equivalence a) y) =
      B.sourceGNSRepresentation a (B.gnsUnitary.symm y) :=
  BoundedStateGNS.gnsUnitary_symm_intertwines B.gns a y

/-! ### The conjugation star-algebra equivalence (reused from P16) -/

/-- Conjugation of a bounded operator by the GNS unitary. -/
noncomputable def gnsConj (T : B.sourceGNS →L[ℂ] B.sourceGNS) :
    B.targetGNS →L[ℂ] B.targetGNS :=
  BoundedStateGNS.gnsConj B.gns T

/-- **The conjugation star-algebra equivalence** (P16): conjugation by the GNS
unitary is a `ℂ`-star-algebra equivalence of the bounded operators on the two
GNS Hilbert spaces. -/
noncomputable def gnsConjStarAlgEquiv :
    (B.sourceGNS →L[ℂ] B.sourceGNS) ≃⋆ₐ[ℂ] (B.targetGNS →L[ℂ] B.targetGNS) :=
  BoundedStateGNS.gnsConjStarAlgEquiv B.gns

@[simp]
theorem gnsConjStarAlgEquiv_apply (T : B.sourceGNS →L[ℂ] B.sourceGNS) :
    B.gnsConjStarAlgEquiv T = B.gnsConj T := rfl

/-- Conjugation carries the source GNS representative of `a` to the target GNS
representative of `equivalence a`. -/
theorem gnsConj_sourceGNSRepresentation (a : B.source) :
    B.gnsConj (B.sourceGNSRepresentation a) =
      B.targetGNSRepresentation (B.model.equivalence a) :=
  BoundedStateGNS.gnsConj_sourceGNSRepresentation B.gns a

/-- Conjugation carries the range of the source GNS representation onto the
range of the target GNS representation. -/
theorem gnsConj_range :
    B.gnsConj '' Set.range B.sourceGNSRepresentation = Set.range B.targetGNSRepresentation :=
  BoundedStateGNS.gnsConj_range B.gns

/-- Transport of commutation along the conjugation. -/
theorem gnsConj_commute_iff (T : B.sourceGNS →L[ℂ] B.sourceGNS) :
    (∀ a : B.source, Commute T (B.sourceGNSRepresentation a)) ↔
      ∀ b : B.target, Commute (B.gnsConj T) (B.targetGNSRepresentation b) :=
  BoundedStateGNS.gnsConj_commute_iff B.gns T

/-- Transport of the algebraic commutant along the conjugation. -/
theorem gnsConj_image_centralizer :
    B.gnsConj '' (Set.range B.sourceGNSRepresentation).centralizer =
      (Set.range B.targetGNSRepresentation).centralizer :=
  BoundedStateGNS.gnsConj_image_centralizer B.gns

/-- Transport of the algebraic bicommutant along the conjugation. -/
theorem gnsConj_image_centralizer_centralizer :
    B.gnsConj '' (Set.range B.sourceGNSRepresentation).centralizer.centralizer =
      (Set.range B.targetGNSRepresentation).centralizer.centralizer :=
  BoundedStateGNS.gnsConj_image_centralizer_centralizer B.gns

end Data

/-! ### The bridge theorem -/

/-- **The bridge theorem.**  Supplied unital complex C⋆ source and target
models, a supplied star-algebra equivalence between them, supplied positive
unital functionals compatible along it (with the supplied continuous target
functional of the C⋆ model), and the order data required by the GNS API yield:

* a `ℂ`-linear isometric equivalence (GNS unitary) `U` of the two GNS Hilbert
  spaces which intertwines the two GNS representations along the supplied
  equivalence; and
* a `ℂ`-star-algebra equivalence of the bounded operators on the two GNS Hilbert
  spaces, given by conjugation by `U`, which carries the source GNS
  representation onto the target GNS representation and transports commutation,
  commutants and bicommutants (in the algebraic `Set.centralizer` sense).

The statement is entirely conditional on the supplied data; no spatial tensor
product, von Neumann bicommutant theorem, normality, quasi-equivalence,
hyperfiniteness, factor type, trace or weight is claimed. -/
theorem bridge_package (B : Data) :
    Isometry B.model.equivalence ∧
      (∀ a : B.source, SuppliedCStarModel.inducedFunctional B.model a = B.sourceState a) ∧
      (∀ (a : B.source) (x : B.sourceGNS),
        B.gnsUnitary (B.sourceGNSRepresentation a x) =
          B.targetGNSRepresentation (B.model.equivalence a) (B.gnsUnitary x)) ∧
      (∀ x y : B.sourceGNS, ⟪B.gnsUnitary x, B.gnsUnitary y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      (∀ a : B.source, B.gnsConjStarAlgEquiv (B.sourceGNSRepresentation a) =
        B.targetGNSRepresentation (B.model.equivalence a)) ∧
      B.gnsConj '' Set.range B.sourceGNSRepresentation =
        Set.range B.targetGNSRepresentation ∧
      B.gnsConj '' (Set.range B.sourceGNSRepresentation).centralizer =
        (Set.range B.targetGNSRepresentation).centralizer ∧
      B.gnsConj '' (Set.range B.sourceGNSRepresentation).centralizer.centralizer =
        (Set.range B.targetGNSRepresentation).centralizer.centralizer :=
  ⟨B.isometry_equivalence, B.inducedFunctional_eq_sourceState, B.gnsUnitary_intertwines,
    B.gnsUnitary_inner, B.gnsConj_sourceGNSRepresentation, B.gnsConj_range,
    B.gnsConj_image_centralizer, B.gnsConj_image_centralizer_centralizer⟩

end CStarGNSBridge

end StabilizerHyperfinite
