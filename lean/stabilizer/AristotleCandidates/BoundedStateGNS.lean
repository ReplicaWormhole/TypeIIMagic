import Formalization.CStarEquivExtension
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Bounded-state GNS representations for a supplied C⋆ model

This module records the bounded-state Gelfand–Naimark–Segal (GNS) entry point
for a *supplied* pair of unital complex C⋆ algebras together with a supplied
star-algebra equivalence and supplied positive unital functionals (states) on
both sides which are compatible along the equivalence.

Everything analytic is taken from Mathlib's
`Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`: the GNS Hilbert spaces are
`PositiveLinearMap.GNS` and the representations are
`PositiveLinearMap.gnsStarAlgHom`.  No new GNS construction is performed here.

This package deliberately constructs **no** product state, **no** intertwining
unitary between the two GNS spaces, **no** bicommutant, von Neumann algebra,
trace or weight, and **no** normality, faithfulness, semifiniteness,
hyperfiniteness or factor classification.  Those belong strictly later.
-/

namespace StabilizerHyperfinite

namespace BoundedStateGNS

open scoped ComplexOrder

/-- Transparent supplied data for the bounded-state GNS step: two unital complex
C⋆ algebras with the partial order and star-ordered-ring structure required by
Mathlib's positive-functional/GNS API, a supplied star-algebra equivalence
between them, supplied positive linear functionals on both sides, their unit
normalizations, and the compatibility of the two functionals along the
equivalence. -/
structure Data where
  /-- The source C⋆ algebra. -/
  source : Type*
  /-- The target C⋆ algebra. -/
  target : Type*
  /-- Supplied unital C⋆ structure on the source. -/
  [sourceCStar : CStarAlgebra source]
  /-- Supplied unital C⋆ structure on the target. -/
  [targetCStar : CStarAlgebra target]
  /-- Supplied partial order on the source, as required by the GNS API. -/
  [sourceOrder : PartialOrder source]
  /-- Supplied partial order on the target, as required by the GNS API. -/
  [targetOrder : PartialOrder target]
  /-- The source order is a star-ordered ring structure. -/
  [sourceStarOrdered : StarOrderedRing source]
  /-- The target order is a star-ordered ring structure. -/
  [targetStarOrdered : StarOrderedRing target]
  /-- The supplied star-algebra equivalence. -/
  equivalence : source ≃⋆ₐ[ℂ] target
  /-- The supplied positive functional on the source. -/
  sourceState : source →ₚ[ℂ] ℂ
  /-- The supplied positive functional on the target. -/
  targetState : target →ₚ[ℂ] ℂ
  /-- The source functional is unital. -/
  sourceState_one : sourceState 1 = 1
  /-- The target functional is unital. -/
  targetState_one : targetState 1 = 1
  /-- The two supplied functionals agree along the supplied equivalence. -/
  state_compat : ∀ a : source, sourceState a = targetState (equivalence a)

attribute [instance] Data.sourceCStar Data.targetCStar Data.sourceOrder
  Data.targetOrder Data.sourceStarOrdered Data.targetStarOrdered

variable (D : Data)

/-! ### The supplied C⋆ isometry, reused -/

/-- The supplied equivalence is isometric (reusing the supplied C⋆ isometry
theorem). -/
theorem isometry_equivalence : Isometry D.equivalence :=
  cstar_starAlgEquiv_isometry D.equivalence

/-- The supplied equivalence is norm-continuous. -/
theorem continuous_equivalence : Continuous D.equivalence :=
  (isometry_equivalence D).continuous

/-- The inverse of the supplied equivalence is isometric. -/
theorem isometry_equivalence_symm : Isometry D.equivalence.symm :=
  cstar_starAlgEquiv_isometry D.equivalence.symm

/-- The inverse of the supplied equivalence is norm-continuous. -/
theorem continuous_equivalence_symm : Continuous D.equivalence.symm :=
  (isometry_equivalence_symm D).continuous

/-! ### The actual Mathlib GNS objects -/

/-- The GNS Hilbert space of the supplied source state, i.e. Mathlib's
`PositiveLinearMap.GNS`. -/
abbrev sourceGNS : Type _ := D.sourceState.GNS

/-- The GNS Hilbert space of the supplied target state, i.e. Mathlib's
`PositiveLinearMap.GNS`. -/
abbrev targetGNS : Type _ := D.targetState.GNS

/-- The GNS representation of the source algebra on `sourceGNS`, i.e. Mathlib's
`PositiveLinearMap.gnsStarAlgHom`. -/
noncomputable def sourceGNSRepresentation :
    D.source →⋆ₐ[ℂ] (sourceGNS D →L[ℂ] sourceGNS D) :=
  D.sourceState.gnsStarAlgHom

/-- The GNS representation of the target algebra on `targetGNS`, i.e. Mathlib's
`PositiveLinearMap.gnsStarAlgHom`. -/
noncomputable def targetGNSRepresentation :
    D.target →⋆ₐ[ℂ] (targetGNS D →L[ℂ] targetGNS D) :=
  D.targetState.gnsStarAlgHom

/-! ### Routine interface facts -/

@[simp]
theorem sourceGNSRepresentation_apply (a : D.source) :
    sourceGNSRepresentation D a = D.sourceState.gnsStarAlgHom a := rfl

@[simp]
theorem targetGNSRepresentation_apply (b : D.target) :
    targetGNSRepresentation D b = D.targetState.gnsStarAlgHom b := rfl

/-- The source GNS representation is unital. -/
@[simp]
theorem sourceGNSRepresentation_one : sourceGNSRepresentation D 1 = 1 :=
  map_one _

/-- The target GNS representation is unital. -/
@[simp]
theorem targetGNSRepresentation_one : targetGNSRepresentation D 1 = 1 :=
  map_one _

/-- The source GNS representation is multiplicative. -/
theorem sourceGNSRepresentation_mul (a b : D.source) :
    sourceGNSRepresentation D (a * b) =
      sourceGNSRepresentation D a * sourceGNSRepresentation D b :=
  map_mul _ _ _

/-- The target GNS representation is multiplicative. -/
theorem targetGNSRepresentation_mul (a b : D.target) :
    targetGNSRepresentation D (a * b) =
      targetGNSRepresentation D a * targetGNSRepresentation D b :=
  map_mul _ _ _

/-- The source GNS representation is additive. -/
theorem sourceGNSRepresentation_add (a b : D.source) :
    sourceGNSRepresentation D (a + b) =
      sourceGNSRepresentation D a + sourceGNSRepresentation D b :=
  map_add _ _ _

/-- The target GNS representation is additive. -/
theorem targetGNSRepresentation_add (a b : D.target) :
    targetGNSRepresentation D (a + b) =
      targetGNSRepresentation D a + targetGNSRepresentation D b :=
  map_add _ _ _

/-- The source GNS representation is ℂ-linear. -/
theorem sourceGNSRepresentation_smul (r : ℂ) (a : D.source) :
    sourceGNSRepresentation D (r • a) = r • sourceGNSRepresentation D a :=
  map_smul _ _ _

/-- The target GNS representation is ℂ-linear. -/
theorem targetGNSRepresentation_smul (r : ℂ) (b : D.target) :
    targetGNSRepresentation D (r • b) = r • targetGNSRepresentation D b :=
  map_smul _ _ _

/-- The source GNS representation is star-preserving. -/
theorem sourceGNSRepresentation_star (a : D.source) :
    sourceGNSRepresentation D (star a) = star (sourceGNSRepresentation D a) :=
  map_star _ _

/-- The target GNS representation is star-preserving. -/
theorem targetGNSRepresentation_star (b : D.target) :
    targetGNSRepresentation D (star b) = star (targetGNSRepresentation D b) :=
  map_star _ _

/-! ### The supplied state data, recorded in the interface -/

/-- The supplied source functional is a state: it is unital. -/
@[simp]
theorem sourceState_one : D.sourceState 1 = 1 := D.sourceState_one

/-- The supplied target functional is a state: it is unital. -/
@[simp]
theorem targetState_one : D.targetState 1 = 1 := D.targetState_one

/-- The supplied source functional is positive on positive elements. -/
theorem sourceState_nonneg {a : D.source} (ha : 0 ≤ a) : 0 ≤ D.sourceState a :=
  D.sourceState.map_nonneg ha

/-- The supplied target functional is positive on positive elements. -/
theorem targetState_nonneg {b : D.target} (hb : 0 ≤ b) : 0 ≤ D.targetState b :=
  D.targetState.map_nonneg hb

/-- The supplied state compatibility, recorded in the interface. -/
theorem state_compat (a : D.source) :
    D.sourceState a = D.targetState (D.equivalence a) :=
  D.state_compat a

/-- The supplied state compatibility, read along the inverse equivalence. -/
theorem state_compat_symm (b : D.target) :
    D.targetState b = D.sourceState (D.equivalence.symm b) := by
  rw [state_compat D (D.equivalence.symm b), StarAlgEquiv.apply_symm_apply]

/-- The compatibility equation, stated as an equality of functions: the target
state pulled back along the supplied equivalence is the source state. -/
theorem sourceState_eq_comp_equivalence :
    (D.sourceState : D.source → ℂ) = (D.targetState : D.target → ℂ) ∘ D.equivalence :=
  funext fun a => state_compat D a

/-- Compatibility is consistent with the unit normalizations. -/
theorem targetState_equivalence_one : D.targetState (D.equivalence 1) = 1 := by
  rw [← state_compat D 1, sourceState_one]

/-- The bounded-state GNS interface package: both GNS representations are unital
star-algebra homomorphisms into the bounded operators on the respective
completed GNS Hilbert spaces, the supplied equivalence is isometric, and the
supplied states are compatible along it. -/
theorem boundedStateGNS_package :
    Isometry D.equivalence ∧
      sourceGNSRepresentation D 1 = 1 ∧
      targetGNSRepresentation D 1 = 1 ∧
      (∀ a b : D.source, sourceGNSRepresentation D (a * b) =
        sourceGNSRepresentation D a * sourceGNSRepresentation D b) ∧
      (∀ a b : D.target, targetGNSRepresentation D (a * b) =
        targetGNSRepresentation D a * targetGNSRepresentation D b) ∧
      (∀ a : D.source, D.sourceState a = D.targetState (D.equivalence a)) :=
  ⟨isometry_equivalence D, sourceGNSRepresentation_one D,
    targetGNSRepresentation_one D, sourceGNSRepresentation_mul D,
    targetGNSRepresentation_mul D, state_compat D⟩

end BoundedStateGNS

end StabilizerHyperfinite
