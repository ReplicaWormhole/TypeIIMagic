import Formalization.CStarEquivExtension

/-!
# Conditional supplied C⋆ model transport

This interface bundles supplied C⋆ algebras, an equivalence, and a continuous
target functional.  It constructs neither norms, completions, tensor products,
normality, GNS representations, nor von Neumann factor data.
-/

namespace StabilizerHyperfinite

namespace SuppliedCStarModel

structure Data where
  source : Type*
  target : Type*
  sourceCStar : CStarAlgebra source
  targetCStar : CStarAlgebra target
  equivalence : source ≃⋆ₐ[ℂ] target
  targetFunctional : target →ₗ[ℂ] ℂ
  targetFunctional_continuous : Continuous targetFunctional

attribute [instance] Data.sourceCStar Data.targetCStar

variable (D : Data)

theorem isometry_equivalence : Isometry D.equivalence :=
  cstar_starAlgEquiv_isometry D.equivalence

theorem isometry_equivalence_symm : Isometry D.equivalence.symm :=
  cstar_starAlgEquiv_isometry D.equivalence.symm

theorem continuous_equivalence : Continuous D.equivalence :=
  (isometry_equivalence D).continuous

theorem continuous_equivalence_symm : Continuous D.equivalence.symm :=
  (isometry_equivalence_symm D).continuous

noncomputable def continuousLinearEquiv : D.source ≃L[ℂ] D.target :=
  cstarStarAlgEquivToContinuousLinearEquiv D.equivalence

@[simp]
theorem continuousLinearEquiv_apply (a : D.source) :
    continuousLinearEquiv D a = D.equivalence a :=
  rfl

noncomputable def inducedFunctional : D.source →ₗ[ℂ] ℂ :=
  pullback D.equivalence D.targetFunctional

@[simp]
theorem inducedFunctional_apply (a : D.source) :
    inducedFunctional D a = D.targetFunctional (D.equivalence a) :=
  rfl

theorem continuous_inducedFunctional : Continuous (inducedFunctional D) :=
  continuous_pullback_of_cstarStarAlgEquiv D.equivalence D.targetFunctional
    D.targetFunctional_continuous

theorem inducedFunctional_pullback_symm :
    pullback D.equivalence.symm (inducedFunctional D) = D.targetFunctional :=
  pullback_symm_pullback D.equivalence D.targetFunctional

theorem isAlgebraicTracialState_inducedFunctional
    (h : IsAlgebraicTracialState D.targetFunctional) :
    IsAlgebraicTracialState (inducedFunctional D) :=
  isAlgebraicTracialState_pullback D.equivalence D.targetFunctional h

theorem isAlgebraicTracialState_inducedFunctional_iff :
    IsAlgebraicTracialState (inducedFunctional D) ↔
      IsAlgebraicTracialState D.targetFunctional :=
  isAlgebraicTracialState_pullback_iff D.equivalence D.targetFunctional

theorem transport_package (h : IsAlgebraicTracialState D.targetFunctional) :
    Isometry D.equivalence ∧ Isometry D.equivalence.symm ∧
      Continuous (inducedFunctional D) ∧
      IsAlgebraicTracialState (inducedFunctional D) :=
  ⟨isometry_equivalence D, isometry_equivalence_symm D,
    continuous_inducedFunctional D, isAlgebraicTracialState_inducedFunctional D h⟩

end SuppliedCStarModel

end StabilizerHyperfinite
