import Formalization.TraceTransport
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Norm-continuity of algebraic star equivalences between C-star models

The algebraic coordinate equivalences developed in this project do not by
themselves construct C-star norms on the direct limits.  This module records
the analytic bridge available once such source and target C-star models have
been supplied: a complex star-algebra equivalence is automatically isometric,
hence a continuous linear equivalence in both directions.
-/

namespace StabilizerHyperfinite

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A complex star-algebra equivalence between C-star algebras is isometric. -/
theorem cstar_starAlgEquiv_isometry (e : A ≃⋆ₐ[ℂ] B) : Isometry e :=
  StarAlgEquiv.isometry e

/-- Package a C-star algebraic star equivalence as a continuous complex linear
equivalence.  This does not construct a normed completion; it proves that a
supplied C-star realization of the coordinate map is norm-continuous. -/
noncomputable def cstarStarAlgEquivToContinuousLinearEquiv
    (e : A ≃⋆ₐ[ℂ] B) : A ≃L[ℂ] B where
  toLinearEquiv :=
    { e.toEquiv with
      map_add' := e.map_add
      map_smul' := e.map_smul' }
  continuous_toFun := (cstar_starAlgEquiv_isometry e).continuous
  continuous_invFun := (cstar_starAlgEquiv_isometry e.symm).continuous

/-- The continuous packaging has the original coordinate equivalence as its
underlying map. -/
theorem cstarStarAlgEquivToContinuousLinearEquiv_apply
    (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    cstarStarAlgEquivToContinuousLinearEquiv e a = e a :=
  rfl

/-- A continuous target functional remains continuous after pullback along a
C-star coordinate equivalence.  Combined with `TraceTransport`, this gives
the norm-continuous part of the induced-trace argument whenever the target
trace has been constructed as a continuous functional. -/
theorem continuous_pullback_of_cstarStarAlgEquiv
    (e : A ≃⋆ₐ[ℂ] B) (tau : B →ₗ[ℂ] ℂ) (h_tau : Continuous tau) :
    Continuous (pullback e tau) := by
  change Continuous fun a => tau (e a)
  exact h_tau.comp (cstar_starAlgEquiv_isometry e).continuous

end StabilizerHyperfinite
