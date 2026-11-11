import Formalization.FiniteMatrixTrace

/-!
# Trace on a finite full-matrix corner

This is the finite-stage trace used by the stabilizer support-corner argument:
whenever a corner has been identified with a nonzero finite matrix factor, its
normalized trace is transported back along that explicit star isomorphism.
-/

namespace StabilizerHyperfinite

variable {A n : Type*}
  [Semiring A] [StarRing A] [Algebra ℂ A]
  [Fintype n] [DecidableEq n] [Nonempty n]

/-- The normalized trace induced on a finite full-matrix corner. -/
noncomputable def finiteCornerTrace (e : A ≃⋆ₐ[ℂ] Matrix n n ℂ) : A →ₗ[ℂ] ℂ :=
  pullback e (normalizedMatrixTrace n)

/-- A finite full-matrix corner has a canonical unital tracial functional. -/
theorem finiteCornerTrace_isUnitalTracial (e : A ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    IsUnitalTracial (finiteCornerTrace e) :=
  isUnitalTracial_pullback e (normalizedMatrixTrace n)
    (normalizedMatrixTrace_isUnitalTracial n)

/-- The finite-corner trace is an algebraic tracial state. -/
theorem finiteCornerTrace_isAlgebraicTracialState (e : A ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    IsAlgebraicTracialState (finiteCornerTrace e) :=
  isAlgebraicTracialState_pullback e (normalizedMatrixTrace n)
    (normalizedMatrixTrace_isAlgebraicTracialState n)

end StabilizerHyperfinite
