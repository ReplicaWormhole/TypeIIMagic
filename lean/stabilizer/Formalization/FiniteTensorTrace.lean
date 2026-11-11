import Formalization.FiniteMatrixTrace
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Normalized trace on a finite tensor product of matrix factors

The finite pure/mixed-coordinate model is represented by the algebraic tensor
product of two full matrix algebras.  Mathlib's Kronecker star-algebra
equivalence identifies it with the full matrix algebra on the product index.
-/

namespace StabilizerHyperfinite

open scoped TensorProduct Kronecker

variable (p r : Type*)
  [Fintype p] [DecidableEq p]
  [Fintype r] [DecidableEq r]

/-- The product normalized trace on two finite matrix factors. -/
noncomputable def finiteTensorTrace :
    (Matrix p p ℂ ⊗[ℂ] Matrix r r ℂ) →ₗ[ℂ] ℂ :=
  pullback (Matrix.kroneckerStarAlgEquiv p r ℂ)
    (normalizedMatrixTrace (p × r))

/-- The finite tensor-product trace is an algebraic tracial state. -/
theorem finiteTensorTrace_isAlgebraicTracialState [Nonempty p] [Nonempty r] :
    IsAlgebraicTracialState (finiteTensorTrace p r) :=
  isAlgebraicTracialState_pullback (Matrix.kroneckerStarAlgEquiv p r ℂ)
    (normalizedMatrixTrace (p × r))
    (normalizedMatrixTrace_isAlgebraicTracialState (p × r))

/-- On elementary tensors, the finite product trace is the product of the
normalized traces of the two factors. -/
theorem finiteTensorTrace_tmul (a : Matrix p p ℂ) (b : Matrix r r ℂ) :
    finiteTensorTrace p r (a ⊗ₜ[ℂ] b) =
      normalizedMatrixTrace p a * normalizedMatrixTrace r b := by
  change normalizedMatrixTrace (p × r)
      (Matrix.kroneckerStarAlgEquiv p r ℂ (a ⊗ₜ[ℂ] b)) = _
  rw [Matrix.kroneckerStarAlgEquiv_apply]
  change (1 / (Fintype.card (p × r) : ℂ)) * Matrix.trace (a ⊗ₖ b) = _
  rw [Matrix.trace_kronecker]
  simp only [normalizedMatrixTrace_apply, Fintype.card_prod, Nat.cast_mul, one_div]
  ring

/-- Appending a finite matrix factor by tensoring with its unit preserves the
normalized trace.  This is the finite-layer compatibility needed before any
inductive-limit construction. -/
theorem finiteTensorTrace_append_right [Nonempty r] (a : Matrix p p ℂ) :
    finiteTensorTrace p r (a ⊗ₜ[ℂ] (1 : Matrix r r ℂ)) =
      normalizedMatrixTrace p a := by
  rw [finiteTensorTrace_tmul, normalizedMatrixTrace_one, mul_one]

/-- The analogous compatibility holds when a factor is adjoined on the left. -/
theorem finiteTensorTrace_append_left [Nonempty p] (b : Matrix r r ℂ) :
    finiteTensorTrace p r ((1 : Matrix p p ℂ) ⊗ₜ[ℂ] b) =
      normalizedMatrixTrace r b := by
  rw [finiteTensorTrace_tmul, normalizedMatrixTrace_one, one_mul]

end StabilizerHyperfinite
