import Formalization.DyadicTensorTower

/-!
# A finite type-I factor times the algebraic qubit product

This is the fully concrete algebraic product model relevant when the pure
sector is finite dimensional.  It deliberately stops before completing the
qubit product to the hyperfinite type-II1 factor.
-/

namespace StabilizerHyperfinite

open scoped TensorProduct

variable (p : Type*) [Fintype p] [DecidableEq p]

/-- The product trace on a finite complex matrix factor tensored with the
concrete algebraic infinite qubit product. -/
noncomputable def finitePureQubitUHFTrace :
    (Matrix p p ℂ ⊗[ℂ] QubitUHFAlgebra) →ₗ[ℂ] ℂ :=
  finiteTypeITensorTrace p qubitUHFTrace

/-- The finite pure-factor times algebraic qubit-product model carries its
normalized algebraic tracial state. -/
theorem finitePureQubitUHFTrace_isAlgebraicTracialState [Nonempty p] :
    IsAlgebraicTracialState (finitePureQubitUHFTrace p) :=
  finiteTypeITensorTrace_isAlgebraicTracialState p qubitUHFTrace
    qubitUHFTrace_isAlgebraicTracialState

/-- On elementary tensors, the product trace is the finite normalized matrix
trace times the algebraic infinite-qubit trace. -/
theorem finitePureQubitUHFTrace_tmul (a : Matrix p p ℂ) (u : QubitUHFAlgebra) :
    finitePureQubitUHFTrace p (a ⊗ₜ[ℂ] u) =
      normalizedMatrixTrace p a * qubitUHFTrace u :=
  finiteTypeITensorTrace_tmul p qubitUHFTrace
    qubitUHFTrace_isAlgebraicTracialState.cyclic a u

/-- On an elementary tensor whose qubit factor is represented at a finite
stage, the product trace is already the corresponding finite-stage product
trace. -/
theorem finitePureQubitUHFTrace_tmul_of
    (a : Matrix p p ℂ) (n : ℕ) (x : QubitTensorPower n) :
    finitePureQubitUHFTrace p
      (a ⊗ₜ[ℂ] DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap n x) =
        normalizedMatrixTrace p a * qubitTensorTrace n x := by
  rw [finitePureQubitUHFTrace_tmul, qubitUHFTrace_of]

end StabilizerHyperfinite
