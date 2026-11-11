import Formalization.FinitePureUHFProduct

/-!
# Transporting the finite-pure product trace to a region algebra

This is the algebraic theorem corresponding to the trace part of the proposed
factorization.  It does not assume the regional star isomorphism: when one is
separately constructed, the concrete finite-pure times qubit-product trace
pulls back along it.
-/

namespace StabilizerHyperfinite

open scoped TensorProduct

variable {A p : Type*}
variable [Semiring A] [StarRing A] [Algebra ℂ A]
variable [Fintype p] [DecidableEq p]

/-- The algebraic tracial state induced on a region algebra by a supplied
star-algebra equivalence to a finite pure matrix factor tensored with the
algebraic qubit product. -/
noncomputable def finitePureQubitUHFInducedTrace
    (e : A ≃⋆ₐ[ℂ] (Matrix p p ℂ ⊗[ℂ] QubitUHFAlgebra)) : A →ₗ[ℂ] ℂ :=
  pullback e (finitePureQubitUHFTrace p)

section State

variable [Nonempty p]

/-- The finite-pure product trace pulls back to an algebraic tracial state. -/
theorem finitePureQubitUHFInducedTrace_isAlgebraicTracialState
    (e : A ≃⋆ₐ[ℂ] (Matrix p p ℂ ⊗[ℂ] QubitUHFAlgebra)) :
    IsAlgebraicTracialState (finitePureQubitUHFInducedTrace e) := by
  exact isAlgebraicTracialState_pullback e (finitePureQubitUHFTrace p)
    (finitePureQubitUHFTrace_isAlgebraicTracialState p)

end State

/-- On a product-model elementary tensor, the induced regional trace is the
normalized pure-sector matrix trace times the compatible qubit-product trace. -/
theorem finitePureQubitUHFInducedTrace_symm_tmul
    (e : A ≃⋆ₐ[ℂ] (Matrix p p ℂ ⊗[ℂ] QubitUHFAlgebra))
    (a : Matrix p p ℂ) (u : QubitUHFAlgebra) :
    finitePureQubitUHFInducedTrace e (e.symm (a ⊗ₜ[ℂ] u)) =
      normalizedMatrixTrace p a * qubitUHFTrace u := by
  change finitePureQubitUHFTrace p (e (e.symm (a ⊗ₜ[ℂ] u))) = _
  rw [e.apply_symm_apply]
  exact finitePureQubitUHFTrace_tmul p a u

section State

variable [Nonempty p]

/-- Existence form of the induced-trace theorem.  The only nontrivial input
is the star-algebra equivalence itself; all state and elementary-tensor
properties are discharged in this project. -/
theorem exists_finitePureQubitUHFInducedTrace
    (e : A ≃⋆ₐ[ℂ] (Matrix p p ℂ ⊗[ℂ] QubitUHFAlgebra)) :
    ∃ tau : A →ₗ[ℂ] ℂ, IsAlgebraicTracialState tau ∧
      ∀ a u, tau (e.symm (a ⊗ₜ[ℂ] u)) =
        normalizedMatrixTrace p a * qubitUHFTrace u := by
  refine ⟨finitePureQubitUHFInducedTrace e,
    finitePureQubitUHFInducedTrace_isAlgebraicTracialState e, ?_⟩
  intro a u
  exact finitePureQubitUHFInducedTrace_symm_tmul e a u

end State

end StabilizerHyperfinite
