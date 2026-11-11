import Formalization.TensorMatrixEquiv

/-!
# The zero-vector state of a matrix-amplified algebra

For the finite pure/mixed Pauli product state, a pure coordinate is evaluated
in the vector state of the first standard basis vector.  This module proves
the algebraic positivity and normalization of that construction over an
arbitrary coefficient algebraic state.
-/

namespace StabilizerHyperfinite

open Matrix

variable {R : Type*} [Semiring R] [Algebra ℂ R]

section MatrixTensor

variable [StarRing R] [StarModule ℂ R]

/-- The matrix-tensor equivalence evaluates an elementary tensor by multiplying
the coefficient on the left by the scalar matrix entry on the right. -/
theorem matrixTensorStarAlgEquiv_tmul_apply
    (a : Matrix (Fin 2) (Fin 2) ℂ) (x : R) (i j : Fin 2) :
    matrixTensorStarAlgEquiv (Fin 2) (a ⊗ₜ[ℂ] x) i j =
      x * algebraMap ℂ R (a i j) := by
  change (matrixEquivTensor (Fin 2) ℂ R).symm (x ⊗ₜ[ℂ] a) i j = _
  rw [matrixEquivTensor_apply_symm]
  change x * algebraMap ℂ R (a i j) = _
  rfl

end MatrixTensor

/-- Apply a functional to the upper-left coefficient of a qubit matrix.
This is the vector state corresponding to the standard ket `|0⟩`. -/
noncomputable def qubitKetZeroStateOver (tau : R →ₗ[ℂ] ℂ) :
    Matrix (Fin 2) (Fin 2) R →ₗ[ℂ] ℂ where
  toFun a := tau (a 0 0)
  map_add' a b := by
    simp
  map_smul' c a := by
    simp

section MatrixTensor

variable [StarRing R] [StarModule ℂ R]

/-- The zero-vector state factors on an elementary matrix tensor. -/
theorem qubitKetZeroStateOver_matrixTensor_tmul (tau : R →ₗ[ℂ] ℂ)
    (a : Matrix (Fin 2) (Fin 2) ℂ) (x : R) :
    qubitKetZeroStateOver tau (matrixTensorStarAlgEquiv (Fin 2) (a ⊗ₜ[ℂ] x)) =
      a 0 0 * tau x := by
  change tau (matrixTensorStarAlgEquiv (Fin 2) (a ⊗ₜ[ℂ] x) 0 0) = _
  rw [matrixTensorStarAlgEquiv_tmul_apply]
  calc
    tau (x * algebraMap ℂ R (a 0 0)) = tau (algebraMap ℂ R (a 0 0) * x) := by
      rw [Algebra.commutes]
    _ = tau ((a 0 0) • x) := by
      rw [Algebra.smul_def]
    _ = a 0 0 * tau x := by
      simp

/-- The normalized qubit trace over a coefficient functional factors on an
elementary matrix tensor. -/
theorem normalizedQubitMatrixTraceOver_matrixTensor_tmul (tau : R →ₗ[ℂ] ℂ)
    (a : Matrix (Fin 2) (Fin 2) ℂ) (x : R) :
    normalizedMatrixTraceOver (Fin 2) tau
  (matrixTensorStarAlgEquiv (Fin 2) (a ⊗ₜ[ℂ] x)) =
        normalizedMatrixTrace (Fin 2) a * tau x := by
  rw [normalizedMatrixTraceOver_apply]
  simp_rw [matrixTensorStarAlgEquiv_tmul_apply]
  have hterm : ∀ c : ℂ, tau (x * algebraMap ℂ R c) = c * tau x := by
    intro c
    calc
      tau (x * algebraMap ℂ R c) = tau (algebraMap ℂ R c * x) := by
        rw [Algebra.commutes]
      _ = tau (c • x) := by
        rw [Algebra.smul_def]
      _ = c * tau x := by
        simp
  simp_rw [hterm]
  rw [← Finset.sum_mul, normalizedMatrixTrace_apply]
  rw [Matrix.trace]
  change (1 / (Fintype.card (Fin 2) : ℂ)) *
      ((∑ i : Fin 2, a i i) * tau x) =
    ((1 / (Fintype.card (Fin 2) : ℂ)) * ∑ i : Fin 2, a.diag i) * tau x
  simp only [Matrix.diag]
  ring

end MatrixTensor

/-- The zero-vector state sends the unit matrix to the coefficient state's
normalization. -/
theorem qubitKetZeroStateOver_one (tau : R →ₗ[ℂ] ℂ) (h_tau_one : tau 1 = 1) :
    qubitKetZeroStateOver tau 1 = 1 := by
  change tau ((1 : Matrix (Fin 2) (Fin 2) R) 0 0) = 1
  simpa using h_tau_one

section Positivity

variable [StarRing R]

/-- Algebraic positivity of the zero-vector state is inherited from the
coefficient state's positivity. -/
theorem qubitKetZeroStateOver_positive (tau : R →ₗ[ℂ] ℂ)
    (h_tau : IsPositiveFunctional tau) :
    IsPositiveFunctional (qubitKetZeroStateOver tau) := by
  intro a
  classical
  let q : Fin 2 → ℝ := fun j => Classical.choose (h_tau (a j 0))
  have hq_nonneg : ∀ j, 0 ≤ q j := fun j =>
    (Classical.choose_spec (h_tau (a j 0))).1
  have hq_value : ∀ j, tau (star (a j 0) * a j 0) = (q j : ℂ) := fun j =>
    (Classical.choose_spec (h_tau (a j 0))).2
  let r : ℝ := ∑ j : Fin 2, q j
  refine ⟨r, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => hq_nonneg j
  · change tau ((star a * a) 0 0) = (r : ℂ)
    rw [Matrix.mul_apply]
    simp only [Matrix.star_apply, map_sum]
    simp_rw [hq_value]
    simp [r]

/-- A pure qubit coordinate over an algebraic state is again an algebraic
state. -/
theorem qubitKetZeroStateOver_isAlgebraicState (tau : R →ₗ[ℂ] ℂ)
    (h_tau : IsAlgebraicState tau) :
    IsAlgebraicState (qubitKetZeroStateOver tau) := by
  refine ⟨?_, ?_⟩
  · exact qubitKetZeroStateOver_one tau h_tau.map_one
  · exact qubitKetZeroStateOver_positive tau h_tau.positive

end Positivity

/-- A pure qubit coordinate evaluates an identity-qubit embedding by the
coefficient functional. -/
theorem qubitKetZeroStateOver_scalar (tau : R →ₗ[ℂ] ℂ) (x : R) :
    qubitKetZeroStateOver tau (Matrix.scalar (Fin 2) x) = tau x := by
  change tau (Matrix.scalar (Fin 2) x 0 0) = tau x
  simp [Matrix.scalar_apply]

/-- The normalized qubit trace also evaluates an identity-qubit embedding by
the coefficient functional. -/
theorem normalizedQubitMatrixTraceOver_scalar (tau : R →ₗ[ℂ] ℂ) (x : R) :
    normalizedMatrixTraceOver (Fin 2) tau (Matrix.scalar (Fin 2) x) = tau x := by
  simp [normalizedMatrixTraceOver_apply, Matrix.scalar_apply]

section Positivity

variable [StarRing R]

/-- A maximally mixed qubit coordinate over an algebraic state is again an
algebraic state. -/
theorem normalizedQubitMatrixTraceOver_isAlgebraicState (tau : R →ₗ[ℂ] ℂ)
    (h_tau : IsAlgebraicState tau) :
    IsAlgebraicState (normalizedMatrixTraceOver (Fin 2) tau) := by
  refine ⟨?_, ?_⟩
  · exact normalizedMatrixTraceOver_one (Fin 2) tau h_tau.map_one
  · exact normalizedMatrixTraceOver_positive (Fin 2) tau h_tau.positive

end Positivity

end StabilizerHyperfinite
