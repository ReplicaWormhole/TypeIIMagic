import Formalization.FiniteMatrixTrace
import Formalization.MatrixOverTrace
import Mathlib.RingTheory.MatrixAlgebra

/-!
# The algebraic tensor product of a matrix factor with a tracial algebra

This module identifies `Matrix n n ℂ ⊗ R` with `Matrix n n R`.  It is the
algebraic finite type-I tensor product used by the trace construction.
-/

namespace StabilizerHyperfinite

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 3000000

variable {R : Type*} [Semiring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The canonical algebra equivalence from a finite complex matrix factor
tensored with `R` to matrices over `R`. -/
noncomputable def matrixTensorAlgEquiv :
    Matrix n n ℂ ⊗[ℂ] R ≃ₐ[ℂ] Matrix n n R :=
  (Algebra.TensorProduct.comm ℂ (Matrix n n ℂ) R).trans (matrixEquivTensor n ℂ R).symm

/-- The complex scalar embedding preserves the involution when its target is
a complex star module. -/
theorem algebraMap_complex_star (c : ℂ) :
    algebraMap ℂ R (star c) = star (algebraMap ℂ R c) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    StarModule.star_smul, star_one]

/-- The canonical algebra equivalence preserves the involution. -/
theorem matrixTensorAlgEquiv_map_star (x : Matrix n n ℂ ⊗[ℂ] R) :
    matrixTensorAlgEquiv n (star x) = star (matrixTensorAlgEquiv n x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [matrixTensorAlgEquiv]
  | tmul a b =>
    simp only [TensorProduct.star_tmul, matrixTensorAlgEquiv, AlgEquiv.trans_apply,
      Algebra.TensorProduct.comm_tmul, matrixEquivTensor_apply_symm]
    ext i j
    change star b * algebraMap ℂ R (star (a j i)) =
      star (b * algebraMap ℂ R (a j i))
    calc
      star b * algebraMap ℂ R (star (a j i)) =
          algebraMap ℂ R (star (a j i)) * star b :=
        (Algebra.commutes (star (a j i)) (star b)).symm
      _ = star (b * algebraMap ℂ R (a j i)) := by
        rw [star_mul, ← algebraMap_complex_star]
  | add x y hx hy =>
    simp only [map_add, star_add, hx, hy]

/-- The canonical matrix-tensor algebra equivalence as a star-algebra
equivalence. -/
noncomputable def matrixTensorStarAlgEquiv :
    Matrix n n ℂ ⊗[ℂ] R ≃⋆ₐ[ℂ] Matrix n n R :=
  StarAlgEquiv.ofAlgEquiv (matrixTensorAlgEquiv n) (matrixTensorAlgEquiv_map_star n)

/-- The normalized trace on the algebraic tensor product of a finite complex
matrix factor with a tracial algebra. -/
noncomputable def finiteTypeITensorTrace (tau : R →ₗ[ℂ] ℂ) :
    (Matrix n n ℂ ⊗[ℂ] R) →ₗ[ℂ] ℂ :=
  pullback (matrixTensorStarAlgEquiv n) (normalizedMatrixTraceOver n tau)

/-- A finite type-I algebraic tensor product with a tracial algebra carries the
product algebraic tracial state. -/
theorem finiteTypeITensorTrace_isAlgebraicTracialState [Nonempty n]
    (tau : R →ₗ[ℂ] ℂ) (h_tau : IsAlgebraicTracialState tau) :
    IsAlgebraicTracialState (finiteTypeITensorTrace n tau) := by
  let e : Matrix n n ℂ ⊗[ℂ] R ≃⋆ₐ[ℂ] Matrix n n R :=
    matrixTensorStarAlgEquiv n
  let sigma : Matrix n n R →ₗ[ℂ] ℂ := normalizedMatrixTraceOver n tau
  have h_sigma : IsAlgebraicTracialState sigma :=
    normalizedMatrixTraceOver_isAlgebraicTracialState n tau h_tau
  refine { toIsAlgebraicState := { map_one := ?_, positive := ?_ }, cyclic := ?_ }
  · exact (congrArg sigma e.map_one).trans h_sigma.map_one
  · intro x
    obtain ⟨r, hr_nonneg, hr_value⟩ := h_sigma.positive (e x)
    refine ⟨r, hr_nonneg, ?_⟩
    have h_image : e (star x * x) = star (e x) * e x :=
      (e.map_mul (star x) x).trans (congrArg (fun z => z * e x) (map_star e x))
    exact (congrArg sigma h_image).trans hr_value
  · intro x y
    exact (congrArg sigma (e.map_mul x y)).trans
      ((h_sigma.cyclic (e x) (e y)).trans (congrArg sigma (e.map_mul y x).symm))

/-- On an elementary tensor, the finite type-I product trace factors as the
normalized matrix trace times the coefficient trace. -/
theorem finiteTypeITensorTrace_tmul (tau : R →ₗ[ℂ] ℂ)
    (h_tau : ∀ x y : R, tau (x * y) = tau (y * x))
    (a : Matrix n n ℂ) (r : R) :
    finiteTypeITensorTrace n tau (a ⊗ₜ[ℂ] r) = normalizedMatrixTrace n a * tau r := by
  change normalizedMatrixTraceOver n tau
      (matrixTensorStarAlgEquiv n (a ⊗ₜ[ℂ] r)) = _
  change normalizedMatrixTraceOver n tau
      ((matrixEquivTensor n ℂ R).symm (r ⊗ₜ[ℂ] a)) = _
  rw [matrixEquivTensor_apply_symm, normalizedMatrixTraceOver_apply,
    normalizedMatrixTrace_apply]
  change (1 / (Fintype.card n : ℂ)) *
      ∑ i : n, tau (r * algebraMap ℂ R (a i i)) =
    ((1 / (Fintype.card n : ℂ)) * ∑ i : n, a i i) * tau r
  have hterm : ∀ c : ℂ, tau (r * algebraMap ℂ R c) = c * tau r := by
    intro c
    calc
      tau (r * algebraMap ℂ R c) = tau (algebraMap ℂ R c * r) := h_tau _ _
      _ = tau (c • r) := by rw [Algebra.smul_def]
      _ = c • tau r := tau.map_smul c r
      _ = c * tau r := rfl
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  ring

end StabilizerHyperfinite
