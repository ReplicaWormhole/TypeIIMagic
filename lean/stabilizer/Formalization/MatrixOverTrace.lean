import Formalization.TraceTransport

/-!
# Matrix amplification of an algebraic tracial state

This is the algebraic finite-type-I factor of the intended product model.  If
`R` carries an algebraic tracial state, its finite matrix amplification carries
the normalized matrix trace obtained by applying the trace of `R` to the
diagonal entries.
-/

namespace StabilizerHyperfinite

open Matrix

variable {R : Type*} [Semiring R] [Algebra ℂ R]
variable (n : Type*) [Fintype n]

/-- Apply a complex-linear functional to the diagonal matrix trace. -/
noncomputable def matrixTraceOver (tau : R →ₗ[ℂ] ℂ) : Matrix n n R →ₗ[ℂ] ℂ where
  toFun a := ∑ i : n, tau (a i i)
  map_add' a b := by
    simp only [Matrix.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Matrix.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- The normalized matrix amplification of an algebraic trace. -/
noncomputable def normalizedMatrixTraceOver (tau : R →ₗ[ℂ] ℂ) : Matrix n n R →ₗ[ℂ] ℂ :=
  (1 / (Fintype.card n : ℂ)) • matrixTraceOver n tau

@[simp]
theorem normalizedMatrixTraceOver_apply (tau : R →ₗ[ℂ] ℂ) (a : Matrix n n R) :
    normalizedMatrixTraceOver n tau a =
      (1 / (Fintype.card n : ℂ)) * ∑ i : n, tau (a i i) :=
  rfl

/-- Normalization makes the amplified trace unital. -/
theorem normalizedMatrixTraceOver_one [DecidableEq n] [Nonempty n]
    (tau : R →ₗ[ℂ] ℂ) (h_tau_one : tau 1 = 1) :
    normalizedMatrixTraceOver n tau 1 = 1 := by
  rw [normalizedMatrixTraceOver_apply]
  have hsum : ∑ i : n, tau ((1 : Matrix n n R) i i) = (Fintype.card n : ℂ) := by
    simp [h_tau_one]
  rw [hsum]
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [div_eq_mul_inv, one_mul]
  exact inv_mul_cancel₀ hcard

/-- The normalized matrix amplification of a cyclic functional is cyclic. -/
theorem normalizedMatrixTraceOver_cyclic (tau : R →ₗ[ℂ] ℂ)
    (h_tau : ∀ x y : R, tau (x * y) = tau (y * x))
    (a b : Matrix n n R) :
    normalizedMatrixTraceOver n tau (a * b) = normalizedMatrixTraceOver n tau (b * a) := by
  classical
  change (1 / (Fintype.card n : ℂ)) * ∑ i : n, tau ((a * b) i i) =
    (1 / (Fintype.card n : ℂ)) * ∑ i : n, tau ((b * a) i i)
  congr 1
  calc
    ∑ i : n, tau ((a * b) i i) = ∑ i : n, ∑ j : n, tau (a i j * b j i) := by
      simp only [Matrix.mul_apply, map_sum]
    _ = ∑ j : n, ∑ i : n, tau (b j i * a i j) := by
      rw [Finset.sum_comm]
      simp_rw [h_tau]
    _ = ∑ i : n, tau ((b * a) i i) := by
      simp only [Matrix.mul_apply, map_sum]

/-- The diagonal trace of a matrix star-square is a finite sum of star-squares
in the coefficient algebra. -/
theorem matrixTraceOver_star_mul_self [StarRing R] (tau : R →ₗ[ℂ] ℂ) (a : Matrix n n R) :
    matrixTraceOver n tau (star a * a) =
      ∑ i : n, ∑ j : n, tau (star (a j i) * a j i) := by
  change ∑ i : n, tau ((star a * a) i i) = _
  simp only [Matrix.mul_apply, Matrix.star_apply, map_sum]

/-- The normalized matrix amplification of a positive functional is positive
on star-squares. -/
theorem normalizedMatrixTraceOver_positive [StarRing R] [Nonempty n] (tau : R →ₗ[ℂ] ℂ)
    (h_tau : IsPositiveFunctional tau) (a : Matrix n n R) :
    ∃ r : ℝ, 0 ≤ r ∧ normalizedMatrixTraceOver n tau (star a * a) = (r : ℂ) := by
  classical
  let q : n → n → ℝ := fun i j => Classical.choose (h_tau (a j i))
  have hq_nonneg : ∀ i j, 0 ≤ q i j := fun i j => (Classical.choose_spec (h_tau (a j i))).1
  have hq_value : ∀ i j, tau (star (a j i) * a j i) = (q i j : ℂ) :=
    fun i j => (Classical.choose_spec (h_tau (a j i))).2
  let r : ℝ := (1 / (Fintype.card n : ℝ)) * ∑ i : n, ∑ j : n, q i j
  refine ⟨r, ?_, ?_⟩
  · apply mul_nonneg
    · exact le_of_lt (one_div_pos.mpr (by exact_mod_cast Fintype.card_pos))
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hq_nonneg i j
  · rw [normalizedMatrixTraceOver_apply]
    change (1 / (Fintype.card n : ℂ)) * matrixTraceOver n tau (star a * a) = (r : ℂ)
    rw [matrixTraceOver_star_mul_self]
    simp_rw [hq_value]
    simp [r]

/-- A finite type-I matrix amplification of an algebraic tracial state is again
an algebraic tracial state. -/
theorem normalizedMatrixTraceOver_isAlgebraicTracialState [StarRing R] [DecidableEq n] [Nonempty n]
    (tau : R →ₗ[ℂ] ℂ) (h_tau : IsAlgebraicTracialState tau) :
    IsAlgebraicTracialState (normalizedMatrixTraceOver n tau) := by
  refine { toIsAlgebraicState := ?_, cyclic := ?_ }
  · exact { map_one := normalizedMatrixTraceOver_one n tau h_tau.map_one
            positive := normalizedMatrixTraceOver_positive n tau h_tau.positive }
  · exact normalizedMatrixTraceOver_cyclic n tau h_tau.cyclic

variable {A : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]

/-- The algebraic trace induced by a finite type-I matrix amplification of a
tracial algebra, transported to an explicitly identified model. -/
noncomputable def matrixAmplificationInducedTrace [StarRing R]
    [DecidableEq n] (e : A ≃⋆ₐ[ℂ] Matrix n n R) (tau : R →ₗ[ℂ] ℂ) : A →ₗ[ℂ] ℂ :=
  pullback e (normalizedMatrixTraceOver n tau)

/-- Once a product model is supplied as a star-algebra equivalence, its finite
type-I matrix amplification induces an algebraic tracial state. -/
theorem matrixAmplificationInducedTrace_isAlgebraicTracialState [StarRing R]
    [DecidableEq n] [Nonempty n] (e : A ≃⋆ₐ[ℂ] Matrix n n R)
    (tau : R →ₗ[ℂ] ℂ) (h_tau : IsAlgebraicTracialState tau) :
    IsAlgebraicTracialState (matrixAmplificationInducedTrace n e tau) :=
  isAlgebraicTracialState_pullback e (normalizedMatrixTraceOver n tau)
    (normalizedMatrixTraceOver_isAlgebraicTracialState n tau h_tau)

end StabilizerHyperfinite
