import Formalization.TraceTransport

/-!
# Normalized trace on a finite matrix factor

Blueprint: `blueprints/001-tensor-product-trace.tex`, finite-stage ingredient
for the support-corner construction.  This file supplies the finite part of the
tracial product: the normalized matrix trace is unital and cyclic.
-/

namespace StabilizerHyperfinite

open Matrix

variable (n : Type*) [Fintype n]

/-- The normalized trace on the full matrix algebra indexed by `n`. -/
noncomputable def normalizedMatrixTrace : Matrix n n ℂ →ₗ[ℂ] ℂ :=
  (1 / (Fintype.card n : ℂ)) • Matrix.traceLinearMap n ℂ ℂ

@[simp]
theorem normalizedMatrixTrace_apply (a : Matrix n n ℂ) :
    normalizedMatrixTrace n a = (1 / (Fintype.card n : ℂ)) * Matrix.trace a :=
  rfl

/-- The normalized matrix trace sends the unit to one. -/
theorem normalizedMatrixTrace_one [DecidableEq n] [Nonempty n] :
    normalizedMatrixTrace n 1 = 1 := by
  rw [normalizedMatrixTrace_apply, Matrix.trace_one]
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [div_eq_mul_inv, one_mul]
  exact inv_mul_cancel₀ hcard

/-- The normalized matrix trace is cyclic. -/
theorem normalizedMatrixTrace_cyclic (a b : Matrix n n ℂ) :
    normalizedMatrixTrace n (a * b) = normalizedMatrixTrace n (b * a) := by
  change (1 / (Fintype.card n : ℂ)) * Matrix.trace (a * b) =
    (1 / (Fintype.card n : ℂ)) * Matrix.trace (b * a)
  rw [Matrix.trace_mul_comm]

/-- The unnormalized trace of a star-square is the sum of the entrywise
complex norm-squares (up to the harmless transpose of the two finite sums). -/
theorem trace_star_mul_self (a : Matrix n n ℂ) :
    Matrix.trace (star a * a) =
      ∑ i : n, ∑ j : n, (Complex.normSq (a j i) : ℂ) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.star_apply,
    ← Complex.normSq_eq_conj_mul_self]

/-- The normalized matrix trace is positive on star-squares. -/
theorem normalizedMatrixTrace_positive [Nonempty n] (a : Matrix n n ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ normalizedMatrixTrace n (star a * a) = (r : ℂ) := by
  let r : ℝ := (1 / (Fintype.card n : ℝ)) *
    ∑ i : n, ∑ j : n, Complex.normSq (a j i)
  refine ⟨r, ?_, ?_⟩
  · apply mul_nonneg
    · exact le_of_lt (one_div_pos.mpr (by exact_mod_cast Fintype.card_pos))
    · exact Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  · rw [normalizedMatrixTrace_apply, trace_star_mul_self]
    simp [r]

/-- The normalized matrix trace is a unital tracial functional. -/
theorem normalizedMatrixTrace_isUnitalTracial [DecidableEq n] [Nonempty n] :
    IsUnitalTracial (normalizedMatrixTrace n) := by
  constructor
  · exact normalizedMatrixTrace_one n
  · exact normalizedMatrixTrace_cyclic n

/-- The normalized matrix trace is an algebraic state. -/
theorem normalizedMatrixTrace_isAlgebraicState [DecidableEq n] [Nonempty n] :
    IsAlgebraicState (normalizedMatrixTrace n) := by
  constructor
  · exact normalizedMatrixTrace_one n
  · exact normalizedMatrixTrace_positive n

/-- The normalized matrix trace is an algebraic tracial state. -/
theorem normalizedMatrixTrace_isAlgebraicTracialState [DecidableEq n] [Nonempty n] :
    IsAlgebraicTracialState (normalizedMatrixTrace n) := by
  refine { toIsAlgebraicState := normalizedMatrixTrace_isAlgebraicState n
           cyclic := normalizedMatrixTrace_cyclic n }

end StabilizerHyperfinite
