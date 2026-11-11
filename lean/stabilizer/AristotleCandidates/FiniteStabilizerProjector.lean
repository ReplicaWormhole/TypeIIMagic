import Mathlib

/-!
# Finite stabilizer group-average projector

Purely algebraic content.  Let `A` be a complex star algebra, `G` a finite
group and `U : G →* A` a unital multiplicative map with

    star (U g) = U g⁻¹.

The group average

    P = (|G| : ℂ)⁻¹ • ∑ g, U g

is self-adjoint, idempotent, and is fixed by every `U g` on both sides.  If in
addition `tr : A →ₗ[ℂ] ℂ` is a linear functional with `tr 1 = 1` which
annihilates `U g` for every `g ≠ 1`, then

    tr P = (|G| : ℂ)⁻¹.

This is the finite stabilizer projector normalization.  No C⋆, GNS, normality,
factor, or rank statement is made: `tr P` is *not* identified with a matrix
rank, and the group-average projector `P` is kept distinct from any normalized
density matrix `ρ = d⁻¹ • ∑ g, U g` of a `d`-dimensional qubit space.
-/

namespace AristotleCandidates

section Translation

variable {A G : Type*} [Ring A] [Group G] [Fintype G]

/-- The sum `∑ g, U g` is invariant under left translation by `U h`. -/
theorem mul_sum_apply (U : G →* A) (h : G) :
    U h * ∑ g : G, U g = ∑ g : G, U g := by
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => (map_mul U h g).symm)

/-- The sum `∑ g, U g` is invariant under right translation by `U h`. -/
theorem sum_mul_apply (U : G →* A) (h : G) :
    (∑ g : G, U g) * U h = ∑ g : G, U g := by
  rw [Finset.sum_mul]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => (map_mul U g h).symm)

end Translation

section GroupAverage

variable {A G : Type*} [Ring A] [Algebra ℂ A] [Group G] [Fintype G]

/-- The group-average element `P = |G|⁻¹ • ∑ g, U g` of a finite group
representation `U : G →* A` inside a complex algebra `A`. -/
noncomputable def groupAverage (U : G →* A) : A :=
  ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, U g

theorem groupAverage_def (U : G →* A) :
    groupAverage U = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, U g := rfl

/-- Every `U h` fixes the group average on the left. -/
theorem mul_groupAverage (U : G →* A) (h : G) :
    U h * groupAverage U = groupAverage U := by
  rw [groupAverage_def, mul_smul_comm, mul_sum_apply]

/-- Every `U h` fixes the group average on the right. -/
theorem groupAverage_mul (U : G →* A) (h : G) :
    groupAverage U * U h = groupAverage U := by
  rw [groupAverage_def, smul_mul_assoc, sum_mul_apply]

/-- The group average is idempotent. -/
theorem groupAverage_mul_self (U : G →* A) :
    groupAverage U * groupAverage U = groupAverage U := by
  have hcard : ((Fintype.card G : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := G))
  calc groupAverage U * groupAverage U
      = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, U g * groupAverage U := by
        nth_rewrite 1 [groupAverage_def (U := U)]
        rw [smul_mul_assoc, Finset.sum_mul]
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ _g : G, groupAverage U := by
        simp only [mul_groupAverage]
    _ = groupAverage U := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          inv_mul_cancel₀ hcard, one_smul]

/-- The group average is self-adjoint when `star (U g) = U g⁻¹`. -/
theorem star_groupAverage [StarRing A] [StarModule ℂ A] (U : G →* A)
    (hU : ∀ g : G, star (U g) = U g⁻¹) :
    star (groupAverage U) = groupAverage U := by
  rw [groupAverage_def, star_smul, star_sum]
  have hstar : star ((Fintype.card G : ℂ))⁻¹ = ((Fintype.card G : ℂ))⁻¹ := by simp
  rw [hstar]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ hU

/-- Normalized trace of the group-average projector: if `tr` is a linear
functional with `tr 1 = 1` which annihilates `U g` for all `g ≠ 1`, then
`tr P = |G|⁻¹`. -/
theorem groupAverage_trace (U : G →* A) (tr : A →ₗ[ℂ] ℂ) (htr_one : tr 1 = 1)
    (htr : ∀ g : G, g ≠ 1 → tr (U g) = 0) :
    tr (groupAverage U) = ((Fintype.card G : ℂ))⁻¹ := by
  rw [groupAverage_def, map_smul, map_sum]
  have hsum : ∑ g : G, tr (U g) = 1 := by
    rw [Finset.sum_eq_single (1 : G)]
    · rw [map_one, htr_one]
    · intro b _ hb
      exact htr b hb
    · intro h
      exact absurd (Finset.mem_univ (1 : G)) h
  rw [hsum, smul_eq_mul, mul_one]

end GroupAverage

end AristotleCandidates
