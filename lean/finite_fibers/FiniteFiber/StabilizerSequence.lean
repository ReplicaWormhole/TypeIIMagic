import FiniteFiber.FiniteStabilizer
import FiniteFiber.StrongSupport

/-!
# Decreasing supports from a nested stabilizer sequence

This file turns an increasing sequence of finite local stabilizer subgroups
into the decreasing projection sequence used by the support-corner theorem.
The order is obtained directly from subgroup averaging: adding stabilizer
constraints reduces the common fixed subspace.

It deliberately does not construct the stabilizer state, its GNS
representation, or the strong limit.  Those analytic steps remain explicit at
the point where this sequence is composed with the finite-fiber theorem.
-/

namespace FiniteFiber

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Group K]

/--
The local code-space supports associated with a sequence of finite stabilizer
subgroups of an arbitrary global stabilizer group.
-/
noncomputable def stabilizerAverageSequence
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S : ℕ → Subgroup K) [∀ n, Fintype (S n)] :
    ℕ → H →L[ℂ] H :=
  fun n => (A.restrict (S n)).average

/--
An increasing sequence of finite stabilizer subgroups supplies the decreasing sequence of
projections required by the strong-support layer.
-/
theorem stabilizerAverageSequence_decreasingProjectionSequence
    {M : VonNeumannAlgebra H}
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S : ℕ → Subgroup K) [∀ n, Fintype (S n)]
    (hmem : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) ∈ M)
    (hmonotone : ∀ n m : ℕ, n ≤ m → S n ≤ S m) :
    DecreasingProjectionSequence M (stabilizerAverageSequence A S) := by
  refine { projection := ?_, decreasing := ?_ }
  · intro n
    apply (A.restrict (S n)).average_isProjectionIn M
    intro s
    exact hmem n s
  · intro n m hnm
    exact A.restrict_average_isSubprojection_of_le (S n) (S m) (hmonotone n m hnm)

/-- A vector stabilized by every finite local group is fixed by every local support. -/
theorem stabilizerAverageSequence_fixes
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S : ℕ → Subgroup K) [∀ n, Fintype (S n)]
    (xi : H)
    (hfix : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) xi = xi) :
    ∀ n : ℕ, stabilizerAverageSequence A S n xi = xi := by
  intro n
  apply (A.restrict (S n)).average_apply_eq_of_forall_fix xi
  intro s
  exact hfix n s

/-- Each local support is nonzero when it fixes a common nonzero vector. -/
theorem stabilizerAverageSequence_ne_zero
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S : ℕ → Subgroup K) [∀ n, Fintype (S n)]
    {xi : H} (hxi : xi ≠ 0)
    (hfix : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) xi = xi) :
    ∀ n : ℕ, stabilizerAverageSequence A S n ≠ 0 := by
  intro n
  apply (A.restrict (S n)).average_ne_zero_of_forall_fix hxi
  intro s
  exact hfix n s

end FiniteFiber
