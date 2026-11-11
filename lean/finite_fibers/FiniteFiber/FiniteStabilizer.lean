import FiniteFiber.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# Finite stabilizer averages

For a finite local stabilizer group, the manuscript defines its code-space
support as the average of the represented group elements.  This file proves
directly that this average is a projection, rather than taking that fact as an
input to the support-corner theorem.

The interface intentionally records only the finite-group and adjoint
properties used below.  It does not yet encode the tensor-product Pauli
realization, the trace/rank calculation proving that the average is nonzero,
or partial-trace compatibility between nested regions.
-/

namespace FiniteFiber

open scoped BigOperators

variable {H G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype G] [Group G]

/--
Finite local symmetry data sufficient for the group-average projection.

For a consistent commuting Hermitian Pauli stabilizer group, `representation`
is its action on the local Hilbert space and `selfAdjoint` holds for every
group element.  No claim is made here that every instance arises from Pauli
operators.
-/
structure SelfAdjointFiniteGroupAction where
  representation : G →* (H →L[ℂ] H)
  selfAdjoint : ∀ g : G, IsSelfAdjoint (representation g)

/-- The normalized average of a finite local symmetry group. -/
noncomputable def SelfAdjointFiniteGroupAction.average
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G)) : H →L[ℂ] H :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, A.representation g

/-- Every represented group element fixes the group average on the left. -/
theorem SelfAdjointFiniteGroupAction.mul_average_left
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G)) (g : G) :
    A.representation g * A.average = A.average := by
  simp only [SelfAdjointFiniteGroupAction.average, mul_smul_comm, Finset.mul_sum]
  rw [show (fun h : G => A.representation g * A.representation h) =
      fun h : G => A.representation (g * h) by
    funext h
    exact (A.representation.map_mul g h).symm]
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) A.representation]

/-- Every represented group element fixes the group average on the right. -/
theorem SelfAdjointFiniteGroupAction.average_mul_right
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G)) (g : G) :
    A.average * A.representation g = A.average := by
  simp only [SelfAdjointFiniteGroupAction.average, smul_mul_assoc, Finset.sum_mul]
  rw [show (fun h : G => A.representation h * A.representation g) =
      fun h : G => A.representation (h * g) by
    funext h
    exact (A.representation.map_mul h g).symm]
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) A.representation]

/-- The normalized finite group average is idempotent. -/
theorem SelfAdjointFiniteGroupAction.average_isIdempotent
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G)) :
    A.average * A.average = A.average := by
  nth_rewrite 1 [SelfAdjointFiniteGroupAction.average]
  rw [smul_mul_assoc, Finset.sum_mul]
  simp_rw [A.mul_average_left]
  rw [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hcard, one_smul]

/-- The average is self-adjoint when every represented stabilizer is. -/
theorem SelfAdjointFiniteGroupAction.average_isSelfAdjoint
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G)) :
    IsSelfAdjoint A.average := by
  change star A.average = A.average
  rw [SelfAdjointFiniteGroupAction.average, star_smul]
  have hscalar : star ((Fintype.card G : ℂ)⁻¹) = (Fintype.card G : ℂ)⁻¹ := by
    norm_num
  rw [hscalar]
  congr 1
  simp only [star_sum]
  have hself (g : G) : star (A.representation g) = A.representation g :=
    (A.selfAdjoint g).star_eq
  simp_rw [hself]

/-- The finite local group average is a projection. -/
theorem SelfAdjointFiniteGroupAction.average_isStarProjection
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G)) :
    IsStarProjection A.average := by
  exact ⟨A.average_isIdempotent, A.average_isSelfAdjoint⟩

/-- A vector fixed by every local stabilizer is fixed by their average. -/
theorem SelfAdjointFiniteGroupAction.average_apply_eq_of_forall_fix
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G)) (x : H)
    (hfix : ∀ g : G, A.representation g x = x) :
    A.average x = x := by
  rw [SelfAdjointFiniteGroupAction.average]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  simp_rw [hfix]
  rw [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hcard, one_smul]

/-- A common nonzero fixed vector proves that the finite group average is nonzero. -/
theorem SelfAdjointFiniteGroupAction.average_ne_zero_of_forall_fix
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G)) {x : H}
    (hx : x ≠ 0) (hfix : ∀ g : G, A.representation g x = x) :
    A.average ≠ 0 := by
  intro hzero
  have hfixed : A.average x = x := A.average_apply_eq_of_forall_fix x hfix
  rw [hzero] at hfixed
  exact hx (by simpa using hfixed.symm)

/-- If every local stabilizer is represented in a von Neumann algebra, so is its average. -/
theorem SelfAdjointFiniteGroupAction.average_mem
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G))
    (M : VonNeumannAlgebra H)
    (hmem : ∀ g : G, A.representation g ∈ M) :
    A.average ∈ M := by
  rw [SelfAdjointFiniteGroupAction.average]
  apply M.toStarSubalgebra.toSubalgebra.smul_mem
  apply M.toStarSubalgebra.toSubalgebra.sum_mem
  intro g _
  exact hmem g

/-- The local group average is a projection in any algebra containing its stabilizers. -/
theorem SelfAdjointFiniteGroupAction.average_isProjectionIn
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G))
    (M : VonNeumannAlgebra H)
    (hmem : ∀ g : G, A.representation g ∈ M) :
    IsProjectionIn M A.average :=
  ⟨A.average_mem M hmem, A.average_isStarProjection⟩

/-- Restrict a finite symmetry action to a subgroup. -/
noncomputable def SelfAdjointFiniteGroupAction.restrict
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G))
    (S : Subgroup G) : SelfAdjointFiniteGroupAction (H := H) (G := S) where
  representation := A.representation.comp S.subtype
  selfAdjoint s := A.selfAdjoint s

/-- The average over an ambient stabilizer group is fixed on the right by a subgroup average. -/
theorem SelfAdjointFiniteGroupAction.average_mul_restrict_average
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G))
    (S : Subgroup G) [Fintype S] :
    A.average * (A.restrict S).average = A.average := by
  change A.average * ((Fintype.card S : ℂ)⁻¹ • ∑ s : S, A.representation s) = A.average
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [A.average_mul_right]
  rw [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul]
  have hcard : (Fintype.card S : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hcard, one_smul]

/-- The average over an ambient stabilizer group is fixed on the left by a subgroup average. -/
theorem SelfAdjointFiniteGroupAction.restrict_average_mul_average
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G))
    (S : Subgroup G) [Fintype S] :
    (A.restrict S).average * A.average = A.average := by
  change ((Fintype.card S : ℂ)⁻¹ • ∑ s : S, A.representation s) * A.average = A.average
  rw [smul_mul_assoc, Finset.sum_mul]
  simp_rw [A.mul_average_left]
  rw [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul]
  have hcard : (Fintype.card S : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hcard, one_smul]

/--
Adding stabilizer constraints decreases the code-space projection: the average
over an ambient finite group lies below the average over each subgroup.
-/
theorem SelfAdjointFiniteGroupAction.average_isSubprojection_restrict_average
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G))
    (S : Subgroup G) [Fintype S] :
    IsSubprojection A.average (A.restrict S).average :=
  ⟨A.average_mul_restrict_average S, A.restrict_average_mul_average S⟩

section CompatibleFiniteActions

variable {K L : Type*}
variable [Fintype K] [Group K] [Fintype L] [Group L]

/--
Compatible averages for nested local stabilizer groups are ordered in the
expected direction.  The inclusion need not be used as a literal subtype: the
only algebraic fact needed is that each small-group operator is the
corresponding large-group operator after inclusion.
-/
theorem SelfAdjointFiniteGroupAction.average_isSubprojection_of_compatible
    (small : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (large : SelfAdjointFiniteGroupAction (H := H) (G := L))
    (inclusion : K →* L)
    (hcompatible : ∀ k : K,
      small.representation k = large.representation (inclusion k)) :
    IsSubprojection large.average small.average := by
  constructor
  · change large.average * ((Fintype.card K : ℂ)⁻¹ • ∑ k : K, small.representation k) =
      large.average
    rw [mul_smul_comm, Finset.mul_sum]
    simp_rw [hcompatible]
    simp_rw [large.average_mul_right]
    rw [Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    rw [smul_smul]
    have hcard : (Fintype.card K : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [inv_mul_cancel₀ hcard, one_smul]
  · change ((Fintype.card K : ℂ)⁻¹ • ∑ k : K, small.representation k) * large.average =
      large.average
    rw [smul_mul_assoc, Finset.sum_mul]
    simp_rw [hcompatible]
    simp_rw [large.mul_average_left]
    rw [Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    rw [smul_smul]
    have hcard : (Fintype.card K : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [inv_mul_cancel₀ hcard, one_smul]

end CompatibleFiniteActions

section NestedFiniteSubgroups

variable {K : Type*} [Group K]

/--
For finite subgroups of an arbitrary (possibly infinite) stabilizer group,
subgroup inclusion decreases the corresponding code-space averages.  This is
the form used for a nested sequence of finite local groups.
-/
theorem SelfAdjointFiniteGroupAction.restrict_average_isSubprojection_of_le
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S T : Subgroup K) [Fintype S] [Fintype T] (hST : S ≤ T) :
    IsSubprojection (A.restrict T).average (A.restrict S).average := by
  refine SelfAdjointFiniteGroupAction.average_isSubprojection_of_compatible
    (A.restrict S) (A.restrict T) (Subgroup.inclusion hST) ?_
  intro s
  change A.representation (s : K) =
    A.representation ((Subgroup.inclusion hST s : T) : K)
  rw [Subgroup.coe_inclusion]

end NestedFiniteSubgroups

end FiniteFiber
