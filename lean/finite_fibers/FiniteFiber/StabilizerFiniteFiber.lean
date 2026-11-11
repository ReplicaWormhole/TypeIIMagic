import FiniteFiber.GNSOrbit
import FiniteFiber.StabilizerSequence

/-!
# Finite central fibers from a nested stabilizer sequence

This is the conditional composition currently supported by the formalization.
It starts from a supplied finite local subgroup sequence and group action,
proves that their averages form the decreasing support sequence, and then
invokes the checked support-corner theorem.

The remaining inputs are intentionally visible: strong convergence of the
decreasing supports and the specified GNS-orbit/corner-traciality conditions.
This file does not claim to construct those analytic data from a quasilocal
stabilizer state.
-/

namespace FiniteFiber

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Group K]

/--
The conditional finite-fiber theorem for a supplied increasing sequence of
finite stabilizer subgroups.  It proves the canonical finite witness `z * q`
in every nonzero central summand, from the displayed stabilizer and GNS
hypotheses.
-/
theorem stabilizerAverageSequence_supportCornerConclusion_of_gnsOrbit
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H}
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S : ℕ → Subgroup K) [∀ n, Fintype (S n)]
    (hmem : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) ∈ M)
    (hmonotone : ∀ n m : ℕ, n ≤ m → S n ≤ S m)
    (hfix : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) xi = xi)
    (hstrong : StronglyTendsTo (stabilizerAverageSequence A S) q)
    (C : GNSOrbitConditions M q xi) :
    SupportCornerConclusion M q xi := by
  let D : DecreasingProjectionSequence M (stabilizerAverageSequence A S) :=
    stabilizerAverageSequence_decreasingProjectionSequence A S hmem hmonotone
  exact D.supportCornerConclusion_of_gnsOrbit hstrong
    (stabilizerAverageSequence_fixes A S xi hfix) C

/--
Conditional canonical strong-limit form of the stabilizer finite-fiber
theorem.  Given the supplied subgroup sequence and GNS-orbit conditions, the
limit is constructed from the decreasing local supports, so no separate
convergence hypothesis is needed.
-/
theorem stabilizerAverageSequence_canonicalSupportCornerConclusion_of_gnsOrbit
    {M : VonNeumannAlgebra H} {xi : H}
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S : ℕ → Subgroup K) [∀ n, Fintype (S n)]
    (hmem : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) ∈ M)
    (hmonotone : ∀ n m : ℕ, n ≤ m → S n ≤ S m)
    (hfix : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) xi = xi)
    (C : GNSOrbitConditions M
      (decreasingProjectionStrongLimit (stabilizerAverageSequence A S)) xi) :
    SupportCornerConclusion M (decreasingProjectionStrongLimit (stabilizerAverageSequence A S)) xi := by
  let D : DecreasingProjectionSequence M (stabilizerAverageSequence A S) :=
    stabilizerAverageSequence_decreasingProjectionSequence A S hmem hmonotone
  exact D.supportCornerConclusion_of_gnsOrbit
    D.stronglyTendsTo_decreasingProjectionStrongLimit
    (stabilizerAverageSequence_fixes A S xi hfix) C

/--
In particular, the von Neumann algebra satisfies this package's
central-summand finite-projection criterion: every nonzero central summand
contains a nonzero finite projection.
-/
theorem stabilizerAverageSequence_semifinite_of_gnsOrbit
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {xi : H}
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S : ℕ → Subgroup K) [∀ n, Fintype (S n)]
    (hmem : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) ∈ M)
    (hmonotone : ∀ n m : ℕ, n ≤ m → S n ≤ S m)
    (hfix : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) xi = xi)
    (hstrong : StronglyTendsTo (stabilizerAverageSequence A S) q)
    (C : GNSOrbitConditions M q xi) :
    IsSemifinite M := by
  let D : DecreasingProjectionSequence M (stabilizerAverageSequence A S) :=
    stabilizerAverageSequence_decreasingProjectionSequence A S hmem hmonotone
  exact D.full_tracial_corner_semifinite_of_gnsOrbit hstrong
    (stabilizerAverageSequence_fixes A S xi hfix) C

/-- Semifiniteness from the canonical strong limit of a nested stabilizer sequence. -/
theorem stabilizerAverageSequence_canonicalSemifinite_of_gnsOrbit
    {M : VonNeumannAlgebra H} {xi : H}
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S : ℕ → Subgroup K) [∀ n, Fintype (S n)]
    (hmem : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) ∈ M)
    (hmonotone : ∀ n m : ℕ, n ≤ m → S n ≤ S m)
    (hfix : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) xi = xi)
    (C : GNSOrbitConditions M
      (decreasingProjectionStrongLimit (stabilizerAverageSequence A S)) xi) :
    IsSemifinite M :=
  (stabilizerAverageSequence_canonicalSupportCornerConclusion_of_gnsOrbit
    A S hmem hmonotone hfix C).semifinite

/-- The canonical finite witness in a specified nonzero central summand. -/
theorem stabilizerAverageSequence_central_witness_of_gnsOrbit
    {M : VonNeumannAlgebra H} {q z : H →L[ℂ] H} {xi : H}
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S : ℕ → Subgroup K) [∀ n, Fintype (S n)]
    (hmem : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) ∈ M)
    (hmonotone : ∀ n m : ℕ, n ≤ m → S n ≤ S m)
    (hfix : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) xi = xi)
    (hstrong : StronglyTendsTo (stabilizerAverageSequence A S) q)
    (C : GNSOrbitConditions M q xi)
    (hz : IsCentralProjection M z) (hz_nonzero : z ≠ 0) :
    IsFiniteProjection M (z * q) ∧ z * q ≠ 0 ∧ IsSubprojection (z * q) z := by
  exact
    (stabilizerAverageSequence_supportCornerConclusion_of_gnsOrbit
      A S hmem hmonotone hfix hstrong C).central_witness z hz hz_nonzero

/-- The canonical finite witness `z * q` using the constructed strong limit. -/
theorem stabilizerAverageSequence_canonicalCentralWitness_of_gnsOrbit
    {M : VonNeumannAlgebra H} {xi : H} {z : H →L[ℂ] H}
    (A : SelfAdjointFiniteGroupAction (H := H) (G := K))
    (S : ℕ → Subgroup K) [∀ n, Fintype (S n)]
    (hmem : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) ∈ M)
    (hmonotone : ∀ n m : ℕ, n ≤ m → S n ≤ S m)
    (hfix : ∀ n : ℕ, ∀ s : S n, A.representation (s : K) xi = xi)
    (C : GNSOrbitConditions M
      (decreasingProjectionStrongLimit (stabilizerAverageSequence A S)) xi)
    (hz : IsCentralProjection M z) (hz_nonzero : z ≠ 0) :
    IsFiniteProjection M (z * decreasingProjectionStrongLimit (stabilizerAverageSequence A S)) ∧
      z * decreasingProjectionStrongLimit (stabilizerAverageSequence A S) ≠ 0 ∧
      IsSubprojection (z * decreasingProjectionStrongLimit (stabilizerAverageSequence A S)) z := by
  exact
    (stabilizerAverageSequence_canonicalSupportCornerConclusion_of_gnsOrbit
      A S hmem hmonotone hfix C).central_witness z hz hz_nonzero

end FiniteFiber
