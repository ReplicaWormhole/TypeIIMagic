import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import FiniteFiber.TracialCorner

/-!
# Full tracial corners and finite central fibers

This is the abstract theorem corresponding to the final support-corner step in
the manuscript.  It proves the package-local central-summand finite-projection
criterion first; a finite-indexed central-projection statement is a direct
specialization.  It does not formalize factors or a type classification.
-/

namespace FiniteFiber

open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
A finite explicit partition by nonzero central projections of a concrete
algebra.  The word ``fiber'' here is indexing terminology only; no factor or
direct-integral hypothesis is encoded.
-/
structure FiniteCentralFiberFamily (M : VonNeumannAlgebra H) (ι : Type*) [Fintype ι] where
  projection : ι → H →L[ℂ] H
  central : ∀ i : ι, IsCentralProjection M (projection i)
  nonzero : ∀ i : ι, projection i ≠ 0
  orthogonal : ∀ i j : ι, i ≠ j → projection i * projection j = 0
  sum_eq_one : ∑ i : ι, projection i = 1

/-- A central slice of the tracial support is finite. -/
theorem central_mul_finite_of_faithful_tracial_corner
    {M : VonNeumannAlgebra H} {q z : H →L[ℂ] H}
    (T : FaithfulTracialCorner M q) (hq : IsProjectionIn M q)
    (hz : IsCentralProjection M z) :
    IsFiniteProjection M (z * q) := by
  exact finite_of_subprojection_of_faithful_tracial_corner T
    (central_mul_isProjectionIn hz hq) (central_mul_subprojection_right hz hq)

/-- Fullness makes every nonzero central slice of the support nonzero. -/
theorem central_mul_nonzero_of_full
    {M : VonNeumannAlgebra H} {q z : H →L[ℂ] H}
    (hfull : IsFullProjection M q) (hz : IsCentralProjection M z) (hz_nonzero : z ≠ 0) :
    z * q ≠ 0 :=
  hfull.2 z hz hz_nonzero

/-- The canonical finite witness below an arbitrary nonzero central projection. -/
theorem canonical_central_witness_of_full_tracial_corner
    {M : VonNeumannAlgebra H} {q z : H →L[ℂ] H}
    (T : FaithfulTracialCorner M q) (hfull : IsFullProjection M q)
    (hz : IsCentralProjection M z) (hz_nonzero : z ≠ 0) :
    IsFiniteProjection M (z * q) ∧ z * q ≠ 0 ∧ IsSubprojection (z * q) z :=
  ⟨central_mul_finite_of_faithful_tracial_corner T hfull.1 hz,
    central_mul_nonzero_of_full hfull hz hz_nonzero,
    central_mul_subprojection_left hz hfull.1⟩

/--
The central-summand theorem: a full tracial corner supplies a nonzero finite
projection below every nonzero central projection.
-/
theorem full_tracial_corner_semifinite
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H}
    (T : FaithfulTracialCorner M q) (hfull : IsFullProjection M q) :
    IsSemifinite M := by
  intro z hz hz_nonzero
  let e : H →L[ℂ] H := z * q
  obtain ⟨he_finite, he_nonzero, hez⟩ :=
    canonical_central_witness_of_full_tracial_corner T hfull hz hz_nonzero
  exact ⟨e, he_finite, he_nonzero, hez⟩

/-- The canonical finite witness in a supplied finite central fiber. -/
theorem finite_central_fiber_canonical_witness
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {ι : Type*} [Fintype ι]
    (T : FaithfulTracialCorner M q) (hfull : IsFullProjection M q)
    (fibers : FiniteCentralFiberFamily M ι) (i : ι) :
    IsFiniteProjection M (fibers.projection i * q) ∧
      fibers.projection i * q ≠ 0 ∧
      IsSubprojection (fibers.projection i * q) (fibers.projection i) := by
  exact canonical_central_witness_of_full_tracial_corner T hfull
    (fibers.central i) (fibers.nonzero i)

/-- Each explicitly supplied finite central fiber contains a nonzero finite projection. -/
theorem finite_central_fiber_has_finite_projection
    {M : VonNeumannAlgebra H} {q : H →L[ℂ] H} {ι : Type*} [Fintype ι]
    (T : FaithfulTracialCorner M q) (hfull : IsFullProjection M q)
    (fibers : FiniteCentralFiberFamily M ι) (i : ι) :
    ∃ e : H →L[ℂ] H,
      IsFiniteProjection M e ∧ e ≠ 0 ∧ IsSubprojection e (fibers.projection i) := by
  exact ⟨fibers.projection i * q, finite_central_fiber_canonical_witness T hfull fibers i⟩

end FiniteFiber
