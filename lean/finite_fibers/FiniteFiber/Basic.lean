import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Projection-comparison vocabulary for finite central fibers

This file uses mathlib's concrete `VonNeumannAlgebra H`.  The definitions below
are deliberately local to this package until an upstream API review determines
their final mathlib names and homes.

The key point is that `IsSemifinite` is stated in the projection form used by
the manuscript: every nonzero central projection majorizes a nonzero finite
projection.  No direct-integral decomposition is assumed or encoded here.
-/

namespace FiniteFiber

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A projection belonging to a concrete von Neumann algebra. -/
def IsProjectionIn (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) : Prop :=
  e ∈ M ∧ IsStarProjection e

/-- The two-sided multiplication form of the subprojection relation. -/
def IsSubprojection (e f : H →L[ℂ] H) : Prop :=
  e * f = e ∧ f * e = e

/-- A partial isometry in the algebraic form used by the corner-support proof. -/
def IsPartialIsometry (v : H →L[ℂ] H) : Prop :=
  v * star v * v = v

/-- Murray--von Neumann equivalence inside a concrete von Neumann algebra. -/
def IsMvNEquivalent (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H) : Prop :=
  ∃ v : H →L[ℂ] H, v ∈ M ∧ star v * v = e ∧ v * star v = f

/-- A finite projection: it is not equivalent to a proper subprojection. -/
def IsFiniteProjection (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) : Prop :=
  IsProjectionIn M e ∧
    ∀ f : H →L[ℂ] H, IsProjectionIn M f → IsMvNEquivalent M e f →
      IsSubprojection f e → f = e

/-- A central projection, expressed directly rather than through a bundled center. -/
def IsCentralProjection (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) : Prop :=
  IsProjectionIn M z ∧ ∀ a : H →L[ℂ] H, a ∈ M → a * z = z * a

/-- Fullness in the exact form used by the support-corner argument. -/
def IsFullProjection (M : VonNeumannAlgebra H) (q : H →L[ℂ] H) : Prop :=
  IsProjectionIn M q ∧
    ∀ z : H →L[ℂ] H, IsCentralProjection M z → z ≠ 0 → z * q ≠ 0

/--
Package-local central-summand finite-projection criterion: every nonzero
central summand contains a nonzero finite projection.  This is the exact
projection-form conclusion used in the manuscript; its equivalence to a
standard trace-theoretic definition of semifiniteness is not formalized here.
-/
def IsSemifinite (M : VonNeumannAlgebra H) : Prop :=
  ∀ z : H →L[ℂ] H, IsCentralProjection M z → z ≠ 0 →
    ∃ e : H →L[ℂ] H,
      IsFiniteProjection M e ∧ e ≠ 0 ∧ IsSubprojection e z

/-- Subprojection is reflexive for projections. -/
theorem isSubprojection_refl {e : H →L[ℂ] H} (he : IsStarProjection e) :
    IsSubprojection e e := by
  have hee : e * e = e := he.isIdempotentElem
  exact ⟨hee, hee⟩

/-- Subprojection is transitive. -/
lemma IsSubprojection.trans {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] {e f g : K →L[ℂ] K}
    (hef : IsSubprojection e f) (hfg : IsSubprojection f g) :
    IsSubprojection e g := by
  constructor
  · calc
      e * g = (e * f) * g := by rw [hef.1]
      _ = e * (f * g) := mul_assoc _ _ _
      _ = e * f := by rw [hfg.1]
      _ = e := hef.1
  · calc
      g * e = g * (f * e) := by rw [hef.2]
      _ = (g * f) * e := by rw [← mul_assoc]
      _ = f * e := by rw [hfg.2]
      _ = e := hef.2

/--
For bounded operators, the usual initial-projection equation in a
Murray--von Neumann witness already implies the partial-isometry equation.
We expose this bridge rather than strengthening the public definition of
Murray--von Neumann equivalence.
-/
theorem isPartialIsometry_of_star_mul_eq_projection
    {v e : H →L[ℂ] H} (he : IsStarProjection e) (h_initial : star v * v = e) :
    IsPartialIsometry v := by
  let w : H →L[ℂ] H := v - v * e
  have hw : star w * w = 0 := by
    dsimp [w]
    rw [star_sub, star_mul, he.isSelfAdjoint.star_eq]
    calc
      (star v - e * star v) * (v - v * e)
          = star v * v - (star v * v) * e - e * (star v * v) +
              e * (star v * v) * e := by
            noncomm_ring
      _ = e - e * e - e * e + e * e * e := by rw [h_initial]
      _ = 0 := by
        repeat rw [he.isIdempotentElem]
        noncomm_ring
  have hw_zero : v - v * e = 0 := by
    simpa [w] using (CStarRing.star_mul_self_eq_zero_iff w).mp hw
  have hve : v * e = v := (sub_eq_zero.mp hw_zero).symm
  calc
    v * star v * v = v * (star v * v) := mul_assoc _ _ _
    _ = v * e := by rw [h_initial]
    _ = v := hve

/-- The difference of nested projections belongs to the algebra and is a projection. -/
theorem isProjectionIn_sub_of_subprojection
    {M : VonNeumannAlgebra H} {f e : H →L[ℂ] H}
    (hf : IsProjectionIn M f) (he : IsProjectionIn M e)
    (hfe : IsSubprojection f e) :
    IsProjectionIn M (e - f) := by
  refine ⟨sub_mem he.1 hf.1, ?_⟩
  exact hf.2.sub_of_mul_eq_left he.2 hfe.1

/-- The projection `e - f` lies below `e` whenever `f` lies below `e`. -/
theorem isSubprojection_sub_of_subprojection
    {f e : H →L[ℂ] H} (he : IsStarProjection e)
    (hfe : IsSubprojection f e) :
    IsSubprojection (e - f) e := by
  have hee : e * e = e := he.isIdempotentElem
  constructor
  · calc
      (e - f) * e = e * e - f * e := sub_mul _ _ _
      _ = e - f := by rw [hee, hfe.1]
  · calc
      e * (e - f) = e * e - e * f := mul_sub _ _ _
      _ = e - f := by rw [hee, hfe.2]

/-- A central projection commutes with every member of the algebra. -/
theorem IsCentralProjection.commutes
    {M : VonNeumannAlgebra H} {z a : H →L[ℂ] H}
    (hz : IsCentralProjection M z) (ha : a ∈ M) :
    z * a = a * z :=
  (hz.2 a ha).symm

/-- Multiplying a projection by a commuting central projection yields a projection. -/
theorem central_mul_isProjectionIn
    {M : VonNeumannAlgebra H} {z q : H →L[ℂ] H}
    (hz : IsCentralProjection M z) (hq : IsProjectionIn M q) :
    IsProjectionIn M (z * q) := by
  refine ⟨mul_mem hz.1.1 hq.1, ?_⟩
  apply hz.1.2.mul hq.2
  rw [commute_iff_eq]
  exact hz.commutes hq.1

/-- A central slice `z * q` lies below the corner support `q`. -/
theorem central_mul_subprojection_right
    {M : VonNeumannAlgebra H} {z q : H →L[ℂ] H}
    (hz : IsCentralProjection M z) (hq : IsProjectionIn M q) :
    IsSubprojection (z * q) q := by
  have hqq : q * q = q := hq.2.isIdempotentElem
  have hqz : q * z = z * q := hz.2 q hq.1
  constructor
  · calc
      (z * q) * q = z * (q * q) := mul_assoc _ _ _
      _ = z * q := by rw [hqq]
  · calc
      q * (z * q) = (q * z) * q := by rw [← mul_assoc]
      _ = (z * q) * q := by rw [hqz]
      _ = z * q := by rw [mul_assoc, hqq]

/-- A central slice `z * q` lies below the central projection `z`. -/
theorem central_mul_subprojection_left
    {M : VonNeumannAlgebra H} {z q : H →L[ℂ] H}
    (hz : IsCentralProjection M z) (hq : IsProjectionIn M q) :
    IsSubprojection (z * q) z := by
  have hzz : z * z = z := hz.1.2.isIdempotentElem
  have hqz : q * z = z * q := hz.2 q hq.1
  constructor
  · calc
      (z * q) * z = z * (q * z) := mul_assoc _ _ _
      _ = z * (z * q) := by rw [hqz]
      _ = (z * z) * q := by rw [← mul_assoc]
      _ = z * q := by rw [hzz]
  · calc
      z * (z * q) = (z * z) * q := by rw [← mul_assoc]
      _ = z * q := by rw [hzz]

end FiniteFiber
