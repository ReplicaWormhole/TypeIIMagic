import FiniteFiber.Basic

/-!
# Faithful tracial corners make their subprojections finite

The functional below is intentionally corner-scoped.  A later GNS/stabilizer
layer must prove that its compressed vector state supplies this interface.
-/

namespace FiniteFiber

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An element of the corner `q M q`, represented in the ambient operator algebra. -/
def IsCornerElement (M : VonNeumannAlgebra H) (q a : H →L[ℂ] H) : Prop :=
  a ∈ M ∧ q * a = a ∧ a * q = a

/--
A complex-linear extension of a functional on `q M q`, tracial only when both
arguments are corner elements and faithful on projections below `q`.  A
faithful positive tracial state on the corner gives this data by compression.
Normality is not used by the algebraic finiteness proof.
-/
structure FaithfulTracialCorner (M : VonNeumannAlgebra H) (q : H →L[ℂ] H) where
  tau : (H →L[ℂ] H) →ₗ[ℂ] ℂ
  tracial : ∀ {a b : H →L[ℂ] H},
    IsCornerElement M q a → IsCornerElement M q b → tau (a * b) = tau (b * a)
  faithful_on_subprojection :
    ∀ r : H →L[ℂ] H, IsProjectionIn M r → IsSubprojection r q → tau r = 0 → r = 0

/--
An equivalence witness between projections below `q` is itself supported by
the corner.  This is the algebraic bridge used before applying corner
traciality.
-/
theorem mvN_witness_in_corner
    {M : VonNeumannAlgebra H} {q e f v : H →L[ℂ] H}
    (hv : v ∈ M) (hv_partial : IsPartialIsometry v)
    (hv_initial : star v * v = e) (hv_final : v * star v = f)
    (heq : IsSubprojection e q) (hfe : IsSubprojection f e) :
    IsCornerElement M q v ∧ IsCornerElement M q (star v) := by
  have hfeq : IsSubprojection f q := hfe.trans heq
  have hv_right_e : v * e = v := by
    calc
      v * e = v * (star v * v) := by rw [hv_initial]
      _ = (v * star v) * v := by rw [← mul_assoc]
      _ = v := hv_partial
  have hv_left_f : f * v = v := by
    calc
      f * v = (v * star v) * v := by rw [hv_final]
      _ = v := hv_partial
  have hstar_partial : star v * v * star v = star v := by
    simpa only [star_mul, star_star] using congrArg star hv_partial
  have hstar_left_e : e * star v = star v := by
    calc
      e * star v = (star v * v) * star v := by rw [hv_initial]
      _ = star v := hstar_partial
  have hstar_right_f : star v * f = star v := by
    calc
      star v * f = star v * (v * star v) := by rw [hv_final]
      _ = star v * v * star v := by rw [← mul_assoc]
      _ = star v := hstar_partial
  constructor
  · refine ⟨hv, ?_, ?_⟩
    · calc
        q * v = q * (f * v) := by rw [hv_left_f]
        _ = (q * f) * v := by rw [← mul_assoc]
        _ = f * v := by rw [hfeq.2]
        _ = v := hv_left_f
    · calc
        v * q = (v * e) * q := by rw [hv_right_e]
        _ = v * (e * q) := mul_assoc _ _ _
        _ = v * e := by rw [heq.1]
        _ = v := hv_right_e
  · refine ⟨star_mem hv, ?_, ?_⟩
    · calc
        q * star v = q * (e * star v) := by rw [hstar_left_e]
        _ = (q * e) * star v := by rw [← mul_assoc]
        _ = e * star v := by rw [heq.2]
        _ = star v := hstar_left_e
    · calc
        star v * q = (star v * f) * q := by rw [hstar_right_f]
        _ = star v * (f * q) := mul_assoc _ _ _
        _ = star v * f := by rw [hfeq.1]
        _ = star v := hstar_right_f

/-- Every projection below the support of a faithful tracial corner is finite. -/
theorem finite_of_subprojection_of_faithful_tracial_corner
    {M : VonNeumannAlgebra H} {q e : H →L[ℂ] H}
    (T : FaithfulTracialCorner M q)
    (he : IsProjectionIn M e) (heq : IsSubprojection e q) :
    IsFiniteProjection M e := by
  refine ⟨he, ?_⟩
  intro f hf hef hfe
  obtain ⟨v, hv, hv_initial, hv_final⟩ := hef
  have hv_partial : IsPartialIsometry v :=
    isPartialIsometry_of_star_mul_eq_projection he.2 hv_initial
  have hdiff : IsProjectionIn M (e - f) :=
    isProjectionIn_sub_of_subprojection hf he hfe
  have hdiff_e : IsSubprojection (e - f) e :=
    isSubprojection_sub_of_subprojection he.2 hfe
  have hdiff_q : IsSubprojection (e - f) q := hdiff_e.trans heq
  obtain ⟨hv_corner, hstarv_corner⟩ :=
    mvN_witness_in_corner hv hv_partial hv_initial hv_final heq hfe
  have htrace_zero : T.tau (e - f) = 0 := by
    calc
      T.tau (e - f) = T.tau e - T.tau f := T.tau.map_sub e f
      _ = T.tau (star v * v) - T.tau (v * star v) := by rw [hv_initial, hv_final]
      _ = 0 := sub_eq_zero.mpr (T.tracial hstarv_corner hv_corner)
  have hdiff_zero : e - f = 0 :=
    T.faithful_on_subprojection (e - f) hdiff hdiff_q htrace_zero
  exact (sub_eq_zero.mp hdiff_zero).symm

end FiniteFiber
