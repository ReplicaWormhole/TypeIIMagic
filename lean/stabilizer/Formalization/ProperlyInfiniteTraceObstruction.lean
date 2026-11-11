import Formalization.TraceTransport

/-!
# Algebraic obstruction to a trace on a properly infinite sector

Two isometries with orthogonal ranges summing to the identity contradict
unital cyclicity.  This is the algebraic core of the reason that an infinite
type-I factor cannot carry a tracial state.
-/

namespace StabilizerHyperfinite

variable {A : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]

/-- A unital cyclic functional cannot exist on an algebra containing two
isometries whose range projections sum to the identity. -/
theorem not_isUnitalTracial_of_two_isometries
    (tau : A →ₗ[ℂ] ℂ) (u v : A)
    (hu : star u * u = 1) (hv : star v * v = 1)
    (h_ranges : u * star u + v * star v = 1) :
    ¬ IsUnitalTracial tau := by
  intro h_tau
  have h_range_trace : tau (u * star u) + tau (v * star v) = 1 := by
    calc
      tau (u * star u) + tau (v * star v) =
          tau (u * star u + v * star v) := (tau.map_add _ _).symm
      _ = tau 1 := by rw [h_ranges]
      _ = 1 := h_tau.map_one
  rw [h_tau.cyclic u (star u), hu, h_tau.map_one,
    h_tau.cyclic v (star v), hv, h_tau.map_one] at h_range_trace
  norm_num at h_range_trace

/-- In particular, no algebraic tracial state exists under the same properly
infinite isometry hypotheses. -/
theorem not_isAlgebraicTracialState_of_two_isometries
    (tau : A →ₗ[ℂ] ℂ) (u v : A)
    (hu : star u * u = 1) (hv : star v * v = 1)
    (h_ranges : u * star u + v * star v = 1) :
    ¬ IsAlgebraicTracialState tau := by
  intro h_tau
  exact not_isUnitalTracial_of_two_isometries tau u v hu hv h_ranges
    ⟨h_tau.map_one, h_tau.cyclic⟩

end StabilizerHyperfinite
