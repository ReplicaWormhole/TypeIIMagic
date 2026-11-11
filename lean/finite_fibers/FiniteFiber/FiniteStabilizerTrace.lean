import FiniteFiber.FiniteStabilizer
import Mathlib.LinearAlgebra.Trace

/-!
# Trace and nonzero support for finite stabilizer averages

The manuscript computes the trace of a local stabilizer average by using that
every nonidentity Pauli stabilizer is traceless.  This file formalizes that
finite-dimensional calculation at the exact abstraction level it uses: a
finite-dimensional represented group with a supplied tracelessness condition
away from the identity.

It deliberately does not prove the Pauli tensor-product tracelessness fact or
the qubit-dimension identity.  Those are separate realization obligations.
-/

namespace FiniteFiber

open scoped BigOperators

variable {H G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [FiniteDimensional ℂ H] [Fintype G] [Group G]

/-- The finite-dimensional operator trace used for local stabilizer supports. -/
noncomputable def finiteGroupOperatorTrace (T : H →L[ℂ] H) : ℂ :=
  LinearMap.trace ℂ H T.toLinearMap

/--
If all nonidentity represented stabilizers are traceless, the group average
has trace `finrank / |G|`.
-/
theorem SelfAdjointFiniteGroupAction.average_trace
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G))
    (htraceless : ∀ g : G, g ≠ 1 → finiteGroupOperatorTrace (A.representation g) = 0) :
    finiteGroupOperatorTrace A.average =
      (Fintype.card G : ℂ)⁻¹ * (Module.finrank ℂ H : ℂ) := by
  rw [SelfAdjointFiniteGroupAction.average]
  unfold finiteGroupOperatorTrace
  have hto : ((Fintype.card G : ℂ)⁻¹ • ∑ g : G, A.representation g).toLinearMap =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (A.representation g).toLinearMap := by
    ext x
    simp
  rw [hto, map_smul, map_sum]
  have hsum : ∑ g : G, (LinearMap.trace ℂ H) (A.representation g).toLinearMap =
      (Module.finrank ℂ H : ℂ) := by
    rw [Finset.sum_eq_single (1 : G)]
    · change finiteGroupOperatorTrace (A.representation 1) = _
      rw [A.representation.map_one]
      change (LinearMap.trace ℂ H) (1 : H →ₗ[ℂ] H) = _
      rw [LinearMap.trace_one]
    · intro b _ hb
      change finiteGroupOperatorTrace (A.representation b) = 0
      exact htraceless b hb
    · simp
  rw [hsum]
  rfl

/--
A nonzero finite-dimensional local Hilbert space and the tracelessness
condition make the local stabilizer support nonzero.
-/
theorem SelfAdjointFiniteGroupAction.average_ne_zero_of_traceless
    (A : SelfAdjointFiniteGroupAction (H := H) (G := G))
    (hdim : Module.finrank ℂ H ≠ 0)
    (htraceless : ∀ g : G, g ≠ 1 → finiteGroupOperatorTrace (A.representation g) = 0) :
    A.average ≠ 0 := by
  intro havg_zero
  have havg_trace := A.average_trace htraceless
  rw [havg_zero] at havg_trace
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hdim' : (Module.finrank ℂ H : ℂ) ≠ 0 := by
    exact_mod_cast hdim
  have hright : (Fintype.card G : ℂ)⁻¹ * (Module.finrank ℂ H : ℂ) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hcard) hdim'
  apply hright
  simpa [finiteGroupOperatorTrace] using havg_trace.symm

end FiniteFiber
