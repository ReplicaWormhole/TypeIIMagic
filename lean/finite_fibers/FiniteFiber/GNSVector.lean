import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Canonical vector in the GNS representation

Mathlib constructs the GNS Hilbert space and star representation from a
positive linear functional, but leaves the explicit cyclic-vector
state-reconstruction statement as future work.  This file supplies the
elementary vector and its matrix-coefficient identity.  It does not construct
the quasilocal algebra, prove a particular finite-volume state is positive, or
establish the regional product-orbit hypotheses used by the support-corner
theorem.
-/

namespace FiniteFiber

open scoped ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The image of the unit in the GNS completion. -/
noncomputable def gnsCyclicVector (f : A →ₚ[ℂ] ℂ) : f.GNS :=
  (f.toPreGNS 1 : f.GNS)

/-- Acting on the canonical vector embeds the corresponding pre-GNS vector. -/
theorem gnsStarAlgHom_apply_gnsCyclicVector
    (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (gnsCyclicVector f) = (f.toPreGNS a : f.GNS) := by
  simp [gnsCyclicVector]

/-- A vanishing GNS norm deviation fixes the canonical vector. -/
theorem gnsStarAlgHom_apply_gnsCyclicVector_eq_of_deviation_eq_zero
    (f : A →ₚ[ℂ] ℂ) (a : A)
    (hzero : f (star (a - 1) * (a - 1)) = 0) :
    f.gnsStarAlgHom a (gnsCyclicVector f) = gnsCyclicVector f := by
  rw [gnsStarAlgHom_apply_gnsCyclicVector]
  apply sub_eq_zero.mp
  change (↑(f.toPreGNS a) : f.GNS) - ↑(f.toPreGNS 1) = 0
  rw [← UniformSpace.Completion.coe_sub, ← map_sub]
  apply norm_eq_zero.mp
  apply (sq_eq_zero_iff).mp
  rw [UniformSpace.Completion.norm_coe]
  rw [PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [hzero]
  norm_num

/-- The canonical GNS vector is cyclic for the represented algebra. -/
theorem denseRange_gnsStarAlgHom_apply_gnsCyclicVector
    (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsCyclicVector f)) := by
  rw [show (fun a : A => f.gnsStarAlgHom a (gnsCyclicVector f)) =
    (fun a : A => (f.toPreGNS a : f.GNS)) from
      funext fun a => gnsStarAlgHom_apply_gnsCyclicVector f a]
  exact DenseRange.comp (g := fun x : f.PreGNS => (x : f.GNS))
    (f := f.toPreGNS) UniformSpace.Completion.denseRange_coe
      f.toPreGNS.surjective.denseRange
      (UniformSpace.Completion.continuous_coe f.PreGNS)

/-- The GNS matrix coefficient of the canonical vector reconstructs the functional. -/
theorem inner_gnsCyclicVector_gnsStarAlgHom_apply
    (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪gnsCyclicVector f, f.gnsStarAlgHom a (gnsCyclicVector f)⟫_ℂ = f a := by
  simp [gnsCyclicVector, PositiveLinearMap.preGNS_inner_def]

/-- A normalized positive functional gives a unit canonical GNS vector. -/
theorem norm_gnsCyclicVector_eq_one
    (f : A →ₚ[ℂ] ℂ) (hunit : f 1 = 1) :
    ‖gnsCyclicVector f‖ = 1 := by
  have hinner : ⟪gnsCyclicVector f, gnsCyclicVector f⟫_ℂ = 1 := by
    simpa [hunit] using inner_gnsCyclicVector_gnsStarAlgHom_apply f (1 : A)
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [@norm_sq_eq_re_inner ℂ, hinner]
  norm_num

end FiniteFiber
