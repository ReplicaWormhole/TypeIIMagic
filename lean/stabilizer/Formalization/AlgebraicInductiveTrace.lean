import Formalization.TraceTransport
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Algebraic inductive-limit trace

This module formalizes the algebraic gluing step behind an infinite tracial
product.  It deliberately stops before C⋆/von-Neumann completion, normality,
or hyperfiniteness.
-/

namespace StabilizerHyperfinite

/-- A complex-valued functional on a unital algebra which is normalized and
cyclic.  Unlike `IsAlgebraicTracialState`, this definition does not presuppose
a star or positivity, so it applies directly to mathlib's algebraic colimit. -/
structure IsUnitalCyclic {A : Type*} [MulOneClass A] (tau : A → ℂ) : Prop where
  map_one : tau 1 = 1
  cyclic : ∀ x y : A, tau (x * y) = tau (y * x)

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type*}
variable [∀ i, Semiring (A i)] [∀ i, StarRing (A i)] [∀ i, Algebra ℂ (A i)]
variable {f : ∀ i j : ι, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable [DirectedSystem A (f · · ·)]

/-- Compatible complex-linear stage traces glue to a complex-linear functional
on the algebraic direct limit. -/
noncomputable def algebraicLimitTrace (tau : ∀ i, A i →ₗ[ℂ] ℂ)
    (compatible : ∀ i j (h : i ≤ j) x, tau j (f i j h x) = tau i x) :
    DirectLimit A f →ₗ[ℂ] ℂ :=
  DirectLimit.Module.lift ℂ ι A f tau compatible

@[simp]
theorem algebraicLimitTrace_of (tau : ∀ i, A i →ₗ[ℂ] ℂ)
    (compatible : ∀ i j (h : i ≤ j) x, tau j (f i j h x) = tau i x)
    (i : ι) (x : A i) :
    algebraicLimitTrace tau compatible (DirectLimit.Module.of ℂ ι A f i x) = tau i x :=
  rfl

/-- The glued functional is uniquely determined by its restrictions to the
finite stages. -/
theorem algebraicLimitTrace_unique (tau : ∀ i, A i →ₗ[ℂ] ℂ)
    (compatible : ∀ i j (h : i ≤ j) x, tau j (f i j h x) = tau i x)
    (phi : DirectLimit A f →ₗ[ℂ] ℂ)
    (h_phi : ∀ i x, phi (DirectLimit.Module.of ℂ ι A f i x) = tau i x) :
    phi = algebraicLimitTrace tau compatible := by
  apply DirectLimit.Module.hom_ext
  intro i
  ext x
  simp only [LinearMap.comp_apply]
  rw [algebraicLimitTrace_of]
  exact h_phi i x

/-- If every finite-stage functional is unital and cyclic, their compatible
algebraic direct-limit functional is unital and cyclic. -/
theorem algebraicLimitTrace_isUnitalCyclic (tau : ∀ i, A i →ₗ[ℂ] ℂ)
    (compatible : ∀ i j (h : i ≤ j) x, tau j (f i j h x) = tau i x)
    (h_tau : ∀ i, IsUnitalCyclic (tau i)) :
    IsUnitalCyclic (algebraicLimitTrace tau compatible) := by
  constructor
  · let i : ι := Classical.arbitrary ι
    change algebraicLimitTrace tau compatible (1 : DirectLimit A f) = 1
    rw [DirectLimit.one_def i]
    exact h_tau i |>.map_one
  · intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ i x y =>
      change algebraicLimitTrace tau compatible
          ((⟦⟨i, x⟩⟧ : DirectLimit A f) * ⟦⟨i, y⟩⟧) =
        algebraicLimitTrace tau compatible
          ((⟦⟨i, y⟩⟧ : DirectLimit A f) * ⟦⟨i, x⟩⟧)
      rw [DirectLimit.mul_def, DirectLimit.mul_def]
      exact h_tau i |>.cyclic x y

end StabilizerHyperfinite
