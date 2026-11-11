import Formalization.AlgebraicLimitStarHom

/-!
# Transporting compatible traces through a quasi-local algebraic equivalence

Compatible finite-stage star-algebra equivalences induce an algebraic
quasi-local equivalence.  This module proves that a compatible tracial-state
family on the target direct system pulls back along that equivalence, with its
value on every finite-stage representative explicitly identified.
-/

namespace StabilizerHyperfinite

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A D : ι → Type*}
variable [∀ i, Semiring (A i)] [∀ i, StarRing (A i)] [∀ i, Algebra ℂ (A i)]
variable [∀ i, Semiring (D i)] [∀ i, StarRing (D i)] [∀ i, Algebra ℂ (D i)]
variable {f : ∀ i j : ι, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable {h : ∀ i j : ι, i ≤ j → D i →⋆ₐ[ℂ] D j}
variable [DirectedSystem A (f · · ·)] [DirectedSystem D (h · · ·)]

/-- Pull back a compatible target-stage trace along the star-algebra
equivalence induced by compatible finite-stage equivalences. -/
noncomputable def algebraicLimitTracePullback
    (e : ∀ i, A i ≃⋆ₐ[ℂ] D i)
    (equivCompatible : ∀ i j (le : i ≤ j) x,
      e j (f i j le x) = h i j le (e i x))
    (tau : ∀ i, D i →ₗ[ℂ] ℂ)
    (traceCompatible : ∀ i j (le : i ≤ j) x,
      tau j (h i j le x) = tau i x) :
    DirectLimit A f →ₗ[ℂ] ℂ :=
  pullback (algebraicLimitStarAlgEquiv e equivCompatible)
    (algebraicLimitTrace tau traceCompatible)

/-- The pulled-back quasi-local functional is an algebraic tracial state
whenever each finite target-stage functional is one. -/
theorem algebraicLimitTracePullback_isAlgebraicTracialState
    (e : ∀ i, A i ≃⋆ₐ[ℂ] D i)
    (equivCompatible : ∀ i j (le : i ≤ j) x,
      e j (f i j le x) = h i j le (e i x))
    (tau : ∀ i, D i →ₗ[ℂ] ℂ)
    (traceCompatible : ∀ i j (le : i ≤ j) x,
      tau j (h i j le x) = tau i x)
    (h_tau : ∀ i, IsAlgebraicTracialState (tau i)) :
    IsAlgebraicTracialState
      (algebraicLimitTracePullback e equivCompatible tau traceCompatible) :=
  isAlgebraicTracialState_pullback (algebraicLimitStarAlgEquiv e equivCompatible)
    (algebraicLimitTrace tau traceCompatible)
    (algebraicLimitTrace_isAlgebraicTracialState tau traceCompatible h_tau)

/-- On a finite-stage representative, the induced quasi-local trace is the
target-stage trace of its prescribed finite-stage image. -/
@[simp]
theorem algebraicLimitTracePullback_of
    (e : ∀ i, A i ≃⋆ₐ[ℂ] D i)
    (equivCompatible : ∀ i j (le : i ≤ j) x,
      e j (f i j le x) = h i j le (e i x))
    (tau : ∀ i, D i →ₗ[ℂ] ℂ)
    (traceCompatible : ∀ i j (le : i ≤ j) x,
      tau j (h i j le x) = tau i x)
    (i : ι) (x : A i) :
    algebraicLimitTracePullback e equivCompatible tau traceCompatible
      (DirectLimit.Module.of ℂ ι A f i x) = tau i (e i x) := by
  change algebraicLimitTrace tau traceCompatible
    (algebraicLimitStarAlgEquiv e equivCompatible
      (DirectLimit.Module.of ℂ ι A f i x)) = tau i (e i x)
  rw [algebraicLimitStarAlgEquiv_of, algebraicLimitTrace_of]

end StabilizerHyperfinite
