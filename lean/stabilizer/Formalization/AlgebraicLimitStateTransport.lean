import Formalization.AlgebraicLimitStarHom

/-!
# Transporting compatible algebraic states through a quasi-local equivalence

Compatible finite-stage star-algebra equivalences transport compatible positive
states to the algebraic directed limit.  This is the non-tracial counterpart
of `AlgebraicLimitTraceTransport`: it is the appropriate interface for the
pure/mixed product state of a stabilizer coordinate decomposition.
-/

namespace StabilizerHyperfinite

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A D : ι → Type*}
variable [∀ i, Semiring (A i)] [∀ i, StarRing (A i)] [∀ i, Algebra ℂ (A i)]
variable [∀ i, Semiring (D i)] [∀ i, StarRing (D i)] [∀ i, Algebra ℂ (D i)]
variable {f : ∀ i j : ι, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable {h : ∀ i j : ι, i ≤ j → D i →⋆ₐ[ℂ] D j}
variable [DirectedSystem A (f · · ·)] [DirectedSystem D (h · · ·)]

/-- Pull back a compatible target-stage state along the star-algebra
equivalence induced by compatible finite-stage equivalences. -/
noncomputable def algebraicLimitStatePullback
    (e : ∀ i, A i ≃⋆ₐ[ℂ] D i)
    (equivCompatible : ∀ i j (le : i ≤ j) x,
      e j (f i j le x) = h i j le (e i x))
    (omega : ∀ i, D i →ₗ[ℂ] ℂ)
    (stateCompatible : ∀ i j (le : i ≤ j) x,
      omega j (h i j le x) = omega i x) :
    DirectLimit A f →ₗ[ℂ] ℂ :=
  pullback (algebraicLimitStarAlgEquiv e equivCompatible)
    (algebraicLimitTrace omega stateCompatible)

/-- The pulled-back quasi-local functional is an algebraic state whenever
each finite target-stage functional is one. -/
theorem algebraicLimitStatePullback_isAlgebraicState
    (e : ∀ i, A i ≃⋆ₐ[ℂ] D i)
    (equivCompatible : ∀ i j (le : i ≤ j) x,
      e j (f i j le x) = h i j le (e i x))
    (omega : ∀ i, D i →ₗ[ℂ] ℂ)
    (stateCompatible : ∀ i j (le : i ≤ j) x,
      omega j (h i j le x) = omega i x)
    (h_omega : ∀ i, IsAlgebraicState (omega i)) :
    IsAlgebraicState
      (algebraicLimitStatePullback e equivCompatible omega stateCompatible) :=
  isAlgebraicState_pullback (algebraicLimitStarAlgEquiv e equivCompatible)
    (algebraicLimitTrace omega stateCompatible)
    (algebraicLimitTrace_isAlgebraicState omega stateCompatible h_omega)

/-- On a finite-stage representative, the induced quasi-local state is the
target-stage state of its prescribed finite-stage image. -/
@[simp]
theorem algebraicLimitStatePullback_of
    (e : ∀ i, A i ≃⋆ₐ[ℂ] D i)
    (equivCompatible : ∀ i j (le : i ≤ j) x,
      e j (f i j le x) = h i j le (e i x))
    (omega : ∀ i, D i →ₗ[ℂ] ℂ)
    (stateCompatible : ∀ i j (le : i ≤ j) x,
      omega j (h i j le x) = omega i x)
    (i : ι) (x : A i) :
    algebraicLimitStatePullback e equivCompatible omega stateCompatible
      (DirectLimit.Module.of ℂ ι A f i x) = omega i (e i x) := by
  change algebraicLimitTrace omega stateCompatible
    (algebraicLimitStarAlgEquiv e equivCompatible
      (DirectLimit.Module.of ℂ ι A f i x)) = omega i (e i x)
  rw [algebraicLimitStarAlgEquiv_of, algebraicLimitTrace_of]

end StabilizerHyperfinite
