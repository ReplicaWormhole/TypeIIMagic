import Formalization.CoordinateQuadraticPhase
import Formalization.FinitePureUHFTraceTransport

/-!
# The finite-support phase map with its induced product trace

This module joins the concrete finite-support quadratic phase construction to
the finite-pure times qubit-UHF product trace.  Its hypotheses are exactly the
regional word-system and basis data that remain to be supplied by the target
operator-algebra model.
-/

namespace StabilizerHyperfinite

open scoped TensorProduct

/-- Once the regional Pauli-word data identify the finite-support phase map
with a word-basis linear equivalence, the resulting star-algebra equivalence
induces the finite-pure times qubit-UHF algebraic tracial state. -/
theorem exists_coordinateQuadraticPhase_finitePureQubitUHFTrace
    {ι A p W : Type*} [LinearOrder ι] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Fintype p] [DecidableEq p] [Nonempty p]
    (discrepancy : ι → ι → ZMod 2)
    (hsymm : ∀ i j, discrepancy i j = discrepancy j i)
    (source : PauliWordStarSystem (ι →₀ ZMod 2) A)
    (target : PauliWordStarSystem W
      (Matrix p p ℂ ⊗[ℂ] QubitUHFAlgebra))
    (labelMap : (ι →₀ ZMod 2) →+ W)
    (sourceExponent : (ι →₀ ZMod 2) → (ι →₀ ZMod 2) → ZMod 4)
    (targetExponent : W → W → ZMod 4)
    (sourceDiag : (ι →₀ ZMod 2) → ZMod 4) (targetDiag : W → ZMod 4)
    (h_source_mul : ∀ v w, source.multiplier v w =
      zmodFourPhase (2 * sourceExponent v w))
    (h_target_mul : ∀ v w, target.multiplier v w =
      zmodFourPhase (2 * targetExponent v w))
    (h_pair : ∀ v w, coordinateBilinear discrepancy v w =
      2 * (sourceExponent v w + targetExponent (labelMap v) (labelMap w)))
    (h_source_star : ∀ v, source.star_multiplier v =
      zmodFourPhase (2 * sourceDiag v))
    (h_target_star : ∀ w, target.star_multiplier w =
      zmodFourPhase (2 * targetDiag w))
    (h_diag : ∀ v, coordinateBilinear discrepancy v v =
      2 * (sourceDiag v + targetDiag (labelMap v)))
    (wordMap : A ≃ₗ[ℂ] (Matrix p p ℂ ⊗[ℂ] QubitUHFAlgebra))
    (basis : Module.Basis (ι →₀ ZMod 2) ℂ A)
    (h_basis : ∀ v, basis v = source.word v)
    (h_one : wordMap 1 = 1)
    (h_word : ∀ v, wordMap (source.word v) =
      PauliWordStarSystem.correctedWordBetween target labelMap
        (fun v => zmodFourPhase (coordinateQuadraticRefinement discrepancy v)) v) :
    ∃ e : A ≃⋆ₐ[ℂ] (Matrix p p ℂ ⊗[ℂ] QubitUHFAlgebra),
      ∃ tau : A →ₗ[ℂ] ℂ, IsAlgebraicTracialState tau ∧
        ∀ a u, tau (e.symm (a ⊗ₜ[ℂ] u)) =
          normalizedMatrixTrace p a * qubitUHFTrace u := by
  let e := coordinateQuadraticPhaseStarAlgEquivOfBasis discrepancy hsymm source target
    labelMap sourceExponent targetExponent sourceDiag targetDiag h_source_mul h_target_mul
    h_pair h_source_star h_target_star h_diag wordMap basis h_basis h_one h_word
  refine ⟨e, ?_⟩
  exact exists_finitePureQubitUHFInducedTrace e

end StabilizerHyperfinite
