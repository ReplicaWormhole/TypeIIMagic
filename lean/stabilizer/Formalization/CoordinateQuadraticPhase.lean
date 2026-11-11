import Formalization.FiniteSupportQuadraticRefinement

/-!
# Concrete finite-support quadratic phases

This module instantiates the abstract quadratic-phase compatibility theorems
with the explicitly constructed finite-support refinement.  The remaining
inputs identify the source and target Pauli exponents and diagonal involution
phases with the concrete coordinate discrepancy pairing.
-/

namespace StabilizerHyperfinite

theorem coordinateQuadraticPhase_multiplicationCompatibleBetween
    {ι W A B : Type*} [LinearOrder ι] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (discrepancy : ι → ι → ZMod 2)
    (hsymm : ∀ i j, discrepancy i j = discrepancy j i)
    (source : PauliWordStarSystem (ι →₀ ZMod 2) A)
    (target : PauliWordStarSystem W B) (labelMap : (ι →₀ ZMod 2) →+ W)
    (sourceExponent : (ι →₀ ZMod 2) → (ι →₀ ZMod 2) → ZMod 4)
    (targetExponent : W → W → ZMod 4)
    (h_source : ∀ v w, source.multiplier v w =
      zmodFourPhase (2 * sourceExponent v w))
    (h_target : ∀ v w, target.multiplier v w =
      zmodFourPhase (2 * targetExponent v w))
    (h_pair : ∀ v w, coordinateBilinear discrepancy v w =
      2 * (sourceExponent v w + targetExponent (labelMap v) (labelMap w))) :
    PauliWordStarSystem.MultiplicationCompatibleBetween source target labelMap
      (fun v => zmodFourPhase (coordinateQuadraticRefinement discrepancy v)) := by
  apply quadraticPhase_multiplicationCompatibleBetween source target labelMap
    (coordinateQuadraticRefinement discrepancy) sourceExponent targetExponent h_source h_target
  intro v w
  calc
    coordinateQuadraticRefinement discrepancy (v + w) =
        coordinateQuadraticRefinement discrepancy v +
          coordinateQuadraticRefinement discrepancy w +
            coordinateBilinear discrepancy v w :=
      coordinateQuadraticRefinement_polarization discrepancy hsymm v w
    _ = coordinateQuadraticRefinement discrepancy v +
          coordinateQuadraticRefinement discrepancy w +
            2 * (sourceExponent v w + targetExponent (labelMap v) (labelMap w)) := by
      rw [h_pair]

theorem coordinateQuadraticPhase_starCompatibleBetween
    {ι W A B : Type*} [LinearOrder ι] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (discrepancy : ι → ι → ZMod 2)
    (hsymm : ∀ i j, discrepancy i j = discrepancy j i)
    (source : PauliWordStarSystem (ι →₀ ZMod 2) A)
    (target : PauliWordStarSystem W B) (labelMap : (ι →₀ ZMod 2) →+ W)
    (sourceDiag : (ι →₀ ZMod 2) → ZMod 4) (targetDiag : W → ZMod 4)
    (h_source : ∀ v, source.star_multiplier v =
      zmodFourPhase (2 * sourceDiag v))
    (h_target : ∀ w, target.star_multiplier w =
      zmodFourPhase (2 * targetDiag w))
    (h_diag : ∀ v, coordinateBilinear discrepancy v v =
      2 * (sourceDiag v + targetDiag (labelMap v))) :
    PauliWordStarSystem.StarCompatibleBetween source target labelMap
      (fun v => zmodFourPhase (coordinateQuadraticRefinement discrepancy v)) := by
  apply quadraticPhase_starCompatibleBetween source target labelMap
    (coordinateQuadraticRefinement discrepancy) sourceDiag targetDiag h_source h_target
  intro v
  calc
    2 * coordinateQuadraticRefinement discrepancy v = coordinateBilinear discrepancy v v :=
      two_coordinateQuadraticRefinement discrepancy hsymm v
    _ = 2 * (sourceDiag v + targetDiag (labelMap v)) := h_diag v

/-- The concrete finite-support phase gives a star-algebra equivalence when
the actual Pauli exponents, diagonal phases, and word-basis linear equivalence
are supplied. -/
noncomputable def coordinateQuadraticPhaseStarAlgEquivOfBasis
    {ι W A B : Type*} [LinearOrder ι] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (discrepancy : ι → ι → ZMod 2)
    (hsymm : ∀ i j, discrepancy i j = discrepancy j i)
    (source : PauliWordStarSystem (ι →₀ ZMod 2) A)
    (target : PauliWordStarSystem W B) (labelMap : (ι →₀ ZMod 2) →+ W)
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
    (wordMap : A ≃ₗ[ℂ] B) (basis : Module.Basis (ι →₀ ZMod 2) ℂ A)
    (h_basis : ∀ v, basis v = source.word v)
    (h_one : wordMap 1 = 1)
    (h_word : ∀ v, wordMap (source.word v) =
      PauliWordStarSystem.correctedWordBetween target labelMap
        (fun v => zmodFourPhase (coordinateQuadraticRefinement discrepancy v)) v) :
    A ≃⋆ₐ[ℂ] B :=
  phaseCorrectedStarAlgEquivOfBasis source target labelMap
    (fun v => zmodFourPhase (coordinateQuadraticRefinement discrepancy v))
    (coordinateQuadraticPhase_multiplicationCompatibleBetween discrepancy hsymm source target
      labelMap sourceExponent targetExponent h_source_mul h_target_mul h_pair)
    (coordinateQuadraticPhase_starCompatibleBetween discrepancy hsymm source target labelMap
      sourceDiag targetDiag h_source_star h_target_star h_diag)
    wordMap basis h_basis h_one h_word

end StabilizerHyperfinite
