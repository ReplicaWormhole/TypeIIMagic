import Formalization.PauliCocycleCompatibility
import Formalization.WordBasisExtension

/-!
# From phase-corrected Pauli words to a star-algebra equivalence

The generator-level cocycle calculation and the basis-extension argument live
in separate modules.  This file joins them for source and target word systems
in potentially different algebras.  It is the precise algebraic interface for
the proposed regional star isomorphism.
-/

namespace StabilizerHyperfinite

section

variable {V W A B : Type*}
variable [AddCommGroup V] [AddCommGroup W]
variable [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
variable [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

namespace PauliWordStarSystem

/-- A phase-corrected target word, allowing source and target words to take
values in different star algebras. -/
def correctedWordBetween (target : PauliWordStarSystem W B) (map : V →+ W)
    (phase : V → ℂ) (v : V) : B :=
  phase v • target.word (map v)

/-- The multiplication equation for phase-corrected words in two distinct
algebras. -/
def MultiplicationCompatibleBetween (source : PauliWordStarSystem V A)
    (target : PauliWordStarSystem W B) (map : V →+ W) (phase : V → ℂ) : Prop :=
  ∀ v w,
    phase v * phase w * target.multiplier (map v) (map w) =
      source.multiplier v w * phase (v + w)

/-- The involution equation for phase-corrected words in two distinct
algebras. -/
def StarCompatibleBetween (source : PauliWordStarSystem V A)
    (target : PauliWordStarSystem W B) (map : V →+ W) (phase : V → ℂ) : Prop :=
  ∀ v,
    star (phase v) * target.star_multiplier (map v) =
      source.star_multiplier v * phase (-v)

/-- The multiplication equation sends every source word product to the
corresponding phase-corrected target word product. -/
theorem correctedWordBetween_mul
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W B)
    (map : V →+ W) (phase : V → ℂ)
    (h_phase : MultiplicationCompatibleBetween source target map phase)
    (v w : V) :
    correctedWordBetween target map phase v * correctedWordBetween target map phase w =
      source.multiplier v w • correctedWordBetween target map phase (v + w) := by
  simp only [correctedWordBetween]
  rw [smul_mul_smul, target.word_mul, smul_smul, smul_smul, map_add]
  rw [h_phase]

/-- The involution equation sends the star of each source word to the star of
the corresponding phase-corrected target word. -/
theorem correctedWordBetween_star
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W B)
    (map : V →+ W) (phase : V → ℂ)
    (h_phase : StarCompatibleBetween source target map phase) (v : V) :
    star (correctedWordBetween target map phase v) =
      source.star_multiplier v • correctedWordBetween target map phase (-v) := by
  simp only [correctedWordBetween]
  rw [star_smul, target.word_star, smul_smul, smul_smul, map_neg]
  rw [h_phase]

end PauliWordStarSystem

/-- A complex-linear equivalence specified on a source Pauli-word basis is a
star-algebra equivalence when its specified target words satisfy the two
phase-compatibility equations. -/
noncomputable def phaseCorrectedStarAlgEquivOfBasis
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W B)
    (labelMap : V →+ W) (phase : V → ℂ)
    (h_mul : PauliWordStarSystem.MultiplicationCompatibleBetween
      source target labelMap phase)
    (h_star : PauliWordStarSystem.StarCompatibleBetween
      source target labelMap phase)
    (map : A ≃ₗ[ℂ] B) (basis : Module.Basis V ℂ A)
    (h_basis : ∀ v, basis v = source.word v)
    (h_one : map 1 = 1)
    (h_word : ∀ v, map (source.word v) =
      PauliWordStarSystem.correctedWordBetween target labelMap phase v) :
    A ≃⋆ₐ[ℂ] B :=
  starAlgEquivOfBasis map basis h_one
    (by
      intro v w
      rw [h_basis v, h_basis w, source.word_mul, map.map_smul,
        h_word (v + w), h_word v, h_word w]
      exact (PauliWordStarSystem.correctedWordBetween_mul source target labelMap phase
        h_mul v w).symm)
    (by
      intro v
      rw [h_basis v, source.word_star, map.map_smul, h_word (-v), h_word v]
      exact (PauliWordStarSystem.correctedWordBetween_star source target labelMap phase
        h_star v).symm)

end

end StabilizerHyperfinite
