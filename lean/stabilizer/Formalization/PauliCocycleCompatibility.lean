import Mathlib

/-!
# Phase compatibility for Pauli-word coordinate maps

An additive symplectic coordinate map controls the commutator of Pauli words,
but it need not preserve a chosen Pauli multiplier.  This module records and
proves the two additional equations needed by a phase-corrected word map:
one for multiplication and one for the involution.  It is intentionally a
generator-level result.  Extending the map to a star-algebra equivalence still
requires a presentation or linear-basis theorem for the relevant Pauli-word
algebra.
-/

namespace StabilizerHyperfinite

section

variable {V W A : Type*}
variable [AddCommGroup V] [AddCommGroup W]
variable [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- Multiplication data for a family of Pauli words.  The multiplier records
the phase in the chosen word convention. -/
structure PauliWordMultiplication (V A : Type*) [AddCommGroup V] [Semiring A]
    [Algebra ℂ A] where
  word : V → A
  multiplier : V → V → ℂ
  word_mul : ∀ v w, word v * word w = multiplier v w • word (v + w)

/-- The involution phase belonging to a chosen Pauli-word convention. -/
structure PauliWordStarSystem (V A : Type*) [AddCommGroup V] [Semiring A]
    [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    extends PauliWordMultiplication V A where
  star_multiplier : V → ℂ
  word_star : ∀ v, star (word v) = star_multiplier v • word (-v)

namespace PauliWordStarSystem

/-- A phase-corrected image of a target Pauli word under an additive label
map. -/
def correctedWord (target : PauliWordStarSystem W A) (map : V →+ W)
    (phase : V → ℂ) (v : V) : A :=
  phase v • target.word (map v)

/-- The multiplication compatibility equation.  Symplecticity alone normally
only compares commutators; this equation compares the chosen multipliers. -/
def MultiplicationCompatible (source : PauliWordStarSystem V A)
    (target : PauliWordStarSystem W A) (map : V →+ W) (phase : V → ℂ) : Prop :=
  ∀ v w,
    phase v * phase w * target.multiplier (map v) (map w) =
      source.multiplier v w * phase (v + w)

/-- The involution compatibility equation for the same phase correction. -/
def StarCompatible (source : PauliWordStarSystem V A)
    (target : PauliWordStarSystem W A) (map : V →+ W) (phase : V → ℂ) : Prop :=
  ∀ v,
    star (phase v) * target.star_multiplier (map v) =
      source.star_multiplier v * phase (-v)

/-- Under the multiplier equation, the phase-corrected map sends the product
of two source word generators to the corresponding product of target words. -/
theorem correctedWord_mul
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W A)
    (map : V →+ W) (phase : V → ℂ)
    (h_phase : MultiplicationCompatible source target map phase) (v w : V) :
    correctedWord target map phase v * correctedWord target map phase w =
      source.multiplier v w • correctedWord target map phase (v + w) := by
  simp only [correctedWord]
  rw [smul_mul_smul, target.word_mul, smul_smul, smul_smul, map_add]
  rw [h_phase]

/-- Under the involution equation, the phase-corrected map sends the star of
a source word generator to the star of its target word. -/
theorem correctedWord_star
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W A)
    (map : V →+ W) (phase : V → ℂ)
    (h_phase : StarCompatible source target map phase) (v : V) :
    star (correctedWord target map phase v) =
      source.star_multiplier v • correctedWord target map phase (-v) := by
  simp only [correctedWord]
  rw [star_smul, target.word_star, smul_smul, smul_smul, map_neg]
  rw [h_phase]

/-- The exact generator-level certificate needed before claiming that an
adapted coordinate map lifts to a Pauli star-algebra map. -/
structure PhaseCorrectedWordMap (source : PauliWordStarSystem V A)
    (target : PauliWordStarSystem W A) where
  labelMap : V →+ W
  phase : V → ℂ
  multiplication_compatible : MultiplicationCompatible source target labelMap phase
  star_compatible : StarCompatible source target labelMap phase

theorem PhaseCorrectedWordMap.map_mul
    {source : PauliWordStarSystem V A} {target : PauliWordStarSystem W A}
    (data : PhaseCorrectedWordMap source target) (v w : V) :
    correctedWord target data.labelMap data.phase v *
        correctedWord target data.labelMap data.phase w =
      source.multiplier v w • correctedWord target data.labelMap data.phase (v + w) :=
  correctedWord_mul source target data.labelMap data.phase data.multiplication_compatible v w

theorem PhaseCorrectedWordMap.map_star
    {source : PauliWordStarSystem V A} {target : PauliWordStarSystem W A}
    (data : PhaseCorrectedWordMap source target) (v : V) :
    star (correctedWord target data.labelMap data.phase v) =
      source.star_multiplier v • correctedWord target data.labelMap data.phase (-v) :=
  correctedWord_star source target data.labelMap data.phase data.star_compatible v

end PauliWordStarSystem

end

end StabilizerHyperfinite
