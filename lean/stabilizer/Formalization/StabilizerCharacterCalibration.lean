import Formalization.PauliCocycleCompatibility

/-!
# Calibrating Pauli phases by stabilizer signs

Pauli labels determine operators only up to phase.  On an isotropic
stabilizer-label subspace, the actual stabilizer signs form a multiplier
character.  This module proves the algebraic cancellation used to calibrate a
coordinate phase correction to those signs.
-/

namespace StabilizerHyperfinite

section

variable {V : Type*} [AddCommMonoid V]

/-- A phase convention compatible with a Pauli multiplier. -/
def IsPauliMultiplierCharacter (multiplier : V → V → Units ℂ)
    (phase : V → Units ℂ) : Prop :=
  ∀ v w, phase v * phase w * multiplier v w = phase (v + w)

/-- The quotient of two phase conventions.  When both have the same multiplier,
this quotient is an ordinary additive character. -/
def quotientPhase (first second : V → Units ℂ) (v : V) : Units ℂ :=
  first v * (second v)⁻¹

/-- Quotienting two solutions of the same multiplier relation cancels the
multiplier and yields a character of the additive label monoid. -/
theorem quotientPhase_mul
    (multiplier : V → V → Units ℂ) (first second : V → Units ℂ)
    (h_first : IsPauliMultiplierCharacter multiplier first)
    (h_second : IsPauliMultiplierCharacter multiplier second) (v w : V) :
    quotientPhase first second (v + w) =
      quotientPhase first second v * quotientPhase first second w := by
  unfold quotientPhase
  rw [← h_first v w, ← h_second v w]
  group
  ac_rfl

/-- Multiply a multiplier phase by an ordinary character. -/
def calibratePhase (phase character : V → Units ℂ) (v : V) : Units ℂ :=
  character v * phase v

/-- Calibration by an additive character preserves the multiplier relation. -/
theorem calibratePhase_isPauliMultiplierCharacter
    (multiplier : V → V → Units ℂ) (phase character : V → Units ℂ)
    (h_phase : IsPauliMultiplierCharacter multiplier phase)
    (h_character : ∀ v w, character (v + w) = character v * character w) :
    IsPauliMultiplierCharacter multiplier (calibratePhase phase character) := by
  intro v w
  unfold calibratePhase
  rw [h_character v w, ← h_phase v w]
  group
  ac_rfl

end

/-- Calibrating the second phase by its quotient with the first recovers the
first phase pointwise. -/
theorem calibratePhase_quotientPhase
    {V : Type*} (first second : V → Units ℂ) (v : V) :
    calibratePhase second (quotientPhase first second) v = first v := by
  unfold calibratePhase quotientPhase
  group

/-- Extend an additive character on a subspace by declaring it trivial on a
chosen complementary subspace. -/
noncomputable def extendCharacterAlongComplement
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W Q : Submodule K V) (h_compl : IsCompl W Q)
    (character : W → Units ℂ) : V → Units ℂ :=
  fun v => character (W.linearProjOfIsCompl Q h_compl v)

/-- The extension along a complement is multiplicative for addition whenever
the original phase is. -/
theorem extendCharacterAlongComplement_mul
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W Q : Submodule K V) (h_compl : IsCompl W Q)
    (character : W → Units ℂ)
    (h_character : ∀ u v, character (u + v) = character u * character v)
    (v w : V) :
    extendCharacterAlongComplement W Q h_compl character (v + w) =
      extendCharacterAlongComplement W Q h_compl character v *
        extendCharacterAlongComplement W Q h_compl character w := by
  unfold extendCharacterAlongComplement
  rw [map_add, h_character]

/-- The extension along a complement restricts to the original character. -/
theorem extendCharacterAlongComplement_apply_subtype
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W Q : Submodule K V) (h_compl : IsCompl W Q)
    (character : W → Units ℂ) (w : W) :
    extendCharacterAlongComplement W Q h_compl character (w : V) = character w := by
  unfold extendCharacterAlongComplement
  rw [Submodule.linearProjOfIsCompl_apply_left h_compl w]

/-- Every additive character on a vector subspace extends to an additive
character on the ambient vector space.  In particular, this applies to the
finite-support Pauli-label spaces over `ZMod 2`. -/
theorem exists_extend_submodule_character
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (character : W → Units ℂ)
    (h_character : ∀ u v, character (u + v) = character u * character v) :
    ∃ extension : V → Units ℂ,
      (∀ v w, extension (v + w) = extension v * extension w) ∧
        ∀ w : W, extension (w : V) = character w := by
  obtain ⟨Q, h_compl⟩ := W.exists_isCompl
  refine ⟨extendCharacterAlongComplement W Q h_compl character, ?_, ?_⟩
  · exact extendCharacterAlongComplement_mul W Q h_compl character h_character
  · exact extendCharacterAlongComplement_apply_subtype W Q h_compl character

/-- Every vector in a module over the Pauli bit field has additive order at
most two. -/
theorem pauliBit_add_self_eq_zero
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (v : V) : v + v = 0 := by
  calc
    v + v = (2 : ZMod 2) • v := (two_smul (ZMod 2) v).symm
    _ = 0 := by
      change ((2 : ℕ) : ZMod 2) • v = 0
      rw [ZMod.natCast_self 2, zero_smul]

/-- An additive character into complex units is normalized at the zero label. -/
theorem additive_character_zero
    {V : Type*} [AddCommMonoid V] (character : V → Units ℂ)
    (h_character : ∀ u v, character (u + v) = character u * character v) :
    character 0 = 1 := by
  have h_zero : character 0 = character 0 * character 0 := by
    simpa using h_character 0 0
  calc
    character 0 = (character 0)⁻¹ * (character 0 * character 0) := by group
   _ = (character 0)⁻¹ * character 0 := by rw [← h_zero]
   _ = 1 := inv_mul_cancel _

/-- An additive character of a Pauli-bit vector space has order at most two
at every label. -/
theorem additive_character_pauliBit_mul_self
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (character : V → Units ℂ)
    (h_character : ∀ u v, character (u + v) = character u * character v)
    (v : V) : character v * character v = 1 := by
  calc
   character v * character v = character (v + v) := (h_character v v).symm
   _ = character 0 := by rw [pauliBit_add_self_eq_zero v]
   _ = 1 := additive_character_zero character h_character

/-- Such an order-two complex phase is fixed by complex conjugation. -/
theorem additive_character_pauliBit_star
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (character : V → Units ℂ)
    (h_character : ∀ u v, character (u + v) = character u * character v)
    (v : V) : star (character v : ℂ) = character v := by
  have h_square : (character v : ℂ) * character v = 1 := by
    have h_unit := additive_character_pauliBit_mul_self character h_character v
    simpa using congrArg (fun u : Units ℂ => (u : ℂ)) h_unit
  rcases mul_self_eq_one_iff.mp h_square with h_one | h_neg_one
  · rw [h_one]
    simp
  · calc
      star (character v : ℂ) = star (-1) := by rw [h_neg_one]
      _ = -1 := by simp
      _ = character v := h_neg_one.symm

/-- Calibrating a Pauli phase by an additive character preserves the
multiplication-compatibility equation. -/
theorem calibratePhase_multiplicationCompatible
    {V W A : Type*} [AddCommGroup V] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W A)
    (map : V →+ W) (phase : V → ℂ) (character : V → Units ℂ)
    (h_phase : PauliWordStarSystem.MultiplicationCompatible source target map phase)
    (h_character : ∀ u v, character (u + v) = character u * character v) :
    PauliWordStarSystem.MultiplicationCompatible source target map
      (fun v => (character v : ℂ) * phase v) := by
  intro v w
  have h_character_complex : (character (v + w) : ℂ) =
      (character v : ℂ) * character w := by
    simpa using congrArg (fun u : Units ℂ => (u : ℂ)) (h_character v w)
  calc
    ((character v : ℂ) * phase v) * ((character w : ℂ) * phase w) *
        target.multiplier (map v) (map w) =
        ((character v : ℂ) * character w) *
          (phase v * phase w * target.multiplier (map v) (map w)) := by
            ring
    _ = ((character v : ℂ) * character w) *
          (source.multiplier v w * phase (v + w)) := by
            rw [h_phase v w]
    _ = source.multiplier v w * ((character (v + w) : ℂ) * phase (v + w)) := by
            rw [h_character_complex]
            ring

/-- Calibrating a Pauli phase by a Pauli-bit character preserves the
involution-compatibility equation. -/
theorem calibratePhase_starCompatible
    {V W A : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W A)
    (map : V →+ W) (phase : V → ℂ) (character : V → Units ℂ)
    (h_phase : PauliWordStarSystem.StarCompatible source target map phase)
    (h_character : ∀ u v, character (u + v) = character u * character v) :
    PauliWordStarSystem.StarCompatible source target map
      (fun v => (character v : ℂ) * phase v) := by
  intro v
  have h_neg : -v = v := by
    exact neg_eq_of_add_eq_zero_right (pauliBit_add_self_eq_zero v)
  rw [h_neg, star_mul, additive_character_pauliBit_star character h_character]
  calc
    (star (phase v) * (character v : ℂ)) * target.star_multiplier (map v) =
        (character v : ℂ) * (star (phase v) * target.star_multiplier (map v)) := by
          ring
    _ = (character v : ℂ) * (source.star_multiplier v * phase v) := by
          rw [h_phase v, h_neg]
    _ = source.star_multiplier v * ((character v : ℂ) * phase v) := by
          ring

end StabilizerHyperfinite
