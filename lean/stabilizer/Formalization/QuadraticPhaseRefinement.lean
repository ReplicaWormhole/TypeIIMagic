import Formalization.StabilizerCharacterCalibration
import Formalization.PhaseCorrectedWordBasisEquiv

/-!
# Quadratic Pauli phase refinements

This module turns a ZMod 4-valued quadratic refinement into the phase
identities required by the Pauli-word compatibility certificate.  The
remaining input is the proof that the finite-support coordinate formula has
the required polarization and diagonal identities.
-/

namespace StabilizerHyperfinite

/-- The fourth-root phase associated with an exponent modulo four. -/
def zmodFourPhase (q : ZMod 4) : ℂ :=
  Complex.I ^ q.val

/-- Fourth-root phases multiply according to addition modulo four. -/
theorem zmodFourPhase_add (a b : ZMod 4) :
    zmodFourPhase (a + b) = zmodFourPhase a * zmodFourPhase b := by
  fin_cases a
  all_goals fin_cases b
  all_goals simp only [zmodFourPhase, ZMod.val_add]
  all_goals norm_num [ZMod.val, pow_succ, Complex.I_mul_I]

/-- Complex conjugation negates the fourth-root exponent. -/
theorem star_zmodFourPhase (a : ZMod 4) :
    star (zmodFourPhase a) = zmodFourPhase (-a) := by
  apply mul_right_cancel₀ (b := zmodFourPhase a)
  · unfold zmodFourPhase
    exact pow_ne_zero _ Complex.I_ne_zero
  · have h_star_mul : star (zmodFourPhase a) * zmodFourPhase a = 1 := by
      unfold zmodFourPhase
      rw [star_pow]
      rw [← mul_pow]
      have h_i : star (Complex.I) * Complex.I = 1 := by
        have h_star_i : star Complex.I = -Complex.I := by
          simpa only [Complex.star_def] using Complex.conj_I
        rw [h_star_i, neg_mul, Complex.I_mul_I, neg_neg]
      rw [h_i, one_pow]
    calc
      star (zmodFourPhase a) * zmodFourPhase a = 1 := h_star_mul
      _ = zmodFourPhase (a + -a) := by simp [zmodFourPhase]
      _ = zmodFourPhase (-a) * zmodFourPhase a :=
        (zmodFourPhase_add a (-a)).trans (mul_comm _ _)

/-- The diagonal parity equation is exactly the exponent identity needed by
the Pauli involution compatibility condition. -/
theorem zmodFour_star_exponent
    (q sourceDiag targetDiag : ZMod 4)
    (h_diag : 2 * q = 2 * (sourceDiag + targetDiag)) :
    -q + 2 * targetDiag = 2 * sourceDiag + q := by
  have h_four : sourceDiag * 4 = 0 := by
    change sourceDiag * ((4 : ℕ) : ZMod 4) = 0
    rw [ZMod.natCast_self 4, mul_zero]
  linear_combination -h_diag - h_four

/-- A quadratic refinement with the stated polarization makes its fourth-root
phase satisfy the Pauli multiplication compatibility equation. -/
theorem quadraticPhase_multiplicationCompatible
    {V W A : Type*} [AddCommGroup V] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W A)
    (map : V →+ W) (q : V → ZMod 4)
    (sourceExponent : V → V → ZMod 4) (targetExponent : W → W → ZMod 4)
    (h_source : ∀ v w, source.multiplier v w =
      zmodFourPhase (2 * sourceExponent v w))
    (h_target : ∀ v w, target.multiplier v w =
      zmodFourPhase (2 * targetExponent v w))
    (h_q : ∀ v w, q (v + w) =
      q v + q w + 2 * (sourceExponent v w + targetExponent (map v) (map w))) :
    PauliWordStarSystem.MultiplicationCompatible source target map
      (fun v => zmodFourPhase (q v)) := by
  intro v w
  rw [h_target, h_source]
  change zmodFourPhase (q v) * zmodFourPhase (q w) *
      zmodFourPhase (2 * targetExponent (map v) (map w)) =
    zmodFourPhase (2 * sourceExponent v w) * zmodFourPhase (q (v + w))
  have h_four : sourceExponent v w * 4 = 0 := by
    change sourceExponent v w * ((4 : ℕ) : ZMod 4) = 0
    rw [ZMod.natCast_self 4, mul_zero]
  calc
    zmodFourPhase (q v) * zmodFourPhase (q w) *
        zmodFourPhase (2 * targetExponent (map v) (map w)) =
      zmodFourPhase (q v + q w) *
        zmodFourPhase (2 * targetExponent (map v) (map w)) := by
          rw [zmodFourPhase_add]
    _ = zmodFourPhase
        (q v + q w + 2 * targetExponent (map v) (map w)) :=
          (zmodFourPhase_add _ _).symm
    _ = zmodFourPhase
        (2 * sourceExponent v w + q (v + w)) := by
          congr 1
          rw [h_q]
          linear_combination -h_four
    _ = zmodFourPhase (2 * sourceExponent v w) *
        zmodFourPhase (q (v + w)) :=
          zmodFourPhase_add _ _

/-- The diagonal identity of a quadratic refinement gives the Pauli
involution-compatibility equation. -/
theorem quadraticPhase_starCompatible
    {V W A : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W A)
    (map : V →+ W) (q : V → ZMod 4)
    (sourceDiag : V → ZMod 4) (targetDiag : W → ZMod 4)
    (h_source : ∀ v, source.star_multiplier v =
      zmodFourPhase (2 * sourceDiag v))
    (h_target : ∀ w, target.star_multiplier w =
      zmodFourPhase (2 * targetDiag w))
    (h_diag : ∀ v, 2 * q v =
      2 * (sourceDiag v + targetDiag (map v))) :
    PauliWordStarSystem.StarCompatible source target map
      (fun v => zmodFourPhase (q v)) := by
  intro v
  rw [h_target, h_source]
  change star (zmodFourPhase (q v)) *
      zmodFourPhase (2 * targetDiag (map v)) =
    zmodFourPhase (2 * sourceDiag v) * zmodFourPhase (q (-v))
  rw [star_zmodFourPhase]
  have h_neg : -v = v := by
    exact neg_eq_of_add_eq_zero_right (pauliBit_add_self_eq_zero v)
  rw [h_neg]
  calc
    zmodFourPhase (-q v) * zmodFourPhase (2 * targetDiag (map v)) =
      zmodFourPhase (-q v + 2 * targetDiag (map v)) :=
        (zmodFourPhase_add _ _).symm
    _ = zmodFourPhase (2 * sourceDiag v + q v) := by
      congr 1
      exact zmodFour_star_exponent (q v) (sourceDiag v) (targetDiag (map v))
        (h_diag v)
    _ = zmodFourPhase (2 * sourceDiag v) * zmodFourPhase (q v) :=
      zmodFourPhase_add _ _

/-- Cross-algebra version of the quadratic-refinement multiplication theorem.
The phase equation is scalar, so its proof does not require source and target
Pauli words to live in the same algebra. -/
theorem quadraticPhase_multiplicationCompatibleBetween
    {V W A B : Type*} [AddCommGroup V] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W B)
    (map : V →+ W) (q : V → ZMod 4)
    (sourceExponent : V → V → ZMod 4) (targetExponent : W → W → ZMod 4)
    (h_source : ∀ v w, source.multiplier v w =
      zmodFourPhase (2 * sourceExponent v w))
    (h_target : ∀ v w, target.multiplier v w =
      zmodFourPhase (2 * targetExponent v w))
    (h_q : ∀ v w, q (v + w) =
      q v + q w + 2 * (sourceExponent v w + targetExponent (map v) (map w))) :
    PauliWordStarSystem.MultiplicationCompatibleBetween source target map
      (fun v => zmodFourPhase (q v)) := by
  intro v w
  rw [h_target, h_source]
  change zmodFourPhase (q v) * zmodFourPhase (q w) *
      zmodFourPhase (2 * targetExponent (map v) (map w)) =
    zmodFourPhase (2 * sourceExponent v w) * zmodFourPhase (q (v + w))
  have h_four : sourceExponent v w * 4 = 0 := by
    change sourceExponent v w * ((4 : ℕ) : ZMod 4) = 0
    rw [ZMod.natCast_self 4, mul_zero]
  calc
    zmodFourPhase (q v) * zmodFourPhase (q w) *
        zmodFourPhase (2 * targetExponent (map v) (map w)) =
      zmodFourPhase (q v + q w) *
        zmodFourPhase (2 * targetExponent (map v) (map w)) := by
          rw [zmodFourPhase_add]
    _ = zmodFourPhase
        (q v + q w + 2 * targetExponent (map v) (map w)) :=
          (zmodFourPhase_add _ _).symm
    _ = zmodFourPhase
        (2 * sourceExponent v w + q (v + w)) := by
          congr 1
          rw [h_q]
          linear_combination -h_four
    _ = zmodFourPhase (2 * sourceExponent v w) *
        zmodFourPhase (q (v + w)) :=
          zmodFourPhase_add _ _

/-- Cross-algebra version of the quadratic-refinement involution theorem. -/
theorem quadraticPhase_starCompatibleBetween
    {V W A B : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W B)
    (map : V →+ W) (q : V → ZMod 4)
    (sourceDiag : V → ZMod 4) (targetDiag : W → ZMod 4)
    (h_source : ∀ v, source.star_multiplier v =
      zmodFourPhase (2 * sourceDiag v))
    (h_target : ∀ w, target.star_multiplier w =
      zmodFourPhase (2 * targetDiag w))
    (h_diag : ∀ v, 2 * q v =
      2 * (sourceDiag v + targetDiag (map v))) :
    PauliWordStarSystem.StarCompatibleBetween source target map
      (fun v => zmodFourPhase (q v)) := by
  intro v
  rw [h_target, h_source]
  change star (zmodFourPhase (q v)) *
      zmodFourPhase (2 * targetDiag (map v)) =
    zmodFourPhase (2 * sourceDiag v) * zmodFourPhase (q (-v))
  rw [star_zmodFourPhase]
  have h_neg : -v = v := by
    exact neg_eq_of_add_eq_zero_right (pauliBit_add_self_eq_zero v)
  rw [h_neg]
  calc
    zmodFourPhase (-q v) * zmodFourPhase (2 * targetDiag (map v)) =
      zmodFourPhase (-q v + 2 * targetDiag (map v)) :=
        (zmodFourPhase_add _ _).symm
    _ = zmodFourPhase (2 * sourceDiag v + q v) := by
      congr 1
      exact zmodFour_star_exponent (q v) (sourceDiag v) (targetDiag (map v))
        (h_diag v)
    _ = zmodFourPhase (2 * sourceDiag v) * zmodFourPhase (q v) :=
      zmodFourPhase_add _ _

/-- The complete algebraic lifting step.  Once a ZMod 4 quadratic refinement
satisfies its polarization and diagonal equations, and the phase-corrected
word map is a specified linear equivalence on a Pauli-word basis, it yields a
genuine star-algebra equivalence between the source and target algebras. -/
noncomputable def quadraticPhaseStarAlgEquivOfBasis
    {V W A B : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W]
    [Semiring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Semiring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (source : PauliWordStarSystem V A) (target : PauliWordStarSystem W B)
    (labelMap : V →+ W) (q : V → ZMod 4)
    (sourceExponent : V → V → ZMod 4) (targetExponent : W → W → ZMod 4)
    (sourceDiag : V → ZMod 4) (targetDiag : W → ZMod 4)
    (h_source_mul : ∀ v w, source.multiplier v w =
      zmodFourPhase (2 * sourceExponent v w))
    (h_target_mul : ∀ v w, target.multiplier v w =
      zmodFourPhase (2 * targetExponent v w))
    (h_q : ∀ v w, q (v + w) =
      q v + q w + 2 * (sourceExponent v w +
        targetExponent (labelMap v) (labelMap w)))
    (h_source_star : ∀ v, source.star_multiplier v =
      zmodFourPhase (2 * sourceDiag v))
    (h_target_star : ∀ w, target.star_multiplier w =
      zmodFourPhase (2 * targetDiag w))
    (h_diag : ∀ v, 2 * q v =
      2 * (sourceDiag v + targetDiag (labelMap v)))
    (wordMap : A ≃ₗ[ℂ] B) (basis : Module.Basis V ℂ A)
    (h_basis : ∀ v, basis v = source.word v)
    (h_one : wordMap 1 = 1)
    (h_word : ∀ v, wordMap (source.word v) =
      PauliWordStarSystem.correctedWordBetween target labelMap
        (fun v => zmodFourPhase (q v)) v) :
    A ≃⋆ₐ[ℂ] B :=
  phaseCorrectedStarAlgEquivOfBasis source target labelMap
    (fun v => zmodFourPhase (q v))
    (quadraticPhase_multiplicationCompatibleBetween source target labelMap q
      sourceExponent targetExponent h_source_mul h_target_mul h_q)
    (quadraticPhase_starCompatibleBetween source target labelMap q sourceDiag
      targetDiag h_source_star h_target_star h_diag)
    wordMap basis h_basis h_one h_word

end StabilizerHyperfinite
