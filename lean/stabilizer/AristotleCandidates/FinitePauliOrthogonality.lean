import Formalization.FiniteQubitPauli
import Formalization.FinitePureMixedQubitState

/-!
# Finite-stage Pauli Hilbert-Schmidt orthogonality

The ordered finite-qubit Pauli words `finiteQubitPauliWord n v` are orthonormal
for the normalized trace `qubitTensorTrace n` of the finite qubit stage:

    qubitTensorTrace n (star (word v) * word w) = if v = w then 1 else 0.

All phase factors coming from the ordered `X^a Z^b` convention are tracked
exactly: the involution multiplier `finiteQubitPauliStarMultiplier` and the
product multiplier `finiteQubitPauliMultiplier` combine to exactly `1` on the
diagonal, which is the content of
`finiteQubitPauliStarMultiplier_mul_multiplier_self`.
-/

namespace StabilizerHyperfinite

/-- Equality of finite Pauli labels is decidable. -/
instance finiteQubitPauliLabelDecidableEq :
    (n : ℕ) → DecidableEq (FiniteQubitPauliLabel n)
  | 0 => (inferInstance : DecidableEq (Fin 1))
  | n + 1 =>
      @instDecidableEqProd _ _ inferInstance (finiteQubitPauliLabelDecidableEq n)

/-- Every finite Pauli label is its own additive inverse. -/
theorem neg_finiteQubitPauliLabel :
    ∀ (n : ℕ) (v : FiniteQubitPauliLabel n), -v = v := by
  intro n
  induction n with
  | zero =>
    intro v
    have hv : v = 0 := Fin.eq_zero v
    rw [hv]
    simp
  | succ n ih =>
    intro v
    match v with
    | (a, b) =>
      match a with
      | (a1, a2) =>
        apply Prod.ext
        · show -(a1, a2) = (a1, a2)
          ext <;> fin_cases a1 <;> fin_cases a2 <;> rfl
        · show -b = b
          exact ih b

/-- A label at stage `n + 1` is trivial exactly when both its leading
one-qubit label and its tail are trivial. -/
theorem finiteQubitPauliLabel_succ_eq_zero_iff (n : ℕ) (a : SingleQubitLabel)
    (v : FiniteQubitPauliLabel n) :
    ((a, v) : FiniteQubitPauliLabel (n + 1)) = 0 ↔ a = 0 ∧ v = 0 := by
  simp [Prod.ext_iff]

/-- The all-mixed product-state expectation of a finite Pauli word is the
indicator of the identity label. -/
theorem qubitPureMixedPauliExpectation_allMixed :
    ∀ (n : ℕ) (v : FiniteQubitPauliLabel n),
      qubitPureMixedPauliExpectation (fun _ => false) n v =
        if v = 0 then 1 else 0 := by
  intro n
  induction n with
  | zero =>
    intro v
    have hv : v = 0 := Fin.eq_zero v
    subst hv
    simp [qubitPureMixedPauliExpectation]
  | succ n ih =>
    intro v
    obtain ⟨a, v⟩ := v
    have hstep : qubitPureMixedPauliExpectation (fun _ => false) (n + 1) (a, v) =
        singleQubitMixedExpectation a *
          qubitPureMixedPauliExpectation (fun _ => false) n v := by
      simp [qubitPureMixedPauliExpectation]
    have hz := finiteQubitPauliLabel_succ_eq_zero_iff n a v
    rw [hstep, ih]
    simp only [singleQubitMixedExpectation]
    by_cases ha : a = 0 <;> by_cases hv : v = 0
    · rw [if_pos ha, if_pos hv, if_pos (hz.mpr ⟨ha, hv⟩), one_mul]
    · rw [if_pos ha, if_neg hv, if_neg fun h => hv (hz.mp h).2, mul_zero]
    · rw [if_neg ha, if_pos hv, if_neg fun h => ha (hz.mp h).1, zero_mul]
    · rw [if_neg ha, if_neg hv, if_neg fun h => ha (hz.mp h).1, zero_mul]

/-- The one-label normalized-trace formula: the finite normalized trace of an
ordered Pauli word is `1` for the identity word and `0` otherwise. -/
theorem qubitTensorTrace_finiteQubitPauliWord (n : ℕ)
    (v : FiniteQubitPauliLabel n) :
    qubitTensorTrace n (finiteQubitPauliWord n v) = if v = 0 then 1 else 0 := by
  rw [← qubitPureMixedState_allMixed, qubitPureMixedState_finiteQubitPauliWord,
    qubitPureMixedPauliExpectation_allMixed]

/-- The exact phase bookkeeping of the ordered convention: the involution
multiplier of a word times the product multiplier of the adjoint word with the
word itself is exactly `1`. -/
theorem finiteQubitPauliStarMultiplier_mul_multiplier_self :
    ∀ (n : ℕ) (v : FiniteQubitPauliLabel n),
      finiteQubitPauliStarMultiplier n v * finiteQubitPauliMultiplier n (-v) v = 1 := by
  intro n
  induction n with
  | zero =>
    intro v
    simp [finiteQubitPauliStarMultiplier, finiteQubitPauliMultiplier]
  | succ n ih =>
    intro v
    rcases v with ⟨a, v'⟩
    have hneg_v' : -v' = v' := neg_finiteQubitPauliLabel n v'
    have hneg : -((a, v') : FiniteQubitPauliLabel (n + 1)) = (a, v') :=
      neg_finiteQubitPauliLabel (n + 1) (a, v')
    rw [hneg]
    unfold finiteQubitPauliStarMultiplier finiteQubitPauliMultiplier
    simp only
    have hih := ih v'
    rw [hneg_v'] at hih
    have hsingle : singleQubitStarMultiplier a * singleQubitMultiplier a a = 1 := by
      rcases a with ⟨a₁, a₂⟩
      fin_cases a₁ <;> fin_cases a₂ <;>
        simp [singleQubitStarMultiplier, singleQubitMultiplier]
    calc singleQubitStarMultiplier a * finiteQubitPauliStarMultiplier n v' *
          (singleQubitMultiplier a a * finiteQubitPauliMultiplier n v' v')
        = (singleQubitStarMultiplier a * singleQubitMultiplier a a) *
            (finiteQubitPauliStarMultiplier n v' *
              finiteQubitPauliMultiplier n v' v') := by ring
      _ = 1 * 1 := by rw [hsingle, hih]
      _ = 1 := by ring

/-- **Hilbert-Schmidt orthonormality of the finite ordered Pauli words.** -/
theorem qubitTensorTrace_star_finiteQubitPauliWord_mul (n : ℕ)
    (v w : FiniteQubitPauliLabel n) :
    qubitTensorTrace n
        (star (finiteQubitPauliWord n v) * finiteQubitPauliWord n w) =
      if v = w then 1 else 0 := by
  rw [finiteQubitPauliWord_star, smul_mul_assoc, finiteQubitPauliWord_mul,
    LinearMap.map_smul, smul_eq_mul, LinearMap.map_smul, smul_eq_mul,
    qubitTensorTrace_finiteQubitPauliWord]
  simp only [neg_add_eq_zero, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [← h]
    exact finiteQubitPauliStarMultiplier_mul_multiplier_self n v
  · rfl

end StabilizerHyperfinite
