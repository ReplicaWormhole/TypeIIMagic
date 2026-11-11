import Formalization.DyadicTensorTower
import Formalization.PauliCocycleCompatibility
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# The explicit one-qubit Pauli word system

This module starts the concrete target-side Pauli construction.  The four
matrices `I`, `X`, `Z`, and `XZ` form the word basis of one qubit in the
ordered convention `X^a Z^b`.
-/

namespace StabilizerHyperfinite

open Matrix

/-- Binary X/Z exponents for one qubit. -/
abbrev SingleQubitLabel := Fin 2 × Fin 2

/-- The identity one-qubit Pauli matrix. -/
def pauliI : QubitMatrix := !![(1 : ℂ), 0; 0, 1]

/-- The one-qubit X Pauli matrix. -/
def pauliX : QubitMatrix := !![(0 : ℂ), 1; 1, 0]

/-- The one-qubit Z Pauli matrix. -/
def pauliZ : QubitMatrix := !![(1 : ℂ), 0; 0, -1]

/-- The ordered product XZ. -/
noncomputable def pauliXZ : QubitMatrix := pauliX * pauliZ

/-- The ordered Pauli word `X^a Z^b` for binary exponents. -/
noncomputable def singleQubitPauliWord : SingleQubitLabel → QubitMatrix
  | (0, 0) => pauliI
  | (1, 0) => pauliX
  | (0, 1) => pauliZ
  | (1, 1) => pauliXZ

/-- The multiplier for the convention `X^a Z^b`: moving the Z exponent of
the left word past the X exponent of the right word contributes a minus sign. -/
def singleQubitMultiplier (v w : SingleQubitLabel) : ℂ :=
  if v.2 = 1 ∧ w.1 = 1 then -1 else 1

/-- The involution multiplier in the ordered convention: only `XZ` changes
sign under adjunction. -/
def singleQubitStarMultiplier (v : SingleQubitLabel) : ℂ :=
  if v.1 = 1 ∧ v.2 = 1 then -1 else 1

@[simp]
theorem pauliI_eq_one : pauliI = 1 := by
  simpa only [pauliI] using (Matrix.one_fin_two (α := ℂ)).symm

@[simp]
theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  rw [pauliX, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

@[simp]
theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  rw [pauliZ, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

theorem pauliZ_mul_pauliX : pauliZ * pauliX = -pauliXZ := by
  simp only [pauliZ, pauliX, pauliXZ, Matrix.mul_fin_two]
  norm_num

@[simp]
theorem star_pauliX : star pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliX, Matrix.star_apply]

@[simp]
theorem star_pauliZ : star pauliZ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliZ, Matrix.star_apply]

@[simp]
theorem star_pauliXZ : star pauliXZ = -pauliXZ := by
  rw [pauliXZ, Matrix.star_mul, star_pauliZ, star_pauliX, pauliZ_mul_pauliX]
  rfl

@[simp]
theorem finTwo_one_add_one : (1 : Fin 2) + 1 = 0 := by
  decide

theorem neg_singleQubitLabel (v : SingleQubitLabel) : -v = v := by
  rcases v with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> rfl

theorem singleQubitPauliWord_mul (v w : SingleQubitLabel) :
    singleQubitPauliWord v * singleQubitPauliWord w =
      singleQubitMultiplier v w • singleQubitPauliWord (v + w) := by
  rcases v with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [singleQubitPauliWord, singleQubitMultiplier, finTwo_one_add_one, pauliI_eq_one,
      pauliX, pauliZ, pauliXZ, Matrix.mul_fin_two, Matrix.one_fin_two]
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j <;> norm_num

theorem singleQubitPauliWord_star (v : SingleQubitLabel) :
    star (singleQubitPauliWord v) =
      singleQubitStarMultiplier v • singleQubitPauliWord (-v) := by
  rcases v with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [singleQubitPauliWord, singleQubitStarMultiplier,
      neg_singleQubitLabel, pauliI_eq_one, pauliX, pauliZ, pauliXZ,
      Matrix.star_apply, Matrix.mul_fin_two, Matrix.one_fin_two]
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j <;> norm_num

/-- The four explicit matrices form a Pauli-word star system in the ordered
`X^a Z^b` convention. -/
noncomputable def singleQubitPauliSystem :
    PauliWordStarSystem SingleQubitLabel QubitMatrix where
  word := singleQubitPauliWord
  multiplier := singleQubitMultiplier
  word_mul := singleQubitPauliWord_mul
  star_multiplier := singleQubitStarMultiplier
  word_star := singleQubitPauliWord_star

/-- The linear combination of the four one-qubit Pauli words with prescribed
coefficient function. -/
noncomputable def singleQubitPauliSynthesizeFun :
    (SingleQubitLabel → ℂ) →ₗ[ℂ] QubitMatrix where
  toFun c :=
    c (0, 0) • pauliI + c (1, 0) • pauliX +
      c (0, 1) • pauliZ + c (1, 1) • pauliXZ
  map_add' c d := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c d := by
    simp only [Pi.smul_apply, smul_add, smul_smul]
    simp only [smul_eq_mul, RingHom.id_apply]

/-- The four Pauli coefficients of a one-qubit matrix in the ordered basis
`I`, `X`, `Z`, `XZ`. -/
noncomputable def singleQubitPauliCoeffFun :
    QubitMatrix →ₗ[ℂ] (SingleQubitLabel → ℂ) where
  toFun M
    | (0, 0) => (M 0 0 + M 1 1) / 2
    | (1, 0) => (M 0 1 + M 1 0) / 2
    | (0, 1) => (M 0 0 - M 1 1) / 2
    | (1, 1) => (M 1 0 - M 0 1) / 2
  map_add' M N := by
    funext label
    rcases label with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp <;> ring
  map_smul' c M := by
    funext label
    rcases label with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp <;> ring

/-- The finite-support linear combination of the explicit Pauli words. -/
noncomputable def singleQubitPauliSynthesize :
    (SingleQubitLabel →₀ ℂ) →ₗ[ℂ] QubitMatrix :=
  singleQubitPauliSynthesizeFun.comp
    (Finsupp.linearEquivFunOnFinite ℂ ℂ SingleQubitLabel).toLinearMap

/-- The finite-support coefficient function of a one-qubit matrix in the
explicit Pauli basis. -/
noncomputable def singleQubitPauliCoeff :
    QubitMatrix →ₗ[ℂ] (SingleQubitLabel →₀ ℂ) :=
  (Finsupp.linearEquivFunOnFinite ℂ ℂ SingleQubitLabel).symm.toLinearMap.comp
    singleQubitPauliCoeffFun

theorem singleQubitPauliCoeffFun_synthesizeFun (c : SingleQubitLabel → ℂ) :
    singleQubitPauliCoeffFun (singleQubitPauliSynthesizeFun c) = c := by
  funext label
  rcases label with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [singleQubitPauliCoeffFun, singleQubitPauliSynthesizeFun,
      pauliI, pauliX, pauliZ, pauliXZ] <;>
      ring

theorem singleQubitPauliSynthesizeFun_coeffFun (M : QubitMatrix) :
    singleQubitPauliSynthesizeFun (singleQubitPauliCoeffFun M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singleQubitPauliCoeffFun, singleQubitPauliSynthesizeFun,
      pauliI, pauliX, pauliZ, pauliXZ] <;>
      ring

theorem singleQubitPauliCoeff_synthesize (c : SingleQubitLabel →₀ ℂ) :
    singleQubitPauliCoeff (singleQubitPauliSynthesize c) = c := by
  apply (Finsupp.linearEquivFunOnFinite ℂ ℂ SingleQubitLabel).injective
  change singleQubitPauliCoeffFun
    (singleQubitPauliSynthesizeFun
      (Finsupp.linearEquivFunOnFinite ℂ ℂ SingleQubitLabel c)) =
        Finsupp.linearEquivFunOnFinite ℂ ℂ SingleQubitLabel c
  exact singleQubitPauliCoeffFun_synthesizeFun _

theorem singleQubitPauliSynthesize_coeff (M : QubitMatrix) :
    singleQubitPauliSynthesize (singleQubitPauliCoeff M) = M := by
  change singleQubitPauliSynthesizeFun
    (Finsupp.linearEquivFunOnFinite ℂ ℂ SingleQubitLabel
      ((Finsupp.linearEquivFunOnFinite ℂ ℂ SingleQubitLabel).symm
        (singleQubitPauliCoeffFun M))) = M
  rw [(Finsupp.linearEquivFunOnFinite ℂ ℂ SingleQubitLabel).apply_symm_apply]
  exact singleQubitPauliSynthesizeFun_coeffFun M

/-- The explicit Pauli coefficient equivalence for one qubit. -/
noncomputable def singleQubitPauliCoeffEquiv :
    QubitMatrix ≃ₗ[ℂ] (SingleQubitLabel →₀ ℂ) :=
  LinearEquiv.ofLinear singleQubitPauliCoeff singleQubitPauliSynthesize
    (by
      apply LinearMap.ext
      intro c
      exact singleQubitPauliCoeff_synthesize c)
    (by
      apply LinearMap.ext
      intro M
      exact singleQubitPauliSynthesize_coeff M)

/-- The four explicit Pauli matrices are a complex linear basis of the
one-qubit matrix algebra. -/
noncomputable def singleQubitPauliBasis :
    Module.Basis SingleQubitLabel ℂ QubitMatrix :=
  Module.Basis.ofRepr singleQubitPauliCoeffEquiv

theorem singleQubitPauliBasis_apply (label : SingleQubitLabel) :
    singleQubitPauliBasis label = singleQubitPauliWord label := by
  change singleQubitPauliSynthesize (Finsupp.single label 1) =
    singleQubitPauliWord label
  rcases label with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [singleQubitPauliSynthesize, singleQubitPauliSynthesizeFun,
      singleQubitPauliWord, Finsupp.linearEquivFunOnFinite_apply,
      pauliI_eq_one]

end StabilizerHyperfinite
