import FiniteFiber.FullPauliLattice

/-!
# The one-site phased Pauli normal form

This file fixes only the literal one-site convention relating the raw
normal-form matrix `X^x Z^z` to the Hermitian representative chosen by
`PauliLabel.ofProjectiveCoordinates`.  The two matrices differ by a fourth
root of unity, which is trivial except at the label `(1, 1)`, where
`X * Z = -i * Y`.

Nothing beyond this one-site table is claimed here: there is no map from
`FullPauliWord`, no finite-region matrix, no multiplicativity statement, and
no compatibility with `FullPauliWord.cocycle` or `FullPauliWord.phaseEmbed`
(the latter is a different map, sending `1` to the sign exponent `2`).
-/

namespace FiniteFiber

/-- The fourth root of unity `i ^ k` attached to a `ZMod 4` phase exponent. -/
noncomputable def zmod4PhaseFactor (k : ZMod 4) : ℂ :=
  Complex.I ^ k.val

/--
The phase correction taking the Hermitian one-site representative to the raw
normal-form product `X^x Z^z`.  It is nontrivial only at `(1, 1)`, where
`X * Z = i^3 * Y`.
-/
def normalFormHermitianCorrection (p : ProjectivePauliLabel) : ZMod 4 :=
  if p = (1, 1) then 3 else 0

/-- The raw one-site normal-form matrix `X^x Z^z`, in this factor order. -/
noncomputable def normalFormOneSiteMatrix (p : ProjectivePauliLabel) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (if p.1 = 0 then 1 else PauliLabel.matrix PauliLabel.X) *
    (if p.2 = 0 then 1 else PauliLabel.matrix PauliLabel.Z)

/--
The one-site normalization: the raw normal-form matrix is the chosen Hermitian
representative multiplied by the fourth root of unity `i ^ c(p)`.
-/
theorem normalFormOneSiteMatrix_eq_phase_smul_hermitian
    (p : ProjectivePauliLabel) :
    normalFormOneSiteMatrix p =
      zmod4PhaseFactor (normalFormHermitianCorrection p) •
        PauliLabel.matrix (PauliLabel.ofProjectiveCoordinates p) := by
  obtain ⟨x, z⟩ := p
  fin_cases x <;> fin_cases z <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [zmod4PhaseFactor, normalFormHermitianCorrection,
          normalFormOneSiteMatrix, PauliLabel.ofProjectiveCoordinates,
          PauliLabel.matrix, Matrix.mul_apply, ZMod.val, Complex.ext_iff,
          Fin.sum_univ_succ, Matrix.one_fin_two]

/-- Convention regression: the correction at the `Y` label is `3`, not `1`. -/
theorem normalFormHermitianCorrection_xy :
    normalFormHermitianCorrection ((1, 1) : ProjectivePauliLabel) = 3 := by
  simp [normalFormHermitianCorrection]

/-- Convention regression: `X * Z = -i * Y`, not `+i * Y` or `± Y`. -/
theorem normalFormOneSiteMatrix_xy :
    normalFormOneSiteMatrix ((1, 1) : ProjectivePauliLabel) =
      (-Complex.I) • PauliLabel.matrix PauliLabel.Y := by
  rw [normalFormOneSiteMatrix_eq_phase_smul_hermitian,
    normalFormHermitianCorrection_xy]
  norm_num [zmod4PhaseFactor, ZMod.val, pow_succ, Complex.I_mul_I,
    PauliLabel.ofProjectiveCoordinates]

end FiniteFiber
