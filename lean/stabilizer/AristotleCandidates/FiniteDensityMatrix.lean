import Formalization.FinitePureMixedQubitState
import Formalization.FiniteQubitPauliSelection

/-!
# Finite-stage density matrices for the pure/mixed qubit product state

This module realizes each finite-stage pure/mixed product functional
`qubitPureMixedState pure n` as an honest density-matrix pairing

    omega_n (a) = Tr (rho_n * a),

where `Tr` is the *ordinary* (unnormalized) iterated matrix trace
`qubitTensorFullTrace` on the concrete tower `QubitTensorPower n`, and the
density matrix `rho_n = qubitPureMixedDensity pure n` is built recursively:

* `rho_0 = 1` is the scalar unit of `QubitTensorPower 0 = ℂ`;
* `rho_(n+1)` is the new leftmost qubit tensored onto `rho_n`, the new factor
  being the pure density matrix `diag (1, 0)` when `pure n = true`, and the
  maximally mixed density matrix `(1/2) I` when `pure n = false`.

All normalizations are explicit.  The ordinary trace `qubitTensorFullTrace n`
sends the unit to the dimension `2 ^ n` (`qubitTensorFullTrace_one`), the
normalized trace of the tower is `2 ^ (-n)` times it
(`qubitTensorTrace_eq_smul_qubitTensorFullTrace`), and the density matrices
have ordinary trace one (`qubitTensorFullTrace_qubitPureMixedDensity`).  The
normalized-trace version of the pairing therefore carries its compensating
dimension factor `2 ^ n` explicitly
(`qubitPureMixedState_eq_dim_mul_qubitTensorTrace_density`).

No infinite-stage, C-star, normality, or factor claim is made here.
-/

namespace StabilizerHyperfinite

open scoped TensorProduct

/-! ## The ordinary (unnormalized) iterated matrix trace -/

/-- The ordinary matrix trace on the finite qubit stage `QubitTensorPower n`.
It is the iterated sum over diagonal entries, with no normalization; on the
unit it takes the value `2 ^ n`. -/
noncomputable def qubitTensorFullTrace : (n : ℕ) → QubitTensorPower n →ₗ[ℂ] ℂ
  | 0 => LinearMap.id
  | n + 1 => matrixTraceOver (Fin 2) (qubitTensorFullTrace n)

theorem qubitTensorFullTrace_zero_apply (z : QubitTensorPower 0) :
    qubitTensorFullTrace 0 z = z := rfl

theorem qubitTensorFullTrace_succ_apply (n : ℕ)
    (a : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) :
    qubitTensorFullTrace (n + 1) a =
      ∑ i : Fin 2, qubitTensorFullTrace n (a i i) := rfl

/-- The ordinary trace of the unit of the `n`-qubit stage is the dimension
`2 ^ n`. -/
theorem qubitTensorFullTrace_one (n : ℕ) :
    qubitTensorFullTrace n (1 : QubitTensorPower n) = (2 : ℂ) ^ n := by
  induction n with
  | zero => simp [qubitTensorFullTrace_zero_apply]
  | succ n ih =>
    show matrixTraceOver (Fin 2) (qubitTensorFullTrace n) (1 : QubitTensorPower (n + 1)) = _
    simp [matrixTraceOver]
    have h0 : (1 : QubitTensorPower (n + 1)) 0 0 = (1 : QubitTensorPower n) := rfl
    have h1 : (1 : QubitTensorPower (n + 1)) 1 1 = (1 : QubitTensorPower n) := rfl
    rw [h0, h1, ih]
    ring

/-- The normalized finite-stage trace is the ordinary trace divided by the
dimension `2 ^ n`.  This is the only permitted way to exchange the two. -/
theorem qubitTensorTrace_eq_smul_qubitTensorFullTrace (n : ℕ)
    (a : QubitTensorPower n) :
    qubitTensorTrace n a = (1 / (2 : ℂ) ^ n) * qubitTensorFullTrace n a := by
  induction n with
  | zero => simp [qubitTensorTrace, qubitTensorFullTrace, scalarTrace]
  | succ n ih =>
    unfold qubitTensorTrace qubitTensorFullTrace
    unfold normalizedMatrixTraceOver
    simp [Fintype.card_fin, matrixTraceOver]
    simp_rw [ih]
    simp
    ring

/-! ## The one-qubit density matrices -/

/-- The pure one-qubit density matrix `diag (1, 0)`, i.e. the rank-one
projection onto the ket `|0⟩`. -/
def ketZeroDensity : QubitMatrix := !![(1 : ℂ), 0; 0, 0]

/-- The maximally mixed one-qubit density matrix `(1/2) I`. -/
noncomputable def maxMixedDensity : QubitMatrix := !![(1 / 2 : ℂ), 0; 0, 1 / 2]

/-- The maximally mixed density matrix is literally `(1/2) I`. -/
theorem maxMixedDensity_eq_smul_one :
    maxMixedDensity = (1 / 2 : ℂ) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [maxMixedDensity, Matrix.one_fin_two]

/-- The pure density matrix is the rank-one projection `diag (1, 0)`. -/
theorem ketZeroDensity_apply :
    ketZeroDensity 0 0 = 1 ∧ ketZeroDensity 0 1 = 0 ∧
      ketZeroDensity 1 0 = 0 ∧ ketZeroDensity 1 1 = 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem trace_ketZeroDensity : Matrix.trace ketZeroDensity = 1 := by
  simp [ketZeroDensity, Matrix.trace_fin_two]

@[simp]
theorem trace_maxMixedDensity : Matrix.trace maxMixedDensity = 1 := by
  norm_num [maxMixedDensity, Matrix.trace_fin_two]

/-- The one-qubit density matrix selected at coordinate `n` by the pure/mixed
pattern. -/
noncomputable def qubitDensityFactor (pure : ℕ → Bool) (n : ℕ) : QubitMatrix :=
  if pure n then ketZeroDensity else maxMixedDensity

/-! ## The finite-stage density matrices -/

/-- The finite-stage density matrix of the pure/mixed product pattern, built
in the concrete tower representation by tensoring the new leftmost qubit's
one-qubit density matrix onto the previous stage. -/
noncomputable def qubitPureMixedDensity (pure : ℕ → Bool) : (n : ℕ) →
    QubitTensorPower n
  | 0 => (1 : ℂ)
  | n + 1 =>
      matrixTensorStarAlgEquiv (Fin 2)
        (qubitDensityFactor pure n ⊗ₜ[ℂ] qubitPureMixedDensity pure n)

/-- The entries of the successor-stage density matrix: the `(i, j)` block is
the scalar entry of the new one-qubit density matrix acting on the previous
density matrix. -/
theorem qubitPureMixedDensity_succ_apply (pure : ℕ → Bool) (n : ℕ)
    (i j : Fin 2) :
    (qubitPureMixedDensity pure (n + 1) : Matrix (Fin 2) (Fin 2) _) i j =
      qubitDensityFactor pure n i j • qubitPureMixedDensity pure n := by
  simp [qubitPureMixedDensity, matrixTensorStarAlgEquiv_tmul_apply,
    Algebra.algebraMap_eq_smul_one]

/-! ## The trace-pairing formula -/

/-- Expansion of the successor-stage trace pairing: the ordinary trace of
`rho_(n+1) * a` is the double sum over the new qubit's matrix entries of the
previous-stage trace pairings against the blocks of `a`. -/
theorem qubitTensorFullTrace_succ_density_mul (pure : ℕ → Bool) (n : ℕ)
    (a : QubitTensorPower (n + 1)) :
    qubitTensorFullTrace (n + 1) (qubitPureMixedDensity pure (n + 1) * a) =
      ∑ i : Fin 2, ∑ k : Fin 2, qubitDensityFactor pure n i k *
        qubitTensorFullTrace n (qubitPureMixedDensity pure n *
          (a : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) k i) := by
  rw [qubitTensorFullTrace_succ_apply]
  congr 1 with i
  rw [Matrix.mul_apply]
  simp_rw [qubitPureMixedDensity_succ_apply, smul_mul_assoc]
  simp

/-- **Density-matrix realization.**  On every finite stage and every finite
observable, the pure/mixed product functional is the ordinary matrix trace
against the finite-stage density matrix. -/
theorem qubitPureMixedState_eq_qubitTensorFullTrace_density
    (pure : ℕ → Bool) (n : ℕ) (a : QubitTensorPower n) :
    qubitPureMixedState pure n a =
      qubitTensorFullTrace n (qubitPureMixedDensity pure n * a) := by
  induction n with
  | zero =>
    simp [qubitPureMixedState, qubitPureMixedDensity, qubitTensorFullTrace, scalarTrace]
  | succ n ih =>
    by_cases h : pure n
    · -- pure case: use qubitKetZeroStateOver
      have htrue : pure n = true := h
      simp [qubitPureMixedState, htrue]
      rw [qubitTensorFullTrace_succ_density_mul]
      simp [qubitKetZeroStateOver]
      simp [qubitDensityFactor, htrue]
      norm_num [ketZeroDensity]
      simp [ih]
    · -- mixed case: use normalizedMatrixTraceOver
      have hfalse : pure n = Bool.false := by simp_all
      simp [qubitPureMixedState, hfalse]
      rw [qubitTensorFullTrace_succ_density_mul]
      simp [qubitDensityFactor, hfalse]
      simp [normalizedMatrixTraceOver, matrixTraceOver, ih]
      norm_num [maxMixedDensity]
      ring

/-- Each finite-stage density matrix has ordinary matrix trace one. -/
theorem qubitTensorFullTrace_qubitPureMixedDensity (pure : ℕ → Bool) (n : ℕ) :
    qubitTensorFullTrace n (qubitPureMixedDensity pure n) = 1 := by
  induction n with
  | zero => simp [qubitTensorFullTrace_zero_apply, qubitPureMixedDensity]
  | succ n ih =>
    rw [show qubitPureMixedDensity pure (n + 1) = qubitPureMixedDensity pure (n + 1) * 1 by simp]
    rw [qubitTensorFullTrace_succ_density_mul]
    have h00 : (1 : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) 0 0 = 1 := rfl
    have h01 : (1 : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) 0 1 = 0 := rfl
    have h10 : (1 : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) 1 0 = 0 := rfl
    have h11 : (1 : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) 1 1 = 1 := rfl
    simp [h00, h01, h10, h11, ih]
    by_cases h : pure n
    · simp [qubitDensityFactor, h, ketZeroDensity]
    · simp [qubitDensityFactor, h, maxMixedDensity]
      norm_num

/-- The same pairing written with the normalized finite-stage trace, with its
compensating dimension factor `2 ^ n` made explicit. -/
theorem qubitPureMixedState_eq_dim_mul_qubitTensorTrace_density
    (pure : ℕ → Bool) (n : ℕ) (a : QubitTensorPower n) :
    qubitPureMixedState pure n a =
      (2 : ℂ) ^ n * qubitTensorTrace n (qubitPureMixedDensity pure n * a) := by
  rw [qubitPureMixedState_eq_qubitTensorFullTrace_density]
  rw [qubitTensorTrace_eq_smul_qubitTensorFullTrace]
  field_simp

/-! ## Pauli expectations -/

/-- The Pauli expectation values of the finite-stage density matrix. -/
theorem qubitTensorFullTrace_density_finiteQubitPauliWord
    (pure : ℕ → Bool) (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitTensorFullTrace n
        (qubitPureMixedDensity pure n * finiteQubitPauliWord n v) =
      qubitPureMixedPauliExpectation pure n v := by
  rw [← qubitPureMixedState_eq_qubitTensorFullTrace_density,
    qubitPureMixedState_finiteQubitPauliWord]

/-- **Selected-Z Pauli expectation formula.**  The ordinary trace pairing of
the finite-stage density matrix with a finite Pauli word is the indicator of
the selected-Z condition of the pure/mixed pattern. -/
theorem qubitTensorFullTrace_density_finiteQubitPauliWord_eq_selectedZIndicator
    (pure : ℕ → Bool) (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitTensorFullTrace n
        (qubitPureMixedDensity pure n * finiteQubitPauliWord n v) =
      finiteQubitPauliSelectedZIndicator pure n v := by
  rw [qubitTensorFullTrace_density_finiteQubitPauliWord,
    qubitPureMixedPauliExpectation_eq_indicator,
    qubitPureMixedPauliIndicator_eq_selectedZIndicator]

open scoped Classical in
/-- The same formula written as an explicit `if`: the pairing is one exactly
on the selected-Z words, and zero otherwise. -/
theorem qubitTensorFullTrace_density_finiteQubitPauliWord_eq_ite
    (pure : ℕ → Bool) (n : ℕ) (v : FiniteQubitPauliLabel n) :
    qubitTensorFullTrace n
        (qubitPureMixedDensity pure n * finiteQubitPauliWord n v) =
      if finiteQubitPauliSelectedZ pure n v then 1 else 0 := by
  rw [qubitTensorFullTrace_density_finiteQubitPauliWord_eq_selectedZIndicator]
  simp [finiteQubitPauliSelectedZIndicator]

end StabilizerHyperfinite
