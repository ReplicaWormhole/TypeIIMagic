import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite-qubit Pauli strings

This file begins the finite-volume realization layer of the stabilizer proof.
It represents an `n`-qubit Hilbert basis recursively, defines the four
one-qubit Pauli matrices and their tensor-product strings, and proves the
trace-orthogonality fact used by the local stabilizer density calculation.

It does not yet construct the infinite lattice, a compatible family of local
groups, or the GNS representation.  Those later layers must consume the exact
finite-dimensional statements proved here.
-/

namespace FiniteFiber

open scoped BigOperators Kronecker

/-- The four Hermitian one-qubit Pauli labels. -/
inductive PauliLabel where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Repr

namespace PauliLabel

/-- The standard matrix for a one-qubit Pauli label. -/
def matrix : PauliLabel → Matrix (Fin 2) (Fin 2) ℂ
  | I => !![1, 0; 0, 1]
  | X => !![0, 1; 1, 0]
  | Y => !![0, -Complex.I; Complex.I, 0]
  | Z => !![1, 0; 0, -1]

/-- The identity Pauli has trace two; each nonidentity Pauli is traceless. -/
theorem matrix_trace (a : PauliLabel) :
    (matrix a).trace = if a = I then 2 else 0 := by
  cases a <;> norm_num [matrix, Matrix.trace_fin_two] <;> decide

/-- A nonidentity one-qubit Pauli is traceless. -/
theorem matrix_trace_eq_zero_of_ne_I {a : PauliLabel} (ha : a ≠ I) :
    (matrix a).trace = 0 := by
  rw [matrix_trace, if_neg ha]

/-- The identity one-qubit Pauli has trace two. -/
theorem matrix_trace_I : (matrix I).trace = 2 := by
  rw [matrix_trace, if_pos rfl]

/-- The explicit matrix for the identity label is the matrix identity. -/
theorem matrix_I_eq_one : matrix I = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

/-- Every one-qubit Pauli matrix is self-adjoint. -/
theorem matrix_isSelfAdjoint (a : PauliLabel) : IsSelfAdjoint (matrix a) := by
  change star (matrix a) = matrix a
  rw [Matrix.star_eq_conjTranspose]
  cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [matrix]

end PauliLabel

/-- A recursively parenthesized computational basis for `n` qubits. -/
def QubitIndex : ℕ → Type
  | 0 => PUnit
  | n + 1 => Fin 2 × QubitIndex n

instance qubitIndexFintype (n : ℕ) : Fintype (QubitIndex n) := by
  induction n with
  | zero =>
      change Fintype PUnit
      infer_instance
  | succ n ih =>
      letI : Fintype (QubitIndex n) := ih
      change Fintype (Fin 2 × QubitIndex n)
      infer_instance

instance qubitIndexDecidableEq (n : ℕ) : DecidableEq (QubitIndex n) := by
  induction n with
  | zero =>
      change DecidableEq PUnit
      infer_instance
  | succ n ih =>
      letI : DecidableEq (QubitIndex n) := ih
      change DecidableEq (Fin 2 × QubitIndex n)
      infer_instance

/-- The recursive computational basis has the expected finite qubit dimension. -/
theorem qubitIndex_card (n : ℕ) : Fintype.card (QubitIndex n) = 2 ^ n := by
  induction n with
  | zero => simp [QubitIndex]
  | succ n ih =>
      simp [QubitIndex, ih, pow_succ, Nat.mul_comm]

/-- The tensor-product matrix of an `n`-qubit Pauli string. -/
def pauliStringMatrix : {n : ℕ} → (Fin n → PauliLabel) →
    Matrix (QubitIndex n) (QubitIndex n) ℂ
  | 0, _ => 1
  | _ + 1, a => PauliLabel.matrix (a 0) ⊗ₖ pauliStringMatrix (fun i => a i.succ)

/-- The trace of a Pauli string factors into the one-qubit traces. -/
theorem pauliStringMatrix_trace : ∀ {n : ℕ} (a : Fin n → PauliLabel),
    (pauliStringMatrix a).trace = ∏ i, (PauliLabel.matrix (a i)).trace := by
  intro n
  induction n with
  | zero =>
      intro a
      simp [pauliStringMatrix, QubitIndex, Matrix.trace]
  | succ n ih =>
      intro a
      rw [pauliStringMatrix, Matrix.trace_kronecker, ih, Fin.prod_univ_succ]

/-- A Pauli string with a nonidentity factor is traceless. -/
theorem pauliStringMatrix_trace_eq_zero_of_exists_ne_I
    {n : ℕ} (a : Fin n → PauliLabel) (h : ∃ i, a i ≠ PauliLabel.I) :
    (pauliStringMatrix a).trace = 0 := by
  rw [pauliStringMatrix_trace]
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (PauliLabel.matrix_trace_eq_zero_of_ne_I hi)

/-- The identity Pauli string has trace equal to the finite qubit dimension. -/
theorem pauliStringMatrix_trace_all_I (n : ℕ) :
    (pauliStringMatrix fun _ : Fin n => PauliLabel.I).trace = (2 : ℂ) ^ n := by
  rw [pauliStringMatrix_trace]
  simp [PauliLabel.matrix_trace_I]

/-- The all-identity Pauli string is the matrix identity. -/
theorem pauliStringMatrix_all_I : ∀ n : ℕ,
    pauliStringMatrix (fun _ : Fin n => PauliLabel.I) = 1 := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change PauliLabel.matrix PauliLabel.I ⊗ₖ
        pauliStringMatrix (fun _ : Fin n => PauliLabel.I) = 1
      rw [PauliLabel.matrix_I_eq_one, ih]
      ext x y
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      by_cases h₁ : x₁ = y₁
      · subst y₁
        by_cases h₂ : x₂ = y₂
        · subst y₂
          simp
        · simp [h₂]
      · by_cases h₂ : x₂ = y₂
        · subst y₂
          simp [h₁]
        · simp [h₁, h₂]

/-- Tensor-product Pauli strings are self-adjoint. -/
theorem pauliStringMatrix_isSelfAdjoint : ∀ {n : ℕ} (a : Fin n → PauliLabel),
    IsSelfAdjoint (pauliStringMatrix a) := by
  intro n
  induction n with
  | zero =>
      intro a
      change star (1 : Matrix (QubitIndex 0) (QubitIndex 0) ℂ) = 1
      simp
  | succ n ih =>
      intro a
      change star (PauliLabel.matrix (a 0) ⊗ₖ pauliStringMatrix (fun i => a i.succ)) =
        PauliLabel.matrix (a 0) ⊗ₖ pauliStringMatrix (fun i => a i.succ)
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
      have hhead : (PauliLabel.matrix (a 0)).conjTranspose = PauliLabel.matrix (a 0) := by
        simpa only [Matrix.star_eq_conjTranspose] using PauliLabel.matrix_isSelfAdjoint (a 0)
      have htail : (pauliStringMatrix fun i => a i.succ).conjTranspose =
          pauliStringMatrix (fun i => a i.succ) := by
        simpa only [Matrix.star_eq_conjTranspose] using ih (fun i => a i.succ)
      rw [hhead, htail]

end FiniteFiber
