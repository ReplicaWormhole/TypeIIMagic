import Formalization.DyadicTensorTower

/-!
# One-qubit partial trace on the recursive matrix realization

This module builds a concrete, finite-dimensional partial-trace interface for
the recursive matrix realization

    `QubitTensorPower (n + 1) = Matrix (Fin 2) (Fin 2) (QubitTensorPower n)`.

The partial trace over the newest qubit is the *ordinary* (unnormalized) sum of
the two diagonal matrix entries,

    `qubitPartialTrace n a = a 0 0 + a 1 1`,

packaged as a complex-linear map
`QubitTensorPower (n + 1) →ₗ[ℂ] QubitTensorPower n`.

All dimension factors are kept explicit.  `qubitPartialTrace` is **not** a
normalized partial trace and is **not** a state: on an identity-qubit embedding
it produces the factor `2`.  The normalized version, which divides by the qubit
dimension `2`, is recorded separately as `qubitPartialTraceNormalized`.

The file proves the finite identities needed later for density matrices:

1. `qubitPartialTrace_scalar` / `qubitPartialTrace_succEmbedding`: the partial
   trace of an identity-qubit embedding `Matrix.scalar (Fin 2) x` is `2 • x`;
2. `qubitPartialTrace_elementaryTensor`: on an elementary matrix tensor `a ⊗ r`
   (realized as the matrix with entries `a i j • r`) the partial trace is the
   ordinary two-by-two matrix trace of `a` acting on the coefficient `r`;
3. `matrixTraceOver_eq_of_qubitPartialTrace`: for *every* complex-linear
   coefficient functional `tau`, the ordinary matrix trace of the large matrix
   equals `tau` applied to the partial trace.  This third identity is proved in
   full generality (arbitrary elements of `QubitTensorPower (n + 1)`, arbitrary
   `tau`), so no elementary-tensor weakening and no extra matrix API is needed.

No C-star, GNS, normality, or factor claim is made anywhere in this file.
-/

namespace StabilizerHyperfinite

open Matrix

/-! ## The unnormalized partial trace over the newest qubit -/

/-- Auxiliary form of the partial trace, stated directly on the matrix type
`Matrix (Fin 2) (Fin 2) (QubitTensorPower n)`, which is the definitional
unfolding of `QubitTensorPower (n + 1)`. -/
noncomputable def qubitPartialTraceAux (n : ℕ) :
    Matrix (Fin 2) (Fin 2) (QubitTensorPower n) →ₗ[ℂ] QubitTensorPower n where
  toFun a := a 0 0 + a 1 1
  map_add' a b := by
    simp only [Matrix.add_apply]
    exact add_add_add_comm _ _ _ _
  map_smul' c a := by
    simp only [Matrix.smul_apply, smul_add]
    rfl

/-- The ordinary (unnormalized) partial trace over the newest qubit of the
recursive matrix realization: the sum of the two diagonal matrix entries,
`a 0 0 + a 1 1`.  It is complex-linear from `QubitTensorPower (n + 1)` to
`QubitTensorPower n`.

This is *not* normalized: on the identity-qubit embedding it returns `2 • x`. -/
noncomputable def qubitPartialTrace (n : ℕ) :
    QubitTensorPower (n + 1) →ₗ[ℂ] QubitTensorPower n :=
  qubitPartialTraceAux n

theorem qubitPartialTrace_apply (n : ℕ)
    (a : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) :
    qubitPartialTrace n a = a 0 0 + a 1 1 :=
  rfl

/-- The normalized partial trace over the newest qubit: the unnormalized
partial trace divided by the qubit dimension `2`.  Only this version is called
normalized, and neither version is claimed to be a state. -/
noncomputable def qubitPartialTraceNormalized (n : ℕ) :
    QubitTensorPower (n + 1) →ₗ[ℂ] QubitTensorPower n :=
  (1 / 2 : ℂ) • qubitPartialTrace n

theorem qubitPartialTraceNormalized_apply (n : ℕ)
    (a : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) :
    qubitPartialTraceNormalized n a = (1 / 2 : ℂ) • (a 0 0 + a 1 1) :=
  rfl

/-! ## Identity-qubit embeddings -/

/-- **Identity 1.** The partial trace of a scalar (identity-qubit) embedding is
`2` times the coefficient. -/
theorem qubitPartialTrace_scalar (n : ℕ) (x : QubitTensorPower n) :
    qubitPartialTrace n (Matrix.scalar (Fin 2) x) = (2 : ℂ) • x := by
  show (Matrix.scalar (Fin 2) x) 0 0 + (Matrix.scalar (Fin 2) x) 1 1 = _
  simp [Matrix.scalar_apply, two_smul]

/-- The partial trace of the one-step identity-qubit embedding used by the
dyadic tower is `2` times the original observable. -/
theorem qubitPartialTrace_succEmbedding (n : ℕ) (x : QubitTensorPower n) :
    qubitPartialTrace n (qubitTensorPowerSuccEmbedding n x) = (2 : ℂ) • x :=
  qubitPartialTrace_scalar n x

/-- The normalized partial trace of an identity-qubit embedding is the original
observable: the dimension factor `2` is exactly cancelled. -/
theorem qubitPartialTraceNormalized_succEmbedding (n : ℕ) (x : QubitTensorPower n) :
    qubitPartialTraceNormalized n (qubitTensorPowerSuccEmbedding n x) = x := by
  rw [qubitPartialTraceNormalized, LinearMap.smul_apply,
    qubitPartialTrace_succEmbedding, smul_smul]
  norm_num

/-! ## Elementary matrix tensors -/

/-- The concrete realization of an elementary tensor `a ⊗ r` inside
`QubitTensorPower (n + 1) = Matrix (Fin 2) (Fin 2) (QubitTensorPower n)`: the
matrix whose `(i, j)` entry is `a i j • r`. -/
noncomputable def qubitElementaryTensor (n : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (r : QubitTensorPower n) : Matrix (Fin 2) (Fin 2) (QubitTensorPower n) :=
  Matrix.of fun i j => a i j • r

theorem qubitElementaryTensor_apply (n : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (r : QubitTensorPower n) (i j : Fin 2) :
    qubitElementaryTensor n a r i j = a i j • r :=
  rfl

/-- The identity-qubit (scalar) embedding is the elementary tensor whose qubit
factor is the two-by-two identity matrix. -/
theorem qubitElementaryTensor_one (n : ℕ) (r : QubitTensorPower n) :
    qubitElementaryTensor n 1 r = Matrix.scalar (Fin 2) r := by
  ext i j
  by_cases h : i = j <;>
    simp [qubitElementaryTensor, Matrix.scalar_apply, Matrix.one_apply, h]

/-- **Identity 2.** On an elementary matrix tensor, the partial trace is the
ordinary two-by-two matrix trace of the qubit factor acting on the
coefficient. -/
theorem qubitPartialTrace_elementaryTensor (n : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (r : QubitTensorPower n) :
    qubitPartialTrace n (qubitElementaryTensor n a r) = Matrix.trace a • r := by
  show a 0 0 • r + a 1 1 • r = Matrix.trace a • r
  rw [Matrix.trace_fin_two, add_smul]

/-! ## Compatibility with coefficient traces -/

/-- **Identity 3, fully generic.** For every complex-linear coefficient
functional `tau`, the ordinary (unnormalized) matrix trace over the newest qubit
of a large matrix equals `tau` evaluated on the partial trace.  The statement
holds for arbitrary elements of `QubitTensorPower (n + 1)`; no elementary-tensor
restriction is needed. -/
theorem matrixTraceOver_eq_of_qubitPartialTrace (n : ℕ)
    (tau : QubitTensorPower n →ₗ[ℂ] ℂ)
    (a : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) :
    matrixTraceOver (Fin 2) tau a = tau (qubitPartialTrace n a) := by
  show ∑ i : Fin 2, tau (a i i) = tau (a 0 0 + a 1 1)
  rw [Fin.sum_univ_two, map_add]

/-- The normalized matrix trace over the newest qubit is the coefficient
functional applied to the normalized partial trace: the dimension factor `1 / 2`
appears on exactly one side. -/
theorem normalizedMatrixTraceOver_eq_of_qubitPartialTraceNormalized (n : ℕ)
    (tau : QubitTensorPower n →ₗ[ℂ] ℂ)
    (a : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) :
    normalizedMatrixTraceOver (Fin 2) tau a = tau (qubitPartialTraceNormalized n a) := by
  have h : ∑ i : Fin 2, tau (a i i) = tau (qubitPartialTrace n a) :=
    matrixTraceOver_eq_of_qubitPartialTrace n tau a
  rw [qubitPartialTraceNormalized, LinearMap.smul_apply, map_smul,
    normalizedMatrixTraceOver_apply, h]
  simp [Fintype.card_fin, smul_eq_mul]

/-- The finite-stage normalized tower trace of a large matrix is the normalized
tower trace of its normalized partial trace. -/
theorem qubitTensorTrace_succ_eq_of_qubitPartialTraceNormalized (n : ℕ)
    (a : QubitTensorPower (n + 1)) :
    qubitTensorTrace (n + 1) a = qubitTensorTrace n (qubitPartialTraceNormalized n a) :=
  normalizedMatrixTraceOver_eq_of_qubitPartialTraceNormalized n (qubitTensorTrace n) a

/-- The unnormalized form of the previous identity, with the dimension factor
`2` displayed explicitly. -/
theorem qubitTensorTrace_succ_eq_of_qubitPartialTrace (n : ℕ)
    (a : QubitTensorPower (n + 1)) :
    (2 : ℂ) * qubitTensorTrace (n + 1) a = qubitTensorTrace n (qubitPartialTrace n a) := by
  rw [qubitTensorTrace_succ_eq_of_qubitPartialTraceNormalized n a,
    qubitPartialTraceNormalized, LinearMap.smul_apply, map_smul, smul_eq_mul,
    ← mul_assoc]
  norm_num

end StabilizerHyperfinite
