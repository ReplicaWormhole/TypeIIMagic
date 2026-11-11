import AristotleCandidates.FiniteDensityMatrix
import AristotleCandidates.OneQubitPartialTrace

/-!
# Density matrices and the ordinary partial trace over the newest qubit

This module connects the recursive finite-stage density matrices
`rho_n = qubitPureMixedDensity pure n` of `AristotleCandidates.FiniteDensityMatrix`
with the ordinary (unnormalized) one-qubit partial trace
`qubitPartialTrace` of `AristotleCandidates.OneQubitPartialTrace`.

The main result is the exact compatibility

    `qubitPartialTrace n rho_(n+1) = rho_n`,

which holds because the newest one-qubit density factor
`qubitDensityFactor pure n` has *ordinary* matrix trace one
(`trace_qubitDensityFactor`).  The computation is factored through the general
elementary-tensor identity `qubitPartialTrace_elementaryTensor`, after
identifying `rho_(n+1)` with the elementary tensor of the new one-qubit factor
against `rho_n` (`qubitPureMixedDensity_succ_eq_elementaryTensor`).

As a corollary we obtain the ordinary full-trace tower identity for the density
matrices, expressed through the partial-trace route and using the project's
*ordinary* trace `qubitTensorFullTrace` (never silently replacing it by the
normalized `qubitTensorTrace`).

Finally, the normalized partial trace is recorded honestly: it does **not**
preserve `rho_n`, it produces the explicit factor `1 / 2`
(`qubitPartialTraceNormalized_qubitPureMixedDensity_succ`).

Everything here is finite-dimensional.  No infinite tensor-product, C-star,
GNS, normality, or factor-classification claim is made.
-/

namespace StabilizerHyperfinite

open Matrix

/-! ## The newest one-qubit density factor has ordinary trace one -/

/-- **The key normalization fact.**  Each selected one-qubit density factor —
the pure projection `diag (1, 0)` or the maximally mixed matrix `(1/2) I` — has
*ordinary* (unnormalized) matrix trace one. -/
@[simp]
theorem trace_qubitDensityFactor (pure : ℕ → Bool) (n : ℕ) :
    Matrix.trace (qubitDensityFactor pure n) = 1 := by
  unfold qubitDensityFactor
  by_cases h : pure n <;> simp [h]

/-! ## The successor density matrix as an elementary tensor -/

/-- The successor-stage density matrix is exactly the concrete elementary
tensor of the newest one-qubit density factor against the previous stage. -/
theorem qubitPureMixedDensity_succ_eq_elementaryTensor (pure : ℕ → Bool) (n : ℕ) :
    (qubitPureMixedDensity pure (n + 1) : Matrix (Fin 2) (Fin 2) (QubitTensorPower n)) =
      qubitElementaryTensor n (qubitDensityFactor pure n)
        (qubitPureMixedDensity pure n) := by
  refine Matrix.ext fun i j => ?_
  rw [qubitPureMixedDensity_succ_apply, qubitElementaryTensor_apply]

/-! ## Partial trace of a one-qubit density factor tensored with any element -/

/-- The general elementary-tensor calculation: tensoring a one-qubit *density*
factor onto an arbitrary previous-stage element and tracing out the newest
qubit returns that element unchanged, precisely because the factor has ordinary
trace one. -/
theorem qubitPartialTrace_densityFactor_elementaryTensor (pure : ℕ → Bool) (n : ℕ)
    (r : QubitTensorPower n) :
    qubitPartialTrace n (qubitElementaryTensor n (qubitDensityFactor pure n) r) = r := by
  rw [qubitPartialTrace_elementaryTensor, trace_qubitDensityFactor, one_smul]

/-! ## Compatibility of the density matrices with the ordinary partial trace -/

/-- **Main theorem.**  The ordinary (unnormalized) partial trace over the newest
qubit maps the finite-stage density matrix `rho_(n+1)` exactly onto `rho_n`.
The reason is that the newest one-qubit density factor has ordinary matrix
trace one. -/
theorem qubitPartialTrace_qubitPureMixedDensity (pure : ℕ → Bool) (n : ℕ) :
    qubitPartialTrace n (qubitPureMixedDensity pure (n + 1)) =
      qubitPureMixedDensity pure n := by
  rw [show (qubitPureMixedDensity pure (n + 1) : QubitTensorPower (n + 1)) =
      qubitElementaryTensor n (qubitDensityFactor pure n) (qubitPureMixedDensity pure n) from
    qubitPureMixedDensity_succ_eq_elementaryTensor pure n]
  exact qubitPartialTrace_densityFactor_elementaryTensor pure n _

/-! ## The ordinary full-trace tower identity, via the partial trace -/

/-- The ordinary tower trace at stage `n + 1` of the density matrix equals the
ordinary tower trace at stage `n` of its partial trace over the newest qubit.
This is the partial-trace route, stated with the ordinary trace
`qubitTensorFullTrace`. -/
theorem qubitTensorFullTrace_succ_density_eq_partialTrace (pure : ℕ → Bool) (n : ℕ) :
    qubitTensorFullTrace (n + 1) (qubitPureMixedDensity pure (n + 1)) =
      qubitTensorFullTrace n
        (qubitPartialTrace n (qubitPureMixedDensity pure (n + 1))) :=
  matrixTraceOver_eq_of_qubitPartialTrace n (qubitTensorFullTrace n) _

/-- **Full-trace tower identity.**  The ordinary trace of the density matrices
is constant along the tower: stage `n + 1` and stage `n` give the same value,
because the partial trace over the newest qubit carries `rho_(n+1)` to
`rho_n`. -/
theorem qubitTensorFullTrace_succ_qubitPureMixedDensity (pure : ℕ → Bool) (n : ℕ) :
    qubitTensorFullTrace (n + 1) (qubitPureMixedDensity pure (n + 1)) =
      qubitTensorFullTrace n (qubitPureMixedDensity pure n) := by
  rw [qubitTensorFullTrace_succ_density_eq_partialTrace,
    qubitPartialTrace_qubitPureMixedDensity]

/-- **Ordinary trace one, obtained through the partial-trace route.**  Iterating
the tower identity down to stage `0` shows that every finite-stage density
matrix has ordinary matrix trace one.  (The same statement is available in
`AristotleCandidates.FiniteDensityMatrix` by a direct computation; here it is a
consequence of the partial-trace compatibility.) -/
theorem qubitTensorFullTrace_qubitPureMixedDensity_via_partialTrace
    (pure : ℕ → Bool) (n : ℕ) :
    qubitTensorFullTrace n (qubitPureMixedDensity pure n) = 1 := by
  induction n with
  | zero => simp [qubitTensorFullTrace_zero_apply, qubitPureMixedDensity]
  | succ n ih => rw [qubitTensorFullTrace_succ_qubitPureMixedDensity, ih]

/-! ## The normalized partial trace introduces a factor `1 / 2` -/

/-- The *normalized* partial trace does **not** preserve the density matrices:
it returns `(1 / 2) • rho_n`, the factor `1 / 2` being the reciprocal of the
qubit dimension. -/
theorem qubitPartialTraceNormalized_qubitPureMixedDensity_succ (pure : ℕ → Bool) (n : ℕ) :
    qubitPartialTraceNormalized n (qubitPureMixedDensity pure (n + 1)) =
      (1 / 2 : ℂ) • qubitPureMixedDensity pure n := by
  rw [qubitPartialTraceNormalized, LinearMap.smul_apply,
    qubitPartialTrace_qubitPureMixedDensity]

end StabilizerHyperfinite
