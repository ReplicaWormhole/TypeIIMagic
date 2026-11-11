# P10 — density matrices and ordinary partial trace

Work only on a new module named
`AristotleCandidates/DensityPartialTrace.lean`.

Import and reuse `AristotleCandidates.FiniteDensityMatrix` and
`AristotleCandidates.OneQubitPartialTrace`.  The scope is finite-dimensional
only.

Let `rho_n := qubitPureMixedDensity pure n`.  Prove the exact compatibility
of the recursive density matrices with the **ordinary, unnormalized** partial
trace over the newest qubit:

    qubitPartialTrace n rho_(n+1) = rho_n.

The reason is that the newest one-qubit density factor has ordinary matrix
trace one.  Make that fact explicit in the proof.  If useful, first prove the
more general elementary-tensor calculation for
`qubitDensityFactor pure n` tensored with `rho_n`.

As a corollary, prove the ordinary full-trace tower identity for these density
matrices, using the project’s `qubitTensorFullTrace` rather than silently
switching to `qubitTensorTrace`.  You may restate an already checked theorem
only if the new theorem genuinely expresses the partial-trace route.

Do not claim that the normalized partial trace preserves `rho_n`: it instead
introduces a factor `1/2`.  If you formalize that version, state this factor
explicitly.  Do not add `sorry`, `admit`, or axioms; do not modify existing
files; and do not make any infinite tensor-product, C-star, GNS, normality, or
factor-classification claim.  The module must build with:

    lake build AristotleCandidates.DensityPartialTrace
