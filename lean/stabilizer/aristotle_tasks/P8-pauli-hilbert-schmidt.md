# P8 — finite Pauli Hilbert-Schmidt orthogonality

Work only on a new module named AristotleCandidates/FinitePauliOrthogonality.lean.

Import Formalization.FiniteQubitPauli and
Formalization.FinitePureMixedQubitState.  Prove finite-stage normalized-trace
orthogonality for the concrete ordered Pauli words.

Preferred theorem:

    qubitTensorTrace n
      (star (finiteQubitPauliWord n v) * finiteQubitPauliWord n w)
      = if v = w then 1 else 0.

All phase factors from the ordered X/Z convention must be tracked exactly; do
not replace the equality by an up-to-phase assertion.  The proof may use the
existing multiplication/star theorems and the all-mixed product-state formula.

At minimum, if the full two-label theorem is blocked, prove the one-label
normalized trace theorem:

    qubitTensorTrace n (finiteQubitPauliWord n v)
      = if v = 0 then 1 else 0,

and document the exact remaining phase or finite-label equality obstacle.

Do not add axioms, sorry, or admit.  Do not modify existing project files or
claim C-star, GNS, normality, or factor results.  Build the owned module with:

    lake build AristotleCandidates.FinitePauliOrthogonality
