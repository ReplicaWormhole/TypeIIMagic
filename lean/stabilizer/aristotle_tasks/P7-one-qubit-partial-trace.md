# P7 — one-qubit partial-trace infrastructure

Work only on a new module named AristotleCandidates/OneQubitPartialTrace.lean.

Build a concrete finite-dimensional partial-trace interface for the recursive
matrix realization QubitTensorPower (n + 1) =
Matrix (Fin 2) (Fin 2) (QubitTensorPower n).

Define the ordinary partial trace over the newest qubit by summing diagonal
matrix entries:

    ptrace(a) = a 0 0 + a 1 1.

Give it the appropriate complex-linear-map structure.  Prove the finite
identities needed later for density matrices:

1. ptrace of an identity-qubit embedding Matrix.scalar x is 2 times x;
2. ptrace on an elementary matrix tensor is the ordinary two-by-two matrix
   trace times the coefficient;
3. the ordinary matrix trace of the large matrix is the ordinary coefficient
   trace after partial trace, in the concrete recursive matrix representation.

Keep all dimension factors explicit.  Do not call ptrace a normalized partial
trace unless it is divided by 2, and do not identify it with a state.

If the fully generic third identity is blocked by a missing matrix API, prove
the strongest checked elementary-tensor version and document the exact missing
lemma.  Do not use sorry, admit, or axiom.  Do not modify existing project
files or make C-star, GNS, normality, or factor claims.  Build the owned module
with:

    lake build AristotleCandidates.OneQubitPartialTrace
