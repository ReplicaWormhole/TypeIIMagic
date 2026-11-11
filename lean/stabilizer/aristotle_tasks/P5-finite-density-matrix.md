# P5 — finite pure/mixed density matrix

Work only on a new module named AristotleCandidates/FiniteDensityMatrix.lean.

Use Formalization.QubitMatrixState, Formalization.FinitePureMixedQubitState,
and the finite-qubit Pauli modules.  Formalize the finite-dimensional density
matrix realization of the already checked pure/mixed functional.

The intended mathematical statement at each finite stage is:

    omega_n(a) = Tr(rho_n a),

where rho_0 is the scalar unit and rho_(n+1) is obtained from rho_n by
tensoring the new coordinate with either the pure density matrix
diag(1,0), when pure n is true, or the maximally mixed density matrix
(1/2) I, when pure n is false.  Make all normalizations explicit: rho_n must
have ordinary matrix trace one, and no normalized trace may be substituted
without its compensating dimension factor.

Preferred deliverable:

1. define the recursive finite density matrices in the concrete
   QubitTensorPower representation;
2. prove the trace-pairing formula for qubitPureMixedState on arbitrary
   finite-stage matrices; and
3. derive the selected-Z Pauli expectation formula as a corollary, reusing
   existing lemmas where helpful.

If the full arbitrary-stage pairing is blocked by a missing Matrix/Tensor API,
do not add axioms, sorry, or admit.  Instead, prove the strongest fully
checked one-qubit or one-step result possible in the owned module and write
the exact API obstruction in that module documentation.

Do not change existing project files.  Do not add an infinite GNS, C-star
completion, normality, or factor-classification claim.  The module must build
with:

    lake build AristotleCandidates.FiniteDensityMatrix
