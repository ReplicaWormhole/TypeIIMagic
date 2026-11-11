# P12 — finite stabilizer projector: normalized and ordinary trace

Work only on a new module named
`AristotleCandidates/FiniteStabilizerDimension.lean`.

Import and reuse `AristotleCandidates.FiniteStabilizerProjector` and
`AristotleCandidates.FiniteDensityMatrix`. Work in the concrete finite qubit
stage `QubitTensorPower n`.

Let `G` be a finite group and `U : G ->* QubitTensorPower n`. Assume that
every nonidentity group element has vanishing normalized qubit trace:

    qubitTensorTrace n (U g) = 0  for g != 1.

Use the already checked normalized group-average calculation to prove

    qubitTensorTrace n (groupAverage U) = (|G| : complex)^(-1),

and then use `qubitTensorTrace_eq_smul_qubitTensorFullTrace` to prove the
ordinary finite-stage trace formula

    qubitTensorFullTrace n (groupAverage U) =
      (2 : complex)^n * (|G| : complex)^(-1).

All dimension factors must appear explicitly. The result should remain
conditional on the vanishing-trace hypothesis and should not claim that `U`
is a Pauli realization unless such data is explicitly supplied.

Optional only if Mathlib’s exact APIs make it fully checkable: derive the
matrix-rank formula for the group-average idempotent in a concrete matrix
model. Do not add axioms, `sorry`, or `admit` if rank APIs block it; the two
trace formulas above are the required deliverable. Do not claim a von
Neumann-algebra, hyperfinite, GNS, or factor result. Build with:

    lake build AristotleCandidates.FiniteStabilizerDimension
