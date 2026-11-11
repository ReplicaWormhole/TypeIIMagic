# P2 — finite pure sector algebraic trace wrapper

Work only on a new module named AristotleCandidates/FinitePureFactor.lean.

Import Formalization.CoordinateQuadraticPhaseTrace.  The existing theorem
StabilizerHyperfinite.exists_coordinateQuadraticPhase_finitePureQubitUHFTrace
constructs, from explicit regional Pauli-word/multiplier/involution data, a
star-algebra equivalence

    e : A ≃⋆ₐ[ℂ] (Matrix p p ℂ ⊗[ℂ] QubitUHFAlgebra)

and an algebraic tracial state tau satisfying

    tau (e.symm (a ⊗ₜ[ℂ] u)) =
      normalizedMatrixTrace p a * qubitUHFTrace u.

Create a clearly named wrapper definition or theorem for the finite-pure
regional model that exposes this result without changing any of its hypotheses.
The documentation and theorem statement must say algebraic and must not claim
a C-star completion, normality, a GNS result, hyperfiniteness, or factor
classification.

No sorry, admit, axiom, or changes outside the owned module are allowed.
Compile the module directly with:

    lake build AristotleCandidates.FinitePureFactor
