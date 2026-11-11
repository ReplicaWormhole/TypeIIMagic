# P4 — finite pure/mixed qubit model sanity check

Work only on a new module named AristotleCandidates/FiniteModelSanity.lean.

Import Formalization.FiniteQubitPauliSelection and
Formalization.FinitePureMixedQubitState.  Import
Formalization.PureCoordinateNotTracial when using the direct-limit
nontraciality theorem.  Produce a compact theorem that
combines existing lemmas to state the finite-coordinate model in the form:

    qubitPureMixedState pure n (finiteQubitPauliWord label)
      = if finiteQubitPauliSelectedZ pure n label then 1 else 0.

Then record the exact finite/infinite direct-limit boundary already supported
by the project: the all-mixed specialization is algebraically tracial, while
the presence of a pure coordinate obstructs algebraic traciality.  Reuse
existing theorems and give the smallest compiling proof.  Do not add an
infinite GNS, factor, or classification claim.

No sorry, admit, or axiom; do not change any existing file.  Compile with:

    lake build AristotleCandidates.FiniteModelSanity
