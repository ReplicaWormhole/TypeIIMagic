# FF22 — trace and fullness of the finite-range stabilizer corner

Read `manuscript/main.tex` and the outputs of FF20--FF21.  Create only
`FiniteFiber/FiniteRangeTracialCorner.lean`.

Starting from the concrete finite-range support-corner package of FF21 and the
finite full-Pauli/quasilocal/GNS infrastructure, prove the strongest available
bridge from the canonical stabilizer vector state to a faithful normal positive
tracial state on `q M q`, and prove that `q` is full.  Work in an explicitly
supplied concrete GNS/von-Neumann representation; all normality and strong-limit
claims must be stated exactly, not hidden in typeclass inference.

The mathematical objective is to derive the three substantive FF20 premises:

1. the support-corner vector functional is tracial and faithful on `q M q`;
2. the support projection is nonzero; and
3. the orbit/fullness argument gives central support `1`.

Finite range by itself may prove fewer facts than these.  Prove every implication
you can, and package any genuinely unavailable bridge as a named explicit
hypothesis with a counterexample-sensitive explanation.  Do not assert the
no-type-III conclusion yet; that is FF23.

No placeholders or new axioms.  Return the complete candidate file, exact
`lake build` result, and a table of derived versus still conditional premises.
