# FF17 — actual finite stabilizer densities from full Pauli words

Read `manuscript/main.tex` and work only in `formalization_finite_fibers`.

Create only `FiniteFiber/FullPauliStabilizerDensity.lean`. Using FF15--FF16,
connect an explicitly finite consistent subgroup of `FullPauliWord Site` to
its finite-region matrix image. Prove that the group average is the same
positive trace-one stabilizer density already constructed abstractly in the
finite-density layer, with the exact sign/central-phase convention preserved.
State all realization, consistency, and finite-support assumptions explicitly.

Do not infer a countable stabilizer system from short-range order, and do not
claim a quasilocal state or GNS result. No placeholders or new axioms.

Acceptance: `lake build FiniteFiber.FullPauliStabilizerDensity` succeeds; the
response distinguishes the checked finite density identity from all global
claims.
