# FF18 — coherent directed system of actual local full-Pauli algebras

Read `manuscript/main.tex` and work only in `formalization_finite_fibers`.

Create only `FiniteFiber/FullPauliDirectedLocalSystem.lean`. From FF16--FF17
and the already checked finite-region embedding coherence, package a directed
system of finite local matrix algebras, actual full-Pauli images, and compatible
finite stabilizer densities along finite-region inclusions. Prove the exact
finite-stage restriction formula and its composition law.

This package is still finite/direct-limit data. Do not call its algebraic
direct limit a C-star algebra, assert positivity on a quotient, or construct a
global state/GNS representation. Do not add axioms or placeholders.

Acceptance: `lake build FiniteFiber.FullPauliDirectedLocalSystem` succeeds and
the response reports the remaining completion/state obligations.
