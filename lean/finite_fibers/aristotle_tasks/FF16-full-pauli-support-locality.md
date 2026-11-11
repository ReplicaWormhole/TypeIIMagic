# FF16 — full-Pauli support and finite-region locality

Read `manuscript/main.tex`, especially the short-range basis and local-algebra
discussion. Work only in `formalization_finite_fibers`.

Create only `FiniteFiber/FullPauliSupportLocality.lean`. Build on FF15,
`FullPauliLattice`, `FiniteRegionQubitAlgebra`, and
`FiniteRegionFullPauliMultiplication`. For a `FullPauliWord Site` whose label
support lies in a finite region `F`, construct its finite-region matrix and
prove that enlarging `F` pads it by the identity through `finiteRegionEmbed`.
State and prove the exact equivalence between the word's explicit finite
support predicate and availability of this local matrix realization; do not
identify it with membership in an unspecified global algebra.

This is finite infrastructure only. Do not construct a quasilocal completion,
state, GNS representation, normality, or a von Neumann algebra. No `sorry`,
`admit`, axiom, `opaque`, `unsafe`, or `native_decide`. If an exact support
equivalence is unavailable, return the strongest compiling one-way locality
theorem and name the missing finite-support lemma.

Acceptance: `lake build FiniteFiber.FullPauliSupportLocality` succeeds and the
response lists every supplied finite-region hypothesis.
