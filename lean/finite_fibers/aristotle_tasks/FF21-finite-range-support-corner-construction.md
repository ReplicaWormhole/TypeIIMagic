# FF21 — finite-range stabilizer support-corner construction

Read `manuscript/main.tex`, especially the general stabilizer and support-corner
discussion, plus all checked `FiniteFiber` modules.  Create only
`FiniteFiber/FiniteRangeSupportCornerConstruction.lean`.

Formalize the *geometric/operator-algebraic input* missing from FF20 for a
countable locally finite lattice equipped with a consistent finite-range
stabilizer system.  Give an explicit Lean structure for the data actually
needed: an exhaustion by finite regions, compatible finite stabilizer support
projections, and their realization in the supplied GNS operator model.  Prove
every finite-stage compatibility and monotonicity fact derivable from that
data.  State the strong-limit existence as an explicit premise unless it is
constructed in the pinned Mathlib; do not replace it by an axiom.

The intended output is a reusable theorem/structure whose conclusion supplies
the decreasing support projections and a candidate nonzero corner projection
`q` to FF20.  If finite range alone does not establish a required compatibility
or nonzeroness property, isolate the exact additional condition (for example
local-code consistency along the exhaustion) and explain why it is necessary.
Do not claim a trace, fullness, type classification, or no-type-III result in
this packet.

No `sorry`, `admit`, axioms, `opaque`, `unsafe`, or `native_decide`.  Return a
compiling file, the exact build command/result, and a short list separating
facts proved from the finite-range definition from supplied analytic premises.
