# P60R — standard positive-cone semifiniteness for the full-corner weight

## Context declaration

- **Infrastructure only:** repair the optional Lane-G global-weight theorem.
  This packet makes no new manuscript claim and does not alter the accepted
  no-central-type-III result of P51.

## Plan alignment

- **Package and lane:** `P60R`; Lane `G` optional recovery.
- **Predecessors:** `P51`, `P50U`, both integrated and locally audited.
  The existing `FullCornerSemifiniteWeight.lean` is an unaccepted P60 recovery
  baseline, not a semantic predecessor: every declaration it is reused for
  must remain locally compiled and be rechecked in this packet.
- **Gate discharged:** prove the standard positive-cone semifiniteness of the
  explicitly constructed global extended-positive trace under the same named
  countable comparison-family hypothesis.
- **Forbidden downstream claims:** no claim that fullness alone produces the
  comparison family/global weight, no direct-integral theorem, no Lane-H
  factorization, and no assertion that a compression certificate by itself is
  standard semifiniteness.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Edit only `AristotleCandidates/FullCornerSemifiniteWeight.lean`.

The current `globalWeight_semifinite` proves that finite comparison projections
give finite compressions. Replace the exported use of that certificate by a
standard positive-cone predicate, for example:

`∀ x ∈ M, x.IsPositive → x ≠ 0 → ∃ y ∈ M,
  y.IsPositive ∧ y ≠ 0 ∧ y ≤ x ∧ globalWeight q Ω v y < ⊤`.

Define the weight's public domain to be positive elements of `M` (or an
equivalent proved subtype/API), and formulate additivity, homogeneity,
normality, faithfulness, traciality, and semifiniteness there. The extended
weight must not be presented as a linear functional on arbitrary operators.

For a nonzero positive `x`, construct its positive square root/factorization
inside the concrete von Neumann algebra, `x = a^* a`, using the pinned Mathlib
continuous functional calculus or new locally proved C-star lemmas. With the
finite comparison projection `p_N`, use

`y_N = a^* p_N a`.

Prove that some `y_N` is nonzero, `y_N` is positive, `y_N ≤ x`, and
`globalWeight q Ω v y_N < ⊤`; derive finite weight from the existing tracial
law and the finite compression `p_N (a a^*) p_N`. The result may continue to
assume `ComparisonFamily`; construction of that family from fullness remains a
separate unproved sigma-finite comparison theorem.

Repair the exported bundle and `full_finite_corner_globalized_weight` so they
state only laws actually proved. Retain the current useful compression theorem
under an honest name rather than deleting it.

## Auxiliary assumptions

No new positive-square-root, factorization, order-density, normality,
faithfulness, traciality, or semifiniteness field may be added. Use only the
existing explicit `ComparisonFamily`, P51/P50U hypotheses, and facts proved in
this file. If pinned Mathlib lacks a needed CFC fact, develop the smallest
local lemma; do not replace it with an axiom or a supplied interface.

## Files and imports

Edit only `AristotleCandidates/FullCornerSemifiniteWeight.lean`; retain the
current imports or add the precise Mathlib CFC/order import needed for a proved
positive square root. Do not modify P51, P50U, the manuscript, or unrelated
files.

## Acceptance criteria

- `lake build AristotleCandidates.FullCornerSemifiniteWeight` passes.
- The standard positive-cone semifiniteness theorem has the literal nonzero
  positive subelement/order-below conclusion above (or a formally equivalent
  standard definition), not merely finite compressions.
- The square-root/factorization and order inequality are proved, with no
  `sorry`, `admit`, new axiom, or new supplied interface.
- The response reports exact declarations, imports, commands, the retained
  comparison-family assumption, and confirms the P51 provenance correction.
