# P47 — center and finite-projection core

## Context declaration

- **Infrastructure only:** reusable concrete von Neumann-algebra definitions and
  order lemmas; this packet makes no manuscript claim.

## Plan alignment

- **Package and lane:** `P47`; Lane `G`.
- **Predecessors:** none.
- **Gate discharged:** provide the algebraic center/corner/fullness vocabulary
  required by Lane G.
- **Forbidden downstream claims:** no projection tower, corner trace, fullness
  of the manuscript projection, global weight, or type-III exclusion.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Create only `AristotleCandidates/CenterFiniteProjectionCore.lean`. For the
project's concrete operator-algebra model, define central elements and central
projections, Murray--von Neumann subequivalence/equivalence of projections,
finite projections, corners, central support, and fullness. Prove the basic
order, compression, and central-intersection lemmas needed later, including the
purely algebraic implication that a full projection meets every nonzero central
projection nontrivially. Reuse Mathlib definitions when they genuinely express
the same notion; otherwise use explicit project-local predicates.

## Auxiliary assumptions

None beyond the typeclass assumptions stated by each definition. Do not claim
operator-topology, normality, or factor classification facts.

## Files and imports

Create only `AristotleCandidates/CenterFiniteProjectionCore.lean`. Start from
`Mathlib.Analysis.VonNeumannAlgebra.Basic` and
`AristotleCandidates.BicommutantVonNeumannCore`; import nothing from a later
P47--P61 packet.

## Acceptance criteria

- `lake build AristotleCandidates.CenterFiniteProjectionCore` succeeds.
- No `sorry`, `admit`, new axiom, `opaque`, or `unsafe` declaration occurs.
- The response lists the exact definitions and proved lemmas and distinguishes
  algebraic projection facts from unproved analytic facts.
- No forbidden downstream claim is stated or smuggled in as a structure field.
