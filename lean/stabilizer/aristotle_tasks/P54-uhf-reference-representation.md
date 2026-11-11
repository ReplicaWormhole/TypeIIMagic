# P54 — faithful UHF reference representation

## Context declaration

- **Infrastructure only:** construct a reusable compatible representation of
  the dyadic algebra; this packet makes no manuscript claim.

## Plan alignment

- **Package and lane:** `P54`; Lane `H`.
- **Predecessors:** none.
- **Gate discharged:** provide a faithful compatible Hilbert/operator
  representation from finite dyadic stages.
- **Forbidden downstream claims:** no assumed infinite tensor-product Hilbert
  space, regional alpha, state identity, spatial tensor product, factor type,
  or trace/weight classification.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Create only `AristotleCandidates/UHFReferenceRepresentation.lean`. Starting
from the checked dyadic finite-stage system, construct compatible finite-stage
Hilbert-space/operator representations and a faithful representation of the
algebraic limit, or the strongest concrete pre-C-star representation supported
by pinned Mathlib. Do not postulate an infinite tensor-product Hilbert space.
If completion of the algebraic representation requires an unavailable API,
state exactly the minimal isometric-representation interface and prove all
finite-stage compatibility and faithfulness facts below that boundary.

## Auxiliary assumptions

List any completion, boundedness, isometry, or faithfulness premise that cannot
be constructed. Do not conceal it in typeclass inference.

## Files and imports

Create only `AristotleCandidates/UHFReferenceRepresentation.lean`. Reuse
`Formalization.DyadicTensorTower`,
`AristotleCandidates.AlgebraicLimitOperatorRepresentation`, and
`AristotleCandidates.ConcreteCStarCompletion` as appropriate.

## Acceptance criteria

- `lake build AristotleCandidates.UHFReferenceRepresentation` succeeds.
- The response separates constructed finite-stage/limit data from any supplied
  completion interface.
- No placeholder, forbidden declaration, or infinite-tensor-product assumption
  is introduced.
