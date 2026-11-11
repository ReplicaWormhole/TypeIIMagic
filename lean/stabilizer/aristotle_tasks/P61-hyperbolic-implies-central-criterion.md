# P61 — reconnect the hyperbolic model to the central criterion

## Context declaration

- **Infrastructure only:** comparison theorem between the two completed lanes;
  it does not supply either lane's missing hypotheses.

## Plan alignment

- **Package and lane:** `P61`; Lane `reconnection`.
- **Predecessors:** `P51`, `P59`, both integrated and locally audited before submission.
- **Gate discharged:** show the explicit Lane-H model satisfies the finite-corner
  criterion used in Lane G.
- **Forbidden downstream claims:** no reverse implication, no claim that the
  general lattice has hyperbolic coordinates, and no direct-integral statement.

## Mathematical target

Create only `AristotleCandidates/HyperbolicImpliesCentralCriterion.lean`. Starting
from the P59 spatial factor model and P51 project-local criterion, construct a
nonzero finite projection/corner in the hyperbolic regional algebra and prove
that every nonzero central projection meets it as required. Keep this as a
comparison theorem; do not identify the two proof routes.

## Auxiliary assumptions

List every transport-of-finiteness or central-support premise not already proved.

## Files and imports

Create only `AristotleCandidates/HyperbolicImpliesCentralCriterion.lean`; import
P51 and P59.

## Acceptance criteria

`lake build AristotleCandidates.HyperbolicImpliesCentralCriterion` succeeds
without forbidden declarations and states the direction of implication exactly.
This packet is disabled in the automatic queue until separately approved.
