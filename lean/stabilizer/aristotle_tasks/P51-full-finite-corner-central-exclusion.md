# P51 — full finite corner and central type-III exclusion

## Context declaration

- **Source basis:** `main.tex:1418-1539`.

## Plan alignment

- **Package and lane:** `P51`; Lane `G`.
- **Predecessors:** `P47`, `P50`, both integrated and locally audited before submission.
- **Gate discharged:** prove `q` finite and full, then produce a nonzero finite
  projection in every nonzero central summand and state the type-III obstruction.
- **Forbidden downstream claims:** no direct integral, no trivial-center claim,
  no global faithful normal semifinite weight, and no Lane-H tensor factorization.

## Mathematical target

Create only `AristotleCandidates/FullFiniteCornerCentralExclusion.lean`. Use the
P50 faithful normal tracial state to prove finiteness of `q`; formalize the
manuscript fullness argument; and prove that for every nonzero central projection
`z`, the projection `zq` is nonzero and finite in the corner/summand `z M_Gamma`.
Define or reuse a project-local predicate expressing the resulting obstruction
to a type-III central summand. A finite-dimensional subalgebra is not sufficient.

## Auxiliary assumptions

State every fullness or comparison premise not derived from the manuscript data.
Do not assume or manufacture a global trace.

## Files and imports

Create only `AristotleCandidates/FullFiniteCornerCentralExclusion.lean`; import
P47 and P50.

## Acceptance criteria

`lake build AristotleCandidates.FullFiniteCornerCentralExclusion` succeeds
without forbidden declarations. The response must identify the exact theorem
whose conclusion contains the nonzero finite projection `zq`.
