# P59T — regional trace and weight

## Context declaration

- **Source basis:** `main.tex:1954-1967`.

## Plan alignment

- **Package and lane:** `P59T`; Lane `H`.
- **Predecessors:** P59R and P50U, integrated and locally audited.
- **Gate discharged:** prove finite-pure tracial-state and infinite-pure
  faithful normal semifinite-weight conclusions with standard normality.
- **Forbidden downstream claims:** no global Lane-G weight, no type-III
  central-decomposition theorem, and no tracial state in the infinite branch.

## Mathematical target

Create only `AristotleCandidates/RegionalTraceWeight.lean`. Treat finite and
infinite pure-coordinate cases separately. In the finite case construct and
prove a faithful ultraweak-normal tracial state. In the infinite case, under an
explicit `[Infinite]` pure-index hypothesis, construct a faithful normal
semifinite tracial weight and prove it has value infinity on the unit. Use the
P50U standard ultraweak-normal interface or prove the requisite comparison;
do not reuse P59's project-local vector-normal predicate.

## Auxiliary assumptions

Only P59R's proved factor model, P58's inherited named weak-closure inputs,
and explicitly listed countability/basis hypotheses for a trace sum. No
supplied trace, normality, faithfulness, traciality, or semifiniteness field is
allowed.

## Files and imports

Create only `AristotleCandidates/RegionalTraceWeight.lean`; import P59R and
P50U.

## Acceptance criteria

`lake build AristotleCandidates.RegionalTraceWeight` succeeds without `sorry`,
axiom, local-normality substitute, or a tracial-state claim in the infinite
branch. Report each branch and standard-normality proof separately.
