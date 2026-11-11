# P48 — general-lattice local-code projection tower

## Context declaration

- **Source basis:** `main.tex:1026-1195`.

## Plan alignment

- **Package and lane:** `P48`; Lane `G`.
- **Predecessors:** none.
- **Gate discharged:** construct the decreasing local-code projections and
  expose the exact data needed to obtain their limiting projection `q`.
- **Forbidden downstream claims:** no trace on the corner, no faithfulness,
  finiteness, fullness, global weight, or type-III conclusion.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Create only `AristotleCandidates/GeneralLatticeProjectionTower.lean`. Formalize
a general countable lattice exhaustion, the finite stabilizer constraints seen
at each stage, the corresponding local-code projections, and their decreasing
order relation. Construct the strong-limit projection `q` using supported
Mathlib APIs if possible. If the pinned library cannot express or prove the
monotone strong limit, isolate precisely that analytic step as a named
structure field and prove all consequences that follow from it. The result
must not assume a hyperbolic basis or tensor-factor coordinates.

## Auxiliary assumptions

List every needed exhaustion, local finiteness, representation, convergence,
or limit-projection hypothesis explicitly. The manuscript-facing result is
conditional whenever such a field is not derived from the cited source data.

## Files and imports

Create only `AristotleCandidates/GeneralLatticeProjectionTower.lean`. Reuse the
finite stabilizer/projector modules and pinned operator APIs; do not import a
later P47--P61 packet.

## Acceptance criteria

- `lake build AristotleCandidates.GeneralLatticeProjectionTower` succeeds.
- The exact Lean declaration representing `q` and every convergence premise is
  reported.
- No placeholder or hidden analytic assumption is introduced.
- The result stays in Lane G and makes none of the forbidden conclusions.
