# P49 — finite-stage trace and compressed quasi-local corner

## Context declaration

- **Source basis:** `main.tex:1133-1261`.

## Plan alignment

- **Package and lane:** `P49`; Lane `G`.
- **Predecessors:** `P47`, `P48`, both integrated and locally audited before submission.
- **Gate discharged:** prove finite-stage cyclicity and its compatible compressed
  quasi-local limit with finite codespace density data explicit.
- **Forbidden downstream claims:** no normality, faithfulness on the von Neumann
  corner, fullness, global weight, or type-III exclusion.

## Mathematical target

Create only `AristotleCandidates/FiniteCornerTrace.lean`. From the integrated
projection tower and explicit finite codespace density matrices, define the
finite-stage compressed functionals, prove compatibility and cyclicity, and
construct the induced algebraic/continuous functional on the compressed
quasi-local C-star algebra to the extent supported by the existing completion
interfaces.

## Auxiliary assumptions

Name every density, positivity, normalization, compatibility, boundedness, or
C-star completion premise not derived in this module. Mark the theorem conditional.

## Files and imports

Create only `AristotleCandidates/FiniteCornerTrace.lean`; import P47 and P48
plus the existing finite density/trace and algebraic inductive-limit modules.

## Acceptance criteria

`lake build AristotleCandidates.FiniteCornerTrace` succeeds without forbidden
declarations. Report exact trace declarations, assumptions, and Plan alignment.
