# P55B — coherent source-limit to UHF bridge

## Context declaration

- **Infrastructure only:** identify the algebraic source assembled in P53 with
  the dyadic finite-coordinate system assembled from P55A. No regional C-star
  or manuscript theorem is completed here.

## Plan alignment

- **Package and lane:** `P55B`; Lane `H`.
- **Predecessors:** `P53`, `P55A`, both integrated and locally audited before
  submission.
- **Gate discharged:** prove finite-stage coherence and the resulting
  algebraic direct-limit equivalence, including separate finite and infinite
  coordinate-index branches.
- **Forbidden downstream claims:** no operator-range completion, regional
  C-star alpha, state identity, GNS tensor split, factor classification, or
  trace/weight conclusion.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Create only `AristotleCandidates/LocalHyperbolicSourceUHFBridge.lean`.

First construct coherent finite orderings of the nested finite coordinate
blocks `A.Coord n` (or an equivalent finite-set-indexed dyadic system) and
prove that the P55A stage maps commute with the P53 source connecting maps.
Do not assume the commuting square. Define the resulting coordinate-dyadic
direct limit and construct

`A.sourceToCoordinateDyadic :
  A.SourceLimit ≃⋆ₐ[ℂ] A.CoordinateDyadicLimit`.

Then prove both mathematically distinct endpoint statements:

1. if `I` is finite, the exhaustion reaches a terminal coordinate block and
   the source limit is star-equivalent to `QubitTensorPower (Nat.card I)`;
2. if `I` is infinite, the stage cardinalities are cofinal in `Nat`, and the
   coordinate-dyadic limit is star-equivalent to `QubitUHFAlgebra`.

Export the composite infinite-branch equivalence as
`A.sourceUHFEquiv : A.SourceLimit ≃⋆ₐ[ℂ] QubitUHFAlgebra` under the exact
`Infinite I` hypothesis, and an explicitly named finite-branch equivalence.
Prove formulas on every canonical stage image and uniqueness from those
formulas.

## Auxiliary assumptions

The P52 exhaustion and P53 `stage_surjective` are available. Do not assume a
coherent enumeration, a commuting square, cofinality, or a direct-limit
equivalence unless a genuine obstruction in pinned Mathlib makes construction
impossible. In that event stop at the smallest proved theorem, name the exact
missing lemma/API, and do not package the desired equivalence as a field.

## Files and imports

Create only `AristotleCandidates/LocalHyperbolicSourceUHFBridge.lean`; import
P53, P55A, and `Formalization.DyadicTensorTower`. Do not edit predecessors.

## Acceptance criteria

- `lake build AristotleCandidates.LocalHyperbolicSourceUHFBridge` passes.
- The coherence squares and finite/infinite branch hypotheses are explicit.
- No `sorry`, `admit`, new axiom, supplied coherent family, or supplied
  direct-limit equivalence is introduced.
- The response reports exact declarations, commands, assumptions, and any
  genuine blocked boundary without making downstream claims.
