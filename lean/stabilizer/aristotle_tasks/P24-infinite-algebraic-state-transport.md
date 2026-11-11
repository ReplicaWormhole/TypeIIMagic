# P24 — infinite algebraic state transport along alpha

## Context declaration

- **Source basis:** `main.tex:1921-1944`

## Mathematical target

Create only `AristotleCandidates/InfiniteAlgebraicStateTransport.lean`.

Build directly on P23's `RegionalLimitData` and on
`algebraicLimitStatePullback`. Given supplied compatible target-stage algebraic
states, define the state pulled back along the P23 algebraic `alpha`. Prove:

1. it is an algebraic state when every target-stage functional is one;
2. its value on every source finite-stage representative is the corresponding
   target-stage expectation after the supplied stage equivalence; and
3. it is uniquely determined by that finite-stage formula.

If appropriate, add a conditional corollary combining P17's finite stabilizer
indicator formula with this direct-limit transport, but keep the finite word
realization and all compatibility hypotheses supplied.

## Auxiliary assumptions

- a P23 `RegionalLimitData` object (all finite-stage equivalences and their
  coherence are supplied);
- compatible target-stage algebraic states; and
- where a stabilizer formula is used, an explicitly supplied finite word/stabilizer
  realization at every stage, compatible with connecting maps.

## Boundary

This is an infinite algebraic direct-limit state, not a C-star-continuous or
normal state. Do not claim a C-star completion, GNS equivalence, spatial tensor
product, von Neumann closure, quasi-equivalence, factor type, hyperfiniteness,
or trace/weight. Do not introduce gLU, refinement, or layer-coherence.

## Files and imports

Use `AristotleCandidates.InfiniteAlgebraicRegionalEquiv` and
`Formalization.AlgebraicLimitStateTransport`; do not modify existing files.

## Acceptance criteria

- `lake build AristotleCandidates.InfiniteAlgebraicStateTransport` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The result identifies the exact finite-stage formula and all explicitly
  supplied hypotheses.
