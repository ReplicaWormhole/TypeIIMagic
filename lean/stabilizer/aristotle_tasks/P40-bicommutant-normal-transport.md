# P40 — bicommutant and normal transport boundary

## Context declaration

- **Source basis:** `main.tex:1970-2004`

## Mathematical target

Create only `AristotleCandidates/BicommutantNormalTransport.lean`. Starting
from P39's GNS unitary, use the checked bicommutant core to prove the algebraic
conjugation formulas for generated bicommutants. Package the precise additional
normality/extension assumptions required to turn this into a normal star
equivalence and to transport normal functionals or folia.

## Boundary

Do not invoke an unproved double-commutant theorem, quasi-equivalence theorem,
or spatial tensor-product theorem. If pinned Mathlib lacks the analytic step,
record its exact statement as an explicit interface, not an axiom.

## Acceptance criteria

`lake build AristotleCandidates.BicommutantNormalTransport` succeeds with no
placeholder and clearly separates algebraic bicommutant facts from analytic
closure/normality facts.
