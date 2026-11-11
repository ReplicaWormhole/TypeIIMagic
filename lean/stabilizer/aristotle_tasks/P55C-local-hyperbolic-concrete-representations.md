# P55C — faithful concrete representations for the source and regional limits

## Context declaration

- **Infrastructure only:** construct concrete C-star models from the algebraic
  P53/P55B data. This package does not yet extend alpha between the closures.

## Plan alignment

- **Package and lane:** `P55C`; Lane `H`.
- **Predecessors:** `P53`, `P54`, `P55B`, all integrated and locally audited
  before submission.
- **Gate discharged:** construct faithful algebraic operator representations
  and their closed operator-range C-star algebras with dense embeddings.
- **Forbidden downstream claims:** no completed C-star alpha, product-state
  identity, GNS tensor split, factor classification, or trace/weight theorem.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Create only
`AristotleCandidates/LocalHyperbolicConcreteRepresentations.lean`.

In the infinite-coordinate branch, transport P54's constructed faithful
`uhfRep` through P55B's `sourceUHFEquiv` to obtain a faithful representation
of `A.SourceLimit`. In the finite-coordinate branch, construct the analogous
faithful finite-matrix representation from P55B's terminal-stage
equivalence. Transport the source representation through P53's
`A.alpha.symm` to obtain a faithful representation of `A.TargetLimit`.

For both branches, define the source and target topological closures of the
operator ranges, prove they are C-star algebras, and construct canonical
injective `StarAlgHom` embeddings with dense range. Export a uniform branch
interface only if every field is filled by the constructions in this file;
do not accept representations, injectivity, closures, or dense range as new
premises.

## Auxiliary assumptions

Only the explicit finite-versus-infinite typeclass branch may be used beyond
the predecessor data. If a pulled-back normed pre-C-star structure is needed,
construct it and prove its C-star identity from the faithful representation;
do not assume norm preservation. Do not claim identification with the
state-dependent GNS von Neumann algebra.

## Files and imports

Create only
`AristotleCandidates/LocalHyperbolicConcreteRepresentations.lean`; import
P53, P54, P55B, and `AristotleCandidates.ConcreteCStarCompletion` as needed.
Do not edit predecessors.

## Acceptance criteria

- `lake build AristotleCandidates.LocalHyperbolicConcreteRepresentations`
  passes.
- Both finite and infinite branches have explicit declarations or an exact
  documented obstruction; the infinite branch actually uses P54/P55B.
- No `sorry`, `admit`, new axiom, or supplied representation/completion
  interface is introduced.
- The response reports exact declarations, commands, and remaining
  assumptions without crossing the forbidden boundary.
