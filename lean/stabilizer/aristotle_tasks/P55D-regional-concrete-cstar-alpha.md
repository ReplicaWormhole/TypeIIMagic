# P55D — concrete regional C-star alpha

## Context declaration

- **Source basis:** `main.tex:1915-1920`.

## Plan alignment

- **Package and lane:** `P55D`; Lane `H`.
- **Predecessors:** `P53`, `P55C`, both integrated and locally audited before
  submission.
- **Gate discharged:** extend the constructed algebraic alpha uniquely between
  the constructed source and regional concrete C-star closures.
- **Forbidden downstream claims:** no product-state equality, GNS tensor split,
  identification with the state-dependent represented von Neumann algebra,
  factor classification, trivial-center theorem, or trace/weight conclusion.

Read `PLAN.md` and `work/TWO-LANE-FORMALIZATION-DECISION.md` before editing.

## Mathematical target

Create only `AristotleCandidates/RegionalConcreteCStarAlpha.lean`. Using the
P55C canonical dense embeddings and P53's constructed algebraic `A.alpha`,
prove the required isometry/compatibility identity on the dense algebraic
ranges and use `Formalization.ConcreteCStarCompletion.extendStarAlgEquiv` (or
an equivalent proved extension) to construct

`A.regionalCStarAlpha : A.SourceConcreteCStar ≃⋆ₐ[ℂ]
  A.TargetConcreteCStar`.

Prove its formula on every source stage image, the corresponding inverse
formula on every target stage image, isometry, surjectivity, and uniqueness
among continuous star-algebra equivalences satisfying the dense formula. The
completed alpha may not be supplied as a field.

## Auxiliary assumptions

None beyond the explicit P53 hypotheses and the constructed finite/infinite
branch data exported by P55C. If P55C exposes a genuine conditional branch,
repeat that condition literally; do not add a regional representation,
faithfulness, boundedness, closure, density, or extension premise here.

## Files and imports

Create only `AristotleCandidates/RegionalConcreteCStarAlpha.lean`; import P53,
P55C, and the checked concrete completion module. Do not edit predecessors.

## Acceptance criteria

- `lake build AristotleCandidates.RegionalConcreteCStarAlpha` passes.
- The C-star equivalence is constructed by density, not accepted as data.
- No `sorry`, `admit`, new axiom, or forbidden downstream declaration is
  introduced.
- The response reports the exact declarations, verification command, and
  finite/infinite branch assumptions.
