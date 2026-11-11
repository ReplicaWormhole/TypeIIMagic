# P59A — concrete pure/mixed product datum

## Context declaration

- **Source basis:** `main.tex:1925-1967`.

## Plan alignment

- **Package and lane:** `P59A`; Lane `H`.
- **Predecessors:** `P55D` and `P56R`, integrated and locally audited.
- **Gate discharged:** construct the concrete coordinate pure/mixed C-star
  product datum required by P57, rather than introducing an arbitrary
  `ProductGNSData` at the regional-factor stage.
- **Forbidden downstream claims:** no completed infinite tensor-product
  Hilbert space, no pure or mixed factor classification, no regional factor
  theorem, no trace/weight theorem, and no new factor/normality premise.

## Mathematical target

Create only `AristotleCandidates/ConcretePureMixedProductData.lean`. For the
selected coordinate set `A.family.selected` and its complement, construct the
actual pure and mixed coordinate quasi-local C-star algebras, their unital
star-homomorphisms into the P55D concrete source C-star algebra, and prove
that their images commute and that the complex linear span of products is
norm dense. Construct the two marginal pure/mixed product functionals and
prove their positivity, unitality, contractivity, and factorization of
P56R's recovered source state on elementary products.

Use those proved objects to define a concrete
`ProductGNSTensor.ProductGNSData`, with the total state being
`cstarProductStateRecovered`. Prove the fields rather than introducing a
`CoordinateSplitData`, `ProductGNSData`, density, product, positivity, or norm
bound field as a new assumption. If conversion from P56R's proved
`IsAlgebraicState` to Mathlib's `PositiveLinearMap` is required, prove that
conversion against the pinned concrete C-star order.

The final declaration should expose the constructed datum (for example
`AlphaData.SourceConcreteRep.concreteProductGNSData`) together with explicit
lemmas identifying its total algebra and total state with P55D/P56R objects.

## Auxiliary assumptions

Only the existing P52/P53/P55D coordinate-model assumptions inherited through
`AlphaData` and `SourceConcreteRep`. Classical decidability may be used
locally for the selected-coordinate partition. No supplied tensor-product,
state, density, factor, weak-closure, normality, trace, or weight premise is
allowed.

## Files and imports

Create only `AristotleCandidates/ConcretePureMixedProductData.lean`; import
P55D, P56R's `RegionalProductStateIdentity`, and P57 only when its concrete
data structure is needed. Do not edit P55D, P56R, P57, P58, the manuscript, or
another candidate.

## Acceptance criteria

- `lake build AristotleCandidates.ConcretePureMixedProductData` succeeds.
- The exported `ProductGNSData` is constructed from the local model and does
  not have any additional assumption/premise argument.
- Commutation, dense product span, each marginal state, product-state
  factorization, and the conversion to `PositiveLinearMap` are reported
  separately.
- No `sorry`, `admit`, new axiom, opaque interface, or supplied factor/trace
  assertion is introduced.
