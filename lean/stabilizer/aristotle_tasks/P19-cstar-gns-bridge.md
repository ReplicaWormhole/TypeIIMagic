# P19 — supplied C-star model to GNS bridge

## Context declaration

- **Source basis:** `main.tex:1915-1958`

## Mathematical target

Create only `AristotleCandidates/CStarGNSBridge.lean`.

Package the existing `SuppliedCStarModel.Data` interface together with
`BoundedStateGNS.Data`. Prove a convenient conditional constructor/theorem:
a supplied complex C-star star-algebra equivalence, supplied positive unital
source and target functionals compatible along it, and the required
continuity data yield the existing GNS unitary intertwiner and the associated
star-algebra equivalence obtained by conjugating bounded operators.

Reuse P13--P16 rather than re-proving GNS. The deliverable should make the
assumptions and resulting names easy for a later regional-algebra theorem to
use.

## Auxiliary assumptions

- supplied unital complex C-star source and target models;
- supplied star-algebra equivalence;
- supplied positive unital functionals/states and their compatibility; and
- any continuity data needed by the existing interfaces.

The conclusion is conditional. Do not claim a spatial tensor product, a von
Neumann bicommutant theorem, normality, quasi-equivalence, hyperfiniteness,
factor type, or a trace/weight theorem.

## Files and imports

Import `AristotleCandidates.CStarTransport`,
`AristotleCandidates.BoundedStateGNS`, and
`AristotleCandidates.GNSCommutantConjugation`, plus only necessary existing
modules. Do not modify existing files.

## Acceptance criteria

- `lake build AristotleCandidates.CStarGNSBridge` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
- The response identifies all external C-star/state assumptions and all
analytic conclusions intentionally not claimed.
