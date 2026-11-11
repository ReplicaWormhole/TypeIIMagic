# P27 — normal von Neumann extension interface

## Context declaration

- **Source basis:** `main.tex:1970-2004`

## Mathematical target

Create only `AristotleCandidates/NormalVonNeumannExtensionInterface.lean`.

Package explicitly supplied von Neumann closures/represented algebras, a
supplied normal star-algebra equivalence extending the P26 C-star/GNS-level
map, and supplied normal functionals. Prove purely formal transport statements
for represented ranges, algebraic centralizers, and pullback of supplied normal
functionals. Reuse P26; do not re-prove GNS.

## Boundary

Do not construct the closures or normal extension, and do not claim
quasi-equivalence, spatial tensor products, hyperfiniteness, factor type, or
trace/weight. No gLU/refinement assumptions.

## Acceptance criteria

- `lake build AristotleCandidates.NormalVonNeumannExtensionInterface` succeeds.
- No `sorry`, `admit`, or axiom is introduced.
