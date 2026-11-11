# P45 — spatial GNS transport of the regional product model

## Mathematical target

Create only `AristotleCandidates/SpatialGNSTensorTransport.lean`.  Use the
checked P39--P44 interfaces and existing GNS/bicommutant files.

Prove the strongest spatial conclusion available from a state-preserving
regional C-star equivalence: construct the GNS isometry/unitary, show it
intertwines the represented dense algebras, and transport the relevant
bicommutant/von-Neumann closures.  Keep normality, density, and closure facts
as explicit assumptions unless Lean's concrete operator API proves them.

The intended conclusion is a reusable conditional spatial isomorphism between
the regional GNS von Neumann algebra and the pure/mixed product von Neumann
algebra.  Do not cite the double-commutant theorem or infinite tensor-product
classification unless it has actually been formalized; isolate missing library
facts as named interfaces.  No final factor label yet.

No placeholders or axioms.  Build and report all remaining analytic premises.
