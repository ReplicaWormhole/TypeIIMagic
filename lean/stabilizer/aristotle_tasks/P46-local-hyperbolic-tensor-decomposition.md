# P46 — local-hyperbolic tensor-product decomposition

## Mathematical target

Create only `AristotleCandidates/LocalHyperbolicTensorDecomposition.lean`.
Read the canonical manuscript and assemble only checked results from P41--P45.

State and prove the final regional theorem in the strongest honest form:
under the explicit coherent-local-coordinate, state-preserving C-star model,
and spatial GNS transport premises, the regional von Neumann algebra is
spatially isomorphic to a pure type-I coordinate factor tensor the mixed
coordinate product factor.  Record the precise cases:

- finite mixed sector: type I;
- infinite mixed sector with finite pure amplification: hyperfinite II1;
- infinite mixed and infinite pure sectors: II-infinity.

Do not claim type III is absent merely from a tensor-product slogan: derive it
from the stated factor alternatives.  Do not claim that the manuscript's bare
finite-support local-basis condition establishes every premise unless P43--P45
proved that implication.  If some input remains conditional, the final theorem
must retain it visibly and state the exact remaining source gap.

No `sorry`, `admit`, axioms, `opaque`, `unsafe`, or `native_decide`.  Return a
compiling candidate and an explicit verdict: recovered manuscript theorem,
conditional theorem, or blocked on a named analytic construction.
