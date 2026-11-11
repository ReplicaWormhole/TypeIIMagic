# P14 — pre-GNS isometry from compatible states

Work only on a new module named `AristotleCandidates/PreGNSIsometry.lean`.

Import and reuse `AristotleCandidates.BoundedStateGNS` and Mathlib's GNS API.
For `D : StabilizerHyperfinite.BoundedStateGNS.Data`, construct the linear map
on Mathlib's pre-GNS spaces induced by the supplied star-algebra equivalence:

    sourceState.PreGNS -> targetState.PreGNS,
    [a] (at the type-synonym/pre-GNS level) |-> [equivalence a].

Use the existing `toPreGNS`/`ofPreGNS` maps transparently rather than defining
a new quotient. Prove that this map is complex-linear and preserves the pre-GNS
inner product exactly, using the supplied state compatibility and preservation
of multiplication and star by the equivalence. Derive the corresponding norm
equality/isometry statement when Mathlib’s available API permits it.

Optional only if it follows directly and fully checks: package the map as a
linear isometric equivalence and/or give the induced map on the completions.
Do not add `sorry`, `admit`, or axioms if the completion API blocks that part;
the pre-GNS inner-product equality is the required deliverable.

Do not claim a product-state construction, a spatial tensor-product
identification, a bicommutant, von Neumann algebra, trace/weight, normality,
faithfulness, semifiniteness, hyperfiniteness, or factor classification. Build
with:

    lake build AristotleCandidates.PreGNSIsometry
