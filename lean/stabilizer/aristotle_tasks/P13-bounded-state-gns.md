# P13 — actual bounded-state GNS representations

Work only on a new module named `AristotleCandidates/BoundedStateGNS.lean`.

Use Mathlib's existing
`Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal` construction. This is a
real bounded-state GNS step, not a new GNS implementation.

Define a transparent supplied-data structure for two unital complex C-star
algebras `source` and `target` containing:

* C-star, partial-order, and star-ordered-ring structures required by
  Mathlib's positive-functional/GNS API;
* a supplied star-algebra equivalence `source ≃⋆ₐ[ℂ] target`;
* supplied positive linear maps `sourceState : source →ₚ[ℂ] ℂ` and
  `targetState : target →ₚ[ℂ] ℂ`;
* their unit normalizations `sourceState 1 = 1`, `targetState 1 = 1`; and
* the compatibility equation
  `sourceState a = targetState (equivalence a)` for every `a`.

With the structure instances activated, define the actual Mathlib objects

    sourceGNS := sourceState.GNS,
    targetGNS := targetState.GNS,
    sourceGNSRepresentation := sourceState.gnsStarAlgHom,
    targetGNSRepresentation := targetState.gnsStarAlgHom.

Prove the routine interface facts that these are unital star-algebra
homomorphisms into bounded operators on the respective completed GNS Hilbert
spaces, and record the given state compatibility in the new interface. Reuse
the supplied-C-star isometry/continuity theorem if it fits.

Do **not** construct a product state, an intertwining unitary between the two
GNS spaces, a bicommutant, a von Neumann algebra, a trace/weight, normality,
faithfulness, semifiniteness, hyperfiniteness, or factor classification. In
particular, this package is the bounded-state GNS entry point; a tracial weight
belongs later on the resulting von Neumann algebra and is not an input here.

Do not add `sorry`, `admit`, or axioms; do not modify existing files. Build
with:

    lake build AristotleCandidates.BoundedStateGNS
