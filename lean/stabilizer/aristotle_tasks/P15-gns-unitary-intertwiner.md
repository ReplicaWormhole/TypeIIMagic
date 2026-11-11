# P15 — GNS unitary and representation intertwining

Work only on a new module named `AristotleCandidates/GNSUnitaryIntertwiner.lean`.

Import and reuse `AristotleCandidates.PreGNSIsometry`. For supplied
`D : StabilizerHyperfinite.BoundedStateGNS.Data`, use the completed maps
`gnsMap` and the completion of `preGNSMapSymm` to prove, if Mathlib’s
completion API permits it, that the completed GNS map is invertible. Package
the result as a complex linear isometric equivalence (a Hilbert-space unitary
in the linear-isometric sense) between `sourceGNS D` and `targetGNS D`.

Then prove the intertwining identity for every `a : D.source`:

    U (sourceGNSRepresentation D a x) =
      targetGNSRepresentation D (D.equivalence a) (U x)

for all GNS vectors `x`. First establish it on the dense pre-GNS elements and
then extend to the completions using Mathlib's completion induction/continuity
tools. Keep the direction and all coercions explicit.

If the completion inverse or the full intertwining extension is blocked by
the pinned API, do not add `sorry`, `admit`, or axioms. Instead prove the
strongest checked pre-GNS or one-sided completion statement and document the
precise API obstruction in the owned module.

Do not claim a product state, spatial tensor-product identification,
bicommutant equality, a von Neumann algebra, trace/weight, normality,
faithfulness, semifiniteness, hyperfiniteness, or factor classification. Build
with:

    lake build AristotleCandidates.GNSUnitaryIntertwiner
