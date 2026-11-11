# P16 — GNS-unitary conjugation of representation commutants

Work only on a new module named
`AristotleCandidates/GNSCommutantConjugation.lean`.

Import and reuse `AristotleCandidates.GNSUnitaryIntertwiner`. For supplied
`D : StabilizerHyperfinite.BoundedStateGNS.Data`, let `U := gnsUnitary D`.
Define the conjugation of bounded operators by `U`, in the direction

    T on sourceGNS |-> U ○ T ○ U^{-1} on targetGNS.

Prove that it sends the source GNS representation of `a` to the target GNS
representation of `D.equivalence a`, using the already checked intertwining
theorem. Then formalize the exact commutation transport statement:

    T commutes with every source GNS representative
    iff
    conjugate(T) commutes with every target GNS representative.

If the available set/centralizer API permits, express this for the
`Set.range` of each representation and derive the corresponding one- or
two-fold centralizer/bicommutant transport statement. Keep the two operator
spaces distinct and use conjugation rather than an ill-typed equality of sets.

If the bicommutant form is blocked by pinned APIs, do not add `sorry`, `admit`,
or axioms: retain the operator-level and single-commutant result, documenting
the exact obstruction. Do not claim an identification with a tensor-product
von Neumann algebra, a normal trace or weight, normality, faithfulness,
semifiniteness, hyperfiniteness, or factor classification. Build with:

    lake build AristotleCandidates.GNSCommutantConjugation
