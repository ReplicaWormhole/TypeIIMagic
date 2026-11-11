# P3 — supplied C-star model transport

Work only on a new module named AristotleCandidates/CStarTransport.lean.

Import Formalization.CStarEquivExtension and the smallest existing trace
transport module needed.  Define a transparent supplied-model interface for
two complex C-star algebras, a complex star-algebra equivalence between them,
and a continuous target linear functional.  Prove, by using the existing
lemmas, that:

1. the star-algebra equivalence and its inverse are isometric and continuous;
2. the pullback functional is continuous; and
3. if the target functional is an algebraic tracial state, its pullback is an
   algebraic tracial state.

This is a conditional transport package only.  It must not pretend to
construct a C-star norm, completion, spatial tensor product, normal state,
GNS representation, or von Neumann factor.  State these boundaries in the
module documentation.

Do not use sorry, admit, axiom, or modify any file other than the owned module.
Compile it directly with:

    lake build AristotleCandidates.CStarTransport
