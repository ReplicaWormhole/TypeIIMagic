# P9 — finite stabilizer group-average projector

Work only on a new module named AristotleCandidates/FiniteStabilizerProjector.lean.

Build an algebraic finite-group-average lemma suitable for stabilizers.  Work
over a complex star algebra A with a finite group G and a unital multiplicative
map U from G into A.  Define

    P = (1 / |G|) sum_{g in G} U(g).

Under the supplied assumptions that star(U(g)) = U(g inverse), prove:

1. P is self-adjoint;
2. P is idempotent;
3. every U(g) fixes P on the left and right.

Then add the normalized-trace calculation for a supplied linear functional tr
with tr(1)=1 and tr(U(g))=0 for every nonidentity g:

    tr(P) = 1 / |G|.

This is the finite stabilizer projector normalization.  Do not identify tr(P)
with a matrix rank unless a separate finite-dimensional rank theorem is proved.
Keep the group-average projector P = |G|^{-1} sum U(g) distinct from the
normalized density matrix rho = d^{-1} sum U(g) in a d-dimensional qubit
space.

Use the concrete Pauli orthogonality module only where it genuinely supplies
the trace-vanishing hypothesis; otherwise keep the result abstract.  Do not
use sorry, admit, or axioms; do not modify existing project files; do not make
C-star, GNS, normality, or factor claims.  Build with:

    lake build AristotleCandidates.FiniteStabilizerProjector
