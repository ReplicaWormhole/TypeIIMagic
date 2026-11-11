# P11 — conditional C-star transport of a finite tracial-weight core

Work only on a new module named
`AristotleCandidates/CStarTracialWeightCore.lean`.

This task deliberately does **not** construct a C-star completion, a weight,
a GNS representation, a von Neumann algebra, or normality/semifiniteness.
Instead it formalizes the algebraic finite part that a later tracial weight is
required to provide and transports it under a *supplied* C-star star-algebra
equivalence.

Use `AristotleCandidates.CStarTransport` where helpful.  Define a clearly
named structure such as `TracialWeightCore A` for a complex star algebra `A`.
It should contain:

* a complex-linear subspace of elements on which the putative weight is finite;
* closure of that subspace under left and right multiplication by arbitrary
  elements (so it is a two-sided finite trace ideal);
* a complex-linear functional on this finite part; and
* a tracial identity `tau(x * y) = tau(y * x)` whenever one factor is in the
  finite trace ideal, with all subtype-membership evidence made explicit.

Then, for a supplied `e : A ≃⋆ₐ[ℂ] B`, construct the pullback core on `A`
from a core on `B`, prove its closure and tracial laws, and prove the
conditional existence-transfer statement:

    Nonempty (TracialWeightCore B) -> Nonempty (TracialWeightCore A).

If convenient, package this specifically for the `SuppliedCStarModel.Data`
interface.  State that the star-algebra equivalence is automatically
continuous/isometric only because the C-star structures are supplied.

Accuracy boundary: this `TracialWeightCore` is only the finite complex-linear
trace ideal of a prospective tracial weight.  It is **not** a definition or
construction of an extended-positive normal semifinite tracial weight.  In
particular, do not claim normality, faithfulness, semifiniteness, positivity,
GNS/spatial tensor identification, bicommutant passage, hyperfiniteness, or
factor type.

Do not add `sorry`, `admit`, or axioms; do not modify existing files.  Build
with:

    lake build AristotleCandidates.CStarTracialWeightCore
