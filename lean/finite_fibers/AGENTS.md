# Local instructions for the finite-fiber Lean package

## Purpose

This package formalizes the abstract support-corner theorem behind the current
Overleaf manuscript.  It is intended to be structurally compatible with a
future mathlib contribution.

## Non-negotiable scope

- Use `VonNeumannAlgebra H` and `IsStarProjection` from mathlib.
- Keep all new definitions in the `FiniteFiber` namespace until an upstream
  naming/API review identifies a suitable mathlib home.
- Do not import or copy declarations from `work/OLD/formalization/` merely to
  make a proof pass.  That project is historical context, not a dependency.
- Do not add axioms, `sorry`, `admit`, `opaque`, `unsafe`, or
  `implemented_by` declarations.
- State every theorem with the exact hypotheses it uses.  In particular,
  normality and the stabilizer/GNS realization are not silently assumed by the
  abstract algebraic theorem.

## Dependency order

1. `Basic.lean`: projections, subprojections, Murray--von Neumann equivalence,
   central projections, finiteness, and semifiniteness.
2. `TracialCorner.lean`: a complex-linear functional tracial only for pairs of
   corner elements, and faithful on projections below the support; prove that
   every subprojection of its support is finite.  Do not strengthen this to a
   trace on the ambient algebra.
3. `FiniteFibers.lean`: use fullness to put a nonzero finite projection in
   every nonzero central summand and specialize to a finite indexed family.
4. `FiniteStabilizer.lean`: finite self-adjoint group averages are
   projections, and compatible subgroup actions decrease their supports.
5. `FiniteStabilizerTrace.lean`: under the explicit nonidentity-tracelessness
   condition, compute the finite group-average trace and prove nonzero local
   support in nonzero finite dimension.
6. `StrongSupport.lean`: construct the canonical strong limit of a decreasing
   projection sequence and prove its membership in the concrete von Neumann
   algebra, projection, and fixed-vector consequences.
7. `StabilizerSequence.lean`: turn an increasing finite-subgroup sequence
   into the decreasing local support sequence and its common fixed vectors.
8. `VectorCorner.lean`: derive projection-faithfulness and fullness from a
   vector functional, dense product orbit, and stated commutation hypotheses.
9. `GNSVector.lean`: construct the image of the unit for an explicitly
   supplied positive functional, prove the vector-coefficient and dense-orbit
   identities, derive unit norm under the explicit normalization condition,
   and derive fixedness from an explicit zero-deviation condition.
10. `GNSOrbit.lean`: compose the prior layers into the central-summand theorem.
   Its corner-traciality field is still an explicit analytic input.
11. `StabilizerFiniteFiber.lean`: compose finite stabilizer averages, the
   canonical strong limit, and specified GNS-orbit data into the finite-fiber
   theorem.
12. `FinitePauli.lean`, `FiniteQubitMatrix.lean`, `FiniteDensity.lean`, `FinitePauliStabilizer.lean`, and
    `FiniteLocalPauli.lean`: construct finite Pauli matrices, actual
    finite-group density matrices, and the expression-level signed partial
    trace identity.  The expression layer has no hidden group/state hypothesis.
13. `FinitePauliGNS.lean`: apply the generic GNS-vector result to a finite
    stabilizer density and prove that each represented finite stabilizer fixes
    its own GNS vector.
14. `FiniteNestedPauli.lean`: under an explicit tensor-coordinate
    decomposition, injective local-group inclusion, and exact survivor iff,
    identify the expression data with the actual positive trace-one stabilizer
    densities and prove their partial-trace compatibility.
15. `FiniteLocalGroupSupport.lean`: from an explicit finite-support map and a
    discarded-label/support detection condition, construct support-defined
    local groups, their canonical nested-region inclusion, and the survivor
    iff used by `FiniteNestedPauli.lean`.
16. `ProjectivePauliLattice.lean` and `FullPauliLattice.lean`: construct the
    finite-support normal-form Pauli groups and the algebraic generated
    consistent stabilizer subgroup.  Do not call this a matrix realization or
    identify syntactic support with local-algebra membership.
17. `FiniteTensorMatrixChain.lean`: construct literal initial/final `Fin`
    tensor coordinates and the trace/partial-trace pairing identity.
18. `FiniteRegionQubitAlgebra.lean`: construct the finite matrix algebra on
    each `F : Finset Site`, the canonical `F' = F \sqcup (F' \setminus F)`
    bit-coordinate split, and the reindexed `A \mapsto A \otimes 1` inclusion
    for `F \subseteq F'`.  Its matrix operator norm is provided through the
    scoped `FiniteFiber.FiniteRegionQubitMatrix` instance.  Do not identify
    Pauli syntax or stabilizer support with these algebras yet, or claim
    multi-region coherence, a colimit, a state, or GNS data.
19. `FiniteRegionPauliMatrices.lean`: realize only a phase-free Hermitian
    `PauliLabel` string as an actual matrix on every finite-region basis, with
    all-identity, self-adjointness, and identity-padding under the checked
    one-inclusion.  This is not a representation or multiplication theorem for
    the `i^phase X^x Z^z` normal form: its finite-region `ZMod 4`/`Y` phase
    aggregation, support/local-algebra membership, and coherence remain
    separate work.
20. `OneSitePauliNormalForm.lean`: fix exactly the one-site conversion from
    the Hermitian `Y` representative to the raw normal-form order,
    `X Z = i^3 Y = -i Y`.  It is not a finite-region or `FullPauliWord`
    representation, multiplication theorem, support/locality statement, or
    coherence result; those require later correction aggregation and cocycle
    work.
21. `FiniteNestedTensorState.lean`: construct the one-inclusion finite-density
    and state restriction in literal finite `Fin` coordinates.
22. `FiniteStabilizerStateChain.lean`: construct sequential transitions by
    composing physical one-site maps, prove their typed identity/composition
    laws, injectivity, and norm preservation, relate endpoint maps to the
    length-indexed physical recursion, and lift adjacent density compatibility
    to every finite sequential transition.
23. `SequentialLocalFunctional.lean`: form the associated quotient module and
    descend compatible finite functionals to a linear functional.  The
    component maps are a coherent directed system of unital star-algebra maps,
    but do not call its module quotient a star-algebra, quasilocal algebra, or
    state until quotient multiplication, star, positivity, and completion are
    proved.
24. `CountablePauliRepresentation.lean`: construct the discrete countable
    binary configuration Hilbert space and its bounded translation/phase
    generators, together with their almost-everywhere action formulas.  Do not
    call this an actual finite local matrix-algebra realization before a
    finite/tail factorization and the operator relations are checked.
25. A later layer must identify the finite-region matrix algebras with the
    full phased Pauli/stabilizer realization and support/local-algebra
    membership, then construct a coherent quasilocal algebra and global state,
    then construct the GNS-orbit/trace hypotheses and any direct-integral/type
    conclusion.  Do not represent that work as completed here.

## Verification

Run the narrow Lake target checks before `lake build`, including
`lake build FiniteFiber.Basic`, `lake build FiniteFiber.TracialCorner`,
`lake build FiniteFiber.FiniteFibers`, `lake build FiniteFiber.FiniteStabilizer`,
`lake build FiniteFiber.FiniteStabilizerTrace`, `lake build FiniteFiber.StrongSupport`, `lake build FiniteFiber.StabilizerSequence`,
`lake build FiniteFiber.VectorCorner`, `lake build FiniteFiber.GNSVector`, `lake build FiniteFiber.GNSOrbit`, and
`lake build FiniteFiber.StabilizerFiniteFiber`, `lake build
FiniteFiber.FinitePauli`, `lake build FiniteFiber.FiniteQubitMatrix`, `lake build
FiniteFiber.FiniteDensity`, `lake build FiniteFiber.FinitePauliStabilizer`, and `lake build
FiniteFiber.FinitePauliGNS`, `lake build FiniteFiber.FiniteLocalPauli`, `lake build FiniteFiber.FiniteNestedPauli`, and
`lake build FiniteFiber.FiniteLocalGroupSupport`, `lake build
FiniteFiber.ProjectivePauliLattice`, `lake build FiniteFiber.FullPauliLattice`,
`lake build FiniteFiber.OneSitePauliNormalForm`,
`lake build FiniteFiber.FiniteTensorMatrixChain`, `lake build
FiniteFiber.FiniteRegionQubitAlgebra`, `lake build
FiniteFiber.FiniteRegionPauliMatrices`, `lake build
FiniteFiber.FiniteNestedTensorState`, and `lake build
FiniteFiber.FiniteStabilizerStateChain`, and `lake build
FiniteFiber.SequentialLocalFunctional`, and `lake build
FiniteFiber.CountablePauliRepresentation`.
Check that the target files contain no placeholders and inspect `#print axioms`
for each public theorem.  Compile the matching TeX records in
`../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I001-full-tracial-corner/`
`../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I002-stabilizer-gns-realization/`,
and `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I003-finite-pauli-density-realization/`.
