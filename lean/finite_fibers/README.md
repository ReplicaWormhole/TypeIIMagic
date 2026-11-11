# Finite-fiber formalization

This is a standalone Lean package for the reusable operator-algebraic core of
the support-corner proof in the project manuscript.  It is intentionally
separate from `work/OLD/formalization/`, which is an archived historical
formalization.

The package uses mathlib's concrete `VonNeumannAlgebra H` and
`IsStarProjection`.  It adds only the missing projection-comparison and
tracial-corner vocabulary needed for the theorem; it does not introduce a
second notion of von Neumann algebra or state an unproved type-classification
axiom.

Read [HANDOFF.md](HANDOFF.md) before editing.  In particular, distinguish:

- checked abstract results in `FiniteFiber/`;
- the checked finite-group support layer in `FiniteStabilizer.lean`, the
  conditional trace/rank calculation in `FiniteStabilizerTrace.lean`, the
  canonical strong limit in `StrongSupport.lean`, and the nested subgroup
  sequence in `StabilizerSequence.lean`;
- the conditional specified-GNS-orbit bridge in `VectorCorner.lean` and
  `GNSOrbit.lean`;
- the checked generic GNS-vector bridge in `GNSVector.lean`: the GNS image of
  the unit reconstructs any supplied positive linear functional, has dense
  represented-algebra orbit, and is unit norm when that functional is
  normalized; it is fixed when the displayed squared deviation has zero
  functional value.  It does not construct the manuscript's quasi-local
  functional;
- the finite-fiber corollary, which is algebraic;
- the checked finite tensor-product Pauli and actual finite stabilizer-density
  layer in `FinitePauli.lean` and `FinitePauliStabilizer.lean`, including
  positivity and finite code-corner traciality, together with
  `FinitePauliGNS.lean`, which proves that every finite stabilizer fixes the
  GNS vector of its own density.  A client that restates this GNS theorem's
  target should write `open scoped FiniteFiber.FiniteQubitMatrix
  MatrixOrder` to activate the finite-matrix C-star structure and matrix
  order used by the construction; the older
  `FinitePauliStabilizerData` scope remains available for compatibility;
- the checked partial-trace identity for normalized signed-Pauli expressions in
  `FiniteDensity.lean` and `FiniteLocalPauli.lean`, under an explicit survivor
  equality;
- the checked conditional actual-nested-group bridge in
  `FiniteNestedPauli.lean`: a tensor-coordinate decomposition, injective local
  subgroup inclusion, and exact survivor condition yield compatible positive,
  trace-one finite densities;
- the checked conditional support-predicate bridge in
  `FiniteLocalGroupSupport.lean`: from an explicit finite-support map and a
  supplied discarded-label/support detection condition, it constructs the
  local subgroups, their canonical inclusion for nested regions, and the exact
  survivor condition.  Its normal-form specialization derives that detection
  condition for an explicitly enumerated finite complement.  The
  tensor-coordinate and matrix-Pauli realization facts remain explicit inputs;
- the algebraic finite-support normal-form layers
  `ProjectivePauliLattice.lean` and `FullPauliLattice.lean`: they construct
  finite local support groups and derive the consistent generated subgroup
  from pairwise-commuting order-two generators, but do not yet identify that
  syntax with the manuscript's matrix Pauli group or local-algebra
  intersections;
- the checked finite-region local-algebra bridge in
  `FiniteRegionQubitAlgebra.lean`: for every finite `F : Finset Site`, it
  constructs the matrix algebra on `F → Fin 2`; for `F ⊆ F'`, it constructs
  the canonical split into `F` and `F' \ F` coordinates and the reindexed
  physical inclusion `A ↦ A ⊗ 1`, with injectivity and operator-norm
  preservation.  Clients using its norm API should open scoped
  `FiniteFiber.FiniteRegionQubitMatrix`.  It does not yet realize full Pauli
  or stabilizer words in these algebras, prove coherence for three regions, or
  construct a colimit, state, or GNS representation;
- the checked phase-free finite-region Pauli layer in
  `FiniteRegionPauliMatrices.lean`: a `PauliLabel` at each site gives its
  coordinate-free tensor-product matrix on `F → Fin 2`; all-identity strings
  are the identity, the strings are self-adjoint, and the checked local
  inclusion pads labels by `I`.  This deliberately does not represent or
  multiply the full `i^phase X^x Z^z` normal form, identify syntactic support
  with local-algebra membership, or establish multi-region coherence;
- the checked one-site normal-form convention in
  `OneSitePauliNormalForm.lean`: it proves `X Z = i^3 Y = -iY` and therefore
  the exact `ZMod 4` correction from the Hermitian `Y` representative to the
  raw `X`-then-`Z` normal form.  It does not yet aggregate that correction
  over a finite region, construct a `FullPauliWord` map, prove
  multiplicativity, or identify local support with a matrix algebra;
- the checked finite-coordinate/state bridge in `FiniteQubitMatrix.lean`,
  `FiniteTensorMatrixChain.lean`, `FiniteNestedTensorState.lean`, and
  `FiniteStabilizerStateChain.lean`: literal initial/final `Fin` coordinates,
  matrix-level factorization of actual signed Pauli strings, physical
  initial-segment locality, trace/partial-trace adjointness, an adapter which
  derives the nested tensor decomposition from literal Pauli labels, adjacent
  actual-density compatibility, and a typed sequential system of injective
  norm-preserving unital star-algebra maps with checked identity and
  composition laws; and
  the endpoint-to-added-block bridge showing that these maps inherit the
  checked Pauli-string padding law; and
  `SequentialLocalFunctional.lean`, which descends those compatible finite
  functionals to its module direct limit.  No multiplication or star operation
  on that quotient, norm-closed quasilocal algebra, or state on such a closure
  is claimed;
- the checked first concrete countable-lattice foundation in
  `CountablePauliRepresentation.lean`: the discrete finite-support binary
  configuration Hilbert space, count-measure translations, bounded one-site
  phase multipliers, their almost-everywhere action formulas, and the complete
  elementary `X`/`Z` generator relations: zero shift, `X` and `Z` involution,
  same-family commutation, same-site anticommutation, and distinct-site mixed
  commutation; it also has the additive initial/tail `Finsupp.filter` split of
  configurations, its recomposition law, coordinate-vanishing laws, and the
  corresponding one-site-generator restrictions;
- the remaining full phased Pauli/stabilizer matrix realization and
  support/local-algebra identification for the finite-region algebras,
  their compatibility with a countable exhaustion,
  countable-lattice extension of discarded-label detection, norm-closed
  quasilocal algebra, global GNS state, local-to-von-Neumann trace extension,
  and direct-integral/type interpretation.

For the complete conditional nested-stabilizer-sequence conclusion, use
`stabilizerAverageSequence_canonicalSupportCornerConclusion_of_gnsOrbit`.
Given a supplied increasing finite-subgroup sequence and the displayed
GNS-orbit/corner-traciality conditions, it constructs the decreasing
finite-group supports and their strong limit, then bundles the support
projection, fixed-vector, fullness, projection-faithfulness, and canonical
all-central witness.  It does not derive those supplied inputs from a
countable stabilizer system.

Run:

```bash
lake build FiniteFiber.Basic
lake build FiniteFiber.TracialCorner
lake build FiniteFiber.FiniteFibers
lake build FiniteFiber.FiniteStabilizer
lake build FiniteFiber.FiniteStabilizerTrace
lake build FiniteFiber.FinitePauli
lake build FiniteFiber.FiniteQubitMatrix
lake build FiniteFiber.FiniteDensity
lake build FiniteFiber.FinitePauliStabilizer
lake build FiniteFiber.FinitePauliGNS
lake build FiniteFiber.FiniteLocalPauli
lake build FiniteFiber.FiniteNestedPauli
lake build FiniteFiber.FiniteLocalGroupSupport
lake build FiniteFiber.ProjectivePauliLattice
lake build FiniteFiber.FullPauliLattice
lake build FiniteFiber.OneSitePauliNormalForm
lake build FiniteFiber.FiniteTensorMatrixChain
lake build FiniteFiber.FiniteRegionQubitAlgebra
lake build FiniteFiber.FiniteRegionPauliMatrices
lake build FiniteFiber.FiniteNestedTensorState
lake build FiniteFiber.FiniteStabilizerStateChain
lake build FiniteFiber.SequentialLocalFunctional
lake build FiniteFiber.CountablePauliRepresentation
lake build FiniteFiber.StrongSupport
lake build FiniteFiber.StabilizerSequence
lake build FiniteFiber.VectorCorner
lake build FiniteFiber.GNSVector
lake build FiniteFiber.GNSOrbit
lake build FiniteFiber.StabilizerFiniteFiber
lake build
lake env lean tests/AxiomAudit.lean
```
