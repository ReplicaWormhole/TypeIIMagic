# Handoff: finite-fiber support-corner formalization

## Read order

1. `AGENTS.md` for scope and prohibition of historical dependencies.
2. The canonical informal theorem note:
   `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I001-full-tracial-corner/technical.tex`.
3. `FiniteFiber/Basic.lean`.
4. `FiniteFiber/TracialCorner.lean`.
5. `FiniteFiber/FiniteFibers.lean`.
6. `FiniteFiber/FiniteStabilizer.lean`.
7. `FiniteFiber/FiniteStabilizerTrace.lean`.
8. `FiniteFiber/FinitePauli.lean`.
9. `FiniteFiber/FiniteQubitMatrix.lean`.
10. `FiniteFiber/FiniteDensity.lean`.
11. `FiniteFiber/FinitePauliStabilizer.lean`.
12. `FiniteFiber/FiniteLocalPauli.lean`.
13. `FiniteFiber/FiniteNestedPauli.lean`.
14. `FiniteFiber/FiniteLocalGroupSupport.lean`.
15. `FiniteFiber/ProjectivePauliLattice.lean`.
16. `FiniteFiber/FullPauliLattice.lean`.
17. `FiniteFiber/FiniteTensorMatrixChain.lean`.
18. `FiniteFiber/FiniteRegionQubitAlgebra.lean`.
19. `FiniteFiber/FiniteRegionPauliMatrices.lean`.
20. `FiniteFiber/OneSitePauliNormalForm.lean`.
21. `FiniteFiber/FiniteNestedTensorState.lean`.
22. `FiniteFiber/FiniteStabilizerStateChain.lean`.
23. `FiniteFiber/SequentialLocalFunctional.lean`.
24. `FiniteFiber/StrongSupport.lean`.
25. `FiniteFiber/StabilizerSequence.lean`.
26. `FiniteFiber/VectorCorner.lean`.
27. `FiniteFiber/GNSVector.lean`.
28. `FiniteFiber/FinitePauliGNS.lean`.
29. `FiniteFiber/GNSOrbit.lean`.
30. `FiniteFiber/StabilizerFiniteFiber.lean`.

## Mathematical contract

The primary formal theorem must prove the current manuscript's abstract
conclusion:

```text
For every nonzero central projection z of M,
zM contains a nonzero finite projection.
```

It is stronger than the finite-fiber corollary.  The theorem must not claim a
direct-integral decomposition or a type classification theorem.  The
finite-fiber corollary is obtained by applying it to explicitly supplied
central projections indexed by a finite type.

## Current proof architecture

`Basic.lean` deliberately models finite projections through the standard
Murray--von Neumann equations in a concrete von Neumann algebra and proves the
derived partial-isometry identity needed by the corner argument.
`TracialCorner.lean` uses a complex-linear functional that is tracial only
when both arguments are supported in the corner, together with faithfulness on
projections below the corner support; this is exactly what is needed to prove
finiteness without introducing unnecessary normality machinery.
`FiniteFibers.lean` combines that with the explicit fullness condition

```text
forall nonzero central z, z * q != 0.
```

The checked nested-stabilizer-sequence application takes a finite self-adjoint
group action, a supplied increasing finite subgroup sequence, and the
remaining specified GNS-orbit data.  From those inputs it establishes:

1. each local group average is a projection in the regional algebra and nested
   subgroups make those supports decrease; their canonical strong limit `q`
   lies in the regional algebra, is a projection, and fixes the GNS vector;
2. the compressed vector functional is faithful on projections below the
   corner support, using the dense product orbit and corner traciality;
3. `q` is full using the same global GNS-density argument.

The single canonical entry point for those bundled clauses is
`stabilizerAverageSequence_canonicalSupportCornerConclusion_of_gnsOrbit`.  Its
`q_projection`, `q_fixes_xi`, `full`, `projection_faithful`, and
`central_witness` fields are the exact checked conclusions; `semifinite` is
their existential central-summand corollary.  The separate
`stabilizerAverageSequence_canonicalCentralWitness_of_gnsOrbit` declaration
supplies the canonical witness in a nonzero central summand.

`FiniteStabilizerTrace.lean` separately proves the local finite-dimensional
calculation under the exact hypotheses that every nonidentity represented
group element is traceless and `Module.finrank ℂ H ≠ 0`.  It is not used to
establish a nonzero global GNS support in the theorem above.

`GNSVector.lean` supplements mathlib's generic GNS construction: for any
supplied positive linear functional on a unital C-star algebra, the image of
the unit has dense represented-algebra orbit and reconstructs the functional
as a vector coefficient.  When the functional sends the unit to one, that
vector has norm one; the vector is fixed whenever the supplied squared
deviation has zero functional value.  `FinitePauliGNS.lean` applies that
criterion to the finite stabilizer density and proves finite stabilizer
invariance of its own GNS vector.  These modules do not construct the
manuscript's quasi-local functional or establish a regional/complementary
product-orbit density statement.

I003 constructs the fixed finite ordered-qubit realization: explicit Hermitian
signed Pauli strings, finite group averages, trace-normalized positive density
matrices, and finite code-corner traciality.  Separately, it proves signed
partial trace for normalized signed-Pauli expressions under the exact survivor
equality; it does not manufacture that equality from trace orthogonality or
assert that arbitrary signed expressions are states.  `FiniteNestedPauli.lean`
then lifts that calculation to actual finite larger and smaller stabilizer
groups, conditional on their explicit tensor-coordinate decomposition,
injective inclusion, and survivor iff.  It proves that the reindexed larger
density is positive and trace-one and that its partial trace is the actual
smaller density.  `FiniteLocalGroupSupport.lean` derives the inclusion and
survivor clauses from a supplied finite-support map and a supplied condition
that discarded identity labels detect support containment.  It does not
construct that support map, the local algebras, or the Pauli-coordinate facts
from a countable lattice.

`ProjectivePauliLattice.lean` and `FullPauliLattice.lean` now construct the
finite-support projective and full normal-form Pauli groups.  The latter also
derives the algebraic consistent stabilizer subgroup from an actual set of
pairwise-commuting order-two generators together with the consistency
condition excluding $-1$, and supplies the Pauli-label support predicate used
to derive discarded-label survival for an explicitly enumerated finite
complement.  This remains an algebraic normal-form result: its labels discard
the central `ZMod 4` phase, and no matrix realization or identification of
syntactic support with membership in a local matrix algebra is asserted.

`FiniteQubitMatrix.lean` exposes the neutral finite-qubit operator-norm
C-star scope.  `FiniteTensorMatrixChain.lean` constructs both a legacy
recursive tail-block coordinate convention and a checked literal
initial/final `Fin`-coordinate split.  It now proves that actual Hermitian
signed Pauli strings factor in those physical coordinates and that embedding
a string extends it by identity labels on the added block.
`FiniteRegionQubitAlgebra.lean` bridges the abstract finite-region lattice
layer to actual finite matrix algebras: its `finiteRegionQubitAlgebra F` is
the matrix algebra on bit assignments `F \to \mathrm{Fin}\,2`, and for each
`F \subseteq F'` its checked `finiteRegionEmbed` is the reindexed
`A \mapsto A \otimes 1` inclusion.  The operator-norm structure is exported
only through `open scoped FiniteFiber.FiniteRegionQubitMatrix`; this fixes the
previous candidate-only local-instance limitation.  It remains independent of
the full Pauli/stabilizer matrix realization and has no multi-region
coherence, colimit, state, or GNS claim.
`FiniteNestedTensorState.lean` uses this to derive the tensor decomposition
of literal-coordinate nested stabilizer data, then proves its finite-density
and state compatibility.  `FiniteStabilizerStateChain.lean` defines longer
transitions by `Nat.leRecOn` from physical one-site inclusions.  It proves
their identity and composition laws at the typed endpoints, preserves the
unital star-algebra structure and the finite operator norm, and proves
injectivity; the resulting linear maps are a checked `DirectedSystem`.  A
stepwise compatible family of actual
finite stabilizer densities restricts along every such transition.  Its
endpoint-to-added-block theorem identifies the maps with the original
length-indexed recursion and transfers the checked signed-Pauli padding law.
Finally,
`SequentialLocalFunctional.lean` descends these compatible values to the
corresponding `Module.DirectLimit` as a complex-linear functional.  It does
not construct multiplication or star on that quotient, positivity there, a
norm completion, or a quasilocal state.

## I004 countable-representation status

`CountablePauliRepresentation.lean` is the beginning of the subsequent
countable-lattice realization.  It defines the discrete countable binary
configuration Hilbert space, count-measure translation operators, and bounded
one-site phase multipliers.  It proves their almost-everywhere action formulas,
translation norm preservation, the zero-shift identity, translation
composition, and the complete elementary `X`/`Z` generator relations:
involution, same-family commutation, same-site anticommutation, and
distinct-site mixed commutation.  It also proves the additive initial/tail
`Finsupp.filter` decomposition of configurations, including recomposition,
the two coordinate-vanishing properties, and the restrictions of a one-site
generator to its appropriate side of a cut.  This is not yet an $L^2$
factorization.  The package does not yet prove a full phased Pauli
representation, the finite/tail matrix-algebra factorization, a concrete local
star-subalgebra chain, a norm-closed quasi-local algebra, or a global state.
The detailed resume record is
`../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I004-countable-pauli-quasilocal-realization/HANDOFF.md`.
The independent I004 reviews are at
`../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I004-countable-pauli-quasilocal-realization/reviews/`.
The final live FF05--FF07 closeout review is at
`../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I004-countable-pauli-quasilocal-realization/aristotle_responses/FF05-FF07-live-closeout-adversarial-review.md`.
FF08, project `5a41c5b2-24ef-4f49-9d6f-03e203a80ff3`, is accepted and
integrated.  Its quarantined archive contributes only the additive initial/tail
split of `CountablePauliConfiguration`; the remote README attribution,
stale HANDOFF deletion, and metadata were rejected.  The review is at
`../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I004-countable-pauli-quasilocal-realization/aristotle_responses/FF08-integration-adversarial-review.md`.
FF09 is a remote-only candidate, project
`f78a4014-b751-45d0-af0a-b1e8a9e32c11`: it asks only for the additive
equivalence between the checked initial/tail configuration subgroups and has
not been retrieved or integrated.

FF09 was subsequently set aside as off-track for the finite-fiber theorem:
it remains remote-only and must not be retrieved or integrated merely because
it completes an additive configuration decomposition.  FF10, project
`88d5f994-e829-4ded-b04a-b38c650e4f8b`, has been accepted and integrated as
`FiniteFiber/FiniteRegionQubitAlgebra.lean`.  Its archive SHA-256 is
`7ca2f97893a1fc872626a0a7095b14887504c36939aa3b1e584cf086b0fa5778`; the
remote snapshot remains quarantined under `aristotle_responses/FF10-extracted/`.
Only its candidate Lean file was used.  The returned local C-star instance was
promoted to a named scoped instance so that the public norm theorem is usable
by downstream files.  The module gives arbitrary finite-region qubit matrix
algebras and the one-inclusion `F \subseteq F'` map `A \mapsto A \otimes 1`;
it does not assert Pauli/stabilizer realization, triple-region coherence, a
directed colimit, quasilocal closure, state/GNS data, or the finite-fiber
theorem.  The task and its prompt review are under
`../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I004-countable-pauli-quasilocal-realization/aristotle_tasks/FF10-finite-region-qubit-local-algebras.md`
and `aristotle_responses/FF10-prompt-adversarial-review.md`; the post-result
review is `aristotle_responses/FF10-integration-adversarial-review.md`.

FF11, project `76d70d89-bf7a-490b-a1ee-6c3512437110`, was accepted and
integrated on August 5, 2026 as `FiniteFiber/FiniteRegionPauliMatrices.lean`.
Its archive SHA-256 is
`acaaeac3024447b211faf050224b9146e978d90c105da094a22b9226d84b529a` and the
complete remote snapshot remains quarantined under
`aristotle_responses/FF11-extracted/`.  Only
`AristotleCandidates/FiniteRegionPauliMatrices.lean` was integrated; it is
byte-identical to the live source.  The remote README attribution insertion,
stale deletion of the FF11 handoff status, `ARISTOTLE_SUMMARY.md`, and its
unverified claim of a commit/push were rejected.

The module realizes a phase-free Hermitian `PauliLabel` string as the
coordinate-free product of one-site matrix entries on every finite-region
basis.  It proves the all-identity and self-adjoint facts and that
`finiteRegionEmbed` pads labels by `I`.  It deliberately does not represent or
multiply `FullPauliWord`: the `i^phase X^x Z^z` normal form still needs its
finite-region `ZMod 4`/Y-count phase aggregation.  No syntactic support/local-algebra
identification, triple-region coherence, colimit, state/GNS, or finite-fiber
claim is made.  Both independent reviews approve the surgical integration;
the task, prompt review, and post-result review are at
`../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I004-countable-pauli-quasilocal-realization/aristotle_tasks/FF11-finite-region-pauli-matrices.md`,
`aristotle_responses/FF11-prompt-adversarial-review.md`, and
`aristotle_responses/FF11-integration-adversarial-review.md`.

FF12, project `c091ae7a-c696-4863-a46f-72c8ab6ca624`, was accepted and
integrated on August 5, 2026 as `FiniteFiber/OneSitePauliNormalForm.lean`.
Its archive SHA-256 is
`624b130a2c08061fa8f60edf33397c5a2dd82b4817569c0acdcd7f14c9da6cbf` and its
complete remote snapshot remains quarantined under
`aristotle_responses/FF12-extracted/`.  Only
`AristotleCandidates/OneSitePauliNormalForm.lean` was integrated; it is
byte-identical to the live source with SHA-256
`6d9e4ae4f3c0ae3a3c3b9d35322d42ddd8d518a07f75441b6b1a61a3984cfc99`.  The
remote README attribution insertion, stale removal of the live FF12 status
from the handoff, and `ARISTOTLE_SUMMARY.md` were rejected.

The module proves the one-site conversion from the Hermitian representative
to the raw normal form: `X Z = i^3 Y = -iY`.  Its phase correction is
nonadditive and equals `3` only at the projective `Y` coordinate; it does not
reuse `FullPauliWord.phaseEmbed`, which is the distinct sign map
`1 ↦ 2`.  It does not define a finite-region or full-word representation,
prove multiplication or cocycle compatibility, identify syntactic support
with local-algebra membership, or claim coherence, a colimit, state/GNS, or
the finite-fiber theorem.  Both independent post-result reviews approve the
integration.  The task, prompt review, and post-result review are at
`../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I004-countable-pauli-quasilocal-realization/aristotle_tasks/FF12-one-site-pauli-normal-form.md`,
`aristotle_responses/FF12-prompt-adversarial-review.md`, and
`aristotle_responses/FF12-integration-adversarial-review.md`.

A later global stabilizer/GNS layer must still establish:

1. the actual countable-lattice Pauli/stabilizer realization in the checked
   finite-region algebras, including a proof that finite support containment
   is the manuscript's local-algebra membership condition;
2. aggregation of the now checked one-site `ZMod 4` correction over arbitrary
   finite regions, its exact padding behavior, and then a full matrix
   realization of the phased normal form compatible with its cocycle.  The
   literal ordered-block factorization and syntactic discarded-label detection
   for an enumerated complement are checked, but no countable-lattice
   local-algebra identification follows yet;
3. a noncommutative star-algebra colimit on the coherent finite system, then a
   norm-closed quasilocal algebra and a positive global state.  The current
   module direct limit and its functional are intentionally weaker than this;
4. construction of the quasi-local state whose generic GNS vector is supplied
   by `GNSVector.lean`, together with compatibility strong enough to lift the
   finite `FinitePauliGNS.lean` stabilizer-invariance result to every global
   local stabilizer;
5. the regional/complementary GNS product-orbit density statement;
6. corner traciality from finite matrix traces, bounded strong continuity, and
   Kaplansky density;
6. any direct-integral or type-III conclusion.

None of those six upstream facts should be marked proved until represented by
checked Lean code.

## Upstream-mathlib direction

Mathlib v4.28 supplies `VonNeumannAlgebra H` and `IsStarProjection`, but not
the finite-projection/Murray--von Neumann/type vocabulary used here.  Candidate
upstream paths are under `Mathlib/Analysis/VonNeumannAlgebra/`.  Before an
upstream PR, replace the provisional `FiniteFiber` names by names agreed with
mathlib maintainers and split generic star-algebra lemmas from concrete
von-Neumann-algebra statements.

## Status discipline

- A passing Lean build proves only the named abstract theorem.
- A compiled TeX note is not proof of the mathematics.
- An adversarial mathematical-fidelity review is required after every
  substantive theorem/API change.

## Current verification record

The checked finite-group/support-corner core is complete as of August 3, 2026.  Reproduce its
verification from this package directory with:

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

The audit is expected to report only `propext`, `Classical.choice`, and
`Quot.sound`.  The independent closeout reports are at:

- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I001-full-tracial-corner/reviews/math_fidelity_review.md`
- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I001-full-tracial-corner/reviews/lean_api_review.md`

The approved I002 adversarial reports are:

- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I002-stabilizer-gns-realization/reviews/math_fidelity_review.md`
- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I002-stabilizer-gns-realization/reviews/lean_api_review.md`

The I003 finite-Pauli/density investigation and its adversarial reports are:

- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I003-finite-pauli-density-realization/technical.tex`
- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I003-finite-pauli-density-realization/reviews/math_fidelity_review.md`
- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I003-finite-pauli-density-realization/reviews/lean_api_review.md`
- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I003-finite-pauli-density-realization/reviews/finite_sequential_directed_system_math_fidelity_review.md`
- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I003-finite-pauli-density-realization/reviews/finite_sequential_directed_system_lean_api_review.md`
- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I003-finite-pauli-density-realization/reviews/finite_sequential_norm_math_fidelity_review.md`
- `../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I003-finite-pauli-density-realization/reviews/finite_sequential_norm_lean_api_review.md`

## FF13--FF14 integration

FF13 and FF14 are integrated and independently adversarially approved.
`FiniteRegionPhasedPauliMatrices.lean` proves the finite-region summed-phase
normal form and identity padding. `FiniteRegionEmbeddingCoherence.lean`
proves the explicit entrywise restriction formula and directed-system
coherence for `finiteRegionEmbed`. Both remain finite-region statements;
full-word multiplication, support/locality, quasilocal completion, state, and
GNS construction remain open.

Verification passed:

```bash
lake env lean FiniteFiber/FiniteRegionEmbeddingCoherence.lean
lake env lean FiniteFiber/FiniteRegionPhasedPauliMatrices.lean
lake build FiniteFiber.FiniteRegionEmbeddingCoherence
lake build FiniteFiber.FiniteRegionPhasedPauliMatrices
lake build FiniteFiber
lake env lean tests/AxiomAudit.lean
lake build
```

Aristotle archive metadata claiming commit/push was not integrated.

## FF15 finite-region full-Pauli multiplication closeout

FF15 is accepted and integrated as
`FiniteFiber/FiniteRegionFullPauliMultiplication.lean`.  The quarantined
archive SHA-256 is
`d1189115efff732746653b26166b1c89a8e9c38b3d5af266c27b158db2ddc02f`;
the candidate module SHA-256 is
`bfa680e974985ce9e040cb0e7c93eb7bf828fa892be1e76131abc9a548cc7d94` and is
byte-identical to the live module.  Only that module and the raw archive were
adopted; remote metadata and all unrelated snapshot files remain quarantined.

The checked theorem `fullPauliRegionMatrix_mul F a b ha` has the explicit
premise `ha : a.label.support ⊆ F` and proves
`fullPauliRegionMatrix F (a * b) = fullPauliRegionMatrix F a *
fullPauliRegionMatrix F b`.  Its phase is the existing
`FullPauliWord.cocycle a.label b.label`; it therefore covers the packet's
intended case in which both words are supported in `F`.  The module also
proves the one-site raw `X`-then-`Z` multiplication relation, finite-region
projective multiplication, the identity-word image, and the image of
`FullPauliWord.negativeIdentity`.  It does not construct a support/local-
algebra identification, directed colimit, quasilocal completion, state/GNS
data, or finite-fiber conclusion.

Verification passed:

```bash
lake build FiniteFiber.FiniteRegionFullPauliMultiplication
lake build
lake env lean tests/AxiomAudit.lean
lake env lean tests/FullPauliMultiplicationAxiomAudit.lean
```

Both audits report only `propext`, `Classical.choice`, and `Quot.sound`.  The
closeout review is at
`../work/2026-08-finite-fiber-von-neumann-formalization/investigations/I004-countable-pauli-quasilocal-realization/aristotle_responses/FF15-live-closeout-adversarial-review.md`.
