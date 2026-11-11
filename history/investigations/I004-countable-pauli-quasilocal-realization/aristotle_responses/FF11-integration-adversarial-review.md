# FF11 candidate integration adversarial review

## Verdict

**APPROVED.**

## Candidate provenance and quarantine

- Aristotle project: `76d70d89-bf7a-490b-a1ee-6c3512437110`.
- Archive: `FF11-finite-region-pauli-matrices.tar.gz`.
- Archive SHA-256:
  `acaaeac3024447b211faf050224b9146e978d90c105da094a22b9226d84b529a`.
- Snapshot: `FF11-extracted/formalization_finite_fibers_aristotle/`.

Only `AristotleCandidates/FiniteRegionPauliMatrices.lean` was used.  It is
byte-identical to the live integrated file
`formalization_finite_fibers/FiniteFiber/FiniteRegionPauliMatrices.lean`
(SHA-256 `86ed3a1eaa5fec5017079f45122ad7d49224a9a9625781cae51860c7e6c91b14`).
The remote README attribution insertion, stale deletion of the FF11 status in
`HANDOFF.md`, `ARISTOTLE_SUMMARY.md`, and its unsupported commit/push claim
were rejected.  No remote metadata or publication status was adopted.

## Mathematical-fidelity review

The candidate is the exact finite-region phase-free object of the manuscript:
for `a : ↥F → PauliLabel`, it defines the matrix entry as the product of the
one-site entries over `↥F`.  This is coordinate-free and introduces no
noncanonical ordering.  The all-identity theorem correctly handles both the
diagonal and off-diagonal cases, including `F = empty`.  The self-adjointness
proof transports the checked one-site Hermiticity entrywise, including the
empty-region case.

For `F ⊆ F'`, the padding theorem has the correct orientation: it is stated
through the live reindexed `finiteRegionEmbed`, factors the site product over
`↥F ⊕ ↥(F' \ F)`, and gives the identity factor on the complement.  It also
covers the empty-complement case.

The phase boundary is preserved.  The module imports no `FullPauliLattice`
material and makes no multiplication, closure, group-homomorphism,
support/locality, coherence, colimit, state, GNS, or finite-projection claim.
In particular, it does not incorrectly identify the Hermitian `Y` label with
the phase-zero `X Z` normal form; the future `ZMod 4`/Y-count correction stays
open.

## Lean/API review and verification

Both independent reviewers approved the candidate.  The Lean/API review found
no blocker or major issue; the harmless `omit [DecidableEq Site]` on the
self-adjoint theorem only generalizes an unused assumption.

The following all passed in `formalization_finite_fibers`:

```bash
lake env lean FiniteFiber/FiniteRegionPauliMatrices.lean
lake build FiniteFiber.FiniteRegionPauliMatrices
lake build FiniteFiber
lake env lean tests/AxiomAudit.lean
lake build
```

The umbrella exports the new module and `tests/AxiomAudit.lean` audits all
three public theorems.  Their direct `#print axioms` results contain only
`propext`, `Classical.choice`, and `Quot.sound`.  The live source has no
`sorry`, `admit`, project-local `axiom`, `opaque`, `unsafe`, or
`implemented_by` declaration.

## Remaining boundary

FF11 establishes only phase-free finite-region Pauli-label matrices and their
one-inclusion identity padding.  The full phased normal-form representation,
matrix realization of actual stabilizer groups, syntactic support/local-algebra
membership, multi-region coherence, quasilocal completion/state, and the
GNS/corner hypotheses for the finite-projection theorem remain open.
