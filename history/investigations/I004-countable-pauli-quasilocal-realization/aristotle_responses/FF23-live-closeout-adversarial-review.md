# FF23 live closeout adversarial review

## Decision

**Accepted at the packet's stated conditional scope.**  The completed archive
`FF23-no-type-three-central-summands.tar.gz` is retained in the designated
quarantine area with SHA-256
`0e7a6d09bce4d24beddf405e01d5f08fff03c0c82c5b8d5b4c2e20006b3cd039` and was
extracted only under `FF23-extracted/`.  No Lean build, dependency update, or
dependency fetch ran in that snapshot.

Only the reviewed candidate module was promoted as
`formalization_finite_fibers/FiniteFiber/FiniteRangeNoTypeIII.lean`, with the
required one-line umbrella import in `FiniteFiber.lean`.  Its declaration and
proof code agrees with the candidate; only its long explanatory comments were
shortened in the live module.  Remote metadata, `ARISTOTLE_SUMMARY.md`,
README/HANDOFF/manuscript changes, manifest/toolchain material, and every
other archive file were rejected.  The manuscript was not modified.

## Scope and exact checked interface

Let `R : FiniteRangeStabilizerSystem Site`,
`Q : QuasilocalEmbedding Site A`, and
`W : QuasilocalStabilizerState R.stabilizerSystem Q`.  The first two are
finite-range geometry and supplied quasilocal-completion data; the last is a
**supplied global stabilizer state**.  FF23 does not construct `Q` or `W`.

### Proved

- `not_summandHasNoNonzeroFiniteProjection_of_isSemifinite hM hz hz0` proves
  `¬ SummandHasNoNonzeroFiniteProjection M z` from exactly
  `hM : IsSemifinite M`, `hz : IsCentralProjection M z`, and `hz0 : z ≠ 0`.
  Here the definition is exactly
  `∀ e, IsFiniteProjection M e → IsSubprojection e z → e = 0`.
- `R.central_summand_finiteProjection_witness W z hz hz0` proves that the
  explicit `z * R.cornerProjection W` is finite in
  `W.localVonNeumannAlgebra`, nonzero, and below `z`.
- `R.central_summand_exists_nonzero_finiteProjection W z hz hz0` proves the
  packet target: every nonzero central `z` in the canonical GNS von Neumann
  algebra has a nonzero finite projection below it.
- `R.isSemifinite_localVonNeumannAlgebra W` packages that statement as
  `IsSemifinite W.localVonNeumannAlgebra`, and
  `R.not_summandHasNoNonzeroFiniteProjection W z hz hz0` derives the exact
  projection-level no-type-III-central-summand restatement.
- `R.cornerProjection_isFiniteProjection W` records the `z = 1` consequence.

These are direct applications of the FF22 checked declaration
`R.supportCornerConclusion_localVonNeumannAlgebra W`, whose conclusion is
`SupportCornerConclusion W.localVonNeumannAlgebra (R.cornerProjection W)
W.gnsVector`.  Thus no new normality, GNS-orbit, fullness, or corner-trace
premise was added or hidden by FF23.

### Conditional

For a general `M : VonNeumannAlgebra W.GNS`, FF23 proves the same witness,
semifiniteness, and projection-level exclusion in
`central_summand_finiteProjection_witness_of_generated`,
`isSemifinite_of_generated`, and
`not_summandHasNoNonzeroFiniteProjection_of_generated` only under exactly:

```text
hM : forall (F : Finset Site) (x : finiteRegionQubitAlgebra F),
  W.gnsRepresentation (Q.embed F x) in M
hgen : W.GeneratedByLocalAlgebra M
```

The canonical theorem has no *additional* premise because FF22 proves these
for `W.localVonNeumannAlgebra`, the bicommutant of the represented local
algebra.  It is nevertheless conditional on the supplied `Q` and `W` data.

### Blocked

The project does not yet construct a simultaneous infinite-lattice quasilocal
C-star completion and compatible global state, nor derive them from finite
range.  It also does not formalize a direct-integral decomposition, its
separability hypotheses, or a fibrewise type classification.  The module's
prose-only standard-decomposition consequence is therefore not a Lean theorem.

### Failed

No failed claim was integrated.  In particular, the module does not claim an
unconditional finite-range physical-model theorem independent of `Q` and `W`,
or a formal no-type-III-fibre theorem.

## Adversarial findings

No blocking defect found.  The load-bearing route is non-circular: FF23 calls
the pre-existing FF22 support-corner conclusion and extracts its
`central_witness`/`semifinite` fields; it does not invoke its own target.
The likely overclaim boundary was checked: ``unconditional'' applies only
after `R`, `Q`, and `W` have been supplied, and the live documentation says so.
Compilation was not treated as an independent construction of the missing
global state or as a direct-integral/type-classification proof.

## Live verification

All checks ran only in the already-built live package:

```text
lake build FiniteFiber.FiniteRangeNoTypeIII  # passed (3199 jobs)
lake build FiniteFiber                        # passed (3212 jobs)
lake build                                    # passed (3212 jobs)
lake env lean tests/AxiomAudit.lean           # passed
```

An explicit `#print axioms` audit of every FF23 public theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The candidate and live FF22
dependencies have identical SHA-256 hashes.  The candidate module and live
module were scanned for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
`implemented_by`, and `native_decide`; no match occurred.  `git diff --check`
passed.

## Cleanup

The archive and extracted dependency-free snapshot are intentional retained
raw response records.  The only live source changes are the FF23 module and
its umbrella import.  All pre-existing unrelated dirty and untracked work was
preserved; no commit, push, dependency change, or manuscript edit occurred.
