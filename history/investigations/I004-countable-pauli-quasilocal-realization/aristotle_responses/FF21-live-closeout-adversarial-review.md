# FF21 live closeout adversarial review

## Decision

**Accepted at the packet's stated conditional scope.**  The completed remote
snapshot is retained only in quarantine as
`FF21-finite-range-support-corner-construction.tar.gz` (SHA-256
`6e7d73c1fbae016aad64c39ce1cf5dbeab1f61befd23ea45f5695a7f2deb8466`) and
was extracted only under `FF21-extracted/`.  No build, dependency update, or
other executable action was run in that snapshot.

Only the reviewed candidate module was integrated into the live package as
`formalization_finite_fibers/FiniteFiber/FiniteRangeSupportCornerConstruction.lean`.
It is byte-identical to the quarantined candidate.  `FiniteFiber.lean` was
changed only to import that module and its already-live FF20 dependency
`ActualStabilizerSupportCorner`.  Remote metadata, README/HANDOFF differences,
and `ARISTOTLE_SUMMARY.md` were not integrated.  The manuscript was not
modified.

## Exact checked interface and status

### Proved

- `FiniteRangeStabilizerSystem Site` packages a surjective enumeration,
  finite self-containing neighbourhoods, a consistent commuting involutive
  `FullPauliWord.StabilizerGeneratorData`, and the exact finite-range premise
  `forall g in generators, exists s, g.label.support subset neighborhood s`.
- `region`, `exhaustion`, `region_mono`, `mem_region`, and
  `exists_region_superset` give a finite monotone exhaustion.  The
  finite-range-specific conclusion is
  `generator_supportedIn_region`.
- `localStabilizer`, `localStabilizerFintype`, `localStabilizer_mono`,
  `exists_mem_localStabilizer`, and `iSup_localStabilizer` give the increasing
  finite local stabilizer sequence.  `LocallyGenerated` is recorded as an
  additional condition; only
  `closure_localGenerators_le_regionStabilizer` is derived from the stated
  data.
- Given the existing explicit interface inputs
  `W : QuasilocalStabilizerState R.stabilizerSystem Q`, `M`, and `hM`,
  `supportProjectionSequence` proves the decreasing represented support
  projections.  `cornerProjection` uses the already checked project-local
  `decreasingProjectionStrongLimit`; its strong convergence, membership and
  projection property, GNS-vector fixedness, and nonzero conclusion are
  respectively `stronglyTendsTo_cornerProjection`,
  `cornerProjection_isProjectionIn`, `cornerProjection_gnsVector`, and
  `cornerProjection_ne_zero`.
- With the still-explicit
  `C : GNSOrbitConditions M (R.cornerProjection W) W.gnsVector`, the exact
  target-facing declarations are
  `finiteRange_supportCornerConclusion_of_gnsOrbit` and
  `finiteRange_central_witness_of_gnsOrbit`.  The latter returns, for each
  nonzero central `z`, a finite nonzero subprojection
  `z * R.cornerProjection W` below `z`.

### Partial / conditional

The packet's geometric/operator-algebraic target is met: it supplies the
finite local sequence and a constructed nonzero candidate corner projection.
The final support-corner conclusion remains conditional on the already
explicit quasilocal completion/state interface `Q`, `W`, local containment
`hM`, and `GNSOrbitConditions` (notably product-orbit fullness and corner
traciality).  The strong-limit route is a project-local supporting theorem,
not a new axiom or an unproved premise.

### Blocked

No Lean obstruction remains for FF21.  The global analytic inputs above are
not blocked proof holes in this module; they are deliberately supplied
premises outside the packet's scope.

### Failed

No failed claim was integrated.  In particular, FF21 does not claim that
finite range supplies local-code equality, a trace, fullness, a type
classification, or a no-type-III theorem.

## Checks

- `lake build FiniteFiber.FiniteRangeSupportCornerConstruction` -- passed.
- `lake build FiniteFiber` -- passed.
- `lake build` -- passed.
- `lake env lean tests/AxiomAudit.lean` -- passed.
- Placeholder/forbidden-declaration scan of the candidate -- no match for
  `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `implemented_by`, or
  `native_decide`.
- `#print axioms` was run for every public FF21 theorem; each reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check` -- passed.

## Adversarial findings and residual risk

No blocking defect found.  The main potential overclaim was that finite range
alone might prove the converse local-generator equality or the analytic
GNS-orbit hypotheses.  The module isolates the former as `LocallyGenerated`
and keeps the latter in the theorem premises.  Compilation and axiom auditing
verify formal consistency only; they do not construct the quasilocal state or
discharge those analytic assumptions.

## Cleanup

The quarantine archive and extracted snapshot are intentional retained raw
response records.  Existing repository-wide dirty and untracked material was
preserved.  No commit, push, dependency fetch, or manuscript change occurred.
