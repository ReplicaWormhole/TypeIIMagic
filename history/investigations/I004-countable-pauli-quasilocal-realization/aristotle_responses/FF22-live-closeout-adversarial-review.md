# FF22 live closeout adversarial review

## Decision

**Accepted at the packet's stated scope.**  The quarantined candidate
`FiniteFiber/FiniteRangeTracialCorner.lean` was byte-identical to the integrated
live module.  The raw archive is
`FF22-finite-range-tracial-corner-fullness.tar.gz` with SHA-256
`6768f9167fa40f7c7464855f7bf7590face3f8678a3916d706b419525142b238`; the
complete dependency-free snapshot remains under `FF22-extracted/` and was not
built or otherwise used as a dependency source.

## Scope and exact checked interface

The accepted module adds a project-local finite-tuple strong-density theorem
and bicommutant construction, then applies them to the FF21 concrete
finite-range support corner.  The candidate is the only imported source
module.  The required umbrella import and public `#print axioms` entries were
added locally; the remote README, handoff, manifest, manuscript, metadata, and
all other snapshot files were rejected.

For explicit `R : FiniteRangeStabilizerSystem Site`, quasilocal completion
`Q`, supplied `W : QuasilocalStabilizerState R.stabilizerSystem Q`, concrete
`M : VonNeumannAlgebra W.GNS`, and FF21 containment premise

```text
hM : forall (F : Finset Site) (x : finiteRegionQubitAlgebra F),
  W.gnsRepresentation (Q.embed F x) in M,
```

the exact new declarations are:

- **proved:** `R.cornerProjection_ne_zero' : R.cornerProjection W != 0`.
- **proved:** `R.cornerProjection_isFullProjection : IsFullProjection M
  (R.cornerProjection W)`.
- **proved, conditional:**
  `R.tracial_cornerProjection W M hM hgen ha hb`, where
  `hgen : W.GeneratedByLocalAlgebra M` and `ha`, `hb` are the exact
  `IsCornerElement M (R.cornerProjection W)` premises.
- **proved, conditional:**
  `R.faithful_cornerProjection W M hM hgen hx hzero`, where `hx` is an exact
  corner-element premise and
  `hzero : vectorFunctional W.gnsVector (star x * x) = 0`; it concludes
  `x = 0`.
- **proved, conditional:** `R.supportCornerConclusion W M hM hgen :
  SupportCornerConclusion M (R.cornerProjection W) W.gnsVector`.

The only added premise is explicitly defined as

```text
W.GeneratedByLocalAlgebra M :=
  forall x in M, forall t,
    (forall a in W.localOperatorAlgebra, a * t = t * a) -> x * t = t * x.
```

Together with `hM`, this identifies `M` with the bicommutant of the represented
local algebra.  This is necessary: FF21's containment premise alone permits a
larger algebra such as `B(H)`, for which the local approximation argument does
not establish corner traciality.

For the canonical constructed algebra
`W.localVonNeumannAlgebra = bicommutant W.localOperatorAlgebra`, that premise
is discharged by
`W.generatedByLocalAlgebra_localVonNeumannAlgebra`.  Hence the following are
**proved with no premise beyond the supplied `R`, `Q`, and `W` data**:

- `R.tracial_cornerProjection_localVonNeumannAlgebra`;
- `R.faithful_cornerProjection_localVonNeumannAlgebra`;
- `R.cornerProjection_isFullProjection_localVonNeumannAlgebra`; and
- `R.supportCornerConclusion_localVonNeumannAlgebra`.

The route is therefore stronger than FF20's prior conditional interface but
does not silently weaken it: the general-algebra form retains `hgen`, while the
canonical-bicommutant specialization proves that exact premise.  The packet's
three targets are met: nonzero support, full central support, and a faithful
tracial corner functional for the canonical `M_Gamma`.  No no-type-III claim is
introduced; FF23 remains responsible for that consequence.

## Adversarial findings

No blocking finding.

- The remote claim that its project was committed/pushed was not adopted.
- A compilation result alone was not treated as the mathematical result.  The
  proof route was checked for its critical scope boundary: the density argument
  only applies to the bicommutant, and this boundary is explicit in
  `GeneratedByLocalAlgebra` before the canonical specialization.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or `implemented_by` token
  occurs in either the candidate or its FF21 predecessor.  The new public
  declarations have explicit axiom-audit entries.

## Live verification

All commands were run only in the already-built live package:

```text
lake build FiniteFiber.FiniteRangeTracialCorner       # passed (3198 jobs)
lake build FiniteFiber.FiniteRangeSupportCornerConstruction  # passed
lake build FiniteFiber                                # passed (3211 jobs)
lake build                                            # passed (3211 jobs)
lake env lean tests/AxiomAudit.lean                   # passed
```

The audit prints only `propext`, `Classical.choice`, and `Quot.sound` for every
new FF22 declaration.  The candidate hash in the live tree is
`ff7797b79959e186083b9d408a5e5a5547b1195a9517edf97657f033d574b562`, equal to
the quarantined candidate hash.

## Residual risk and cleanup

This formalizes a conditional construction from a supplied quasilocal
completion/state and finite-range stabilizer system; it does not construct
those inputs from a physical lattice model, identify all finite local algebras
with the full global quasilocal algebra, or prove the FF23 no-type-III theorem.
Those are correctly outside FF22.  Pre-existing unrelated dirty/untracked
repository work was preserved.  No manuscript file was modified and no commit,
push, dependency update, or archive build was performed.
