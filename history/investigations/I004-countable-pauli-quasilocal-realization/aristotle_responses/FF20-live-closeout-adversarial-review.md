# FF20 live closeout adversarial review

## Decision

**Accepted at the packet's stated conditional scope.**  The downloaded
Aristotle archive is retained in quarantine as
`FF20-stabilizer-support-corner-instantiation.tar.gz` (SHA-256
`5097660af857a567d1a2ef5a0f415a7377f358528459651af95d1c1246d548fb`) and
was extracted only under `FF20-extracted/`.  The only integrated source is
`formalization_finite_fibers/FiniteFiber/ActualStabilizerSupportCorner.lean`,
which is byte-identical to the candidate.  Remote metadata, source context,
README/HANDOFF differences, and the remote summary's commit/push assertion
were not integrated.

## Scope audit

The module connects the actual full-Pauli local system and FF19's conditional
quasilocal/GNS interface to the already checked support-corner result.  It
adds no axiom, `sorry`, `admit`, `opaque`, `unsafe`, or `implemented_by`
declaration.  It does not modify the manuscript.

### Proved in the live package

- `QuasilocalEmbedding.wordElement`, `embed_eq_wordElement`, `wordElement_one`,
  `wordElement_mul`, and `wordHom` give a region-independent unital
  multiplicative image of a `FullPauliWord`.
- `QuasilocalStabilizerState.stabilizerRepresentation`, `stabilizerAction`,
  `isSelfAdjoint_stabilizerRepresentation`,
  `stabilizerRepresentation_gnsVector`, and `stabilizerRepresentation_mem`
  give the represented actual stabilizer action, its self-adjointness, GNS
  vector invariance, and membership from the stated local-algebra containment.
- `actualStabilizerSystem_supportCornerConclusion_of_gnsOrbit` concludes
  `SupportCornerConclusion M q W.gnsVector` from exactly
  `W`, `M`, `hM`, finite `T`, `hmonotone`, `hstrong`, and
  `C : GNSOrbitConditions M q W.gnsVector`.
- `actualStabilizerSystem_canonicalSupportCornerConclusion_of_gnsOrbit` has
  the same inputs except that it uses the constructed decreasing strong limit
  and therefore has no `hstrong` premise.
- `actualStabilizerSystem_central_witness_of_gnsOrbit` restates the target:
  for `hz : IsCentralProjection M z` and `hz_nonzero : z != 0`, it returns
  `IsFiniteProjection M (z * q) /\\ z * q != 0 /\\ IsSubprojection (z * q) z`.
- `actualStabilizerSystem_semifinite_of_gnsOrbit` is the corresponding
  conditional `IsSemifinite M` corollary.

### Still conditional / not proved

The theorem does not construct the quasilocal completion or global state
(`Q`, `W`), the ambient regional von Neumann algebra and containment `hM`, an
exhausting finite subgroup sequence `T`, a noncanonical strong-limit proof
`hstrong`, or `GNSOrbitConditions` (in particular the regional/product-orbit
data, fullness, and corner traciality).  Thus it does **not** establish that
these inputs follow from the manuscript short-range condition; it also makes
no direct-integral or type-III claim.  This is the packet-required conditional
instantiation, not a completion of the global model.

## Checks

- `lake build FiniteFiber.ActualStabilizerSupportCorner` -- passed.
- `lake build` -- passed.
- `lake env lean tests/AxiomAudit.lean` -- passed; existing audited declarations
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for every public FF20 definition/theorem -- only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder scan of the candidate module -- no matches.

## Adversarial findings

No blocking finding.  The potential overclaim -- treating the FF19 interface
or the GNS-orbit conditions as constructed consequences of a short-range
model -- is avoided in both the declarations and module documentation.
Residual mathematical risk is precisely the unconstructed global hypotheses
listed above; successful compilation does not discharge them.
